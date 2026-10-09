import MA4RestartArrow20261003.CurrentColorHom
import MA4RestartArrow20261003.LeftTracedReplacement
import MA4RestartEuler20261003.OldUnselectedPivotBoundary
namespace QuiverProofs.MA4RestartArrow20261003.CurrentColoredActualFrame
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open QuiverProofs MAExistenceLiterature MAExistenceCoefficients MAExistenceCompanions
open MAExistenceTeamBRootPositivity MAExistenceTeamDJointSeed MAExistenceSupportChronology
open MAExistenceTeamCTriangleOutside MAExistenceTeamCCertificateTransport
open MA4RestartWeightedQuiverModel MA4RestartFreePathProjectives MA4RestartModelExt MA4RestartResolvedModelEuler
open MA4RestartMatrixEuler
open MA4RestartActualSignedNormalization MA4RestartActualFrameNoThreeCycle
open MA4RestartArrow20261003.AdjacentExceptionalFrame MA4RestartArrow20261003.SignedAdjacentLeftHom
open MA4RestartArrow20261003.ActualLeftSweep MA4RestartArrow20261003.ActualFrameChronology
open MA4RestartArrow20261003.CurrentColorHom MA4RestartArrow20261003.LeftTracedReplacement
set_option maxHeartbeats 0
local instance actualHasExt (B : Matrix 4) (K : Type) [Field K] :
    HasExt.{0} (Representation B K) := representation_hasExt B K
local instance actualEnoughProjectives (B : Matrix 4) (K : Type) [Field K] :
    EnoughProjectives (Representation B K) := representation_enoughProjectives B K

local instance actualFiniteBiproducts (B : Matrix 4) (K : Type) [Field K] :
    HasFiniteBiproducts (Representation B K) := Abelian.hasFiniteBiproducts

theorem current_normalized_colored_frame
    (B₀ U : Matrix 4) (K : Type) [Field K] (hB₀ : SkewSymmetric B₀)
    (hs : Cosquare.add U (Cosquare.transpose U) = initialCompanion B₀)
    (ha : Cosquare.add U (Cosquare.scale (-1) (Cosquare.transpose U)) = reverse B₀)
    (w : List (Fin 4)) (hInv : SeedInv B₀ w)
    (hOld : UnorderedActualRealization (vertexFunctor B₀ K) (principalSeed B₀ w).2)
    (p : Relabeling 4) (hNumeric : OrderedRootFrame B₀ U (columnRelabel (principalSeed B₀ w).2 p)) :
    let D := columnRelabel (principalSeed B₀ w).2 p
    ∃ M : Fin 4 → Representation B₀ K,
      ExceptionalFrame (vertexFunctor B₀ K) M ∧
      (∀ a, dimensionVector B₀ K (M a) = fun b => colorSign (columnColor D) a * D b a) ∧
      (∀ a b, (Module.finrank K ((vertexFunctor B₀ K b).obj (M a)) : Int) =
        branchSign (columnColor D a) * D b a) ∧
      (∀ a b, a < b → columnColor D a = columnColor D b → ∀ f : M a ⟶ M b, f = 0) := by
  let D := columnRelabel (principalSeed B₀ w).2 p
  let B := (principalSeed B₀ w).1
  let A := coefficientCompanion B₀ (principalSeed B₀ w).2
  let E := coefficientBilinear U (principalSeed B₀ w).2
  let c := columnColor D
  obtain ⟨M,s,hM,hSigned⟩ := current_order_actual_realization (vertexFunctor B₀ K)
    (model_hereditary B₀ K) (model_finite_hom_ext B₀ K) U
    (model_euler_pairing B₀ K U hB₀ hs ha) _ p ⟨hNumeric.2.2.1,hNumeric.2.2.2⟩ hOld
  obtain ⟨hForced,hDim⟩ := actual_signed_dimensions_normalized B₀ K U D hNumeric.2.2.1 M s
    (fun a => (hSigned a).1) (fun a => (hSigned a).2)
  have hParts := coefficientBilinear_parts B₀ U B (principalSeed B₀ w).2 hs ha hInv.exchangeOrigin
  have hForward : ∀ a b, a < b → E (p.toFun a) (p.toFun b) = -B (p.toFun a) (p.toFun b) := by
    intro a b hab
    have hLower : E (p.toFun b) (p.toFun a) = 0 := by
      change coefficientBilinear U D b a = 0
      rw [coefficient_bilinear_pairing]; exact hNumeric.2.2.2 b a hab
    have h := congrFun (congrFun hParts.2 (p.toFun a)) (p.toFun b)
    change E (p.toFun a) (p.toFun b) + (-1) * E (p.toFun b) (p.toFun a) = -B (p.toFun a) (p.toFun b) at h
    rw [hLower] at h; omega
  have hComp : ∀ a b, a < b → (relabel A p) b a = -(relabel B p) a b := by
    intro a b hab
    have hLower : E (p.toFun b) (p.toFun a) = 0 := by
      change coefficientBilinear U D b a = 0
      rw [coefficient_bilinear_pairing]; exact hNumeric.2.2.2 b a hab
    have h := congrFun (congrFun hParts.1 (p.toFun b)) (p.toFun a)
    change E (p.toFun b) (p.toFun a) + E (p.toFun a) (p.toFun b) = A (p.toFun b) (p.toFun a) at h
    rw [hLower,hForward a b hab] at h
    change A _ _ = -B _ _; omega
  have hEuler : ∀ a b, a < b →
      (Module.finrank K (M a ⟶ M b) : Int) - (Module.finrank K (Ext (M a) (M b) 1) : Int) =
        -(if c a = c b then 1 else -1) * (relabel B p) a b := by
    intro a b hab
    have h := normalized_frame_model_euler B₀ K U D hB₀ hs ha M hM.finiteVertices hDim a b
    have hf : coefficientBilinear U D a b = -(relabel B p) a b := hForward a b hab
    rw [normalizedEuler,hf] at h
    change colorSign c a * colorSign c b * -(relabel B p) a b = _ at h
    cases hc : c a <;> cases hd : c b <;>
      simp only [colorSign,hc,hd,Bool.false_eq_true,Bool.true_eq_false,↓reduceIte,
        neg_mul,one_mul,neg_one_mul,neg_neg] at h ⊢ <;> omega
  have hSigns : ∀ a b, 0 < (relabel B p) a b →
      (0 < (relabel A p) a b ↔ c a = false ∧ c b = true) := by
    intro a b hab
    exact hInv.arrowSigns (p.toFun a) (p.toFun b) hab
  have hSame : ∀ a b, a < b → c a = c b → ∀ f : M a ⟶ M b, f = 0 := by
    intro a b hab hc
    exact same_color_hom_zero (vertexFunctor B₀ K) M hM (model_hereditary B₀ K)
      (relabel B p) (relabel A p) c (relabel_skew B p (principalSeed_skew B₀ hB₀ w)) hSigns
      (fun a b => Module.finrank K (M a ⟶ M b)) (fun a b => Module.finrank K (Ext (M a) (M b) 1))
      (fun a b => model_hom_finrank_zero_iff B₀ K _ _ (hM.finiteVertices a) (hM.finiteVertices b))
      (fun a b => model_ext_finrank_zero_iff B₀ K _ _ (hM.finiteVertices a) (hM.finiteVertices b))
      hEuler hComp a b hab hc
  refine ⟨M,hM,hDim,?_,hSame⟩
  intro a b
  have h := congrFun (hDim a) b
  exact h
#print axioms current_normalized_colored_frame
end QuiverProofs.MA4RestartArrow20261003.CurrentColoredActualFrame
