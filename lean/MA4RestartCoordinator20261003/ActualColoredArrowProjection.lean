import MA4RestartCoordinator20261003.ColoredArrowProjection
import MA4RestartEuler20261003.ResolvedModelEuler
import MA4RestartArrow20261003.AdjacentExceptionalFrame
import QuiverProofs.MAExistenceTeamBRootOrderClosure
import QuiverProofs.MAExistenceTeamCTriangleOutside

/-! Derive the numerical arrow rule from actual ordered objects. The color
block and same-color Hom vanishing are the explicit categorical facts that
the chronological construction must preserve. No numerical arrow rule or
new seed invariant is supplied to this projection. -/
namespace QuiverProofs.MA4RestartActualColoredArrowProjection
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open ProperOrder MAExistenceLiterature MAExistenceCompanions
open MAExistenceTeamBRootPositivity MAExistenceTeamBRootOrderClosure
open MAExistenceTeamCTriangleOutside
open MAExistenceCoefficients MAExistenceTeamDJointSeed
open MAExistenceTeamCCertificateTransport MAExistenceTeamCRootSigns
open MA4RestartWeightedQuiverModel MA4RestartModelExt MA4RestartMatrixEuler
open MA4RestartResolvedModelEuler MA4RestartColoredArrowProjection
open MA4RestartArrow20261003.AdjacentExceptionalFrame
set_option maxHeartbeats 0

local instance actualHasExt (B : Matrix 4) (K : Type) [Field K] :
    HasExt.{0} (Representation B K) := representation_hasExt B K

private theorem actual_hom_finrank_zero (B : Matrix 4) (K : Type) [Field K]
    (X Y : Representation B K) (h : ∀ f : X ⟶ Y, f = 0) :
    Module.finrank K (X ⟶ Y) = 0 := by
  letI : Subsingleton (X ⟶ Y) := ⟨fun f g => by rw [h f,h g]⟩
  exact Module.finrank_zero_of_subsingleton (R := K) (M := X ⟶ Y)

private theorem actual_ext_finrank_zero (B : Matrix 4) (K : Type) [Field K]
    (X Y : Representation B K) (h : ∀ e : Ext X Y 1, e = 0) :
    Module.finrank K (Ext X Y 1) = 0 := by
  letI : Subsingleton (Ext X Y 1) := ⟨fun e f => by rw [h e,h f]⟩
  exact Module.finrank_zero_of_subsingleton (R := K) (M := Ext X Y 1)

theorem arrowSigns_of_actual_colored_frame
    (B₀ U B C : Matrix 4) (K : Type) [Field K]
    (hB₀ : SkewSymmetric B₀) (hB : SkewSymmetric B)
    (hs : Cosquare.add U (Cosquare.transpose U) = initialCompanion B₀)
    (ha : Cosquare.add U (Cosquare.scale (-1) (Cosquare.transpose U)) = reverse B₀)
    (hOrigin : B = Cosquare.mul (Cosquare.mul (Cosquare.transpose C) B₀) C)
    (p : CyclicOrder) (g : Colors)
    (M : Fin 4 → Representation B₀ K)
    (hFrame : ExceptionalFrame (vertexFunctor B₀ K) M)
    (hDims : ∀ a b, (Module.finrank K ((vertexFunctor B₀ K b).obj (M a)) : Int) =
      colorSign g (p.toFun a) * C b (p.toFun a))
    (hSameHom : ∀ a b, a < b → g (p.toFun a) = g (p.toFun b) →
      ∀ f : M a ⟶ M b, f = 0)
    (hBlock : GreenBeforeRed g p) :
    ArrowSigns B (coefficientCompanion B₀ C) g := by
  let E : Matrix 4 := fun i j => pairing U (column C i) (column C j)
  have hFactor (a b : Fin 4) :
      colorSign g (p.toFun a) * colorSign g (p.toFun b) * E (p.toFun a) (p.toFun b) =
        (Module.finrank K (M a ⟶ M b) : Int) - (Module.finrank K (Ext (M a) (M b) 1) : Int) := by
    have hx : dimensionVector B₀ K (M a) =
        fun x => colorSign g (p.toFun a) * column C (p.toFun a) x := by
      funext x
      exact hDims a x
    have hy : dimensionVector B₀ K (M b) =
        fun x => colorSign g (p.toFun b) * column C (p.toFun b) x := by
      funext x
      exact hDims b x
    calc
      _ = pairing U (dimensionVector B₀ K (M a)) (dimensionVector B₀ K (M b)) := by
        rw [hx,hy]
        simp only [E,pairing]
        ring
      _ = _ := model_euler_pairing B₀ K U hB₀ hs ha (M a) (M b)
        (hFrame.finiteVertices a) (hFrame.finiteVertices b)
  have hParts := eulerParts_of_origin B₀ U B C hs ha hOrigin
  refine arrowSigns_of_colored_upper_euler B (coefficientCompanion B₀ C) E g hB p
    (fun i j => (hParts i j).1) (fun i j => (hParts i j).2) ?_ ?_ hBlock
  · intro a b hab
    have hf := hFactor b a
    rw [actual_hom_finrank_zero B₀ K (M b) (M a) (hFrame.reverseHom a b hab),
      actual_ext_finrank_zero B₀ K (M b) (M a) (hFrame.reverseExt a b hab)] at hf
    cases hca : g (p.toFun a) <;> cases hcb : g (p.toFun b) <;>
      simp only [colorSign,hca,hcb,Bool.false_eq_true,↓reduceIte] at hf <;> omega
  · intro a b hab hColor
    have hf := hFactor a b
    have hMul : colorSign g (p.toFun a) * colorSign g (p.toFun b) = 1 := by
      unfold colorSign
      rw [← hColor]
      cases hc : g (p.toFun a) <;> simp [hc]
    rw [hMul,one_mul,
      actual_hom_finrank_zero B₀ K (M a) (M b) (hSameHom a b hab hColor)] at hf
    omega

/-- Exact original chronology: the next exchange origin is derived from
the old six-field invariant before any next arrow rule is established. -/
theorem chronological_next_arrowSigns_of_actual_colored_frame
    (B₀ U : Matrix 4) (K : Type) [Field K]
    (hB₀ : SkewSymmetric B₀)
    (hs : Cosquare.add U (Cosquare.transpose U) = initialCompanion B₀)
    (ha : Cosquare.add U (Cosquare.scale (-1) (Cosquare.transpose U)) = reverse B₀)
    (w : List (Fin 4)) (hOld : SeedInv B₀ w) (k : Fin 4)
    (p : CyclicOrder) (M : Fin 4 → Representation B₀ K)
    (hFrame : ExceptionalFrame (vertexFunctor B₀ K) M)
    (hDims : ∀ a b, (Module.finrank K ((vertexFunctor B₀ K b).obj (M a)) : Int) =
      colorSign (columnColor (principalSeed B₀ (w ++ [k])).2) (p.toFun a) *
        (principalSeed B₀ (w ++ [k])).2 b (p.toFun a))
    (hSameHom : ∀ a b, a < b →
      columnColor (principalSeed B₀ (w ++ [k])).2 (p.toFun a) =
        columnColor (principalSeed B₀ (w ++ [k])).2 (p.toFun b) →
      ∀ f : M a ⟶ M b, f = 0)
    (hBlock : GreenBeforeRed (columnColor (principalSeed B₀ (w ++ [k])).2) p) :
    ArrowSigns (principalSeed B₀ (w ++ [k])).1
      (coefficientCompanion B₀ (principalSeed B₀ (w ++ [k])).2)
      (columnColor (principalSeed B₀ (w ++ [k])).2) := by
  have hC := seedInv_signCoherent B₀ hB₀ w hOld
  have hOrigin := exchange_coefficientBasis_update B₀ (principalSeed B₀ w).1
    (principalSeed B₀ w).2 (principalSeed_skew B₀ hB₀ w)
    (columnColor (principalSeed B₀ w).2) k
    (fun hk => ((color_iff_green hC k).mp hk).1)
    (fun hk => ((color_iff_red hC k).mp hk).1) hOld.exchangeOrigin
  have he : principalSeed B₀ (w ++ [k]) = mutateSeed (principalSeed B₀ w) k :=
    evolve_append_singleton B₀ identityCoefficients w k
  have hOriginNext : (principalSeed B₀ (w ++ [k])).1 =
      Cosquare.mul (Cosquare.mul (Cosquare.transpose (principalSeed B₀ (w ++ [k])).2) B₀)
        (principalSeed B₀ (w ++ [k])).2 := by
    simpa only [he,mutateSeed] using hOrigin
  exact arrowSigns_of_actual_colored_frame B₀ U
    (principalSeed B₀ (w ++ [k])).1 (principalSeed B₀ (w ++ [k])).2 K
    hB₀ (principalSeed_skew B₀ hB₀ (w ++ [k])) hs ha hOriginNext p
    (columnColor (principalSeed B₀ (w ++ [k])).2) M hFrame hDims hSameHom hBlock

#check arrowSigns_of_actual_colored_frame
#print axioms arrowSigns_of_actual_colored_frame
#check chronological_next_arrowSigns_of_actual_colored_frame
#print axioms chronological_next_arrowSigns_of_actual_colored_frame
end QuiverProofs.MA4RestartActualColoredArrowProjection
