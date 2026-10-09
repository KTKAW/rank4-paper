import MA4RestartArrow20261003.ActualLeftSweep
import MA4RestartArrow20261003.FrameReordering

/-! Actual old-to-new chronology, with current SeedInv used only to select
its actual compatible sweep. Realization is a separate OLD joint-induction
field, initialized by actual original simples. No current static SeedInv
alone supplies objects; NEXT ArrowSigns is not assumed or concluded here. -/
namespace QuiverProofs.MA4RestartArrow20261003.ActualFrameChronology
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open QuiverProofs MAExistenceSupportChronology MAExistenceTeamBRootPositivity
open MAExistenceTeamDJointSeed MAExistenceCoefficients MAExistenceCompanions
open MAExistenceLiterature MAExistenceTeamBAdjacentHurwitz Cosquare
open QuiverProofs.MA4RestartArrow20261003.AdjacentExceptionalFrame
open QuiverProofs.MA4RestartArrow20261003.SignedAdjacentLeftHom
open QuiverProofs.MA4RestartArrow20261003.ActualLeftSweep
open QuiverProofs.MA4RestartArrow20261003.FrameReordering
universe w v u z
variable {K : Type w} [Field K] {C : Type u}
  [Category.{v} C] [Abelian C] [Linear K C] [HasExt.{z} C]
  [EnoughProjectives C] [HasFiniteBiproducts C]
set_option maxHeartbeats 0

/-- OLD actual objects in some exceptional order; it makes no numerical
invariant or color claim and is not a root-realization oracle. -/
def UnorderedActualRealization (F : Fin 4 → C ⥤ ModuleCat.{v} K)
    (D : Matrix 4) : Prop := ∃ p : Relabeling 4, ActualRealization F (columnRelabel D p)

theorem reorder_actual_realization
    (F : Fin 4 → C ⥤ ModuleCat.{v} K)
    (hHered : ∀ T : C, HasProjectiveDimensionLT T 2)
    (hFinite : ∀ X Y : C,
      (∀ a, Module.Finite K ((F a).obj X)) →
      (∀ a, Module.Finite K ((F a).obj Y)) →
      Module.Finite K (X ⟶ Y) ∧ Module.Finite K (Ext X Y 1))
    (U : Matrix 4)
    (hEuler : ∀ X Y : C,
      (∀ a, Module.Finite K ((F a).obj X)) →
      (∀ a, Module.Finite K ((F a).obj Y)) →
      pairing U (vertexDimensions F X) (vertexDimensions F Y) =
        (Module.finrank K (X ⟶ Y) : Int) - (Module.finrank K (Ext X Y 1) : Int))
    (D : Matrix 4) (p : Relabeling 4)
    (hUpper : EulerUnitUpper U (columnRelabel D p))
    (hD : ActualRealization F D) : ActualRealization F (columnRelabel D p) := by
  obtain ⟨M, s, hM, hSigned⟩ := hD
  let dH := fun a b => Module.finrank K (M a ⟶ M b)
  let dE := fun a b => Module.finrank K (Ext (M a) (M b) 1)
  have hHZ : ∀ a b, dH a b = 0 ↔ ∀ f : M a ⟶ M b, f = 0 := by
    intro a b
    letI := (hFinite (M a) (M b) (hM.finiteVertices a) (hM.finiteVertices b)).1
    exact Module.finrank_zero_iff.trans ⟨fun h f => @Subsingleton.elim _ h f 0,
      fun h => ⟨fun f g => by rw [h f, h g]⟩⟩
  have hEZ : ∀ a b, dE a b = 0 ↔ ∀ x : Ext (M a) (M b) 1, x = 0 := by
    intro a b
    letI := (hFinite (M a) (M b) (hM.finiteVertices a) (hM.finiteVertices b)).2
    exact Module.finrank_zero_iff.trans ⟨fun h x => @Subsingleton.elim _ h x 0,
      fun h => ⟨fun x y => by rw [h x, h y]⟩⟩
  let pe : Fin 4 ≃ Fin 4 := ⟨p.toFun, p.invFun, p.left_inv, p.right_inv⟩
  have hOldUpper : ∀ a b, a < b →
      (dH (pe b) (pe a) : Int) - (dE (pe b) (pe a) : Int) = 0 := by
    intro a b hab
    have hx : vertexDimensions F (M (pe b)) = fun r => s (pe b) * column D (pe b) r := by
      funext r; exact (hSigned (pe b)).2 r
    have hy : vertexDimensions F (M (pe a)) = fun r => s (pe a) * column D (pe a) r := by
      funext r; exact (hSigned (pe a)).2 r
    have he := hEuler (M (pe b)) (M (pe a)) (hM.finiteVertices (pe b)) (hM.finiteVertices (pe a))
    change _ = (dH (pe b) (pe a) : Int) - (dE (pe b) (pe a) : Int) at he
    rw [← he, hx, hy]
    have hz : pairing U (column D (pe b)) (column D (pe a)) = 0 := hUpper.2 b a hab
    have hFactor : pairing U (fun r => s (pe b) * column D (pe b) r)
        (fun r => s (pe a) * column D (pe a) r) =
        s (pe b) * s (pe a) * pairing U (column D (pe b)) (column D (pe a)) := by
      simp only [pairing]; ring
    rw [hFactor, hz]
    ring
  refine ⟨(fun a => M (pe a)), (fun a => s (pe a)),
    exceptional_frame_reorder F M hM hHered dH dE hHZ hEZ pe hOldUpper, ?_⟩
  intro a
  exact ⟨(hSigned (pe a)).1, (hSigned (pe a)).2⟩

theorem current_order_actual_realization
    (F : Fin 4 → C ⥤ ModuleCat.{v} K)
    (hHered : ∀ T : C, HasProjectiveDimensionLT T 2)
    (hFinite : ∀ X Y : C,
      (∀ a, Module.Finite K ((F a).obj X)) →
      (∀ a, Module.Finite K ((F a).obj Y)) →
      Module.Finite K (X ⟶ Y) ∧ Module.Finite K (Ext X Y 1))
    (U : Matrix 4)
    (hEuler : ∀ X Y : C,
      (∀ a, Module.Finite K ((F a).obj X)) →
      (∀ a, Module.Finite K ((F a).obj Y)) →
      pairing U (vertexDimensions F X) (vertexDimensions F Y) =
        (Module.finrank K (X ⟶ Y) : Int) - (Module.finrank K (Ext X Y 1) : Int))
    (D : Matrix 4) (p : Relabeling 4)
    (hUpper : EulerUnitUpper U (columnRelabel D p))
    (hD : UnorderedActualRealization F D) : ActualRealization F (columnRelabel D p) := by
  obtain ⟨q, hQ⟩ := hD
  let r : Relabeling 4 := q.symm.trans p
  have hRel : columnRelabel (columnRelabel D q) r = columnRelabel D p := by
    funext a j
    exact congrArg (D a) (q.right_inv (p.toFun j))
  have hUpper' : EulerUnitUpper U (columnRelabel (columnRelabel D q) r) := by
    rw [hRel]; exact hUpper
  have hNext := reorder_actual_realization F hHered hFinite U hEuler
    (columnRelabel D q) r hUpper' hQ
  rw [hRel] at hNext
  exact hNext

/-- The red chronological mutation has actual objects and the exact next
signed columns. All STATIC model hypotheses will be discharged once for
the fixed weighted path representation category. NEXT colored Hom/Ext and
ArrowSigns remain a separate unrestricted-preservation frontier. -/
theorem principalSeed_red_actual_realization
    (F : Fin 4 → C ⥤ ModuleCat.{v} K)
    (hZero : ∀ a, (F a).PreservesZeroMorphisms)
    (hLimits : ∀ a, PreservesFiniteLimits (F a))
    (hColimits : ∀ a, PreservesFiniteColimits (F a))
    (hJointEpi : ∀ {M V : C} (e : M ⟶ V), (∀ a, Epi ((F a).map e)) → Epi e)
    (hHered : ∀ T : C, HasProjectiveDimensionLT T 2)
    (hFinite : ∀ X Y : C,
      (∀ a, Module.Finite K ((F a).obj X)) →
      (∀ a, Module.Finite K ((F a).obj Y)) →
      Module.Finite K (X ⟶ Y) ∧ Module.Finite K (Ext X Y 1))
    (B₀ U : Matrix 4)
    (hEuler : ∀ X Y : C,
      (∀ a, Module.Finite K ((F a).obj X)) →
      (∀ a, Module.Finite K ((F a).obj Y)) →
      pairing U (vertexDimensions F X) (vertexDimensions F Y) =
        (Module.finrank K (X ⟶ Y) : Int) - (Module.finrank K (Ext X Y 1) : Int))
    (hB₀ : SkewSymmetric B₀)
    (hs₀ : add U (transpose U) = initialCompanion B₀)
    (ha₀ : add U (scale (-1) (transpose U)) = reverse B₀)
    (w : List (Fin 4)) (hInv : SeedInv B₀ w)
    (hOld : UnorderedActualRealization F (principalSeed B₀ w).2)
    (k : Fin 4) (hk : columnColor (principalSeed B₀ w).2 k = false) :
    ∃ (p : ProperOrder.CyclicOrder) (q : Fin 4) (hqt : q ≤ p.invFun k),
      Compatible (principalSeed B₀ w).1 (columnColor (principalSeed B₀ w).2) k p ∧
      GreenBeforeRed (columnColor (principalSeed B₀ w).2) p ∧
      ActualRealization F (columnRelabel (principalSeed B₀ w).2 p) ∧
      (∀ r : Fin 4, q ≤ r → r ≤ p.invFun k →
        ActualRealization F (leftSweep U (columnRelabel (principalSeed B₀ w).2 p)
          (p.invFun k) r)) ∧
      ActualRealization F (columnRelabel (principalSeed B₀ (w ++ [k])).2
        (p.trans (leftPermutation (p.invFun k) q hqt))) := by
  obtain ⟨p, q, hqt, hp, hColors, hRoot, hRoots, hTerminal, hExact⟩ :=
    principalSeed_red_fullFrameSweep B₀ U hB₀ hs₀ ha₀ w hInv k hk
  have hCurrent := current_order_actual_realization F hHered hFinite U hEuler
    (principalSeed B₀ w).2 p hRoot.2.2 hOld
  have hSweeps := fun r (hrt : r ≤ p.invFun k) =>
    left_sweep_actual_realization F hZero hLimits hColimits hJointEpi
      hHered hFinite U hEuler _ (p.invFun k) r hrt hCurrent
  refine ⟨p, q, hqt, hp, hColors, hCurrent, (fun r _ hrt => hSweeps r hrt), ?_⟩
  rw [← hExact]
  exact negate_column_actual_realization F _ q (hSweeps q hqt)

theorem principalSeed_red_unordered_actual_realization
    (F : Fin 4 → C ⥤ ModuleCat.{v} K)
    (hZero : ∀ a, (F a).PreservesZeroMorphisms)
    (hLimits : ∀ a, PreservesFiniteLimits (F a))
    (hColimits : ∀ a, PreservesFiniteColimits (F a))
    (hJointEpi : ∀ {M V : C} (e : M ⟶ V), (∀ a, Epi ((F a).map e)) → Epi e)
    (hHered : ∀ T : C, HasProjectiveDimensionLT T 2)
    (hFinite : ∀ X Y : C,
      (∀ a, Module.Finite K ((F a).obj X)) →
      (∀ a, Module.Finite K ((F a).obj Y)) →
      Module.Finite K (X ⟶ Y) ∧ Module.Finite K (Ext X Y 1))
    (B₀ U : Matrix 4)
    (hEuler : ∀ X Y : C,
      (∀ a, Module.Finite K ((F a).obj X)) →
      (∀ a, Module.Finite K ((F a).obj Y)) →
      pairing U (vertexDimensions F X) (vertexDimensions F Y) =
        (Module.finrank K (X ⟶ Y) : Int) - (Module.finrank K (Ext X Y 1) : Int))
    (hB₀ : SkewSymmetric B₀)
    (hs₀ : add U (transpose U) = initialCompanion B₀)
    (ha₀ : add U (scale (-1) (transpose U)) = reverse B₀)
    (w : List (Fin 4)) (hInv : SeedInv B₀ w)
    (hOld : UnorderedActualRealization F (principalSeed B₀ w).2)
    (k : Fin 4) (hk : columnColor (principalSeed B₀ w).2 k = false) :
    UnorderedActualRealization F (principalSeed B₀ (w ++ [k])).2 := by
  obtain ⟨p, q, hqt, hp, hc, hOldOrder, hSweeps, hNext⟩ :=
    principalSeed_red_actual_realization F hZero hLimits hColimits hJointEpi
      hHered hFinite B₀ U hEuler hB₀ hs₀ ha₀ w hInv hOld k hk
  exact ⟨p.trans (leftPermutation (p.invFun k) q hqt), hNext⟩

#print axioms principalSeed_red_unordered_actual_realization
#print axioms reorder_actual_realization
#print axioms current_order_actual_realization
#print axioms principalSeed_red_actual_realization
end QuiverProofs.MA4RestartArrow20261003.ActualFrameChronology
