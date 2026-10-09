import MA4RestartArrow20261003.AdjacentRightMutation
import MA4RestartArrow20261003.ActualFrameChronology
import QuiverProofs.MAExistenceSupportChronology

/-! Actual finite right-sweep realization for one fixed category and exact
vertex functors. Only OLD actual realization is supplied. Uniform ambient
Hom/Ext finiteness and Euler identity must come from the actual model;
no next representation, branch, dimension, or ArrowSigns is assumed. -/
namespace QuiverProofs.MA4RestartArrow20261003.ActualRightSweep
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open QuiverProofs MAExistenceSupportChronology MAExistenceTeamBRootPositivity
open MAExistenceLiterature MAExistenceCoefficients MAExistenceCompanions
open MAExistenceTeamDJointSeed Cosquare
open QuiverProofs.MA4RestartArrow20261003.AdjacentExceptionalFrame
open QuiverProofs.MA4RestartArrow20261003.SignedAdjacentRightHom
open QuiverProofs.MA4RestartArrow20261003.AdjacentRightMutation
open QuiverProofs.MA4RestartArrow20261003.AdjacentExceptionalRightFrame
open QuiverProofs.MA4RestartArrow20261003.ActualLeftSweep
open QuiverProofs.MA4RestartArrow20261003.ActualFrameChronology
universe w v u z
variable {K : Type w} [Field K] {C : Type u}
  [Category.{v} C] [Abelian C] [Linear K C] [HasExt.{z} C]
  [EnoughProjectives C] [HasFiniteBiproducts C]
set_option maxHeartbeats 0

/-- The uniform MODEL Euler identity identifies the actually derived
Hom-minus-Ext coefficient with the original numerical rightMove coefficient. -/
theorem right_move_actual_realization
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
    (U : Matrix 4)
    (hEuler : ∀ X Y : C,
      (∀ a, Module.Finite K ((F a).obj X)) →
      (∀ a, Module.Finite K ((F a).obj Y)) →
      pairing U (vertexDimensions F X) (vertexDimensions F Y) =
        (Module.finrank K (X ⟶ Y) : Int) - (Module.finrank K (Ext X Y 1) : Int))
    (D : Matrix 4) (t : Fin 4) (ht : t < 3) (hD : ActualRealization F D) :
    ActualRealization F (rightMove U D t) := by
  obtain ⟨M, s, hM, hSigned⟩ := hD
  have hFin := hFinite (M t) (M (t+1)) (hM.finiteVertices t) (hM.finiteVertices (t+1))
  letI := hFin.1
  letI := hFin.2
  let χ : Int := (Module.finrank K (M t ⟶ M (t+1)) : Int) -
    (Module.finrank K (Ext (M t) (M (t+1)) 1) : Int)
  have hx : vertexDimensions F (M t) = fun a => s t * column D t a := by
    funext a; exact (hSigned t).2 a
  have hy : vertexDimensions F (M (t+1)) = fun a => s (t+1) * column D (t+1) a := by
    funext a; exact (hSigned (t+1)).2 a
  have hFactor : pairing U (vertexDimensions F (M t)) (vertexDimensions F (M (t+1))) =
      s t * s (t+1) * pairing U (column D t) (column D (t+1)) := by
    rw [hx, hy]
    simp only [pairing]
    ring
  have he := hEuler (M t) (M (t+1)) (hM.finiteVertices t) (hM.finiteVertices (t+1))
  change pairing U (vertexDimensions F (M t)) (vertexDimensions F (M (t+1))) = χ at he
  rw [hFactor] at he
  have hWeight : pairing U (column D t) (column D (t+1)) = s t * s (t+1) * χ := by
    rcases (hSigned t).1 with hs | hs <;> rcases (hSigned (t+1)).1 with hs' | hs'
    all_goals simp only [hs, hs', one_mul, neg_one_mul, neg_neg] at he ⊢
    all_goals omega
  obtain ⟨Q, sq, hNext, hDims, hPos⟩ :=
    adjacent_right_mutation F hZero hLimits hColimits hJointEpi M hM D s hSigned hHered t ht
  have hMove : rightColumns D (s t * s (t+1) * χ) t = rightMove U D t := by
    rw [← hWeight]
    rfl
  refine ⟨rightObjects M t Q, rightSigns s t sq, hNext, ?_⟩
  rw [← hMove]
  exact hDims

/-- Every one of the ten actual right intervals has a constructed full
exceptional-frame realization, with all future finite vertex spaces derived. -/
theorem right_sweep_actual_realization
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
    (U : Matrix 4)
    (hEuler : ∀ X Y : C,
      (∀ a, Module.Finite K ((F a).obj X)) →
      (∀ a, Module.Finite K ((F a).obj Y)) →
      pairing U (vertexDimensions F X) (vertexDimensions F Y) =
        (Module.finrank K (X ⟶ Y) : Int) - (Module.finrank K (Ext X Y 1) : Int))
    (D : Matrix 4) (t q : Fin 4) (htq : t ≤ q) (hD : ActualRealization F D) :
    ActualRealization F (rightSweep U D t q) := by
  fin_cases t <;> fin_cases q <;> try omega
  all_goals simp only [rightSweep, Fin.reduceFinMk, ↓reduceIte]
  all_goals
    repeat first
      | exact hD
      | apply right_move_actual_realization F hZero hLimits hColimits hJointEpi
          hHered hFinite U hEuler _ _ (by decide)

theorem right_sweep_terminal_actual_realization
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
    (U : Matrix 4)
    (hEuler : ∀ X Y : C,
      (∀ a, Module.Finite K ((F a).obj X)) →
      (∀ a, Module.Finite K ((F a).obj Y)) →
      pairing U (vertexDimensions F X) (vertexDimensions F Y) =
        (Module.finrank K (X ⟶ Y) : Int) - (Module.finrank K (Ext X Y 1) : Int))
    (D : Matrix 4) (t q : Fin 4) (htq : t ≤ q) (hD : ActualRealization F D) :
    ActualRealization F (negateColumn (rightSweep U D t q) q) :=
  negate_column_actual_realization F (rightSweep U D t q) q
    (right_sweep_actual_realization F hZero hLimits hColimits hJointEpi
      hHered hFinite U hEuler D t q htq hD)

/-- The green chronological mutation has actual objects and the exact next
signed columns. All STATIC model hypotheses will be discharged once for
the fixed weighted path representation category. NEXT colored Hom/Ext and
ArrowSigns remain a separate unrestricted-preservation frontier. -/
theorem principalSeed_green_actual_realization
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
    (k : Fin 4) (hk : columnColor (principalSeed B₀ w).2 k = true) :
    ∃ (p : ProperOrder.CyclicOrder) (q : Fin 4) (htq : p.invFun k ≤ q),
      Compatible (principalSeed B₀ w).1 (columnColor (principalSeed B₀ w).2) k p ∧
      GreenBeforeRed (columnColor (principalSeed B₀ w).2) p ∧
      ActualRealization F (columnRelabel (principalSeed B₀ w).2 p) ∧
      (∀ r : Fin 4, p.invFun k ≤ r → r ≤ q →
        ActualRealization F (rightSweep U (columnRelabel (principalSeed B₀ w).2 p)
          (p.invFun k) r)) ∧
      ActualRealization F (columnRelabel (principalSeed B₀ (w ++ [k])).2
        (p.trans (rightPermutation (p.invFun k) q htq))) := by
  obtain ⟨p, q, htq, hp, hColors, hRoot, hRoots, hTerminal, hExact⟩ :=
    principalSeed_green_fullFrameSweep B₀ U hB₀ hs₀ ha₀ w hInv k hk
  have hCurrent := current_order_actual_realization F hHered hFinite U hEuler
    (principalSeed B₀ w).2 p hRoot.2.2 hOld
  have hSweeps := fun r (htr : p.invFun k ≤ r) =>
    right_sweep_actual_realization F hZero hLimits hColimits hJointEpi
      hHered hFinite U hEuler _ (p.invFun k) r htr hCurrent
  refine ⟨p, q, htq, hp, hColors, hCurrent, (fun r htr _ => hSweeps r htr), ?_⟩
  rw [← hExact]
  exact negate_column_actual_realization F _ q (hSweeps q htq)

theorem principalSeed_green_unordered_actual_realization
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
    (k : Fin 4) (hk : columnColor (principalSeed B₀ w).2 k = true) :
    UnorderedActualRealization F (principalSeed B₀ (w ++ [k])).2 := by
  obtain ⟨p, q, htq, hp, hc, hOldOrder, hSweeps, hNext⟩ :=
    principalSeed_green_actual_realization F hZero hLimits hColimits hJointEpi
      hHered hFinite B₀ U hEuler hB₀ hs₀ ha₀ w hInv hOld k hk
  exact ⟨p.trans (rightPermutation (p.invFun k) q htq), hNext⟩

#print axioms principalSeed_green_actual_realization
#print axioms principalSeed_green_unordered_actual_realization
#print axioms right_move_actual_realization
#print axioms right_sweep_actual_realization
#print axioms right_sweep_terminal_actual_realization
end QuiverProofs.MA4RestartArrow20261003.ActualRightSweep
