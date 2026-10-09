import MA4RestartArrow20261003.AdjacentLeftMutation
import QuiverProofs.MAExistenceSupportChronology

/-! Actual finite left-sweep realization for one fixed category and exact
vertex functors. Only OLD actual realization is supplied. Uniform ambient
Hom/Ext finiteness and Euler identity must come from the actual model;
no next representation, branch, dimension, or ArrowSigns is assumed. -/
namespace QuiverProofs.MA4RestartArrow20261003.ActualLeftSweep
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open MAExistenceSupportChronology MAExistenceTeamBRootPositivity
open QuiverProofs.MA4RestartArrow20261003.AdjacentExceptionalFrame
open QuiverProofs.MA4RestartArrow20261003.SignedAdjacentLeftHom
open QuiverProofs.MA4RestartArrow20261003.AdjacentLeftMutation
universe w v u z
variable {K : Type w} [Field K] {C : Type u}
  [Category.{v} C] [Abelian C] [Linear K C] [HasExt.{z} C]
  [EnoughProjectives C] [HasFiniteBiproducts C]
set_option maxHeartbeats 0

noncomputable def vertexDimensions (F : Fin 4 → C ⥤ ModuleCat.{v} K) (X : C) : Vector4 :=
  fun a => (Module.finrank K ((F a).obj X) : Int)

/-- An actual ordered frame realizes the signed numerical columns. -/
def ActualRealization (F : Fin 4 → C ⥤ ModuleCat.{v} K) (D : Matrix 4) : Prop :=
  ∃ (M : Fin 4 → C) (s : Fin 4 → Int), ExceptionalFrame F M ∧ SignedDimensions F M D s

/-- The uniform MODEL Euler identity identifies the actually derived
Hom-minus-Ext coefficient with the original numerical leftMove coefficient. -/
theorem left_move_actual_realization
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
    ActualRealization F (leftMove U D t) := by
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
    adjacent_left_mutation F hZero hLimits hColimits hJointEpi M hM D s hSigned hHered t ht
  have hMove : leftColumns D (s t * s (t+1) * χ) t = leftMove U D t := by
    rw [← hWeight]
    rfl
  refine ⟨leftObjects M t Q, leftSigns s t sq, hNext, ?_⟩
  rw [← hMove]
  exact hDims

/-- Every one of the ten actual left intervals has a constructed full
exceptional-frame realization, with all future finite vertex spaces derived. -/
theorem left_sweep_actual_realization
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
    (D : Matrix 4) (t q : Fin 4) (hqt : q ≤ t) (hD : ActualRealization F D) :
    ActualRealization F (leftSweep U D t q) := by
  fin_cases t <;> fin_cases q <;> try omega
  all_goals simp only [leftSweep, Fin.reduceFinMk, ↓reduceIte]
  all_goals
    repeat first
      | exact hD
      | apply left_move_actual_realization F hZero hLimits hColimits hJointEpi
          hHered hFinite U hEuler _ _ (by decide)

/-- The terminal pivot negation changes its signed interpretation while
retaining the same actual objects and all exceptional-frame properties. -/
theorem negate_column_actual_realization
    (F : Fin 4 → C ⥤ ModuleCat.{v} K) (D : Matrix 4) (q : Fin 4)
    (hD : ActualRealization F D) : ActualRealization F (negateColumn D q) := by
  obtain ⟨M, s, hM, hSigned⟩ := hD
  let sn := fun j => if j = q then -s j else s j
  refine ⟨M, sn, hM, ?_⟩
  intro j
  by_cases hj : j = q
  · subst j
    constructor
    · rcases (hSigned q).1 with hs | hs <;> simp [sn, hs]
    · intro a
      rw [(hSigned q).2 a]
      simp [sn, negateColumn]
  · constructor
    · simpa [sn, hj] using (hSigned j).1
    · intro a
      simpa [sn, negateColumn, hj] using (hSigned j).2 a

theorem left_sweep_terminal_actual_realization
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
    (D : Matrix 4) (t q : Fin 4) (hqt : q ≤ t) (hD : ActualRealization F D) :
    ActualRealization F (negateColumn (leftSweep U D t q) q) :=
  negate_column_actual_realization F (leftSweep U D t q) q
    (left_sweep_actual_realization F hZero hLimits hColimits hJointEpi
      hHered hFinite U hEuler D t q hqt hD)

#print axioms left_move_actual_realization
#print axioms left_sweep_actual_realization
#print axioms negate_column_actual_realization
#print axioms left_sweep_terminal_actual_realization
end QuiverProofs.MA4RestartArrow20261003.ActualLeftSweep
