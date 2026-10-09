import MA4RestartArrow20261003.AdjacentExceptionalFrame
import MA4RestartArrow20261003.SignedLeftShear

/-! Actual whole-frame left Hom construction with exact signed-column
bookkeeping. The coefficient is the actual Hom-basis multiplicity. -/
namespace QuiverProofs.MA4RestartArrow20261003.SignedAdjacentLeftHom
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open QuiverProofs.MA4RestartArrow20261003.AdjacentExceptionalFrame
open QuiverProofs.MA4RestartArrow20261003.SignedLeftShear
universe w v u z
variable {K : Type w} [Field K] {C : Type u}
  [Category.{v} C] [Abelian C] [Linear K C] [HasExt.{z} C]
set_option maxHeartbeats 0

/-- Exact old object interpretation for a signed four-column frame. -/
def SignedDimensions (F : Fin 4 → C ⥤ ModuleCat.{v} K) (M : Fin 4 → C)
    (D : Fin 4 → Fin 4 → Int) (s : Fin 4 → Int) : Prop :=
  ∀ j, (s j = 1 ∨ s j = -1) ∧
    ∀ a, (Module.finrank K ((F a).obj (M j)) : Int) = s j * D a j

def leftColumns (D : Fin 4 → Fin 4 → Int) (m : Int) (t : Fin 4) :
    Fin 4 → Fin 4 → Int := fun a j =>
  if j = t then D a (t+1) else if j = t+1 then D a t - m * D a (t+1) else D a j

def leftSigns (s : Fin 4 → Int) (t : Fin 4) (sq : Int) : Fin 4 → Int := fun j =>
  if j = t then s (t+1) else if j = t+1 then sq else s j

/-- The full old basis determines actual Hom dimension, including n=0. -/
theorem hom_basis_multiplicity (X Y : C) (n : ℕ)
    (f : Module.Basis (Fin n) K (X ⟶ Y)) :
    Module.Finite K (X ⟶ Y) ∧ Module.finrank K (X ⟶ Y) = n := by
  exact ⟨Module.Finite.of_basis f, by simpa using Module.finrank_eq_card_basis f⟩

/-- Construct the actual adjacent frame and signs for the signed column
shear from old finite, rigid scalar-End objects. The positive representative
at every vertex and the actual Hom coefficient are derived, not supplied. -/
theorem signed_left_hom_adjacent
    (F : Fin 4 → C ⥤ ModuleCat.{v} K)
    (hZero : ∀ a, (F a).PreservesZeroMorphisms)
    (hLimits : ∀ a, PreservesFiniteLimits (F a))
    (hColimits : ∀ a, PreservesFiniteColimits (F a))
    (hJointEpi : ∀ {M V : C} (e : M ⟶ V), (∀ a, Epi ((F a).map e)) → Epi e)
    (M : Fin 4 → C) (hM : ExceptionalFrame F M)
    (D : Fin 4 → Fin 4 → Int) (s : Fin 4 → Int)
    (hD : SignedDimensions F M D s)
    (hHered : ∀ T : C, HasProjectiveDimensionLT T 2)
    (t : Fin 4) (ht : t < 3) (n : ℕ)
    [HasBiproduct (fun _ : Fin n => M (t+1))]
    (f : Module.Basis (Fin n) K (M t ⟶ M (t+1)))
    (hForward : ∀ x : Ext (M t) (M (t+1)) 1, x = 0) :
    let e := biproduct.lift (f := fun _ : Fin n => M (t+1)) (fun j => f j)
    ∃ (Q : C) (sq : Int),
      ((Mono e ∧ ¬ Epi e ∧ Q = cokernel e) ∨
       (Epi e ∧ ¬ Mono e ∧ Q = kernel e)) ∧
      ExceptionalFrame F (leftObjects M t Q) ∧
      SignedDimensions F (leftObjects M t Q)
        (leftColumns D (s t * s (t+1) * (n : Int)) t) (leftSigns s t sq) ∧
      Module.finrank K (M t ⟶ M (t+1)) = n ∧
      (∃ a, 0 < Module.finrank K ((F a).obj Q)) := by
  let u := fun a => s t * D a t
  let v := fun a => s (t+1) * D a (t+1)
  obtain ⟨Q, hBranch, hFrame, hDim, hPos⟩ :=
    left_hom_adjacent_frame F hZero hLimits hColimits hJointEpi M hM hHered t ht n f
      hForward u v (hD t).2 (hD (t+1)).2
  obtain ⟨sq, hSq, hQ⟩ := signed_left_shear_normalization
    (fun a => D a t) (fun a => D a (t+1)) u v
    (fun a => (Module.finrank K ((F a).obj Q) : Int))
    (s t) (s (t+1)) (n : Int) (hD t).1 (hD (t+1)).1
    (fun _ => rfl) (fun _ => rfl) hDim
  have ht1 : t < t+1 := by fin_cases t <;> simp_all
  have hAt : leftObjects M t Q t = M (t+1) := by simp [leftObjects]
  have hNext : leftObjects M t Q (t+1) = Q := by simp [leftObjects, ne_of_gt ht1]
  have hSigned : SignedDimensions F (leftObjects M t Q)
      (leftColumns D (s t * s (t+1) * (n : Int)) t) (leftSigns s t sq) := by
    intro j
    by_cases hj : j = t
    · subst j
      constructor
      · simpa [leftSigns] using (hD (t+1)).1
      · intro a
        rw [hAt]
        simpa [leftSigns, leftColumns] using (hD (t+1)).2 a
    · by_cases hj1 : j = t+1
      · subst j
        constructor
        · simpa [leftSigns, ne_of_gt ht1] using hSq
        · intro a
          rw [hNext]
          simpa [leftSigns, leftColumns, ne_of_gt ht1] using hQ a
      · have he : leftObjects M t Q j = M j := by simp [leftObjects, hj, hj1]
        constructor
        · simpa [leftSigns, hj, hj1] using (hD j).1
        · intro a
          rw [he]
          simpa [leftSigns, leftColumns, hj, hj1] using (hD j).2 a
  exact ⟨Q, sq, hBranch, hFrame, hSigned, (hom_basis_multiplicity _ _ n f).2, hPos⟩

#print axioms hom_basis_multiplicity
#print axioms signed_left_hom_adjacent
end QuiverProofs.MA4RestartArrow20261003.SignedAdjacentLeftHom
