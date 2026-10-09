import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.LocalRing.Basic

/-! Scalar, division and local endomorphism gates from explicit one-dimensional
Hom data. No root, exceptional realization, rigidity or Euler identity is
constructed by these statements; norm alone supplies none of these premises. -/
namespace QuiverProofs.MACompletionScalarEndomorphisms
open CategoryTheory
universe w v u
variable {K : Type w} [Field K] {C : Type u}
  [Category.{v} C] [Preadditive C] [Linear K C]

/-- A nonzero identity spans a one-dimensional endomorphism space. -/
theorem scalar_end_of_finrank_one (R : C) [Module.Finite K (R ⟶ R)]
    (hId : (𝟙 R : R ⟶ R) ≠ 0) (hDim : Module.finrank K (R ⟶ R) = 1) :
    ∀ g : R ⟶ R, ∃ c : K, g = c • 𝟙 R := by
  intro g
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero'
    (𝟙 R : R ⟶ R) hId).mp hDim g
  exact ⟨c, hc.symm⟩

/-- Scalar endomorphisms over a field are zero or isomorphisms. -/
theorem end_zero_or_iso_of_scalar_end (R : C)
    (hEnd : ∀ g : R ⟶ R, ∃ c : K, g = c • 𝟙 R) :
    ∀ g : R ⟶ R, g = 0 ∨ IsIso g := by
  intro g
  obtain ⟨c, rfl⟩ := hEnd g
  by_cases hc : c = 0
  · left; simp [hc]
  · right
    refine ⟨⟨c⁻¹ • 𝟙 R, ?_, ?_⟩⟩
    · simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp,
        smul_smul, inv_mul_cancel₀ hc, one_smul]
    · simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp,
        smul_smul, mul_inv_cancel₀ hc, one_smul]

/-- The same explicit scalar property and nonzero identity supply the local
End ring needed by the ordinary hereditary map theorem. -/
theorem local_end_of_scalar_end (R : C)
    (hId : (𝟙 R : R ⟶ R) ≠ 0)
    (hEnd : ∀ g : R ⟶ R, ∃ c : K, g = c • 𝟙 R) :
    IsLocalRing (End R) := by
  letI : Nontrivial (End R) := ⟨⟨1, 0, hId⟩⟩
  apply IsLocalRing.of_surjective' (algebraMap K (End R))
  intro g
  obtain ⟨c, hc⟩ := hEnd g
  refine ⟨c, ?_⟩
  rw [Algebra.algebraMap_eq_smul_one]
  exact hc.symm

#print axioms scalar_end_of_finrank_one
#print axioms end_zero_or_iso_of_scalar_end
#print axioms local_end_of_scalar_end
end QuiverProofs.MACompletionScalarEndomorphisms
