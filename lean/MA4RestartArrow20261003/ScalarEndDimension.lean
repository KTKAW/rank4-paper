import MA4Coordinator20261003.ScalarEndomorphisms
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! Convert a proved scalar-End replacement into finite End and End
finrank one. This uses its actual nonzero identity; no root-norm inference. -/
namespace QuiverProofs.MA4RestartArrow20261003.ScalarEndDimension
open CategoryTheory
open Module Submodule
universe w v u
variable {K : Type w} [Field K] {C : Type u}
  [Category.{v} C] [Preadditive C] [Linear K C]

/-- Actual scalar endomorphisms export finiteness of End. -/
theorem finite_end_of_scalar_end (Q : C)
    (hEnd : ∀ g : Q ⟶ Q, ∃ c : K, g = c • 𝟙 Q) :
    Module.Finite K (Q ⟶ Q) := by
  apply Module.Finite.of_surjective (LinearMap.toSpanSingleton K (Q ⟶ Q) (𝟙 Q))
  intro g
  obtain ⟨c, hc⟩ := hEnd g
  exact ⟨c, hc.symm⟩

/-- The proved nonzero identity and scalar End give the actual End rank. -/
theorem end_finrank_one_of_scalar_end (Q : C) (hId : 𝟙 Q ≠ 0)
    (hEnd : ∀ g : Q ⟶ Q, ∃ c : K, g = c • 𝟙 Q) :
    Module.finrank K (Q ⟶ Q) = 1 := by
  apply (finrank_eq_one_iff_of_nonzero' (𝟙 Q) hId).mpr
  intro g
  obtain ⟨c, hc⟩ := hEnd g
  exact ⟨c, hc.symm⟩

#print axioms finite_end_of_scalar_end
#print axioms end_finrank_one_of_scalar_end
end QuiverProofs.MA4RestartArrow20261003.ScalarEndDimension
