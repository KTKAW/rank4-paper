import Mathlib.CategoryTheory.Abelian.Projective.Dimension

/-! Narrow hereditary exactness fact for the proposed absent-leg evaluation
argument. It is an abstract categorical lemma; no realization from the current
SeedInv, universal evaluation map, or uniform arrow supplier is claimed. -/
namespace QuiverProofs.MA4Arrow20261003.AbsentEvaluationExt
open CategoryTheory CategoryTheory.Abelian
universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- If U has projective dimension at most one, Ext1(U,-) vanishing passes
from the middle to the quotient in any short exact sequence. -/
theorem extOne_quotient_vanishes (U : C) [HasProjectiveDimensionLT U 2]
    {S : ShortComplex C} (hS : S.ShortExact)
    (h₂ : ∀ e : Ext U S.X₂ 1, e = 0) :
    ∀ e : Ext U S.X₃ 1, e = 0 := by
  intro e
  obtain ⟨x, hx⟩ := Ext.covariant_sequence_exact₃ U hS e (show 1 + 1 = 2 from rfl)
    (Ext.eq_zero_of_hasProjectiveDimensionLT _ 2 (by rfl))
  rw [← hx, h₂ x, Ext.zero_comp]

/-- A target with nonzero Ext1(U,-) cannot be the quotient of an
Ext1(U,-)-orthogonal middle object under the same hereditary assumption. -/
theorem no_shortExact_of_nonzero_extOne (U : C) [HasProjectiveDimensionLT U 2]
    {S : ShortComplex C} (h₂ : ∀ e : Ext U S.X₂ 1, e = 0)
    (h₃ : ∃ e : Ext U S.X₃ 1, e ≠ 0) : ¬ S.ShortExact := by
  intro hS
  obtain ⟨e, he⟩ := h₃
  exact he (extOne_quotient_vanishes U hS h₂ e)

/-- The evaluation-argument consumer: no epimorphism from an Ext1-orthogonal
object to an object with nonzero Ext1, for a source of projective dimension
at most one. No assertion constructs this categorical data from SeedInv. -/
theorem no_epi_of_nonzero_extOne (U M V : C) [HasProjectiveDimensionLT U 2]
    (g : M ⟶ V) (hM : ∀ e : Ext U M 1, e = 0)
    (hV : ∃ e : Ext U V 1, e ≠ 0) : ¬ Epi g := by
  intro hg
  letI := hg
  exact no_shortExact_of_nonzero_extOne U
    (S := ShortComplex.mk (CategoryTheory.Limits.kernel.ι g) g
      (CategoryTheory.Limits.kernel.condition g)) hM hV
    { exact := ShortComplex.exact_kernel g }

#print axioms extOne_quotient_vanishes
#print axioms no_shortExact_of_nonzero_extOne
#print axioms no_epi_of_nonzero_extOne
end QuiverProofs.MA4Arrow20261003.AbsentEvaluationExt
