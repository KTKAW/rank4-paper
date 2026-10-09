import Mathlib.CategoryTheory.Abelian.Projective.Dimension

/-! The exact class-valued hereditary bound from a genuine projective SES. -/
universe w v u
namespace MA4RestartEuler20261003
open CategoryTheory CategoryTheory.Abelian
variable {C : Type u} [Category.{v} C] [Abelian C]

lemma projective_length_one_dimension_bound {S : ShortComplex C}
    (hS : S.ShortExact) [Projective S.X₁] [Projective S.X₂] :
    HasProjectiveDimensionLT S.X₃ 2 := by
  exact hS.hasProjectiveDimensionLT_X₃ 1 inferInstance inferInstance

lemma projective_length_one_ordinary_ext_bound [HasExt.{w} C]
    {S : ShortComplex C} (hS : S.ShortExact) [Projective S.X₁] [Projective S.X₂]
    (N : C) (n : ℕ) (hn : 2 ≤ n) (e : Ext S.X₃ N n) : e = 0 := by
  letI := projective_length_one_dimension_bound hS
  exact Ext.eq_zero_of_hasProjectiveDimensionLT e 2 hn

lemma global_hereditary_ordinary_ext_bound [HasExt.{w} C]
    (hHered : ∀ T : C, HasProjectiveDimensionLT T 2)
    (X Y : C) (n : ℕ) (hn : 2 ≤ n) (e : Ext X Y n) : e = 0 := by
  letI := hHered X
  exact Ext.eq_zero_of_hasProjectiveDimensionLT e 2 hn

#print axioms projective_length_one_dimension_bound
#print axioms projective_length_one_ordinary_ext_bound
end MA4RestartEuler20261003
