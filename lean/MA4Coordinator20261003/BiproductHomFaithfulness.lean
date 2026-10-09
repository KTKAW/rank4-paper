import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Basis.Basic

/-! The evaluation endomorphism-injectivity gate, on an actual finite
biproduct and supplied independent Hom maps. No realization, pair purity,
Hom dimension, or scalar-endomorphism property is constructed from roots. -/
namespace QuiverProofs.MACompletionBiproductHomFaithfulness
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
universe w v u
variable {K : Type w} [Field K] {C : Type u}
  [Category.{v} C] [Preadditive C] [Linear K C]
set_option maxHeartbeats 0

/-- A finite independent evaluation family detects every source
endomorphism when every endomorphism of the summand is scalar. -/
theorem end_postcomp_evaluation_eq_zero {J : Type} [Fintype J]
    (R V : C) [HasBiproduct (fun _ : J => R)]
    (f : J → (R ⟶ V))
    (hEnd : ∀ g : R ⟶ R, ∃ c : K, g = c • 𝟙 R)
    (hLin : LinearIndependent K f)
    (A : (⨁ fun _ : J => R) ⟶ (⨁ fun _ : J => R))
    (hA : A ≫ biproduct.desc (f := fun _ : J => R) f = 0) : A = 0 := by
  classical
  choose c hc using fun i j : J =>
    hEnd (biproduct.ι (fun _ : J => R) i ≫ A ≫ biproduct.π (fun _ : J => R) j)
  apply biproduct.hom_ext' A 0
  intro i
  apply biproduct.hom_ext _ _
  intro j
  have hs : ∑ b : J, c i b • f b = 0 := by
    calc
      ∑ b : J, c i b • f b =
          ∑ b : J, (biproduct.ι (fun _ : J => R) i ≫ A ≫
            biproduct.π (fun _ : J => R) b) ≫ f b := by
        apply Finset.sum_congr rfl
        intro b _
        rw [hc i b]
        simp
      _ = biproduct.ι (fun _ : J => R) i ≫ A ≫
          biproduct.desc (f := fun _ : J => R) f := by
        rw [biproduct.desc_eq (f := fun _ : J => R) (g := f), comp_sum, comp_sum]
        simp only [Category.assoc]
      _ = 0 := by rw [hA, comp_zero]
  have hz : c i j = 0 := (Fintype.linearIndependent_iff.mp hLin) (c i) hs j
  simp only [comp_zero, zero_comp, Category.assoc, hc i j, hz, zero_smul]

theorem end_postcomp_evaluation_injective {J : Type} [Fintype J]
    (R V : C) [HasBiproduct (fun _ : J => R)]
    (f : J → (R ⟶ V))
    (hEnd : ∀ g : R ⟶ R, ∃ c : K, g = c • 𝟙 R)
    (hLin : LinearIndependent K f) :
    Function.Injective (fun A : (⨁ fun _ : J => R) ⟶ (⨁ fun _ : J => R) =>
      A ≫ biproduct.desc (f := fun _ : J => R) f) := by
  intro A B hAB
  apply sub_eq_zero.mp
  apply end_postcomp_evaluation_eq_zero R V f hEnd hLin
  simp only [sub_comp, hAB, sub_self]

/-- A supplied full Hom basis gives the gate for the actual biproduct map.
No assertion realizes this basis or the summand from numerical root data. -/
theorem hom_basis_evaluation_end_faithfulness {J : Type} [Fintype J]
    (R V : C) [HasBiproduct (fun _ : J => R)]
    (f : Module.Basis J K (R ⟶ V))
    (hEnd : ∀ g : R ⟶ R, ∃ c : K, g = c • 𝟙 R) :
    ∀ A : (⨁ fun _ : J => R) ⟶ (⨁ fun _ : J => R),
      A ≫ biproduct.desc (f := fun _ : J => R) (fun j => f j) = 0 → A = 0 :=
  fun A hA => end_postcomp_evaluation_eq_zero R V (fun j => f j)
    hEnd f.linearIndependent A hA

#print axioms end_postcomp_evaluation_eq_zero
#print axioms end_postcomp_evaluation_injective
#print axioms hom_basis_evaluation_end_faithfulness
end QuiverProofs.MACompletionBiproductHomFaithfulness
