import MA4EulerMonoEpi01a0fee4
import MA4Coordinator20261003.ScalarEndomorphisms
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.LinearAlgebra.Basis.Basic

/-! Direct dual Hom-mutation map gates. The actual coevaluation is
`biproduct.lift` of a supplied full Hom basis. All finite cardinalities,
including zero, are allowed. No opposite category, map dichotomy premise,
replacement exceptionality, or root realization is used. -/
namespace QuiverProofs.MA4RestartArrow20261003.CoevaluationMap
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open CategoryTheory.Preadditive
universe w v u z
set_option maxHeartbeats 0

section Factorization
variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The actual image identity, target-End faithfulness and source division
endomorphisms imply the coevaluation-direction map dichotomy. -/
theorem mono_or_epi_of_factorization_identity {X I M : C}
    (π : X ⟶ I) [Epi π] (ι : I ⟶ M) [Mono ι]
    (a : I ⟶ X) (b : M ⟶ I)
    (hidentity : a ≫ π + ι ≫ b = 𝟙 I)
    (hfaith : Function.Injective (fun A : M ⟶ M => (π ≫ ι) ≫ A))
    (hdivision : ∀ d : X ⟶ X, d = 0 ∨ IsIso d) :
    Mono (π ≫ ι) ∨ Epi (π ≫ ι) := by
  rcases hdivision (π ≫ a) with hz | hi
  · have ha : a = 0 := (cancel_epi π).mp (by simpa using hz)
    have hb : ι ≫ b = 𝟙 I := by simpa only [ha, zero_comp, zero_add] using hidentity
    have hright : b ≫ ι = 𝟙 M := hfaith (by
      calc
        (π ≫ ι) ≫ (b ≫ ι) = π ≫ (ι ≫ b) ≫ ι := by simp only [Category.assoc]
        _ = (π ≫ ι) ≫ (𝟙 M) := by rw [hb]; simp)
    letI : Epi (b ≫ ι) := by rw [hright]; infer_instance
    letI : Epi ι := epi_of_epi b ι
    right
    infer_instance
  · letI := hi
    letI : Mono π := mono_of_mono π a
    left
    infer_instance
end Factorization

section LinearHom
variable {K : Type w} [Field K] {C : Type u}
  [Category.{v} C] [Preadditive C] [Linear K C]

/-- An independent Hom family detects maps from its target biproduct to
one summand. The statement also applies to the empty biproduct. -/
theorem coevaluation_comp_summand_eq_zero {J : Type} [Fintype J]
    (X Y : C) [HasBiproduct (fun _ : J => Y)]
    (f : J → (X ⟶ Y))
    (hEnd : ∀ g : Y ⟶ Y, ∃ c : K, g = c • 𝟙 Y)
    (hLin : LinearIndependent K f)
    (h : (⨁ fun _ : J => Y) ⟶ Y)
    (hh : biproduct.lift (f := fun _ : J => Y) f ≫ h = 0) : h = 0 := by
  classical
  choose c hc using fun j : J => hEnd (biproduct.ι (fun _ : J => Y) j ≫ h)
  have hs : ∑ j : J, c j • f j = 0 := by
    calc
      ∑ j : J, c j • f j =
          ∑ j : J, f j ≫ biproduct.ι (fun _ : J => Y) j ≫ h := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hc j]
        simp
      _ = biproduct.lift (f := fun _ : J => Y) f ≫ h := by
        rw [biproduct.lift_eq, sum_comp]
        simp only [Category.assoc]
      _ = 0 := hh
  have hz : ∀ j, c j = 0 := (Fintype.linearIndependent_iff.mp hLin) c hs
  apply biproduct.hom_ext' h 0
  intro j
  simp only [comp_zero, hc j, hz j, zero_smul]

/-- Target endomorphisms are detected by precomposition with the actual
coevaluation, using the independent maps and scalar End of the summand. -/
theorem end_precomp_coevaluation_eq_zero {J : Type} [Fintype J]
    (X Y : C) [HasBiproduct (fun _ : J => Y)]
    (f : J → (X ⟶ Y))
    (hEnd : ∀ g : Y ⟶ Y, ∃ c : K, g = c • 𝟙 Y)
    (hLin : LinearIndependent K f)
    (A : (⨁ fun _ : J => Y) ⟶ (⨁ fun _ : J => Y))
    (hA : biproduct.lift (f := fun _ : J => Y) f ≫ A = 0) : A = 0 := by
  apply biproduct.hom_ext A 0
  intro j
  simpa only [zero_comp] using coevaluation_comp_summand_eq_zero X Y f hEnd hLin
    (A ≫ biproduct.π (fun _ : J => Y) j) (by rw [← Category.assoc, hA, zero_comp])

theorem end_precomp_coevaluation_injective {J : Type} [Fintype J]
    (X Y : C) [HasBiproduct (fun _ : J => Y)]
    (f : J → (X ⟶ Y))
    (hEnd : ∀ g : Y ⟶ Y, ∃ c : K, g = c • 𝟙 Y)
    (hLin : LinearIndependent K f) :
    Function.Injective (fun A : (⨁ fun _ : J => Y) ⟶ (⨁ fun _ : J => Y) =>
      biproduct.lift (f := fun _ : J => Y) f ≫ A) := by
  intro A B hAB
  apply sub_eq_zero.mp
  apply end_precomp_coevaluation_eq_zero X Y f hEnd hLin
  simp only [comp_sub, hAB, sub_self]

/-- Fullness of the Hom basis gives the dual universal factorization. -/
theorem hom_basis_coevaluation_factor {J : Type} [Fintype J]
    (X Y : C) [HasBiproduct (fun _ : J => Y)]
    (f : Module.Basis J K (X ⟶ Y)) (g : X ⟶ Y) :
    ∃ h : (⨁ fun _ : J => Y) ⟶ Y,
      biproduct.lift (f := fun _ : J => Y) (fun j => f j) ≫ h = g := by
  classical
  refine ⟨biproduct.desc (fun j : J => f.repr g j • 𝟙 Y), ?_⟩
  rw [biproduct.lift_desc]
  simpa only [Linear.comp_smul, Category.comp_id] using f.sum_repr g
end LinearHom

section Ext
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]

/-- Vanishing in the first Ext argument passes to every finite biproduct
bicone. This is proved directly, with no opposite-category Ext transfer. -/
theorem ext_bicone_first_vanishes {J : Type*} [Fintype J] (U : C)
    {R : J → C} {c : Bicone R} (hc : c.IsBilimit) (n : ℕ)
    (hR : ∀ a, ∀ e : Ext (R a) U n, e = 0) :
    ∀ e : Ext c.pt U n, e = 0 := by
  intro e
  let E := Ext.biproductAddEquiv hc U n
  apply E.injective
  ext a
  simpa only [map_zero, Pi.zero_apply] using hR a (E e a)

theorem extOne_biproduct_first_vanishes {J : Type*} [Fintype J] (U : C)
    (R : J → C) [HasBiproduct R]
    (hR : ∀ a, ∀ e : Ext (R a) U 1, e = 0) :
    ∀ e : Ext (⨁ R) U 1, e = 0 :=
  ext_bicone_first_vanishes U (biproduct.isBilimit R) 1 hR

theorem mono_or_epi_of_reverse_extOne_zero {X M : C} (f : X ⟶ M)
    (hHered : ∀ T : C, HasProjectiveDimensionLT T 2)
    (hReverse : ∀ e : Ext M X 1, e = 0)
    (hfaith : Function.Injective (fun A : M ⟶ M => f ≫ A))
    (hdivision : ∀ d : X ⟶ X, d = 0 ∨ IsIso d) : Mono f ∨ Epi f := by
  obtain ⟨a, b, hab⟩ :=
    MA4EulerMonoEpi01a0fee4.image_identity_of_reverse_extOne_zero f hHered hReverse
  have hfac := Abelian.image.fac f
  have hfaith' : Function.Injective (fun A : M ⟶ M =>
      (Abelian.factorThruImage f ≫ Abelian.image.ι f) ≫ A) := by
    simpa only [hfac] using hfaith
  simpa only [hfac] using mono_or_epi_of_factorization_identity
    (Abelian.factorThruImage f) (Abelian.image.ι f) a b hab hfaith' hdivision
end Ext

section ActualCoevaluation
variable {K : Type w} [Field K] {C : Type u}
  [Category.{v} C] [Abelian C] [Linear K C] [HasExt.{z} C]

/-- An old Hom basis, scalar old endomorphisms and reverse Ext vanishing
construct the actual coevaluation dichotomy. No new-object data are input. -/
theorem hom_basis_coevaluation_mono_or_epi (X Y : C) (n : ℕ)
    [HasBiproduct (fun _ : Fin n => Y)]
    (f : Module.Basis (Fin n) K (X ⟶ Y))
    (hEndX : ∀ g : X ⟶ X, ∃ c : K, g = c • 𝟙 X)
    (hEndY : ∀ g : Y ⟶ Y, ∃ c : K, g = c • 𝟙 Y)
    (hHered : ∀ T : C, HasProjectiveDimensionLT T 2)
    (hReverse : ∀ e : Ext Y X 1, e = 0) :
    Mono (biproduct.lift (f := fun _ : Fin n => Y) (fun j => f j)) ∨
    Epi (biproduct.lift (f := fun _ : Fin n => Y) (fun j => f j)) :=
  mono_or_epi_of_reverse_extOne_zero _ hHered
    (extOne_biproduct_first_vanishes X (fun _ : Fin n => Y) (fun _ => hReverse))
    (end_precomp_coevaluation_injective X Y (fun j => f j) hEndY f.linearIndependent)
    (QuiverProofs.MACompletionScalarEndomorphisms.end_zero_or_iso_of_scalar_end X hEndX)

omit [HasExt C] in
/-- Reverse Hom vanishing and a nonzero old source exclude an isomorphism
for any map to the finite copies, including the zero-copy case. -/
theorem coevaluation_not_isIso (X Y : C) (n : ℕ)
    [HasBiproduct (fun _ : Fin n => Y)]
    (f : X ⟶ (⨁ fun _ : Fin n => Y))
    (hReverseHom : ∀ g : Y ⟶ X, g = 0) (hId : 𝟙 X ≠ 0) : ¬ IsIso f := by
  intro hi
  letI := hi
  have hinv : inv f = 0 := by
    apply biproduct.hom_ext' (inv f) 0
    intro j
    simpa only [comp_zero] using hReverseHom (biproduct.ι (fun _ : Fin n => Y) j ≫ inv f)
  apply hId
  calc
    𝟙 X = f ≫ inv f := (IsIso.hom_inv_id f).symm
    _ = 0 := by rw [hinv, comp_zero]

/-- The Hom mutation branches are strict using only old pair data. -/
theorem hom_basis_coevaluation_strict_branches (X Y : C) (n : ℕ)
    [HasBiproduct (fun _ : Fin n => Y)]
    (f : Module.Basis (Fin n) K (X ⟶ Y))
    (hEndX : ∀ g : X ⟶ X, ∃ c : K, g = c • 𝟙 X)
    (hEndY : ∀ g : Y ⟶ Y, ∃ c : K, g = c • 𝟙 Y)
    (hHered : ∀ T : C, HasProjectiveDimensionLT T 2)
    (hReverse : ∀ e : Ext Y X 1, e = 0)
    (hReverseHom : ∀ g : Y ⟶ X, g = 0) (hId : 𝟙 X ≠ 0) :
    let e := biproduct.lift (f := fun _ : Fin n => Y) (fun j => f j)
    (Mono e ∧ ¬ Epi e) ∨ (Epi e ∧ ¬ Mono e) := by
  dsimp only
  have hni := coevaluation_not_isIso X Y n
    (biproduct.lift (f := fun _ : Fin n => Y) (fun j => f j)) hReverseHom hId
  rcases hom_basis_coevaluation_mono_or_epi X Y n f hEndX hEndY hHered hReverse with hm | he
  · left
    refine ⟨hm, ?_⟩
    intro he
    letI := hm
    letI := he
    exact hni (isIso_of_mono_of_epi _)
  · right
    refine ⟨he, ?_⟩
    intro hm
    letI := hm
    letI := he
    exact hni (isIso_of_mono_of_epi _)
end ActualCoevaluation

#print axioms hom_basis_coevaluation_mono_or_epi
#print axioms hom_basis_coevaluation_strict_branches
end QuiverProofs.MA4RestartArrow20261003.CoevaluationMap
