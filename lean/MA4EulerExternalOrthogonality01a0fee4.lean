import Mathlib.CategoryTheory.Abelian.Projective.Dimension

/-! Actual Hom/Ext orthogonality with unchanged objects across a short exact
sequence, then at arbitrary finite-copy maps' chosen kernels and cokernels.
No pair purity, next frame, root realization or dimensions are assumed. -/
namespace MA4EulerExternalOrthogonality01a0fee4
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
set_option maxHeartbeats 0

/-- Right orthogonality passes from both first terms to the quotient.
The Ext1 boundary comes from Hom of the first term; no hereditary bound. -/
theorem quotient_outside_orthogonality {S : ShortComplex C} (hS : S.ShortExact) (T : C)
    (hM : (∀ f : S.X₁ ⟶ T, f = 0) ∧ (∀ e : Ext S.X₁ T 1, e = 0))
    (hV : (∀ f : S.X₂ ⟶ T, f = 0) ∧ (∀ e : Ext S.X₂ T 1, e = 0)) :
    (∀ f : S.X₃ ⟶ T, f = 0) ∧ (∀ e : Ext S.X₃ T 1, e = 0) := by
  letI := hS.epi_g
  constructor
  · intro f
    apply (cancel_epi S.g).mp
    simpa only [comp_zero] using hV.1 (S.g ≫ f)
  · intro e
    obtain ⟨y, hy⟩ := Ext.contravariant_sequence_exact₃ hS T e (hV.2 _)
      (show 1 + 0 = 1 from rfl)
    have hy0 : y = 0 := by
      rw [← Ext.mk₀_homEquiv₀_apply y, hM.1 (Ext.homEquiv₀ y), Ext.mk₀_zero]
    rw [← hy, hy0, Ext.comp_zero]

/-- Left orthogonality passes to the quotient under the bound on the fixed
outside source T. The bound controls Ext2(T,first term). -/
theorem quotient_inside_orthogonality (T : C) [HasProjectiveDimensionLT T 2]
    {S : ShortComplex C} (hS : S.ShortExact)
    (hM : (∀ f : T ⟶ S.X₁, f = 0) ∧ (∀ e : Ext T S.X₁ 1, e = 0))
    (hV : (∀ f : T ⟶ S.X₂, f = 0) ∧ (∀ e : Ext T S.X₂ 1, e = 0)) :
    (∀ f : T ⟶ S.X₃, f = 0) ∧ (∀ e : Ext T S.X₃ 1, e = 0) := by
  constructor
  · intro f
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₃ T hS (Ext.mk₀ f)
      (show 0 + 1 = 1 from rfl) (hM.2 _)
    have hy0 : y = 0 := by
      rw [← Ext.mk₀_homEquiv₀_apply y, hV.1 (Ext.homEquiv₀ y), Ext.mk₀_zero]
    apply (Ext.mk₀_bijective T S.X₃).injective
    rw [Ext.mk₀_zero, ← hy, hy0, Ext.zero_comp]
  · intro e
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₃ T hS e
      (show 1 + 1 = 2 from rfl)
      (Ext.eq_zero_of_hasProjectiveDimensionLT _ 2 (by rfl))
    rw [← hy, hV.2 y, Ext.zero_comp]

/-- Right orthogonality passes from the middle and quotient to the subobject
under the bound on the quotient S.X3, controlling Ext2(S.X3,T). -/
theorem kernel_outside_orthogonality {S : ShortComplex C}
    [HasProjectiveDimensionLT S.X₃ 2] (hS : S.ShortExact) (T : C)
    (hM : (∀ f : S.X₂ ⟶ T, f = 0) ∧ (∀ e : Ext S.X₂ T 1, e = 0))
    (hV : (∀ f : S.X₃ ⟶ T, f = 0) ∧ (∀ e : Ext S.X₃ T 1, e = 0)) :
    (∀ f : S.X₁ ⟶ T, f = 0) ∧ (∀ e : Ext S.X₁ T 1, e = 0) := by
  constructor
  · intro f
    obtain ⟨y, hy⟩ := Ext.contravariant_sequence_exact₁ hS T (Ext.mk₀ f)
      (show 1 + 0 = 1 from rfl) (hV.2 _)
    have hy0 : y = 0 := by
      rw [← Ext.mk₀_homEquiv₀_apply y, hM.1 (Ext.homEquiv₀ y), Ext.mk₀_zero]
    apply (Ext.mk₀_bijective S.X₁ T).injective
    rw [Ext.mk₀_zero, ← hy, hy0, Ext.comp_zero]
  · intro e
    obtain ⟨y, hy⟩ := Ext.contravariant_sequence_exact₁ hS T e
      (show 1 + 1 = 2 from rfl)
      (Ext.eq_zero_of_hasProjectiveDimensionLT _ 2 (by rfl))
    rw [← hy, hM.2 y, Ext.comp_zero]

/-- Left orthogonality passes from the middle and quotient to the kernel.
The Ext1 boundary comes from Hom(T,quotient); no hereditary bound. -/
theorem kernel_inside_orthogonality (T : C) {S : ShortComplex C} (hS : S.ShortExact)
    (hM : (∀ f : T ⟶ S.X₂, f = 0) ∧ (∀ e : Ext T S.X₂ 1, e = 0))
    (hV : (∀ f : T ⟶ S.X₃, f = 0) ∧ (∀ e : Ext T S.X₃ 1, e = 0)) :
    (∀ f : T ⟶ S.X₁, f = 0) ∧ (∀ e : Ext T S.X₁ 1, e = 0) := by
  letI := hS.mono_f
  constructor
  · intro f
    apply (cancel_mono S.f).mp
    simpa only [zero_comp] using hM.1 (f ≫ S.f)
  · intro e
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ T hS e (hM.2 _)
      (show 0 + 1 = 1 from rfl)
    have hy0 : y = 0 := by
      rw [← Ext.mk₀_homEquiv₀_apply y, hV.1 (Ext.homEquiv₀ y), Ext.mk₀_zero]
    rw [← hy, hy0, Ext.zero_comp]

/-- Any actual finite biproduct preserves Hom/Ext vanishing in the source
variable, including an empty family. -/
theorem finite_biproduct_outside_orthogonality {J : Type*} [Fintype J]
    (R : J → C) [HasBiproduct R] (T : C)
    (hR : ∀ j, (∀ f : R j ⟶ T, f = 0) ∧ (∀ e : Ext (R j) T 1, e = 0)) :
    (∀ f : (⨁ R) ⟶ T, f = 0) ∧ (∀ e : Ext (⨁ R) T 1, e = 0) := by
  constructor
  · intro f
    apply biproduct.hom_ext' f 0
    intro j
    simpa only [comp_zero] using (hR j).1 (biproduct.ι R j ≫ f)
  · intro e
    let E := Ext.biproductAddEquiv (biproduct.isBilimit R) T 1
    apply E.injective
    ext j
    simpa only [map_zero, Pi.zero_apply] using (hR j).2 (E e j)

/-- Any actual finite biproduct preserves Hom/Ext vanishing in the target
variable, including an empty family. -/
theorem finite_biproduct_inside_orthogonality {J : Type*} [Fintype J]
    (T : C) (R : J → C) [HasBiproduct R]
    (hR : ∀ j, (∀ f : T ⟶ R j, f = 0) ∧ (∀ e : Ext T (R j) 1, e = 0)) :
    (∀ f : T ⟶ (⨁ R), f = 0) ∧ (∀ e : Ext T (⨁ R) 1, e = 0) := by
  constructor
  · intro f
    apply biproduct.hom_ext f 0
    intro j
    simpa only [zero_comp] using (hR j).1 (f ≫ biproduct.π R j)
  · intro e
    let E := Ext.addEquivBiproduct T (biproduct.isBilimit R) 1
    apply E.injective
    ext j
    simpa only [map_zero, Pi.zero_apply] using (hR j).2 (E e j)

/-- Actual monic map from n copies; its chosen cokernel stays orthogonal to
an unchanged outside target whenever both old objects were orthogonal. -/
theorem copies_cokernel_outside_orthogonality (R V T : C) (n : Nat)
    [HasBiproduct (fun _ : Fin n => R)]
    (e : (⨁ fun _ : Fin n => R) ⟶ V) [Mono e]
    (hR : (∀ f : R ⟶ T, f = 0) ∧ (∀ x : Ext R T 1, x = 0))
    (hV : (∀ f : V ⟶ T, f = 0) ∧ (∀ x : Ext V T 1, x = 0)) :
    (∀ f : cokernel e ⟶ T, f = 0) ∧ (∀ x : Ext (cokernel e) T 1, x = 0) :=
  quotient_outside_orthogonality
    (S := ShortComplex.mk e (cokernel.π e) (cokernel.condition e))
    { exact := ShortComplex.exact_cokernel e } T
    (finite_biproduct_outside_orthogonality (fun _ : Fin n => R) T (fun _ => hR)) hV

/-- The opposite direction uses the bound on the unchanged outside T. -/
theorem copies_cokernel_inside_orthogonality (T R V : C) (n : Nat)
    [HasBiproduct (fun _ : Fin n => R)] [HasProjectiveDimensionLT T 2]
    (e : (⨁ fun _ : Fin n => R) ⟶ V) [Mono e]
    (hR : (∀ f : T ⟶ R, f = 0) ∧ (∀ x : Ext T R 1, x = 0))
    (hV : (∀ f : T ⟶ V, f = 0) ∧ (∀ x : Ext T V 1, x = 0)) :
    (∀ f : T ⟶ cokernel e, f = 0) ∧ (∀ x : Ext T (cokernel e) 1, x = 0) :=
  quotient_inside_orthogonality T
    (S := ShortComplex.mk e (cokernel.π e) (cokernel.condition e))
    { exact := ShortComplex.exact_cokernel e }
    (finite_biproduct_inside_orthogonality T (fun _ : Fin n => R) (fun _ => hR)) hV

/-- Actual epimorphism from n copies; its chosen kernel stays orthogonal to
an unchanged outside target under the bound on V. -/
theorem copies_kernel_outside_orthogonality (R V T : C) (n : Nat)
    [HasBiproduct (fun _ : Fin n => R)] [HasProjectiveDimensionLT V 2]
    (e : (⨁ fun _ : Fin n => R) ⟶ V) [Epi e]
    (hR : (∀ f : R ⟶ T, f = 0) ∧ (∀ x : Ext R T 1, x = 0))
    (hV : (∀ f : V ⟶ T, f = 0) ∧ (∀ x : Ext V T 1, x = 0)) :
    (∀ f : kernel e ⟶ T, f = 0) ∧ (∀ x : Ext (kernel e) T 1, x = 0) :=
  kernel_outside_orthogonality
    (S := ShortComplex.mk (kernel.ι e) e (kernel.condition e))
    { exact := ShortComplex.exact_kernel e } T
    (finite_biproduct_outside_orthogonality (fun _ : Fin n => R) T (fun _ => hR)) hV

/-- The opposite kernel direction needs no hereditary bound. -/
theorem copies_kernel_inside_orthogonality (T R V : C) (n : Nat)
    [HasBiproduct (fun _ : Fin n => R)]
    (e : (⨁ fun _ : Fin n => R) ⟶ V) [Epi e]
    (hR : (∀ f : T ⟶ R, f = 0) ∧ (∀ x : Ext T R 1, x = 0))
    (hV : (∀ f : T ⟶ V, f = 0) ∧ (∀ x : Ext T V 1, x = 0)) :
    (∀ f : T ⟶ kernel e, f = 0) ∧ (∀ x : Ext T (kernel e) 1, x = 0) :=
  kernel_inside_orthogonality T
    (S := ShortComplex.mk (kernel.ι e) e (kernel.condition e))
    { exact := ShortComplex.exact_kernel e }
    (finite_biproduct_inside_orthogonality T (fun _ : Fin n => R) (fun _ => hR)) hV

#print axioms quotient_outside_orthogonality
#print axioms quotient_inside_orthogonality
#print axioms kernel_outside_orthogonality
#print axioms kernel_inside_orthogonality
end MA4EulerExternalOrthogonality01a0fee4
