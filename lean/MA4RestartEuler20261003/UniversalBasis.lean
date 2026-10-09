import MA4RestartEuler20261003.UniversalExtension
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.LinearAlgebra.Basis.Basic

/-! The Ext scalar action is constructed from actual scalar identity morphisms.
It is not an independently supplied module structure. -/

universe r w v u
namespace MA4RestartEuler20261003
open Module
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
  CategoryTheory.Abelian CategoryTheory.Preadditive
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
variable (K : Type r) [Field K] [Linear K C]

noncomputable instance extSourceModule (X Y : C) (n : ℕ) : Module K (Ext X Y n) where
  smul c e := (Ext.mk₀ (c • 𝟙 X)).comp e (zero_add n)
  one_smul e := by
    change (Ext.mk₀ ((1 : K) • 𝟙 X)).comp e (zero_add n) = e
    simp
  mul_smul a b e := by
    change (Ext.mk₀ ((a * b) • 𝟙 X)).comp e (zero_add n) =
      (Ext.mk₀ (a • 𝟙 X)).comp ((Ext.mk₀ (b • 𝟙 X)).comp e (zero_add n)) (zero_add n)
    rw [← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀]
    simp [smul_smul, mul_comm]
  smul_zero c := by
    change (Ext.mk₀ (c • 𝟙 X)).comp (0 : Ext X Y n) (zero_add n) = 0
    simp
  smul_add c a b := by
    change (Ext.mk₀ (c • 𝟙 X)).comp (a + b) (zero_add n) = _
    exact Ext.comp_add _ _ _ _
  zero_smul e := by
    change (Ext.mk₀ ((0 : K) • 𝟙 X)).comp e (zero_add n) = 0
    simp
  add_smul a b e := by
    change (Ext.mk₀ ((a + b) • 𝟙 X)).comp e (zero_add n) =
      (Ext.mk₀ (a • 𝟙 X)).comp e (zero_add n) + (Ext.mk₀ (b • 𝟙 X)).comp e (zero_add n)
    simp [add_smul, Ext.mk₀_add]

lemma ext_source_smul {X Y : C} {n : ℕ} (c : K) (e : Ext X Y n) :
    c • e = (Ext.mk₀ (c • 𝟙 X)).comp e (zero_add n) := rfl

lemma ext_source_smul_mk_zero_comp {X Z Y : C} {n : ℕ}
    (c : K) (f : X ⟶ Z) (e : Ext Z Y n) :
    (Ext.mk₀ (c • f)).comp e (zero_add n) =
      c • ((Ext.mk₀ f).comp e (zero_add n)) := by
  rw [ext_source_smul, ← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀]
  simp

lemma ext_one_source_smul_eq_target [EnoughProjectives C]
    {X Y : C} (c : K) (e : Ext X Y 1) :
    c • e = e.comp (Ext.mk₀ (c • 𝟙 Y)) (add_zero 1) := by
  obtain ⟨E, i, p, wip, h, he⟩ := ext_one_has_short_exact_representative X Y e
  let S := ShortComplex.mk i p wip
  let φ : S ⟶ S :=
    { τ₁ := c • 𝟙 Y
      τ₂ := c • 𝟙 E
      τ₃ := c • 𝟙 X
      comm₁₂ := by simp [S]
      comm₂₃ := by simp [S] }
  rw [ext_source_smul]
  have hn := ext_class_naturality h h φ
  simpa [φ, he] using hn

noncomputable def extensionBoundary (X : C) {S : ShortComplex C}
    (hS : S.ShortExact) : (X ⟶ S.X₃) →ₗ[K] Ext X S.X₁ 1 where
  toFun f := (Ext.mk₀ f).comp hS.extClass (zero_add 1)
  map_add' f g := by simp [Ext.mk₀_add]
  map_smul' c f := ext_source_smul_mk_zero_comp K c f hS.extClass

lemma boundary_on_scalar_lift {J : Type} [Fintype J]
    (X Y E : C) [HasBiproduct (fun _ : J => X)]
    (i : Y ⟶ E) (p : E ⟶ (⨁ fun _ : J => X)) (wip : i ≫ p = 0)
    (hS : (ShortComplex.mk i p wip).ShortExact)
    (β : J → Ext X Y 1)
    (hβ : ∀ j, (Ext.mk₀ (biproduct.ι (fun _ : J => X) j)).comp
      hS.extClass (zero_add 1) = β j) (c : J → K) :
    extensionBoundary K X hS (biproduct.lift (fun j => c j • 𝟙 X)) =
      ∑ j, c j • β j := by
  classical
  change (Ext.mk₀ (biproduct.lift (fun j => c j • 𝟙 X))).comp hS.extClass (zero_add 1) = _
  rw [biproduct.lift_eq (g := fun j => c j • 𝟙 X), Ext.mk₀_sum, Ext.sum_comp]
  apply Finset.sum_congr rfl
  intro j _
  rw [Linear.smul_comp, Category.id_comp, ext_source_smul_mk_zero_comp, hβ]

lemma universal_boundary_bijective {J : Type} [Fintype J]
    (X Y E : C) [HasBiproduct (fun _ : J => X)]
    (i : Y ⟶ E) (p : E ⟶ (⨁ fun _ : J => X)) (wip : i ≫ p = 0)
    (hS : (ShortComplex.mk i p wip).ShortExact)
    (β : Basis J K (Ext X Y 1))
    (hβ : ∀ j, (Ext.mk₀ (biproduct.ι (fun _ : J => X) j)).comp
      hS.extClass (zero_add 1) = β j)
    (hX : ∀ f : X ⟶ X, ∃ c : K, f = c • 𝟙 X) :
    Function.Bijective (extensionBoundary K X hS) := by
  classical
  have hz : ∀ f : X ⟶ (⨁ fun _ : J => X),
      extensionBoundary K X hS f = 0 → f = 0 := by
    intro f hf
    choose c hc using fun j => hX (f ≫ biproduct.π (fun _ : J => X) j)
    have hfc : f = biproduct.lift (fun j => c j • 𝟙 X) := by
      apply biproduct.hom_ext
      intro j
      simpa using hc j
    have hc0 : ∑ j, c j • β j = 0 := by
      rw [← boundary_on_scalar_lift K X Y E i p wip hS β hβ c, ← hfc]
      exact hf
    have hcZ : c = 0 :=
      β.linearIndependent.fintypeLinearCombination_injective (by
        simpa [Fintype.linearCombination_apply] using hc0)
    rw [hfc, hcZ]
    apply biproduct.hom_ext
    intro j
    simp
  constructor
  · intro f g hfg
    have hzero : extensionBoundary K X hS (f - g) = 0 := by
      rw [map_sub, hfg, sub_self]
    exact sub_eq_zero.mp (hz (f - g) hzero)
  · intro e
    refine ⟨biproduct.lift (fun j => β.repr e j • 𝟙 X), ?_⟩
    rw [boundary_on_scalar_lift K X Y E i p wip hS β hβ]
    exact β.sum_repr e

lemma universal_extension_has_short_exact [EnoughProjectives C]
    {J : Type} [Fintype J] (X Y : C) [HasBiproduct (fun _ : J => X)]
    (β : Basis J K (Ext X Y 1))
    (hX : ∀ f : X ⟶ X, ∃ c : K, f = c • 𝟙 X) :
    ∃ (E : C) (i : Y ⟶ E) (p : E ⟶ (⨁ fun _ : J => X))
      (wip : i ≫ p = 0) (hS : (ShortComplex.mk i p wip).ShortExact),
      (∀ j, (Ext.mk₀ (biproduct.ι (fun _ : J => X) j)).comp
        hS.extClass (zero_add 1) = β j) ∧
      Function.Bijective (extensionBoundary K X hS) := by
  obtain ⟨E, i, p, wip, hS, _, hβ⟩ :=
    finite_extension_tuple_has_short_exact_representative X Y β
  exact ⟨E, i, p, wip, hS, hβ,
    universal_boundary_bijective K X Y E i p wip hS β hβ hX⟩

lemma universal_extension_pair_orthogonality {J : Type} [Fintype J]
    (X Y E : C) [HasBiproduct (fun _ : J => X)]
    (i : Y ⟶ E) (p : E ⟶ (⨁ fun _ : J => X)) (wip : i ≫ p = 0)
    (hS : (ShortComplex.mk i p wip).ShortExact)
    (hδ : Function.Bijective (extensionBoundary K X hS))
    (hHom : ∀ f : X ⟶ Y, f = 0) (hExt : ∀ e : Ext X X 1, e = 0) :
    (∀ f : X ⟶ E, f = 0) ∧ (∀ e : Ext X E 1, e = 0) := by
  constructor
  · intro f
    have hfp : extensionBoundary K X hS (f ≫ p) = 0 := by
      dsimp [extensionBoundary]
      rw [← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero]
      have hg : (Ext.mk₀ p).comp hS.extClass (zero_add 1) = 0 := hS.comp_extClass
      rw [hg, Ext.comp_zero]
    have hz : f ≫ p = 0 := hδ.1 (by simpa using hfp)
    let a := hS.fIsKernel.lift (KernelFork.ofι f hz)
    have ha : a ≫ i = f := hS.fIsKernel.fac _ WalkingParallelPair.zero
    rw [hHom a, zero_comp] at ha
    exact ha.symm
  · intro e
    have hz : e.comp (Ext.mk₀ p) (add_zero 1) = 0 := by
      let A := Ext.addEquivBiproduct X (biproduct.isBilimit (fun _ : J => X)) 1
      apply A.injective
      ext j
      simpa using hExt (A (e.comp (Ext.mk₀ p) (add_zero 1)) j)
    obtain ⟨a, ha⟩ := Ext.covariant_sequence_exact₂ X hS e hz
    obtain ⟨f, hf⟩ := hδ.2 a
    rw [← hf] at ha
    dsimp [extensionBoundary] at ha
    rw [Ext.comp_assoc_of_third_deg_zero] at ha
    have hi : hS.extClass.comp (Ext.mk₀ i) (add_zero 1) = 0 := hS.extClass_comp
    rw [hi, Ext.comp_zero] at ha
    exact ha.symm

lemma universal_extension_rigid {J : Type} [Fintype J]
    (X Y E : C) [HasBiproduct (fun _ : J => X)]
    (i : Y ⟶ E) (p : E ⟶ (⨁ fun _ : J => X)) (wip : i ≫ p = 0)
    (hS : (ShortComplex.mk i p wip).ShortExact)
    (hXE : ∀ e : Ext X E 1, e = 0)
    (hYY : ∀ e : Ext Y Y 1, e = 0) (hYX : ∀ e : Ext Y X 1, e = 0) :
    ∀ e : Ext E E 1, e = 0 := by
  have hYE : ∀ e : Ext Y E 1, e = 0 := by
    intro e
    have hz : e.comp (Ext.mk₀ p) (add_zero 1) = 0 := by
      let A := Ext.addEquivBiproduct Y (biproduct.isBilimit (fun _ : J => X)) 1
      apply A.injective
      ext j
      simpa using hYX (A (e.comp (Ext.mk₀ p) (add_zero 1)) j)
    obtain ⟨a, ha⟩ := Ext.covariant_sequence_exact₂ Y hS e hz
    simpa [hYY a] using ha.symm
  have hPE : ∀ e : Ext (⨁ fun _ : J => X) E 1, e = 0 := by
    intro e
    let A := Ext.biproductAddEquiv (biproduct.isBilimit (fun _ : J => X)) E 1
    apply A.injective
    ext j
    simpa using hXE (A e j)
  intro e
  obtain ⟨a, ha⟩ := Ext.contravariant_sequence_exact₂ hS E e
    (hYE ((Ext.mk₀ i).comp e (zero_add 1)))
  simpa [hPE a] using ha.symm

omit [HasExt.{w} C] in
lemma universal_extension_scalar_end {J : Type} [Fintype J]
    (X Y E : C) [HasBiproduct (fun _ : J => X)]
    (i : Y ⟶ E) (p : E ⟶ (⨁ fun _ : J => X)) (wip : i ≫ p = 0)
    (hS : (ShortComplex.mk i p wip).ShortExact)
    (hXE : ∀ f : X ⟶ E, f = 0) (hYX : ∀ f : Y ⟶ X, f = 0)
    (hY : ∀ f : Y ⟶ Y, ∃ c : K, f = c • 𝟙 Y) :
    ∀ f : E ⟶ E, ∃ c : K, f = c • 𝟙 E := by
  have hYP : ∀ f : Y ⟶ (⨁ fun _ : J => X), f = 0 := by
    intro f
    apply biproduct.hom_ext
    intro j
    simpa using hYX (f ≫ biproduct.π (fun _ : J => X) j)
  have hPE : ∀ f : (⨁ fun _ : J => X) ⟶ E, f = 0 := by
    intro f
    apply biproduct.hom_ext'
    intro j
    simpa using hXE (biproduct.ι (fun _ : J => X) j ≫ f)
  intro f
  let a := hS.fIsKernel.lift (KernelFork.ofι (i ≫ f)
    (by rw [Category.assoc]; exact hYP (i ≫ f ≫ p)))
  have ha : a ≫ i = i ≫ f := hS.fIsKernel.fac _ WalkingParallelPair.zero
  obtain ⟨c, hc⟩ := hY a
  have hiz : i ≫ (f - c • 𝟙 E) = 0 := by
    rw [comp_sub, ← ha, hc]
    simp
  let b := hS.gIsCokernel.desc (CokernelCofork.ofπ (f - c • 𝟙 E) hiz)
  have hb : p ≫ b = f - c • 𝟙 E := hS.gIsCokernel.fac _ WalkingParallelPair.one
  rw [hPE b, comp_zero] at hb
  exact ⟨c, sub_eq_zero.mp hb.symm⟩

omit [HasExt.{w} C] in
lemma extension_middle_identity_nonzero {Y E P : C}
    (i : Y ⟶ E) (p : E ⟶ P) (wip : i ≫ p = 0)
    (hS : (ShortComplex.mk i p wip).ShortExact) (hY : (𝟙 Y : Y ⟶ Y) ≠ 0) :
    (𝟙 E : E ⟶ E) ≠ 0 := by
  letI : Mono i := hS.mono_f
  intro hz
  apply hY
  rw [← cancel_mono i]
  simp only [id_comp, zero_comp]
  simpa using congrArg (fun f => i ≫ f) hz

lemma universal_extension_exceptional [EnoughProjectives C]
    {J : Type} [Fintype J] (X Y : C) [HasBiproduct (fun _ : J => X)]
    (β : Basis J K (Ext X Y 1))
    (hX : ∀ f : X ⟶ X, ∃ c : K, f = c • 𝟙 X)
    (hY : ∀ f : Y ⟶ Y, ∃ c : K, f = c • 𝟙 Y)
    (hXY : ∀ f : X ⟶ Y, f = 0) (hYX : ∀ f : Y ⟶ X, f = 0)
    (hXX : ∀ e : Ext X X 1, e = 0) (hYY : ∀ e : Ext Y Y 1, e = 0)
    (hYXext : ∀ e : Ext Y X 1, e = 0) (hYid : (𝟙 Y : Y ⟶ Y) ≠ 0) :
    ∃ (E : C) (i : Y ⟶ E) (p : E ⟶ (⨁ fun _ : J => X))
      (wip : i ≫ p = 0) (hS : (ShortComplex.mk i p wip).ShortExact),
      (∀ j, (Ext.mk₀ (biproduct.ι (fun _ : J => X) j)).comp
        hS.extClass (zero_add 1) = β j) ∧
      (∀ f : X ⟶ E, f = 0) ∧ (∀ e : Ext X E 1, e = 0) ∧
      (∀ e : Ext E E 1, e = 0) ∧
      (∀ f : E ⟶ E, ∃ c : K, f = c • 𝟙 E) ∧ (𝟙 E : E ⟶ E) ≠ 0 := by
  obtain ⟨E, i, p, wip, hS, hβ, hδ⟩ := universal_extension_has_short_exact K X Y β hX
  obtain ⟨hHE, hEE⟩ := universal_extension_pair_orthogonality K X Y E i p wip hS hδ hXY hXX
  exact ⟨E, i, p, wip, hS, hβ, hHE, hEE,
    universal_extension_rigid X Y E i p wip hS hEE hYY hYXext,
    universal_extension_scalar_end K X Y E i p wip hS hHE hYX hY,
    extension_middle_identity_nonzero i p wip hS hYid⟩

#print axioms universal_extension_exceptional

end MA4RestartEuler20261003
