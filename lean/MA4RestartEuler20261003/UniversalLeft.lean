import MA4RestartEuler20261003.UniversalClosure

/-! Constructed left universal extension: Y^J → E → X. -/
universe r w v u
namespace MA4RestartEuler20261003
open Module CategoryTheory CategoryTheory.Category CategoryTheory.Limits
  CategoryTheory.Abelian CategoryTheory.Preadditive
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
variable (K : Type r) [Field K] [Linear K C] [EnoughProjectives C]

lemma ext_target_smul_mk_zero_comp {X Z Y : C}
    (c : K) (e : Ext X Z 1) (f : Z ⟶ Y) :
    e.comp (Ext.mk₀ (c • f)) (add_zero 1) =
      c • (e.comp (Ext.mk₀ f) (add_zero 1)) := by
  rw [ext_one_source_smul_eq_target, Ext.comp_assoc_of_second_deg_zero,
    Ext.mk₀_comp_mk₀]
  simp

noncomputable def leftExtensionBoundary {S : ShortComplex C}
    (hS : S.ShortExact) (Y : C) : (S.X₁ ⟶ Y) →ₗ[K] Ext S.X₃ Y 1 where
  toFun f := hS.extClass.comp (Ext.mk₀ f) (add_zero 1)
  map_add' f g := by simp [Ext.mk₀_add]
  map_smul' c f := ext_target_smul_mk_zero_comp K c hS.extClass f

lemma left_boundary_on_scalar_desc {J : Type} [Fintype J]
    (X Y E : C) [HasBiproduct (fun _ : J => Y)]
    (i : (⨁ fun _ : J => Y) ⟶ E) (p : E ⟶ X) (wip : i ≫ p = 0)
    (hS : (ShortComplex.mk i p wip).ShortExact)
    (β : J → Ext X Y 1)
    (hβ : ∀ j, hS.extClass.comp (Ext.mk₀ (biproduct.π (fun _ : J => Y) j))
      (add_zero 1) = β j) (c : J → K) :
    leftExtensionBoundary K hS Y (biproduct.desc (fun j => c j • 𝟙 Y)) =
      ∑ j, c j • β j := by
  classical
  change hS.extClass.comp (Ext.mk₀ (biproduct.desc (fun j => c j • 𝟙 Y))) (add_zero 1) = _
  rw [biproduct.desc_eq (g := fun j => c j • 𝟙 Y), Ext.mk₀_sum, Ext.comp_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Linear.comp_smul, Category.comp_id, ext_target_smul_mk_zero_comp, hβ]

lemma left_universal_boundary_bijective {J : Type} [Fintype J]
    (X Y E : C) [HasBiproduct (fun _ : J => Y)]
    (i : (⨁ fun _ : J => Y) ⟶ E) (p : E ⟶ X) (wip : i ≫ p = 0)
    (hS : (ShortComplex.mk i p wip).ShortExact)
    (β : Basis J K (Ext X Y 1))
    (hβ : ∀ j, hS.extClass.comp (Ext.mk₀ (biproduct.π (fun _ : J => Y) j))
      (add_zero 1) = β j)
    (hY : ∀ f : Y ⟶ Y, ∃ c : K, f = c • 𝟙 Y) :
    Function.Bijective (leftExtensionBoundary K hS Y) := by
  classical
  have hz : ∀ f : (⨁ fun _ : J => Y) ⟶ Y,
      leftExtensionBoundary K hS Y f = 0 → f = 0 := by
    intro f hf
    choose c hc using fun j => hY (biproduct.ι (fun _ : J => Y) j ≫ f)
    have hfc : f = biproduct.desc (fun j => c j • 𝟙 Y) := by
      apply biproduct.hom_ext'
      intro j
      simpa using hc j
    have hc0 : ∑ j, c j • β j = 0 := by
      rw [← left_boundary_on_scalar_desc K X Y E i p wip hS β hβ c, ← hfc]
      exact hf
    have hcZ : c = 0 := β.linearIndependent.fintypeLinearCombination_injective (by
      simpa [Fintype.linearCombination_apply] using hc0)
    rw [hfc,hcZ]
    apply biproduct.hom_ext'
    intro j
    simp
  constructor
  · intro f g hfg
    have hzero : leftExtensionBoundary K hS Y (f - g) = 0 := by
      rw [map_sub,hfg,sub_self]
    exact sub_eq_zero.mp (hz (f - g) hzero)
  · intro e
    refine ⟨biproduct.desc (fun j => β.repr e j • 𝟙 Y), ?_⟩
    rw [left_boundary_on_scalar_desc K X Y E i p wip hS β hβ]
    exact β.sum_repr e

lemma left_universal_extension_has_short_exact {J : Type} [Fintype J]
    (X Y : C) [HasBiproduct (fun _ : J => Y)]
    (β : Basis J K (Ext X Y 1))
    (hY : ∀ f : Y ⟶ Y, ∃ c : K, f = c • 𝟙 Y) :
    ∃ (E : C) (i : (⨁ fun _ : J => Y) ⟶ E) (p : E ⟶ X)
      (wip : i ≫ p = 0) (hS : (ShortComplex.mk i p wip).ShortExact),
      (∀ j, hS.extClass.comp (Ext.mk₀ (biproduct.π (fun _ : J => Y) j))
        (add_zero 1) = β j) ∧ Function.Bijective (leftExtensionBoundary K hS Y) := by
  let A := Ext.addEquivBiproduct X (biproduct.isBilimit (fun _ : J => Y)) 1
  obtain ⟨E,i,p,wip,hS,he⟩ := ext_one_has_short_exact_representative X
    (⨁ fun _ : J => Y) (A.symm β)
  have hβ : ∀ j, hS.extClass.comp (Ext.mk₀ (biproduct.π (fun _ : J => Y) j))
      (add_zero 1) = β j := by
    intro j
    change A hS.extClass j = β j
    rw [he, A.apply_symm_apply]
  exact ⟨E,i,p,wip,hS,hβ,left_universal_boundary_bijective K X Y E i p wip hS β hβ hY⟩

lemma left_universal_extension_pair_orthogonality {J : Type} [Fintype J]
    (X Y E : C) [HasBiproduct (fun _ : J => Y)]
    (i : (⨁ fun _ : J => Y) ⟶ E) (p : E ⟶ X) (wip : i ≫ p = 0)
    (hS : (ShortComplex.mk i p wip).ShortExact)
    (hδ : Function.Bijective (leftExtensionBoundary K hS Y))
    (hHom : ∀ f : X ⟶ Y, f = 0) (hExt : ∀ e : Ext Y Y 1, e = 0) :
    (∀ f : E ⟶ Y, f = 0) ∧ (∀ e : Ext E Y 1, e = 0) := by
  constructor
  · intro f
    have hif : leftExtensionBoundary K hS Y (i ≫ f) = 0 := by
      dsimp [leftExtensionBoundary]
      rw [← Ext.mk₀_comp_mk₀, ← Ext.comp_assoc_of_third_deg_zero]
      have hi : hS.extClass.comp (Ext.mk₀ i) (add_zero 1) = 0 := hS.extClass_comp
      rw [hi, Ext.zero_comp]
    have hz : i ≫ f = 0 := hδ.1 (by simpa using hif)
    let a := hS.gIsCokernel.desc (CokernelCofork.ofπ f hz)
    have ha : p ≫ a = f := hS.gIsCokernel.fac _ WalkingParallelPair.one
    rw [hHom a, comp_zero] at ha
    exact ha.symm
  · intro e
    have hz : (Ext.mk₀ i).comp e (zero_add 1) = 0 := by
      let A := Ext.biproductAddEquiv (biproduct.isBilimit (fun _ : J => Y)) Y 1
      apply A.injective
      ext j
      simpa using hExt (A ((Ext.mk₀ i).comp e (zero_add 1)) j)
    obtain ⟨a, ha⟩ := Ext.contravariant_sequence_exact₂ hS Y e hz
    obtain ⟨f, hf⟩ := hδ.2 a
    rw [← hf] at ha
    dsimp [leftExtensionBoundary] at ha
    rw [← Ext.comp_assoc_of_third_deg_zero] at ha
    have hp : (Ext.mk₀ p).comp hS.extClass (zero_add 1) = 0 := hS.comp_extClass
    rw [hp, Ext.zero_comp] at ha
    exact ha.symm

omit [EnoughProjectives C] in
lemma left_universal_extension_rigid {J : Type} [Fintype J]
    (X Y E : C) [HasBiproduct (fun _ : J => Y)]
    (i : (⨁ fun _ : J => Y) ⟶ E) (p : E ⟶ X) (wip : i ≫ p = 0)
    (hS : (ShortComplex.mk i p wip).ShortExact)
    (hEY : ∀ e : Ext E Y 1, e = 0)
    (hXX : ∀ e : Ext X X 1, e = 0) (hYX : ∀ e : Ext Y X 1, e = 0) :
    ∀ e : Ext E E 1, e = 0 := by
  have hEX : ∀ e : Ext E X 1, e = 0 := by
    intro e
    have hz : (Ext.mk₀ i).comp e (zero_add 1) = 0 := by
      let A := Ext.biproductAddEquiv (biproduct.isBilimit (fun _ : J => Y)) X 1
      apply A.injective
      ext j
      simpa using hYX (A ((Ext.mk₀ i).comp e (zero_add 1)) j)
    obtain ⟨a, ha⟩ := Ext.contravariant_sequence_exact₂ hS X e hz
    simpa [hXX a] using ha.symm
  have hEP : ∀ e : Ext E (⨁ fun _ : J => Y) 1, e = 0 := by
    intro e
    let A := Ext.addEquivBiproduct E (biproduct.isBilimit (fun _ : J => Y)) 1
    apply A.injective
    ext j
    simpa using hEY (A e j)
  intro e
  obtain ⟨a, ha⟩ := Ext.covariant_sequence_exact₂ E hS e
    (hEX (e.comp (Ext.mk₀ p) (add_zero 1)))
  simpa [hEP a] using ha.symm

omit [HasExt.{w} C] [EnoughProjectives C] in
lemma left_universal_extension_scalar_end {J : Type} [Fintype J]
    (X Y E : C) [HasBiproduct (fun _ : J => Y)]
    (i : (⨁ fun _ : J => Y) ⟶ E) (p : E ⟶ X) (wip : i ≫ p = 0)
    (hS : (ShortComplex.mk i p wip).ShortExact)
    (hEY : ∀ f : E ⟶ Y, f = 0) (hYX : ∀ f : Y ⟶ X, f = 0)
    (hX : ∀ f : X ⟶ X, ∃ c : K, f = c • 𝟙 X) :
    ∀ f : E ⟶ E, ∃ c : K, f = c • 𝟙 E := by
  have hPX : ∀ f : (⨁ fun _ : J => Y) ⟶ X, f = 0 := by
    intro f
    apply biproduct.hom_ext'
    intro j
    simpa using hYX (biproduct.ι (fun _ : J => Y) j ≫ f)
  have hEP : ∀ f : E ⟶ (⨁ fun _ : J => Y), f = 0 := by
    intro f
    apply biproduct.hom_ext
    intro j
    simpa using hEY (f ≫ biproduct.π (fun _ : J => Y) j)
  intro f
  let a := hS.gIsCokernel.desc (CokernelCofork.ofπ (f ≫ p)
    (hPX (i ≫ f ≫ p)))
  have ha : p ≫ a = f ≫ p := hS.gIsCokernel.fac _ WalkingParallelPair.one
  obtain ⟨c, hc⟩ := hX a
  have hpz : (f - c • 𝟙 E) ≫ p = 0 := by
    rw [sub_comp, ← ha, hc]
    simp
  let b := hS.fIsKernel.lift (KernelFork.ofι (f - c • 𝟙 E) hpz)
  have hb : b ≫ i = f - c • 𝟙 E := hS.fIsKernel.fac _ WalkingParallelPair.zero
  rw [hEP b, zero_comp] at hb
  exact ⟨c, sub_eq_zero.mp hb.symm⟩

omit [HasExt.{w} C] [EnoughProjectives C] in
lemma extension_middle_identity_nonzero_of_quotient {P E X : C}
    (i : P ⟶ E) (p : E ⟶ X) (wip : i ≫ p = 0)
    (hS : (ShortComplex.mk i p wip).ShortExact) (hX : (𝟙 X : X ⟶ X) ≠ 0) :
    (𝟙 E : E ⟶ E) ≠ 0 := by
  letI : Epi p := hS.epi_g
  intro hz
  apply hX
  rw [← cancel_epi p]
  simp only [comp_id, comp_zero]
  simpa using congrArg (fun f => f ≫ p) hz

lemma left_universal_extension_exceptional
    {J : Type} [Fintype J] (X Y : C) [HasBiproduct (fun _ : J => Y)]
    (β : Basis J K (Ext X Y 1))
    (hX : ∀ f : X ⟶ X, ∃ c : K, f = c • 𝟙 X)
    (hY : ∀ f : Y ⟶ Y, ∃ c : K, f = c • 𝟙 Y)
    (hXY : ∀ f : X ⟶ Y, f = 0) (hYX : ∀ f : Y ⟶ X, f = 0)
    (hXX : ∀ e : Ext X X 1, e = 0) (hYY : ∀ e : Ext Y Y 1, e = 0)
    (hYXext : ∀ e : Ext Y X 1, e = 0) (hXid : (𝟙 X : X ⟶ X) ≠ 0) :
    ∃ (E : C) (i : (⨁ fun _ : J => Y) ⟶ E) (p : E ⟶ X)
      (wip : i ≫ p = 0) (hS : (ShortComplex.mk i p wip).ShortExact),
      (∀ j, hS.extClass.comp (Ext.mk₀ (biproduct.π (fun _ : J => Y) j))
        (add_zero 1) = β j) ∧
      (∀ f : E ⟶ Y, f = 0) ∧ (∀ e : Ext E Y 1, e = 0) ∧
      (∀ e : Ext E E 1, e = 0) ∧
      (∀ f : E ⟶ E, ∃ c : K, f = c • 𝟙 E) ∧ (𝟙 E : E ⟶ E) ≠ 0 := by
  obtain ⟨E, i, p, wip, hS, hβ, hδ⟩ := left_universal_extension_has_short_exact K X Y β hY
  obtain ⟨hHE, hEE⟩ := left_universal_extension_pair_orthogonality K X Y E i p wip hS hδ hXY hYY
  exact ⟨E, i, p, wip, hS, hβ, hHE, hEE,
    left_universal_extension_rigid X Y E i p wip hS hEE hXX hYXext,
    left_universal_extension_scalar_end K X Y E i p wip hS hHE hYX hX,
    extension_middle_identity_nonzero_of_quotient i p wip hS hXid⟩

omit [EnoughProjectives C] in
lemma left_extension_copies_outside_orthogonality {J : Type} [Fintype J]
    (X Y E T : C) [HasBiproduct (fun _ : J => Y)]
    (i : (⨁ fun _ : J => Y) ⟶ E) (p : E ⟶ X) (wip : i ≫ p = 0)
    (hS : (ShortComplex.mk i p wip).ShortExact)
    (hY : (∀ f : Y ⟶ T, f = 0) ∧ (∀ e : Ext Y T 1, e = 0))
    (hX : (∀ f : X ⟶ T, f = 0) ∧ (∀ e : Ext X T 1, e = 0)) :
    (∀ f : E ⟶ T, f = 0) ∧ (∀ e : Ext E T 1, e = 0) :=
  extension_middle_outside_orthogonality hS T
    (MA4EulerExternalOrthogonality01a0fee4.finite_biproduct_outside_orthogonality
      (fun _ : J => Y) T (fun _ => hY)) hX

omit [EnoughProjectives C] in
lemma left_extension_copies_inside_orthogonality {J : Type} [Fintype J]
    (T X Y E : C) [HasBiproduct (fun _ : J => Y)]
    (i : (⨁ fun _ : J => Y) ⟶ E) (p : E ⟶ X) (wip : i ≫ p = 0)
    (hS : (ShortComplex.mk i p wip).ShortExact)
    (hY : (∀ f : T ⟶ Y, f = 0) ∧ (∀ e : Ext T Y 1, e = 0))
    (hX : (∀ f : T ⟶ X, f = 0) ∧ (∀ e : Ext T X 1, e = 0)) :
    (∀ f : T ⟶ E, f = 0) ∧ (∀ e : Ext T E 1, e = 0) :=
  extension_middle_inside_orthogonality T hS
    (MA4EulerExternalOrthogonality01a0fee4.finite_biproduct_inside_orthogonality
      T (fun _ : J => Y) (fun _ => hY)) hX

omit [HasExt.{w} C] [EnoughProjectives C] [Linear K C] in
lemma left_extension_vertex_dimensions
    (F : Fin 4 → C ⥤ ModuleCat.{v} K)
    (hZero : ∀ a, (F a).PreservesZeroMorphisms)
    (hLimits : ∀ a, PreservesFiniteLimits (F a))
    (hColimits : ∀ a, PreservesFiniteColimits (F a))
    (X Y E : C) (n : ℕ) [HasBiproduct (fun _ : Fin n => Y)]
    (i : (⨁ fun _ : Fin n => Y) ⟶ E) (p : E ⟶ X) (wip : i ≫ p = 0)
    (hS : (ShortComplex.mk i p wip).ShortExact)
    (hX : ∀ a, Module.Finite K ((F a).obj X))
    (hY : ∀ a, Module.Finite K ((F a).obj Y)) :
    (∀ a, Module.Finite K ((F a).obj E)) ∧
    ∀ a, (Module.finrank K ((F a).obj E) : Int) =
      (n : Int) * (Module.finrank K ((F a).obj Y) : Int) +
        (Module.finrank K ((F a).obj X) : Int) := by
  have hP : ∀ a, Module.Finite K ((F a).obj (⨁ fun _ : Fin n => Y)) := by
    intro a
    letI := hZero a
    letI := hLimits a
    letI := hColimits a
    letI := hY a
    exact mapped_finite_copies (F a) Y n
  have hE := vertex_extension_middle_finite F hZero hLimits hColimits
    (ShortComplex.mk i p wip) hS hP hX
  refine ⟨hE, ?_⟩
  intro a
  have hd := QuiverProofs.MACompletionExactVertexDimensions.vertex_shortExact_dimension_add
    F hZero hLimits hColimits (ShortComplex.mk i p wip) hS hP hE hX a
  change (Module.finrank K ((F a).obj E) : Int) =
    (Module.finrank K ((F a).obj (⨁ fun _ : Fin n => Y)) : Int) +
      (Module.finrank K ((F a).obj X) : Int) at hd
  letI := hZero a
  letI := hLimits a
  letI := hColimits a
  letI := hY a
  rw [mapped_copies_finrank] at hd
  exact_mod_cast hd

lemma left_universal_extension_finite_frame
    (F : Fin 4 → C ⥤ ModuleCat.{v} K)
    (hZero : ∀ a, (F a).PreservesZeroMorphisms)
    (hLimits : ∀ a, PreservesFiniteLimits (F a))
    (hColimits : ∀ a, PreservesFiniteColimits (F a))
    (X Y : C) (n : ℕ) [HasBiproduct (fun _ : Fin n => Y)]
    (β : Basis (Fin n) K (Ext X Y 1))
    (hX : ∀ f : X ⟶ X, ∃ c : K, f = c • 𝟙 X)
    (hY : ∀ f : Y ⟶ Y, ∃ c : K, f = c • 𝟙 Y)
    (hXY : ∀ f : X ⟶ Y, f = 0) (hYX : ∀ f : Y ⟶ X, f = 0)
    (hXX : ∀ e : Ext X X 1, e = 0) (hYY : ∀ e : Ext Y Y 1, e = 0)
    (hYXext : ∀ e : Ext Y X 1, e = 0) (hXid : (𝟙 X : X ⟶ X) ≠ 0)
    (hXfinite : ∀ a, Module.Finite K ((F a).obj X))
    (hYfinite : ∀ a, Module.Finite K ((F a).obj Y)) :
    ∃ (E : C) (i : (⨁ fun _ : Fin n => Y) ⟶ E) (p : E ⟶ X)
      (wip : i ≫ p = 0) (hS : (ShortComplex.mk i p wip).ShortExact),
      (∀ j, hS.extClass.comp (Ext.mk₀ (biproduct.π (fun _ : Fin n => Y) j))
        (add_zero 1) = β j) ∧
      (∀ f : E ⟶ Y, f = 0) ∧ (∀ e : Ext E Y 1, e = 0) ∧
      (∀ e : Ext E E 1, e = 0) ∧
      (∀ f : E ⟶ E, ∃ c : K, f = c • 𝟙 E) ∧ (𝟙 E : E ⟶ E) ≠ 0 ∧
      (∀ a, Module.Finite K ((F a).obj E)) ∧
      (∀ a, (Module.finrank K ((F a).obj E) : Int) =
        (n : Int) * (Module.finrank K ((F a).obj Y) : Int) +
          (Module.finrank K ((F a).obj X) : Int)) ∧
      (∀ T : C,
        ((∀ f : Y ⟶ T, f = 0) ∧ (∀ e : Ext Y T 1, e = 0)) →
        ((∀ f : X ⟶ T, f = 0) ∧ (∀ e : Ext X T 1, e = 0)) →
        (∀ f : E ⟶ T, f = 0) ∧ (∀ e : Ext E T 1, e = 0)) ∧
      (∀ T : C,
        ((∀ f : T ⟶ Y, f = 0) ∧ (∀ e : Ext T Y 1, e = 0)) →
        ((∀ f : T ⟶ X, f = 0) ∧ (∀ e : Ext T X 1, e = 0)) →
        (∀ f : T ⟶ E, f = 0) ∧ (∀ e : Ext T E 1, e = 0)) := by
  obtain ⟨E,i,p,wip,hS,hβ,hHE,hEE,hRigid,hScalar,hId⟩ :=
    left_universal_extension_exceptional K X Y β hX hY hXY hYX hXX hYY hYXext hXid
  obtain ⟨hFinite,hDim⟩ := left_extension_vertex_dimensions K F hZero hLimits hColimits
    X Y E n i p wip hS hXfinite hYfinite
  exact ⟨E,i,p,wip,hS,hβ,hHE,hEE,hRigid,hScalar,hId,hFinite,hDim,
    fun T hYT hXT => left_extension_copies_outside_orthogonality X Y E T i p wip hS hYT hXT,
    fun T hTY hTX => left_extension_copies_inside_orthogonality T X Y E i p wip hS hTY hTX⟩

#print axioms left_universal_extension_exceptional
#print axioms left_universal_extension_finite_frame

end MA4RestartEuler20261003
