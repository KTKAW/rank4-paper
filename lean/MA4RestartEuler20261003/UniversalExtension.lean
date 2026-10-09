import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import Mathlib.CategoryTheory.Abelian.Projective.Dimension

/-! Construction of an actual short exact representative of an Ext1 class.
The category has enough projectives; no extension-object existence is supplied. -/

universe w' w v u
namespace MA4RestartEuler20261003

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
  CategoryTheory.Abelian CategoryTheory.Preadditive

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

omit [HasExt.{w} C] in
lemma cone_desc_naturality
    {S T : ShortComplex (CochainComplex C ℤ)} (φ : S ⟶ T) :
    CochainComplex.mappingCone.map S.f T.f φ.τ₁ φ.τ₂ φ.comm₁₂.symm ≫
        CochainComplex.mappingCone.descShortComplex T =
      CochainComplex.mappingCone.descShortComplex S ≫ φ.τ₃ := by
  ext n
  simp only [CochainComplex.mappingCone.ext_from_iff _ (n + 1) n rfl,
    HomologicalComplex.comp_f]
  constructor
  · simp [CochainComplex.mappingCone.map, CochainComplex.mappingCone.descShortComplex]
  · simp [CochainComplex.mappingCone.map, CochainComplex.mappingCone.descShortComplex,
      ← HomologicalComplex.comp_f, φ.comm₂₃.symm]

omit [HasExt.{w} C] in
lemma derived_delta_naturality [HasDerivedCategory.{w'} C]
    {S T : ShortComplex (CochainComplex C ℤ)}
    (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T) :
    DerivedCategory.Q.map φ.τ₃ ≫ DerivedCategory.triangleOfSESδ hT =
      DerivedCategory.triangleOfSESδ hS ≫
        (DerivedCategory.Q.map φ.τ₁)⟦(1 : ℤ)⟧' := by
  let A := CochainComplex.mappingCone.map S.f T.f φ.τ₁ φ.τ₂ φ.comm₁₂.symm
  have hqS := CochainComplex.mappingCone.quasiIso_descShortComplex hS
  have hqT := CochainComplex.mappingCone.quasiIso_descShortComplex hT
  have hq : DerivedCategory.Q.map A ≫
      DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex T) =
      DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex S) ≫
        DerivedCategory.Q.map φ.τ₃ := by
    simp only [← Functor.map_comp, A, cone_desc_naturality]
  have hd := (CochainComplex.mappingCone.triangleMap
    S.f T.f φ.τ₁ φ.τ₂ φ.comm₁₂.symm).comm₃
  dsimp at hd
  dsimp [DerivedCategory.triangleOfSESδ]
  rw [← cancel_epi (DerivedCategory.Q.map
    (CochainComplex.mappingCone.descShortComplex S))]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  rw [← reassoc_of% hq, IsIso.hom_inv_id_assoc]
  rw [← Functor.map_comp_assoc]
  change DerivedCategory.Q.map
      (CochainComplex.mappingCone.map S.f T.f φ.τ₁ φ.τ₂ φ.comm₁₂.symm ≫
        (CochainComplex.mappingCone.triangle T.f).mor₃) ≫ _ = _
  rw [← hd, Functor.map_comp]
  simp only [Category.assoc]
  exact congrArg (fun f => DerivedCategory.Q.map
    (CochainComplex.mappingCone.triangle S.f).mor₃ ≫ f)
    ((DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.naturality φ.τ₁)

omit [HasExt.{w} C] in
lemma single_delta_naturality [HasDerivedCategory.{w'} C]
    {S T : ShortComplex C} (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T) :
    (DerivedCategory.singleFunctor C 0).map φ.τ₃ ≫ hT.singleδ =
      hS.singleδ ≫ ((DerivedCategory.singleFunctor C 0).map φ.τ₁)⟦(1 : ℤ)⟧' := by
  let F := HomologicalComplex.single C (ComplexShape.up ℤ) 0
  let ψ : S.map F ⟶ T.map F :=
    { τ₁ := F.map φ.τ₁
      τ₂ := F.map φ.τ₂
      τ₃ := F.map φ.τ₃
      comm₁₂ := by dsimp [ShortComplex.map]; rw [← F.map_comp, ← F.map_comp, φ.comm₁₂]
      comm₂₃ := by dsimp [ShortComplex.map]; rw [← F.map_comp, ← F.map_comp, φ.comm₂₃] }
  have hn := derived_delta_naturality (hS.map_of_exact F) (hT.map_of_exact F) ψ
  let e := (SingleFunctors.evaluation _ _ 0).mapIso
    (DerivedCategory.singleFunctorsPostcompQIso C)
  have h₃ := e.hom.naturality φ.τ₃
  have h₁ := e.inv.naturality φ.τ₁
  dsimp [ShortComplex.ShortExact.singleδ]
  dsimp [ψ, F] at hn
  change DerivedCategory.Q.map (((CochainComplex.singleFunctors C).functor 0).map φ.τ₃) ≫
    DerivedCategory.triangleOfSESδ (hT.map_of_exact F) =
    DerivedCategory.triangleOfSESδ (hS.map_of_exact F) ≫
      (DerivedCategory.Q.map (((CochainComplex.singleFunctors C).functor 0).map φ.τ₁))⟦(1 : ℤ)⟧'
    at hn
  dsimp [e] at h₃ h₁
  rw [reassoc_of% h₃, reassoc_of% hn]
  simp only [Category.assoc]
  rw [← Functor.map_comp, h₁, Functor.map_comp]

lemma ext_class_naturality {S T : ShortComplex C}
    (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T) :
    (Ext.mk₀ φ.τ₃).comp hT.extClass (zero_add 1) =
      hS.extClass.comp (Ext.mk₀ φ.τ₁) (add_zero 1) := by
  letI := HasDerivedCategory.standard C
  apply Ext.homEquiv.{max u v}.injective
  simp only [Ext.comp_hom, Ext.mk₀_hom, ShortComplex.ShortExact.extClass_hom,
    ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀]
  exact single_delta_naturality hS hT φ

noncomputable def extensionPushoutProjection {S : ShortComplex C}
    (Y : C) (u : S.X₁ ⟶ Y) : pushout S.f u ⟶ S.X₃ :=
  pushout.desc S.g 0 (by simp)

omit [HasExt.{w} C] in
lemma extension_pushout_short_exact {S : ShortComplex C}
    (hS : S.ShortExact) (Y : C) (u : S.X₁ ⟶ Y) :
    (ShortComplex.mk (pushout.inr S.f u) (extensionPushoutProjection Y u)
      (by simp [extensionPushoutProjection])).ShortExact := by
  letI := hS.mono_f
  letI := hS.epi_g
  have hp : pushout.inl S.f u ≫ extensionPushoutProjection Y u = S.g := by
    simp [extensionPushoutProjection]
  letI : Epi (extensionPushoutProjection Y u) := epi_of_epi_fac hp
  have hc : IsColimit (CokernelCofork.ofπ (extensionPushoutProjection Y u)
      (show pushout.inr S.f u ≫ extensionPushoutProjection Y u = 0 by
        simp [extensionPushoutProjection])) := by
    apply CokernelCofork.IsColimit.ofπ'
    intro Z k hk
    let a := hS.gIsCokernel.desc (CokernelCofork.ofπ (pushout.inl S.f u ≫ k)
      (by rw [← Category.assoc, pushout.condition, Category.assoc, hk, comp_zero]))
    refine ⟨a, ?_⟩
    apply pushout.hom_ext
    · simp only [← Category.assoc, hp, a]
      exact hS.gIsCokernel.fac _ WalkingParallelPair.one
    · simp [extensionPushoutProjection, hk]
  exact { exact := ShortComplex.exact_of_g_is_cokernel _ hc }

lemma extension_pushout_ext_class {S : ShortComplex C}
    (hS : S.ShortExact) (Y : C) (u : S.X₁ ⟶ Y) :
    (extension_pushout_short_exact hS Y u).extClass =
      hS.extClass.comp (Ext.mk₀ u) (add_zero 1) := by
  let T := ShortComplex.mk (pushout.inr S.f u) (extensionPushoutProjection Y u)
    (by simp [extensionPushoutProjection])
  let φ : S ⟶ T :=
    { τ₁ := u
      τ₂ := pushout.inl S.f u
      τ₃ := 𝟙 S.X₃
      comm₁₂ := by dsimp [T]; exact pushout.condition.symm
      comm₂₃ := by simp [T, extensionPushoutProjection] }
  have hn := ext_class_naturality hS (extension_pushout_short_exact hS Y u) φ
  simpa [φ] using hn

lemma ext_one_has_short_exact_representative [EnoughProjectives C]
    (Z Y : C) (α : Ext Z Y 1) :
    ∃ (E : C) (i : Y ⟶ E) (p : E ⟶ Z) (wip : i ≫ p = 0)
      (h : (ShortComplex.mk i p wip).ShortExact), h.extClass = α := by
  let S := ShortComplex.mk (kernel.ι (Projective.π Z)) (Projective.π Z)
    (kernel.condition (Projective.π Z))
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel S.g) }
  obtain ⟨γ, hγ⟩ := Ext.contravariant_sequence_exact₃ hS Y α
    (Ext.eq_zero_of_projective _) (show 1 + 0 = 1 by rfl)
  let u := Ext.homEquiv₀ γ
  refine ⟨pushout S.f u, pushout.inr S.f u, extensionPushoutProjection Y u,
    by simp [extensionPushoutProjection], extension_pushout_short_exact hS Y u, ?_⟩
  rw [extension_pushout_ext_class]
  simpa [u, Ext.mk₀_homEquiv₀_apply] using hγ

/-- An actual simultaneous extension realizes every prescribed finite tuple of
Ext1 classes as its connecting values on the actual biproduct injections. -/
lemma finite_extension_tuple_has_short_exact_representative [EnoughProjectives C]
    {J : Type*} [Fintype J] (X Y : C) [HasBiproduct (fun _ : J => X)]
    (β : J → Ext X Y 1) :
    ∃ (E : C) (i : Y ⟶ E) (p : E ⟶ (⨁ fun _ : J => X))
      (wip : i ≫ p = 0) (h : (ShortComplex.mk i p wip).ShortExact),
      (Ext.biproductAddEquiv (biproduct.isBilimit (fun _ : J => X)) Y 1) h.extClass = β ∧
      ∀ j, (Ext.mk₀ (biproduct.ι (fun _ : J => X) j)).comp h.extClass (zero_add 1) = β j := by
  let A := Ext.biproductAddEquiv (biproduct.isBilimit (fun _ : J => X)) Y 1
  obtain ⟨E, i, p, wip, h, he⟩ :=
    ext_one_has_short_exact_representative (⨁ fun _ : J => X) Y (A.symm β)
  refine ⟨E, i, p, wip, h, ?_, ?_⟩
  · rw [he]; exact A.apply_symm_apply β
  · intro j
    change A h.extClass j = β j
    rw [he, A.apply_symm_apply]

#print axioms ext_class_naturality
#print axioms ext_one_has_short_exact_representative
#print axioms finite_extension_tuple_has_short_exact_representative

end MA4RestartEuler20261003
