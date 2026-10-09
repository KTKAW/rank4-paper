import MA4RestartEuler20261003.UniversalBasis
import MA4EulerExternalOrthogonality01a0fee4
import MA4Coordinator20261003.ExactVertexDimensions
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-! External orthogonality and actual finite vertex dimensions of extension
middle objects. The finite model endpoints are supplied; next finiteness is derived. -/
universe r w v u
namespace MA4RestartEuler20261003
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
  CategoryTheory.Abelian CategoryTheory.Preadditive
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

lemma extension_middle_outside_orthogonality {S : ShortComplex C}
    (hS : S.ShortExact) (T : C)
    (h₁ : (∀ f : S.X₁ ⟶ T, f = 0) ∧ (∀ e : Ext S.X₁ T 1, e = 0))
    (h₃ : (∀ f : S.X₃ ⟶ T, f = 0) ∧ (∀ e : Ext S.X₃ T 1, e = 0)) :
    (∀ f : S.X₂ ⟶ T, f = 0) ∧ (∀ e : Ext S.X₂ T 1, e = 0) := by
  constructor
  · intro f
    let a := hS.gIsCokernel.desc (CokernelCofork.ofπ f (h₁.1 (S.f ≫ f)))
    have ha : S.g ≫ a = f := hS.gIsCokernel.fac _ WalkingParallelPair.one
    rw [h₃.1 a, comp_zero] at ha
    exact ha.symm
  · intro e
    obtain ⟨a, ha⟩ := Ext.contravariant_sequence_exact₂ hS T e
      (h₁.2 ((Ext.mk₀ S.f).comp e (zero_add 1)))
    simpa [h₃.2 a] using ha.symm

lemma extension_middle_inside_orthogonality (T : C) {S : ShortComplex C}
    (hS : S.ShortExact)
    (h₁ : (∀ f : T ⟶ S.X₁, f = 0) ∧ (∀ e : Ext T S.X₁ 1, e = 0))
    (h₃ : (∀ f : T ⟶ S.X₃, f = 0) ∧ (∀ e : Ext T S.X₃ 1, e = 0)) :
    (∀ f : T ⟶ S.X₂, f = 0) ∧ (∀ e : Ext T S.X₂ 1, e = 0) := by
  constructor
  · intro f
    let a := hS.fIsKernel.lift (KernelFork.ofι f (h₃.1 (f ≫ S.g)))
    have ha : a ≫ S.f = f := hS.fIsKernel.fac _ WalkingParallelPair.zero
    rw [h₁.1 a, zero_comp] at ha
    exact ha.symm
  · intro e
    obtain ⟨a, ha⟩ := Ext.covariant_sequence_exact₂ T hS e
      (h₃.2 (e.comp (Ext.mk₀ S.g) (add_zero 1)))
    simpa [h₁.2 a] using ha.symm

lemma extension_copies_outside_orthogonality {J : Type} [Fintype J]
    (X Y E T : C) [HasBiproduct (fun _ : J => X)]
    (i : Y ⟶ E) (p : E ⟶ (⨁ fun _ : J => X)) (wip : i ≫ p = 0)
    (hS : (ShortComplex.mk i p wip).ShortExact)
    (hY : (∀ f : Y ⟶ T, f = 0) ∧ (∀ e : Ext Y T 1, e = 0))
    (hX : (∀ f : X ⟶ T, f = 0) ∧ (∀ e : Ext X T 1, e = 0)) :
    (∀ f : E ⟶ T, f = 0) ∧ (∀ e : Ext E T 1, e = 0) :=
  extension_middle_outside_orthogonality hS T hY
    (MA4EulerExternalOrthogonality01a0fee4.finite_biproduct_outside_orthogonality
      (fun _ : J => X) T (fun _ => hX))

lemma extension_copies_inside_orthogonality {J : Type} [Fintype J]
    (T X Y E : C) [HasBiproduct (fun _ : J => X)]
    (i : Y ⟶ E) (p : E ⟶ (⨁ fun _ : J => X)) (wip : i ≫ p = 0)
    (hS : (ShortComplex.mk i p wip).ShortExact)
    (hY : (∀ f : T ⟶ Y, f = 0) ∧ (∀ e : Ext T Y 1, e = 0))
    (hX : (∀ f : T ⟶ X, f = 0) ∧ (∀ e : Ext T X 1, e = 0)) :
    (∀ f : T ⟶ E, f = 0) ∧ (∀ e : Ext T E 1, e = 0) :=
  extension_middle_inside_orthogonality T hS hY
    (MA4EulerExternalOrthogonality01a0fee4.finite_biproduct_inside_orthogonality
      T (fun _ : J => X) (fun _ => hX))

variable {K : Type r} [Field K]

omit [HasExt.{w} C] in
lemma moduleCat_extension_middle_finite (S : ShortComplex (ModuleCat.{v} K))
    (hS : S.ShortExact) [Module.Finite K S.X₁] [Module.Finite K S.X₃] :
    Module.Finite K S.X₂ := by
  letI : Module.Finite K (LinearMap.range S.f.hom) :=
    Module.Finite.of_surjective S.f.hom.rangeRestrict (by
      intro y
      obtain ⟨x, hx⟩ := y.property
      exact ⟨x, Subtype.ext hx⟩)
  letI : Module.Finite K (LinearMap.ker S.g.hom) := by
    rw [← hS.exact.moduleCat_range_eq_ker]
    infer_instance
  let e := LinearMap.quotKerEquivOfSurjective S.g.hom hS.moduleCat_surjective_g
  letI : Module.Finite K (S.X₂ ⧸ LinearMap.ker S.g.hom) :=
    Module.Finite.of_injective e.toLinearMap e.injective
  exact Module.Finite.of_submodule_quotient (LinearMap.ker S.g.hom)

omit [HasExt.{w} C] in
lemma vertex_extension_middle_finite
    (F : Fin 4 → C ⥤ ModuleCat.{v} K)
    (hZero : ∀ a, (F a).PreservesZeroMorphisms)
    (hLimits : ∀ a, PreservesFiniteLimits (F a))
    (hColimits : ∀ a, PreservesFiniteColimits (F a))
    (S : ShortComplex C) (hS : S.ShortExact)
    (h₁ : ∀ a, Module.Finite K ((F a).obj S.X₁))
    (h₃ : ∀ a, Module.Finite K ((F a).obj S.X₃)) :
    ∀ a, Module.Finite K ((F a).obj S.X₂) := by
  intro a
  letI := hZero a
  letI := hLimits a
  letI := hColimits a
  letI : Module.Finite K (S.map (F a)).X₁ := h₁ a
  letI : Module.Finite K (S.map (F a)).X₃ := h₃ a
  exact moduleCat_extension_middle_finite (S.map (F a)) (hS.map_of_exact (F a))

omit [HasExt.{w} C] in
lemma mapped_finite_copies (F : C ⥤ ModuleCat.{v} K)
    [F.PreservesZeroMorphisms] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (X : C) (n : ℕ) [HasBiproduct (fun _ : Fin n => X)]
    [Module.Finite K (F.obj X)] :
    Module.Finite K (F.obj (⨁ fun _ : Fin n => X)) := by
  letI : PreservesBiproduct (fun _ : Fin n => X) F := preservesBiproduct_of_preservesProduct F
  letI : ∀ j : Fin n, Module.Finite K ((F.obj ∘ (fun _ : Fin n => X)) j) := fun _ => by
    change Module.Finite K (F.obj X)
    infer_instance
  let e := F.mapBiproduct (fun _ : Fin n => X) ≪≫
    ModuleCat.biproductIsoPi (F.obj ∘ (fun _ : Fin n => X))
  exact Module.Finite.of_injective e.toLinearEquiv.toLinearMap e.toLinearEquiv.injective

omit [HasExt.{w} C] in
lemma mapped_copies_finrank (F : C ⥤ ModuleCat.{v} K)
    [F.PreservesZeroMorphisms] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (X : C) (n : ℕ) [HasBiproduct (fun _ : Fin n => X)]
    [Module.Finite K (F.obj X)] :
    Module.finrank K (F.obj (⨁ fun _ : Fin n => X)) = n * Module.finrank K (F.obj X) := by
  letI : PreservesBiproduct (fun _ : Fin n => X) F := preservesBiproduct_of_preservesProduct F
  let e := F.mapBiproduct (fun _ : Fin n => X) ≪≫
    ModuleCat.biproductIsoPi (F.obj ∘ (fun _ : Fin n => X))
  rw [e.toLinearEquiv.finrank_eq]
  simp [Module.finrank_pi_fintype]

omit [HasExt.{w} C] in
lemma extension_vertex_dimensions
    (F : Fin 4 → C ⥤ ModuleCat.{v} K)
    (hZero : ∀ a, (F a).PreservesZeroMorphisms)
    (hLimits : ∀ a, PreservesFiniteLimits (F a))
    (hColimits : ∀ a, PreservesFiniteColimits (F a))
    (X Y E : C) (n : ℕ) [HasBiproduct (fun _ : Fin n => X)]
    (i : Y ⟶ E) (p : E ⟶ (⨁ fun _ : Fin n => X)) (wip : i ≫ p = 0)
    (hS : (ShortComplex.mk i p wip).ShortExact)
    (hX : ∀ a, Module.Finite K ((F a).obj X))
    (hY : ∀ a, Module.Finite K ((F a).obj Y)) :
    (∀ a, Module.Finite K ((F a).obj E)) ∧
    ∀ a, (Module.finrank K ((F a).obj E) : Int) =
      (Module.finrank K ((F a).obj Y) : Int) +
        (n : Int) * (Module.finrank K ((F a).obj X) : Int) := by
  have hP : ∀ a, Module.Finite K ((F a).obj (⨁ fun _ : Fin n => X)) := by
    intro a
    letI := hZero a
    letI := hLimits a
    letI := hColimits a
    letI := hX a
    exact mapped_finite_copies (F a) X n
  have hE := vertex_extension_middle_finite F hZero hLimits hColimits
    (ShortComplex.mk i p wip) hS hY hP
  refine ⟨hE, ?_⟩
  intro a
  have hd := QuiverProofs.MACompletionExactVertexDimensions.vertex_shortExact_dimension_add
    F hZero hLimits hColimits (ShortComplex.mk i p wip) hS hY hE hP a
  change (Module.finrank K ((F a).obj E) : Int) =
    (Module.finrank K ((F a).obj Y) : Int) +
      (Module.finrank K ((F a).obj (⨁ fun _ : Fin n => X)) : Int) at hd
  letI := hZero a
  letI := hLimits a
  letI := hColimits a
  letI := hX a
  rw [mapped_copies_finrank] at hd
  exact_mod_cast hd

lemma universal_extension_finite_frame [Linear K C] [EnoughProjectives C]
    (F : Fin 4 → C ⥤ ModuleCat.{v} K)
    (hZero : ∀ a, (F a).PreservesZeroMorphisms)
    (hLimits : ∀ a, PreservesFiniteLimits (F a))
    (hColimits : ∀ a, PreservesFiniteColimits (F a))
    (X Y : C) (n : ℕ) [HasBiproduct (fun _ : Fin n => X)]
    (β : Module.Basis (Fin n) K (Ext X Y 1))
    (hX : ∀ f : X ⟶ X, ∃ c : K, f = c • 𝟙 X)
    (hY : ∀ f : Y ⟶ Y, ∃ c : K, f = c • 𝟙 Y)
    (hXY : ∀ f : X ⟶ Y, f = 0) (hYX : ∀ f : Y ⟶ X, f = 0)
    (hXX : ∀ e : Ext X X 1, e = 0) (hYY : ∀ e : Ext Y Y 1, e = 0)
    (hYXext : ∀ e : Ext Y X 1, e = 0) (hYid : (𝟙 Y : Y ⟶ Y) ≠ 0)
    (hXfinite : ∀ a, Module.Finite K ((F a).obj X))
    (hYfinite : ∀ a, Module.Finite K ((F a).obj Y)) :
    ∃ (E : C) (i : Y ⟶ E) (p : E ⟶ (⨁ fun _ : Fin n => X))
      (wip : i ≫ p = 0) (hS : (ShortComplex.mk i p wip).ShortExact),
      (∀ j, (Ext.mk₀ (biproduct.ι (fun _ : Fin n => X) j)).comp
        hS.extClass (zero_add 1) = β j) ∧
      (∀ f : X ⟶ E, f = 0) ∧ (∀ e : Ext X E 1, e = 0) ∧
      (∀ e : Ext E E 1, e = 0) ∧
      (∀ f : E ⟶ E, ∃ c : K, f = c • 𝟙 E) ∧ (𝟙 E : E ⟶ E) ≠ 0 ∧
      (∀ a, Module.Finite K ((F a).obj E)) ∧
      (∀ a, (Module.finrank K ((F a).obj E) : Int) =
        (Module.finrank K ((F a).obj Y) : Int) +
          (n : Int) * (Module.finrank K ((F a).obj X) : Int)) ∧
      (∀ T : C,
        ((∀ f : Y ⟶ T, f = 0) ∧ (∀ e : Ext Y T 1, e = 0)) →
        ((∀ f : X ⟶ T, f = 0) ∧ (∀ e : Ext X T 1, e = 0)) →
        (∀ f : E ⟶ T, f = 0) ∧ (∀ e : Ext E T 1, e = 0)) ∧
      (∀ T : C,
        ((∀ f : T ⟶ Y, f = 0) ∧ (∀ e : Ext T Y 1, e = 0)) →
        ((∀ f : T ⟶ X, f = 0) ∧ (∀ e : Ext T X 1, e = 0)) →
        (∀ f : T ⟶ E, f = 0) ∧ (∀ e : Ext T E 1, e = 0)) := by
  obtain ⟨E,i,p,wip,hS,hβ,hHE,hEE,hRigid,hScalar,hId⟩ :=
    universal_extension_exceptional K X Y β hX hY hXY hYX hXX hYY hYXext hYid
  obtain ⟨hFinite,hDim⟩ := extension_vertex_dimensions F hZero hLimits hColimits
    X Y E n i p wip hS hXfinite hYfinite
  exact ⟨E,i,p,wip,hS,hβ,hHE,hEE,hRigid,hScalar,hId,hFinite,hDim,
    fun T hYT hXT => extension_copies_outside_orthogonality X Y E T i p wip hS hYT hXT,
    fun T hTY hTX => extension_copies_inside_orthogonality T X Y E i p wip hS hTY hTX⟩

#print axioms extension_vertex_dimensions
#print axioms universal_extension_finite_frame

end MA4RestartEuler20261003
