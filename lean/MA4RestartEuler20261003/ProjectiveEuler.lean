import MA4RestartEuler20261003.UniversalLeft
import MA4RestartCoordinator20261003.FreePathProjectives
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Actual Hom/Ext Euler identity of a length-one projective presentation. -/
universe r w v u
namespace MA4RestartEuler20261003
open Module CategoryTheory CategoryTheory.Category CategoryTheory.Limits
  CategoryTheory.Abelian CategoryTheory.Preadditive
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
variable (K : Type r) [Field K] [Linear K C] [EnoughProjectives C]

omit [HasExt.{w} C] [EnoughProjectives C] in
def homPrecompose {A B : C} (f : A ⟶ B) (N : C) : (B ⟶ N) →ₗ[K] (A ⟶ N) where
  toFun g := f ≫ g
  map_add' g h := by simp
  map_smul' c g := by simp

omit [HasExt.{w} C] [EnoughProjectives C] in
lemma hom_precompose_injective {A B : C} (f : A ⟶ B) [Epi f] (N : C) :
    Function.Injective (homPrecompose K f N) := by
  intro g h he
  exact (cancel_epi f).mp he

omit [HasExt.{w} C] [EnoughProjectives C] in
noncomputable def finiteBiproductHomCoordinates {J : Type} [Fintype J]
    (R : J → C) [HasBiproduct R] (N : C) :
    ((⨁ R) ⟶ N) ≃ₗ[K] (∀ j, R j ⟶ N) where
  toFun f j := biproduct.ι R j ≫ f
  invFun f := biproduct.desc f
  left_inv f := by apply biproduct.hom_ext'; intro j; simp
  right_inv f := by funext j; simp
  map_add' f g := by funext j; simp
  map_smul' c f := by funext j; simp

omit [HasExt.{w} C] [EnoughProjectives C] in
lemma finite_biproduct_hom_finite {J : Type} [Fintype J]
    (R : J → C) [HasBiproduct R] (N : C)
    (h : ∀ j, Module.Finite K (R j ⟶ N)) : Module.Finite K ((⨁ R) ⟶ N) := by
  letI (j : J) : Module.Finite K (R j ⟶ N) := h j
  let e := finiteBiproductHomCoordinates K R N
  exact Module.Finite.of_injective e.toLinearMap e.injective

omit [HasExt.{w} C] [EnoughProjectives C] in
lemma finite_biproduct_hom_finrank {J : Type} [Fintype J]
    (R : J → C) [HasBiproduct R] (N : C)
    (h : ∀ j, Module.Finite K (R j ⟶ N)) :
    Module.finrank K ((⨁ R) ⟶ N) = ∑ j, Module.finrank K (R j ⟶ N) := by
  letI (j : J) : Module.Finite K (R j ⟶ N) := h j
  rw [(finiteBiproductHomCoordinates K R N).finrank_eq]
  exact Module.finrank_pi_fintype K

noncomputable def projectiveResolutionBoundary {S : ShortComplex C}
    (hS : S.ShortExact) (N : C) : (S.X₁ ⟶ N) →ₗ[K] Ext S.X₃ N 1 :=
  leftExtensionBoundary K hS N

lemma projective_boundary_surjective {S : ShortComplex C}
    (hS : S.ShortExact) [Projective S.X₂] (N : C) :
    Function.Surjective (projectiveResolutionBoundary K hS N) := by
  intro e
  obtain ⟨a,ha⟩ := Ext.contravariant_sequence_exact₃ hS N e
    (Ext.eq_zero_of_projective _) (show 1 + 0 = 1 by rfl)
  refine ⟨Ext.homEquiv₀ a, ?_⟩
  dsimp [projectiveResolutionBoundary,leftExtensionBoundary]
  rw [Ext.mk₀_homEquiv₀_apply]
  exact ha

lemma projective_boundary_kernel {S : ShortComplex C}
    (hS : S.ShortExact) (N : C) :
    LinearMap.ker (projectiveResolutionBoundary K hS N) =
      LinearMap.range (homPrecompose K S.f N) := by
  ext f
  constructor
  · intro hf
    have hz : hS.extClass.comp (Ext.mk₀ f) (add_zero 1) = 0 := hf
    obtain ⟨a,ha⟩ := Ext.contravariant_sequence_exact₁ hS N (Ext.mk₀ f)
      (show 1 + 0 = 1 by rfl) hz
    refine ⟨Ext.homEquiv₀ a, ?_⟩
    apply Ext.homEquiv₀.symm.injective
    dsimp [homPrecompose]
    rw [← Ext.mk₀_comp_mk₀, Ext.mk₀_homEquiv₀_apply]
    exact ha
  · rintro ⟨g,rfl⟩
    change hS.extClass.comp (Ext.mk₀ (S.f ≫ g)) (add_zero 1) = 0
    rw [← Ext.mk₀_comp_mk₀, ← Ext.comp_assoc_of_third_deg_zero,
      hS.extClass_comp, Ext.zero_comp]

noncomputable def projectiveExtQuotientEquiv {S : ShortComplex C}
    (hS : S.ShortExact) [Projective S.X₂] (N : C) :
    ((S.X₁ ⟶ N) ⧸ LinearMap.range (homPrecompose K S.f N)) ≃ₗ[K] Ext S.X₃ N 1 := by
  rw [← projective_boundary_kernel K hS N]
  exact LinearMap.quotKerEquivOfSurjective (projectiveResolutionBoundary K hS N)
    (projective_boundary_surjective K hS N)

omit [HasExt.{w} C] [EnoughProjectives C] in
noncomputable def resolutionHomKernelEquiv {S : ShortComplex C}
    (hS : S.ShortExact) (N : C) :
    (S.X₃ ⟶ N) ≃ₗ[K] LinearMap.ker (homPrecompose K S.f N) where
  toFun f := ⟨S.g ≫ f, by change S.f ≫ (S.g ≫ f) = 0; rw [← Category.assoc,S.zero,zero_comp]⟩
  invFun x := hS.gIsCokernel.desc (CokernelCofork.ofπ x.val x.property)
  left_inv f := by
    letI : Epi S.g := hS.epi_g
    apply (cancel_epi S.g).mp
    exact hS.gIsCokernel.fac _ WalkingParallelPair.one
  right_inv x := by
    apply Subtype.ext
    exact hS.gIsCokernel.fac _ WalkingParallelPair.one
  map_add' f g := by apply Subtype.ext; change S.g ≫ (f + g) = _; simp
  map_smul' c f := by apply Subtype.ext; change S.g ≫ (c • f) = _; simp

omit [EnoughProjectives C] in
lemma projective_resolution_ext_ge_two_zero {S : ShortComplex C}
    (hS : S.ShortExact) [Projective S.X₁] [Projective S.X₂] (N : C) (n : ℕ) :
    ∀ e : Ext S.X₃ N (n + 2), e = 0 := by
  intro e
  obtain ⟨a,ha⟩ := Ext.contravariant_sequence_exact₃ hS N e
    (Ext.eq_zero_of_projective _) (show 1 + (n + 1) = n + 2 by omega)
  rw [Ext.eq_zero_of_projective a,Ext.comp_zero] at ha
  exact ha.symm

lemma projective_resolution_finite_euler {S : ShortComplex C}
    (hS : S.ShortExact) [Projective S.X₁] [Projective S.X₂] (N : C)
    [Module.Finite K (S.X₂ ⟶ N)] [Module.Finite K (S.X₁ ⟶ N)] :
    Module.Finite K (S.X₃ ⟶ N) ∧ Module.Finite K (Ext S.X₃ N 1) ∧
    ((Module.finrank K (S.X₃ ⟶ N) : Int) - (Module.finrank K (Ext S.X₃ N 1) : Int) =
      (Module.finrank K (S.X₂ ⟶ N) : Int) - (Module.finrank K (S.X₁ ⟶ N) : Int)) ∧
    (∀ n, ∀ e : Ext S.X₃ N (n + 2), e = 0) := by
  letI : Epi S.g := hS.epi_g
  letI : Module.Finite K (S.X₃ ⟶ N) := Module.Finite.of_injective
    (homPrecompose K S.g N) (hom_precompose_injective K S.g N)
  let δ := projectiveResolutionBoundary K hS N
  have hδ : Function.Surjective δ := projective_boundary_surjective K hS N
  letI : Module.Finite K (Ext S.X₃ N 1) := Module.Finite.of_surjective δ hδ
  refine ⟨inferInstance,inferInstance,?_,projective_resolution_ext_ge_two_zero hS N⟩
  have h₀ := (homPrecompose K S.f N).finrank_range_add_finrank_ker
  have h₁ := δ.finrank_range_add_finrank_ker
  have hr : LinearMap.range δ = ⊤ := LinearMap.range_eq_top.mpr hδ
  rw [hr, finrank_top] at h₁
  rw [projective_boundary_kernel K hS N] at h₁
  rw [← (resolutionHomKernelEquiv K hS N).finrank_eq] at h₀
  have h₀i : (Module.finrank K (LinearMap.range (homPrecompose K S.f N)) : Int) +
      (Module.finrank K (S.X₃ ⟶ N) : Int) = (Module.finrank K (S.X₂ ⟶ N) : Int) := by
    exact_mod_cast h₀
  have h₁i : (Module.finrank K (Ext S.X₃ N 1) : Int) +
      (Module.finrank K (LinearMap.range (homPrecompose K S.f N)) : Int) =
      (Module.finrank K (S.X₁ ⟶ N) : Int) := by
    exact_mod_cast h₁
  omega

#print axioms projective_resolution_finite_euler

end MA4RestartEuler20261003

namespace QuiverProofs.MA4RestartModelExt
open Module CategoryTheory CategoryTheory.Limits MA4RestartWeightedQuiverModel
  MA4RestartFreePathProjectives
variable (B : Matrix 4) (K : Type) [Field K]

noncomputable def moduleHomCoordinates (W V : ModuleCat.{0} K) [Module.Finite K W] :
    (W ⟶ V) ≃ₗ[K] (Fin (Module.finrank K W) → V) :=
  (ModuleCat.homLinearEquiv (R := K) (S := K)).trans ((Module.finBasis K W).constr K).symm

theorem module_hom_finite (W V : ModuleCat.{0} K)
    [Module.Finite K W] [Module.Finite K V] : Module.Finite K (W ⟶ V) := by
  let e := moduleHomCoordinates K W V
  exact Module.Finite.of_injective e.toLinearMap e.injective

theorem module_hom_finrank (W V : ModuleCat.{0} K)
    [Module.Finite K W] [Module.Finite K V] :
    Module.finrank K (W ⟶ V) = Module.finrank K W * Module.finrank K V := by
  rw [(moduleHomCoordinates K W V).finrank_eq]
  simp [Module.finrank_pi_fintype]

theorem free_path_hom_finite (i : Vertex B) (W : ModuleCat.{0} K)
    (N : Representation B K) [Module.Finite K W] [Module.Finite K (N.obj i)] :
    Module.Finite K (freePath B K i W ⟶ N) := by
  letI := module_hom_finite K W (N.obj i)
  let e := freePathHomLinearEquiv B K i W N
  exact Module.Finite.of_injective e.toLinearMap e.injective

theorem free_path_hom_finrank (i : Vertex B) (W : ModuleCat.{0} K)
    (N : Representation B K) [Module.Finite K W] [Module.Finite K (N.obj i)] :
    Module.finrank K (freePath B K i W ⟶ N) =
      Module.finrank K W * Module.finrank K (N.obj i) := by
  rw [(freePathHomLinearEquiv B K i W N).finrank_eq]
  exact module_hom_finrank K W (N.obj i)

theorem finite_free_path_family_hom_finite {J : Type} [Fintype J]
    (i : J → Vertex B) (W : J → ModuleCat.{0} K) (N : Representation B K)
    [HasBiproduct (fun j => freePath B K (i j) (W j))]
    (hW : ∀ j, Module.Finite K (W j)) (hN : ∀ j, Module.Finite K (N.obj (i j))) :
    Module.Finite K ((⨁ fun j => freePath B K (i j) (W j)) ⟶ N) := by
  apply MA4RestartEuler20261003.finite_biproduct_hom_finite K
  intro j
  letI := hW j
  letI := hN j
  exact free_path_hom_finite B K (i j) (W j) N

theorem finite_free_path_family_hom_finrank {J : Type} [Fintype J]
    (i : J → Vertex B) (W : J → ModuleCat.{0} K) (N : Representation B K)
    [HasBiproduct (fun j => freePath B K (i j) (W j))]
    (hW : ∀ j, Module.Finite K (W j)) (hN : ∀ j, Module.Finite K (N.obj (i j))) :
    Module.finrank K ((⨁ fun j => freePath B K (i j) (W j)) ⟶ N) =
      ∑ j, Module.finrank K (W j) * Module.finrank K (N.obj (i j)) := by
  have hH : ∀ j, Module.Finite K (freePath B K (i j) (W j) ⟶ N) := by
    intro j
    letI := hW j
    letI := hN j
    exact free_path_hom_finite B K (i j) (W j) N
  rw [MA4RestartEuler20261003.finite_biproduct_hom_finrank K _ _ hH]
  apply Finset.sum_congr rfl
  intro j _
  letI := hW j
  letI := hN j
  exact free_path_hom_finrank B K (i j) (W j) N

/-- Actual Ext smallness is derived on the fixed model, not an unresolved model input. -/
theorem representation_hasExt : HasExt.{0} (Representation B K) := by
  letI : EnoughProjectives (Representation B K) := representation_enoughProjectives B K
  exact hasExt_of_enoughProjectives (Representation B K)

local instance modelEnoughProjectives : EnoughProjectives (Representation B K) :=
  representation_enoughProjectives B K

local instance modelHasExt : HasExt.{0} (Representation B K) := representation_hasExt B K

theorem model_projective_resolution_finite_euler {S : ShortComplex (Representation B K)}
    (hS : S.ShortExact) [Projective S.X₁] [Projective S.X₂] (N : Representation B K)
    [Module.Finite K (S.X₂ ⟶ N)] [Module.Finite K (S.X₁ ⟶ N)] :
    Module.Finite K (S.X₃ ⟶ N) ∧ Module.Finite K (Abelian.Ext S.X₃ N 1) ∧
    ((Module.finrank K (S.X₃ ⟶ N) : Int) - (Module.finrank K (Abelian.Ext S.X₃ N 1) : Int) =
      (Module.finrank K (S.X₂ ⟶ N) : Int) - (Module.finrank K (S.X₁ ⟶ N) : Int)) ∧
    (∀ n, ∀ e : Abelian.Ext S.X₃ N (n + 2), e = 0) :=
  MA4RestartEuler20261003.projective_resolution_finite_euler K hS N

theorem finite_free_path_resolution_euler
    {J₀ J₁ : Type} [Fintype J₀] [Fintype J₁]
    (i₀ : J₀ → Vertex B) (W₀ : J₀ → ModuleCat.{0} K)
    (i₁ : J₁ → Vertex B) (W₁ : J₁ → ModuleCat.{0} K)
    [HasBiproduct (fun j => freePath B K (i₀ j) (W₀ j))]
    [HasBiproduct (fun j => freePath B K (i₁ j) (W₁ j))]
    (M N : Representation B K)
    (d : (⨁ fun j => freePath B K (i₁ j) (W₁ j)) ⟶
      (⨁ fun j => freePath B K (i₀ j) (W₀ j)))
    (p : (⨁ fun j => freePath B K (i₀ j) (W₀ j)) ⟶ M)
    (wdp : d ≫ p = 0) (hS : (ShortComplex.mk d p wdp).ShortExact)
    (hW₀ : ∀ j, Module.Finite K (W₀ j)) (hW₁ : ∀ j, Module.Finite K (W₁ j))
    (hN : ∀ a, Module.Finite K ((vertexFunctor B K a).obj N)) :
    Module.Finite K (M ⟶ N) ∧ Module.Finite K (Abelian.Ext M N 1) ∧
    ((Module.finrank K (M ⟶ N) : Int) - (Module.finrank K (Abelian.Ext M N 1) : Int) =
      ((∑ j, Module.finrank K (W₀ j) * Module.finrank K (N.obj (i₀ j))) : Int) -
      ((∑ j, Module.finrank K (W₁ j) * Module.finrank K (N.obj (i₁ j))) : Int)) ∧
    (∀ n, ∀ e : Abelian.Ext M N (n + 2), e = 0) := by
  have hN₀ : ∀ j, Module.Finite K (N.obj (i₀ j)) := fun j => hN (i₀ j).index
  have hN₁ : ∀ j, Module.Finite K (N.obj (i₁ j)) := fun j => hN (i₁ j).index
  letI (j : J₀) : Projective (freePath B K (i₀ j) (W₀ j)) :=
    freePath_projective B K (i₀ j) (W₀ j)
  letI (j : J₁) : Projective (freePath B K (i₁ j) (W₁ j)) :=
    freePath_projective B K (i₁ j) (W₁ j)
  letI : Projective (⨁ fun j => freePath B K (i₀ j) (W₀ j)) := inferInstance
  letI : Projective (⨁ fun j => freePath B K (i₁ j) (W₁ j)) := inferInstance
  letI := finite_free_path_family_hom_finite B K i₀ W₀ N hW₀ hN₀
  letI := finite_free_path_family_hom_finite B K i₁ W₁ N hW₁ hN₁
  obtain ⟨hHom,hExt,hd,hHigher⟩ := model_projective_resolution_finite_euler B K hS N
  refine ⟨hHom,hExt,?_,hHigher⟩
  change (Module.finrank K (M ⟶ N) : Int) -
    (Module.finrank K (Abelian.Ext M N 1) : Int) =
    (Module.finrank K ((⨁ fun j => freePath B K (i₀ j) (W₀ j)) ⟶ N) : Int) -
    (Module.finrank K ((⨁ fun j => freePath B K (i₁ j) (W₁ j)) ⟶ N) : Int) at hd
  rw [finite_free_path_family_hom_finrank B K i₀ W₀ N hW₀ hN₀,
    finite_free_path_family_hom_finrank B K i₁ W₁ N hW₁ hN₁] at hd
  simpa only [Nat.cast_sum,Nat.cast_mul] using hd

#print axioms model_projective_resolution_finite_euler
#print axioms finite_free_path_resolution_euler

#print axioms representation_hasExt
end QuiverProofs.MA4RestartModelExt
