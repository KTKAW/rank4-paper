import MA4RestartCoordinator20261003.WeightedQuiverModel
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.Algebra.Module.Projective

/-! Free path representations, with no finiteness assumption on path sets.
The actual Hom correspondence is used to lift through epimorphisms.
No hereditary resolution or Euler identity is assumed or concluded here. -/
namespace QuiverProofs.MA4RestartFreePathProjectives
open CategoryTheory CategoryTheory.Limits
open QuiverProofs.MA4RestartWeightedQuiverModel
set_option maxHeartbeats 0
noncomputable section
variable (B : Matrix 4) (K : Type) [Field K]

local instance representationFiniteBiproducts : HasFiniteBiproducts (Representation B K) :=
  Abelian.hasFiniteBiproducts

/-- All finitely supported path-labelled vectors from a fixed source. -/
def freePath (i : Paths (Vertex B)) (W : ModuleCat.{0} K) : Representation B K where
  obj j := ModuleCat.of K ((i ⟶ j) →₀ W)
  map f := ModuleCat.ofHom (Finsupp.lmapDomain W K (fun p => p ≫ f))
  map_id j := by
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext
    intro p x
    simp
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext
    intro p x
    simp [Category.assoc]

/-- The lift of a linear map at the source along every path. -/
def freePathDesc (i : Paths (Vertex B)) (W : ModuleCat.{0} K)
    (M : Representation B K) (f : W ⟶ M.obj i) : freePath B K i W ⟶ M where
  app j := ModuleCat.ofHom (Finsupp.lsum K (fun p : i ⟶ j => (f ≫ M.map p).hom))
  naturality {j l} g := by
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext
    intro p x
    simp only [freePath, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
      LinearMap.comp_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
      Finsupp.lsum_single]
    exact congrArg (fun h : M.obj i ⟶ M.obj l => h (f x)) (M.map_comp p g)

theorem freePathDesc_single (i j : Paths (Vertex B)) (W : ModuleCat.{0} K)
    (M : Representation B K) (f : W ⟶ M.obj i) (p : i ⟶ j) (x : W) :
    (freePathDesc B K i W M f).app j (Finsupp.single p x) = M.map p (f x) := by
  change (Finsupp.lsum K (fun q : i ⟶ j => (f ≫ M.map q).hom))
    (Finsupp.single p x) = _
  rw [Finsupp.lsum_single]
  rfl

/-- Evaluation on the nil path is the inverse of the path lift. -/
def freePathRestrict (i : Paths (Vertex B)) (W : ModuleCat.{0} K)
    (M : Representation B K) (f : freePath B K i W ⟶ M) : W ⟶ M.obj i :=
  ModuleCat.ofHom ((f.app i).hom.comp (Finsupp.lsingle (𝟙 i)))

theorem freePathRestrict_desc (i : Paths (Vertex B)) (W : ModuleCat.{0} K)
    (M : Representation B K) (f : W ⟶ M.obj i) :
    freePathRestrict B K i W M (freePathDesc B K i W M f) = f := by
  apply ModuleCat.hom_ext
  ext x
  change (Finsupp.lsum K (fun p : i ⟶ i => (f ≫ M.map p).hom))
    (Finsupp.single (𝟙 i) x) = f x
  simp [Finsupp.lsum_single]

theorem freePathDesc_restrict (i : Paths (Vertex B)) (W : ModuleCat.{0} K)
    (M : Representation B K) (f : freePath B K i W ⟶ M) :
    freePathDesc B K i W M (freePathRestrict B K i W M f) = f := by
  apply NatTrans.ext
  funext j
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro p x
  have h := congrArg (fun g : (freePath B K i W).obj i ⟶ M.obj j =>
    g (Finsupp.single (𝟙 i) x)) (f.naturality p)
  simpa [freePath, freePathDesc, freePathRestrict] using h.symm

/-- Actual evaluation correspondence; neither endpoint Hom space is supplied. -/
def freePathHomEquiv (i : Paths (Vertex B)) (W : ModuleCat.{0} K)
    (M : Representation B K) : (freePath B K i W ⟶ M) ≃ (W ⟶ M.obj i) where
  toFun := freePathRestrict B K i W M
  invFun := freePathDesc B K i W M
  left_inv := freePathDesc_restrict B K i W M
  right_inv := freePathRestrict_desc B K i W M

/-- The path-Hom correspondence respects the actual scalar composition. -/
def freePathHomLinearEquiv (i : Paths (Vertex B)) (W : ModuleCat.{0} K)
    (M : Representation B K) : (freePath B K i W ⟶ M) ≃ₗ[K] (W ⟶ M.obj i) where
  __ := freePathHomEquiv B K i W M
  map_add' f g := by rfl
  map_smul' c f := by rfl

theorem freePathRestrict_comp (i : Paths (Vertex B)) (W : ModuleCat.{0} K)
    (M N : Representation B K) (f : freePath B K i W ⟶ M) (g : M ⟶ N) :
    freePathRestrict B K i W N (f ≫ g) = freePathRestrict B K i W M f ≫ g.app i := by
  apply ModuleCat.hom_ext
  rfl

/-- Every field vector space is projective, including infinite-dimensional ones. -/
theorem modulecat_field_projective (W : ModuleCat.{0} K) : Projective W := by
  refine ⟨?_⟩
  intro E X f e _
  obtain ⟨g, hg⟩ := Module.projective_lifting_property e.hom f.hom
    ((ModuleCat.epi_iff_surjective e).mp inferInstance)
  exact ⟨ModuleCat.ofHom g, ModuleCat.hom_ext hg⟩

/-- Projectivity is lifted by the actual path-Hom correspondence, rather than
inferred from projectivity of the vertex spaces. -/
theorem freePath_projective (i : Paths (Vertex B)) (W : ModuleCat.{0} K) :
    Projective (freePath B K i W) := by
  letI : Projective W := modulecat_field_projective K W
  refine ⟨?_⟩
  intro E X f e _
  obtain ⟨g, hg⟩ := Projective.factors (freePathRestrict B K i W X f) (e.app i)
  refine ⟨freePathDesc B K i W E g, ?_⟩
  apply (freePathHomEquiv B K i W X).injective
  change freePathRestrict B K i W X (freePathDesc B K i W E g ≫ e) = _
  rw [freePathRestrict_comp, freePathRestrict_desc, hg]
  rfl

/-- A finite vertex sum supplies an actual projective cover of every representation. -/
def freeCover (M : Representation B K) : Representation B K :=
  ⨁ fun i : Vertex B => freePath B K (i : Paths (Vertex B)) (M.obj i)

theorem freeCover_projective (M : Representation B K) : Projective (freeCover B K M) := by
  letI (i : Vertex B) : Projective (freePath B K (i : Paths (Vertex B)) (M.obj i)) :=
    freePath_projective B K i (M.obj i)
  unfold freeCover
  infer_instance

def freeCoverTo (M : Representation B K) : freeCover B K M ⟶ M :=
  biproduct.desc fun i => freePathDesc B K i (M.obj i) M (𝟙 (M.obj i))

theorem freeCoverTo_epi (M : Representation B K) : Epi (freeCoverTo B K M) := by
  apply (NatTrans.epi_iff_epi_app _).mpr
  intro j
  apply (ModuleCat.epi_iff_surjective _).mpr
  intro x
  refine ⟨(biproduct.ι (fun i : Vertex B => freePath B K i (M.obj i)) j).app j
    (Finsupp.single (𝟙 j) x), ?_⟩
  change ((biproduct.ι (fun i : Vertex B => freePath B K i (M.obj i)) j ≫
    freeCoverTo B K M).app j) (Finsupp.single (𝟙 j) x) = x
  rw [freeCoverTo, biproduct.ι_desc]
  rw [freePathDesc_single]
  simp

/-- The fixed original model has enough projectives, with no caller-supplied
presentation and no restriction on weights, supports, or path sets. -/
theorem representation_enoughProjectives : EnoughProjectives (Representation B K) := by
  refine ⟨?_⟩
  intro M
  letI : Projective (freeCover B K M) := freeCover_projective B K M
  letI : Epi (freeCoverTo B K M) := freeCoverTo_epi B K M
  exact ⟨{ p := freeCover B K M, f := freeCoverTo B K M }⟩

#print axioms freePath_projective
#print axioms freeCoverTo_epi
#print axioms representation_enoughProjectives

end
end QuiverProofs.MA4RestartFreePathProjectives
