import QuiverProofs.Mutation
import Mathlib.CategoryTheory.PathCategory.Basic
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Linear.FunctorCategory
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! An actual fixed weighted-quiver representation category for every original
integer matrix. Vertex evaluation is constructed, exact, preserves monomorphisms,
jointly reflects epimorphisms, and finite vertex objects have finite Hom spaces.
EnoughProjectives, the hereditary resolution, the Euler identity, and complete
root-frame realization are not proved by this file. -/
namespace QuiverProofs.MA4RestartWeightedQuiverModel
open CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 0

/-- A distinct four-vertex type keeps the original matrix in its quiver instance. -/
structure Vertex (B : Matrix 4) where
  index : Fin 4
deriving DecidableEq

def vertexEquiv (B : Matrix 4) : Vertex B ≃ Fin 4 where
  toFun := Vertex.index
  invFun := fun a => ⟨a⟩
  left_inv := by intro a; cases a; rfl
  right_inv := by intro a; rfl

instance vertexFintype (B : Matrix 4) : Fintype (Vertex B) :=
  Fintype.ofEquiv (Fin 4) (vertexEquiv B).symm

/-- Exactly max(B_ij,0) arrows i→j; negative and zero entries give no arrows. -/
instance weightedQuiver (B : Matrix 4) : Quiver (Vertex B) where
  Hom i j := Fin (B i.index j.index).toNat

instance weightedArrowFintype (B : Matrix 4) (i j : Vertex B) :
    Fintype (Quiver.Hom i j) := by
  change Fintype (Fin (B i.index j.index).toNat)
  infer_instance

/-- The category remains fixed throughout all mutations from this B. -/
abbrev Representation (B : Matrix 4) (K : Type) [Field K] :=
  Paths (Vertex B) ⥤ ModuleCat.{0} K

/-- Actual vertex evaluation, on the original four coordinate labels. -/
def vertexFunctor (B : Matrix 4) (K : Type) [Field K] (a : Fin 4) :
    Representation B K ⥤ ModuleCat.{0} K :=
  (evaluation (Paths (Vertex B)) (ModuleCat.{0} K)).obj (⟨a⟩ : Vertex B)

variable (B : Matrix 4) (K : Type) [Field K]

noncomputable def representation_abelian : Abelian (Representation B K) := inferInstance

def representation_linear : Linear K (Representation B K) := inferInstance

theorem vertex_preserves_zero (a : Fin 4) :
    (vertexFunctor B K a).PreservesZeroMorphisms := by
  unfold vertexFunctor
  infer_instance

theorem vertex_preserves_finite_limits (a : Fin 4) :
    PreservesFiniteLimits (vertexFunctor B K a) := by
  unfold vertexFunctor
  infer_instance

theorem vertex_preserves_finite_colimits (a : Fin 4) :
    PreservesFiniteColimits (vertexFunctor B K a) := by
  unfold vertexFunctor
  infer_instance

theorem vertex_preserves_mono {M N : Representation B K} (f : M ⟶ N) [Mono f] :
    ∀ a, Mono ((vertexFunctor B K a).map f) := by
  intro a
  unfold vertexFunctor
  infer_instance

theorem vertices_jointly_reflect_epi {M N : Representation B K} (f : M ⟶ N)
    (h : ∀ a, Epi ((vertexFunctor B K a).map f)) : Epi f := by
  apply (NatTrans.epi_iff_epi_app f).mpr
  intro a
  cases a with
  | mk a => exact h a

/-- Natural transformations embed linearly into the actual four vertex Hom spaces. -/
def vertexHomEmbedding (M N : Representation B K) :
    (M ⟶ N) →ₗ[K]
      (∀ a : Fin 4, ((vertexFunctor B K a).obj M ⟶ (vertexFunctor B K a).obj N)) :=
  LinearMap.pi (fun a => NatTrans.appLinearMap (R := K) (F := M) (G := N)
    (⟨a⟩ : Paths (Vertex B)))

theorem vertexHomEmbedding_injective (M N : Representation B K) :
    Function.Injective (vertexHomEmbedding B K M N) := by
  intro f g h
  apply NatTrans.ext
  funext a
  cases a with
  | mk a => exact congrArg (fun p => p a) h

/-- Finite old vertex spaces construct finiteness of the actual Hom space;
it is not an abstract dimension supplied by a root-frame realization. -/
theorem finite_hom_of_finite_vertices (M N : Representation B K)
    (hM : ∀ a, Module.Finite K ((vertexFunctor B K a).obj M))
    (hN : ∀ a, Module.Finite K ((vertexFunctor B K a).obj N)) :
    Module.Finite K (M ⟶ N) := by
  classical
  letI (a : Fin 4) : Module.Finite K ((vertexFunctor B K a).obj M) := hM a
  letI (a : Fin 4) : Module.Finite K ((vertexFunctor B K a).obj N) := hN a
  let basis (a : Fin 4) := Module.finBasis K ((vertexFunctor B K a).obj M)
  let e : (M ⟶ N) →ₗ[K]
      (∀ a : Fin 4, Fin (Module.finrank K ((vertexFunctor B K a).obj M)) →
        (vertexFunctor B K a).obj N) :=
    { toFun := fun f a i => ((vertexFunctor B K a).map f) (basis a i)
      map_add' := by intro f g; rfl
      map_smul' := by intro c f; rfl }
  have he : Function.Injective e := by
    intro f g h
    apply NatTrans.ext
    funext a
    cases a with
    | mk a =>
      apply ModuleCat.hom_ext
      apply (basis a).ext
      intro i
      exact congrArg (fun p => p a i) h
  exact Module.Finite.of_injective e he

#print axioms vertices_jointly_reflect_epi
#print axioms vertexHomEmbedding_injective
#print axioms finite_hom_of_finite_vertices
end QuiverProofs.MA4RestartWeightedQuiverModel
