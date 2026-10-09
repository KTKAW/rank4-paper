import MA4RestartArrow20261003.LeftHomMutationDimensions
import MA4RestartArrow20261003.VertexCopies

/-! Strong actual left Hom mutation using only the original two finite
vertex vectors. Copy spaces and copy dimensions are derived internally;
all next rigidity, scalar/nonzero/local End, finite vertices, positive
normalization, and both outside orthogonality laws remain conclusions. -/
namespace QuiverProofs.MA4RestartArrow20261003.LeftHomMutationOldVertices
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe w v u z
variable {K : Type w} [Field K] {C : Type u}
  [Category.{v} C] [Abelian C] [Linear K C] [HasExt.{z} C]
set_option maxHeartbeats 0

open QuiverProofs.MA4RestartArrow20261003.LeftHomMutationDimensions
open QuiverProofs.MA4RestartArrow20261003.VertexCopies

theorem left_hom_mutation_from_old_vertices (X Y : C) (n : ℕ)
    [HasBiproduct (fun _ : Fin n => Y)]
    (f : Module.Basis (Fin n) K (X ⟶ Y))
    (hHered : ∀ T : C, HasProjectiveDimensionLT T 2)
    (hReverseHom : ∀ g : Y ⟶ X, g = 0)
    (hReverseExt : ∀ x : Ext Y X 1, x = 0)
    (hForwardExt : ∀ x : Ext X Y 1, x = 0)
    (hRigidX : ∀ x : Ext X X 1, x = 0)
    (hRigidY : ∀ x : Ext Y Y 1, x = 0)
    (hIdX : 𝟙 X ≠ 0)
    (hEndX : ∀ g : X ⟶ X, ∃ c : K, g = c • 𝟙 X)
    (hEndY : ∀ g : Y ⟶ Y, ∃ c : K, g = c • 𝟙 Y)
    (F : Fin 4 → C ⥤ ModuleCat.{v} K)
    (hZero : ∀ a, (F a).PreservesZeroMorphisms)
    (hLimits : ∀ a, PreservesFiniteLimits (F a))
    (hColimits : ∀ a, PreservesFiniteColimits (F a))
    (hJointEpi : ∀ {M V : C} (e : M ⟶ V), (∀ a, Epi ((F a).map e)) → Epi e)
    (hX : ∀ a, Module.Finite K ((F a).obj X))
    (hY : ∀ a, Module.Finite K ((F a).obj Y))
    (dX dY : Fin 4 → Int)
    (hDimX : ∀ a, (Module.finrank K ((F a).obj X) : Int) = dX a)
    (hDimY : ∀ a, (Module.finrank K ((F a).obj Y) : Int) = dY a) :
    let e := biproduct.lift (f := fun _ : Fin n => Y) (fun j => f j)
    let δ := fun a => dX a - (n : Int) * dY a
    ∃ Q : C,
      ((Mono e ∧ ¬ Epi e ∧ Q = cokernel e) ∨
       (Epi e ∧ ¬ Mono e ∧ Q = kernel e)) ∧
      (∀ g : Q ⟶ Y, g = 0) ∧
      (∀ x : Ext Q Y 1, x = 0) ∧
      (∀ x : Ext Q Q 1, x = 0) ∧
      (∀ d : Q ⟶ Q, ∃ c : K, d = c • 𝟙 Q) ∧
      𝟙 Q ≠ 0 ∧ IsLocalRing (End Q) ∧
      Module.Finite K (Q ⟶ Q) ∧ Module.finrank K (Q ⟶ Q) = 1 ∧
      (∀ a, Module.Finite K ((F a).obj Q)) ∧
      (∀ a, (Module.finrank K ((F a).obj Q) : Int) =
        if (∀ b, 0 ≤ δ b) then δ a else -δ a) ∧
      (∃ a, 0 < Module.finrank K ((F a).obj Q)) ∧
      (∀ T : C,
        ((∀ g : X ⟶ T, g = 0) ∧ (∀ x : Ext X T 1, x = 0)) →
        ((∀ g : Y ⟶ T, g = 0) ∧ (∀ x : Ext Y T 1, x = 0)) →
        ((∀ g : Q ⟶ T, g = 0) ∧ (∀ x : Ext Q T 1, x = 0))) ∧
      (∀ T : C,
        ((∀ g : T ⟶ X, g = 0) ∧ (∀ x : Ext T X 1, x = 0)) →
        ((∀ g : T ⟶ Y, g = 0) ∧ (∀ x : Ext T Y 1, x = 0)) →
        ((∀ g : T ⟶ Q, g = 0) ∧ (∀ x : Ext T Q 1, x = 0))) :=
  left_hom_mutation_with_dimensions X Y n f hHered hReverseHom hReverseExt
    hForwardExt hRigidX hRigidY hIdX hEndX hEndY F hZero hLimits hColimits hJointEpi
    hX (vertex_copies_finite F hZero hLimits Y n hY) dX dY hDimX
    (vertex_copies_dimension F hZero hLimits Y n hY dY hDimY)

theorem left_hom_mutation_from_old_vertices_of_nonzero_hom (X Y : C) (n : ℕ)
    [HasBiproduct (fun _ : Fin n => Y)]
    (f : Module.Basis (Fin n) K (X ⟶ Y))
    (hHered : ∀ T : C, HasProjectiveDimensionLT T 2)
    (hReverseHom : ∀ g : Y ⟶ X, g = 0)
    (hReverseExt : ∀ x : Ext Y X 1, x = 0)
    (hRigidX : ∀ x : Ext X X 1, x = 0)
    (hRigidY : ∀ x : Ext Y Y 1, x = 0)
    (hIdX : 𝟙 X ≠ 0) (hIdY : 𝟙 Y ≠ 0)
    (hEndX : ∀ g : X ⟶ X, ∃ c : K, g = c • 𝟙 X)
    (hEndY : ∀ g : Y ⟶ Y, ∃ c : K, g = c • 𝟙 Y)
    (hHom : ∃ g : X ⟶ Y, g ≠ 0)
    (F : Fin 4 → C ⥤ ModuleCat.{v} K)
    (hZero : ∀ a, (F a).PreservesZeroMorphisms)
    (hLimits : ∀ a, PreservesFiniteLimits (F a))
    (hColimits : ∀ a, PreservesFiniteColimits (F a))
    (hJointEpi : ∀ {M V : C} (e : M ⟶ V), (∀ a, Epi ((F a).map e)) → Epi e)
    (hX : ∀ a, Module.Finite K ((F a).obj X))
    (hY : ∀ a, Module.Finite K ((F a).obj Y))
    (dX dY : Fin 4 → Int)
    (hDimX : ∀ a, (Module.finrank K ((F a).obj X) : Int) = dX a)
    (hDimY : ∀ a, (Module.finrank K ((F a).obj Y) : Int) = dY a) :
    let e := biproduct.lift (f := fun _ : Fin n => Y) (fun j => f j)
    let δ := fun a => dX a - (n : Int) * dY a
    ∃ Q : C,
      ((Mono e ∧ ¬ Epi e ∧ Q = cokernel e) ∨
       (Epi e ∧ ¬ Mono e ∧ Q = kernel e)) ∧
      (∀ g : Q ⟶ Y, g = 0) ∧
      (∀ x : Ext Q Y 1, x = 0) ∧
      (∀ x : Ext Q Q 1, x = 0) ∧
      (∀ d : Q ⟶ Q, ∃ c : K, d = c • 𝟙 Q) ∧
      𝟙 Q ≠ 0 ∧ IsLocalRing (End Q) ∧
      Module.Finite K (Q ⟶ Q) ∧ Module.finrank K (Q ⟶ Q) = 1 ∧
      (∀ a, Module.Finite K ((F a).obj Q)) ∧
      (∀ a, (Module.finrank K ((F a).obj Q) : Int) =
        if (∀ b, 0 ≤ δ b) then δ a else -δ a) ∧
      (∃ a, 0 < Module.finrank K ((F a).obj Q)) ∧
      (∀ T : C,
        ((∀ g : X ⟶ T, g = 0) ∧ (∀ x : Ext X T 1, x = 0)) →
        ((∀ g : Y ⟶ T, g = 0) ∧ (∀ x : Ext Y T 1, x = 0)) →
        ((∀ g : Q ⟶ T, g = 0) ∧ (∀ x : Ext Q T 1, x = 0))) ∧
      (∀ T : C,
        ((∀ g : T ⟶ X, g = 0) ∧ (∀ x : Ext T X 1, x = 0)) →
        ((∀ g : T ⟶ Y, g = 0) ∧ (∀ x : Ext T Y 1, x = 0)) →
        ((∀ g : T ⟶ Q, g = 0) ∧ (∀ x : Ext T Q 1, x = 0))) :=
  left_hom_mutation_with_dimensions_of_nonzero_hom X Y n f hHered hReverseHom hReverseExt
    hRigidX hRigidY hIdX hIdY hEndX hEndY hHom F hZero hLimits hColimits hJointEpi
    hX (vertex_copies_finite F hZero hLimits Y n hY) dX dY hDimX
    (vertex_copies_dimension F hZero hLimits Y n hY dY hDimY)

#print axioms left_hom_mutation_from_old_vertices
#print axioms left_hom_mutation_from_old_vertices_of_nonzero_hom
end QuiverProofs.MA4RestartArrow20261003.LeftHomMutationOldVertices
