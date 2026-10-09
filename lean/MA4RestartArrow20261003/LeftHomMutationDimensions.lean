import MA4RestartArrow20261003.LeftHomMutation
import MA4RestartArrow20261003.CoevaluationExternal
import MA4RestartArrow20261003.ScalarEndDimension
import MA4Coordinator20261003.ExactVertexDimensions
import MA4RestartCoordinator20261003.VertexFiniteness

/-! Actual left Hom mutation with every vertex finite, End finite/rank one,
all-coordinate positive-normalized shear and both outside orthogonality laws.
The finite new vertices are conclusions from old finite vertices. The reused
coordinator VertexFiniteness parent is author-audited and pinned separately;
its independent review status remains explicit in the accompanying evidence. -/
namespace QuiverProofs.MA4RestartArrow20261003.LeftHomMutationDimensions
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open QuiverProofs.MA4RestartArrow20261003.LeftHomMutation
open QuiverProofs.MA4RestartArrow20261003.CoevaluationExternal
open QuiverProofs.MA4RestartArrow20261003.ScalarEndDimension
open QuiverProofs.MACompletionExactVertexDimensions
open QuiverProofs.MA4RestartVertexFiniteness
universe w v u z
variable {K : Type w} [Field K] {C : Type u}
  [Category.{v} C] [Abelian C] [Linear K C] [HasExt.{z} C]
set_option maxHeartbeats 0

/-- Every replacement datum is constructed from old pair/vertex data; the
formula and sign apply to all four coordinates and every n, including zero. -/
theorem left_hom_mutation_with_dimensions (X Y : C) (n : ℕ)
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
    (hCopies : ∀ a, Module.Finite K ((F a).obj (⨁ fun _ : Fin n => Y)))
    (dX dY : Fin 4 → Int)
    (hDimX : ∀ a, (Module.finrank K ((F a).obj X) : Int) = dX a)
    (hDimCopies : ∀ a,
      (Module.finrank K ((F a).obj (⨁ fun _ : Fin n => Y)) : Int) = (n : Int) * dY a) :
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
        ((∀ g : T ⟶ Q, g = 0) ∧ (∀ x : Ext T Q 1, x = 0))) := by
  classical
  let e := biproduct.lift (f := fun _ : Fin n => Y) (fun j => f j)
  let δ := fun a => dX a - (n : Int) * dY a
  obtain ⟨Q, hBranch, hQY, hExtQY, hRigidQ, hEndQ, hIdQ, hLocalQ⟩ :=
    left_hom_mutation_exists X Y n f hHered hReverseHom hReverseExt hForwardExt
      hRigidX hRigidY hIdX hEndX hEndY
  have hFiniteQ : ∀ a, Module.Finite K ((F a).obj Q) := by
    rcases hBranch with hm | he
    · rcases hm with ⟨hm, _, rfl⟩
      letI : Mono e := hm
      exact cokernel_vertex_finite F hZero hLimits hColimits X
        (⨁ fun _ : Fin n => Y) e hCopies
    · rcases he with ⟨he, _, rfl⟩
      letI : Epi e := he
      exact kernel_vertex_finite F hZero hLimits hColimits X
        (⨁ fun _ : Fin n => Y) e hX
  have hPositiveQ : ∃ a, 0 < Module.finrank K ((F a).obj Q) :=
    positive_vertex_dimension_of_nonzero F hJointEpi Q hFiniteQ hIdQ
  have hDimQ : ∀ a, (Module.finrank K ((F a).obj Q) : Int) =
      if (∀ b, 0 ≤ δ b) then δ a else -δ a := by
    rcases hBranch with hm | he
    · rcases hm with ⟨hm, _, rfl⟩
      letI : Mono e := hm
      have hd := mapped_cokernel_dimension_difference F hZero hLimits hColimits
        X (⨁ fun _ : Fin n => Y) e hX hCopies
      dsimp [e] at hd
      have hneg : ¬ ∀ b, 0 ≤ δ b := by
        intro hnn
        obtain ⟨b, hb⟩ := hPositiveQ
        have hdb := hd b
        rw [hDimX b, hDimCopies b] at hdb
        have hnb := hnn b
        dsimp [δ] at hnb
        omega
      intro a
      rw [if_neg hneg]
      have hda := hd a
      rw [hDimX a, hDimCopies a] at hda
      dsimp [δ]
      omega
    · rcases he with ⟨he, _, rfl⟩
      letI : Epi e := he
      have hd := mapped_kernel_dimension_difference F hZero hLimits hColimits
        X (⨁ fun _ : Fin n => Y) e hX hCopies
      dsimp [e] at hd
      have hnonneg : ∀ b, 0 ≤ δ b := by
        intro b
        have hdb := hd b
        rw [hDimX b, hDimCopies b] at hdb
        dsimp [δ]
        omega
      intro a
      rw [if_pos hnonneg]
      simpa only [hDimX a, hDimCopies a] using hd a
  have hOutside : ∀ T : C,
      ((∀ g : X ⟶ T, g = 0) ∧ (∀ x : Ext X T 1, x = 0)) →
      ((∀ g : Y ⟶ T, g = 0) ∧ (∀ x : Ext Y T 1, x = 0)) →
      ((∀ g : Q ⟶ T, g = 0) ∧ (∀ x : Ext Q T 1, x = 0)) := by
    intro T hXT hYT
    rcases hBranch with hm | he
    · rcases hm with ⟨hm, _, rfl⟩
      letI : Mono e := hm
      exact coevaluation_cokernel_outside_orthogonality X Y T n e hXT hYT
    · rcases he with ⟨he, _, rfl⟩
      letI : Epi e := he
      letI := hHered (⨁ fun _ : Fin n => Y)
      exact coevaluation_kernel_outside_orthogonality X Y T n e hXT hYT
  have hInside : ∀ T : C,
      ((∀ g : T ⟶ X, g = 0) ∧ (∀ x : Ext T X 1, x = 0)) →
      ((∀ g : T ⟶ Y, g = 0) ∧ (∀ x : Ext T Y 1, x = 0)) →
      ((∀ g : T ⟶ Q, g = 0) ∧ (∀ x : Ext T Q 1, x = 0)) := by
    intro T hTX hTY
    rcases hBranch with hm | he
    · rcases hm with ⟨hm, _, rfl⟩
      letI : Mono e := hm
      letI := hHered T
      exact coevaluation_cokernel_inside_orthogonality T X Y n e hTX hTY
    · rcases he with ⟨he, _, rfl⟩
      letI : Epi e := he
      exact coevaluation_kernel_inside_orthogonality T X Y n e hTX hTY
  exact ⟨Q, hBranch, hQY, hExtQY, hRigidQ, hEndQ, hIdQ, hLocalQ,
    finite_end_of_scalar_end Q hEndQ, end_finrank_one_of_scalar_end Q hIdQ hEndQ,
    hFiniteQ, hDimQ, hPositiveQ, hOutside, hInside⟩

/-- On nonzero old Hom, pair purity derives forward Ext vanishing before
constructing the finite replacement, its normalized dimension and outside laws. -/
theorem left_hom_mutation_with_dimensions_of_nonzero_hom (X Y : C) (n : ℕ)
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
    (hCopies : ∀ a, Module.Finite K ((F a).obj (⨁ fun _ : Fin n => Y)))
    (dX dY : Fin 4 → Int)
    (hDimX : ∀ a, (Module.finrank K ((F a).obj X) : Int) = dX a)
    (hDimCopies : ∀ a,
      (Module.finrank K ((F a).obj (⨁ fun _ : Fin n => Y)) : Int) = (n : Int) * dY a) :
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
        ((∀ g : T ⟶ Q, g = 0) ∧ (∀ x : Ext T Q 1, x = 0))) := by
  letI := QuiverProofs.MACompletionScalarEndomorphisms.local_end_of_scalar_end X hIdX hEndX
  letI := QuiverProofs.MACompletionScalarEndomorphisms.local_end_of_scalar_end Y hIdY hEndY
  exact left_hom_mutation_with_dimensions X Y n f hHered hReverseHom hReverseExt
    (QuiverProofs.MACompletionPairPurity.extOne_vanishes_of_nonzero_hom_rigid X Y
      hHered hReverseExt hRigidX hRigidY hHom)
    hRigidX hRigidY hIdX hEndX hEndY F hZero hLimits hColimits hJointEpi
    hX hCopies dX dY hDimX hDimCopies

#print axioms left_hom_mutation_with_dimensions
#print axioms left_hom_mutation_with_dimensions_of_nonzero_hom
end QuiverProofs.MA4RestartArrow20261003.LeftHomMutationDimensions
