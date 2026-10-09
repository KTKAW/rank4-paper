import MA4RestartArrow20261003.CoevaluationKernel
import MA4Coordinator20261003.PairPurity

/-! Construct the left Hom-mutation object from old exceptional-pair data.
For coevaluation e:X→Y^n the replacement tuple is (Y,Q), with Q the actual
cokernel or kernel. Both strict branches and replacement exceptionality are
derived. The positive-Hom version derives forward Ext vanishing by pair
purity. No fixed representation model or root-frame realization is asserted. -/
namespace QuiverProofs.MA4RestartArrow20261003.LeftHomMutation
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open QuiverProofs.MA4RestartArrow20261003.CoevaluationMap
open QuiverProofs.MA4RestartArrow20261003.CoevaluationCokernel
open QuiverProofs.MA4RestartArrow20261003.CoevaluationKernel
open QuiverProofs.MACompletionScalarEndomorphisms
open QuiverProofs.MACompletionPairPurity
universe w v u z
variable {K : Type w} [Field K] {C : Type u}
  [Category.{v} C] [Abelian C] [Linear K C] [HasExt.{z} C]
set_option maxHeartbeats 0

/-- All finite multiplicities, including zero, with the forward Ext-zero
Hom branch explicit. No map branch or new-object properties are premises. -/
theorem left_hom_mutation_exists (X Y : C) (n : ℕ)
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
    (hEndY : ∀ g : Y ⟶ Y, ∃ c : K, g = c • 𝟙 Y) :
    let e := biproduct.lift (f := fun _ : Fin n => Y) (fun j => f j)
    ∃ Q : C,
      ((Mono e ∧ ¬ Epi e ∧ Q = cokernel e) ∨
       (Epi e ∧ ¬ Mono e ∧ Q = kernel e)) ∧
      (∀ g : Q ⟶ Y, g = 0) ∧
      (∀ x : Ext Q Y 1, x = 0) ∧
      (∀ x : Ext Q Q 1, x = 0) ∧
      (∀ d : Q ⟶ Q, ∃ c : K, d = c • 𝟙 Q) ∧
      𝟙 Q ≠ 0 ∧ IsLocalRing (End Q) := by
  let e := biproduct.lift (f := fun _ : Fin n => Y) (fun j => f j)
  rcases hom_basis_coevaluation_strict_branches X Y n f hEndX hEndY
    hHered hReverseExt hReverseHom hIdX with hm | he
  · letI : Mono e := hm.1
    letI := hHered (cokernel e)
    refine ⟨cokernel e, Or.inl ⟨hm.1, hm.2, rfl⟩,
      hom_coevaluation_cokernel_summand_zero X Y n f hEndY,
      extOne_coevaluation_cokernel_summand_zero X Y n f hRigidY,
      coevaluation_cokernel_rigid X Y n f hRigidY,
      coevaluation_cokernel_scalar_end X Y n f hReverseExt hEndX hEndY,
      cokernel_id_ne_zero_of_not_epi e hm.2,
      coevaluation_cokernel_local_end X Y n f hm.2 hReverseExt hEndX hEndY⟩
  · letI : Epi e := he.1
    letI := hHered (⨁ fun _ : Fin n => Y)
    refine ⟨kernel e, Or.inr ⟨he.1, he.2, rfl⟩,
      hom_coevaluation_kernel_summand_zero X Y n f hRigidY,
      extOne_coevaluation_kernel_summand_zero X Y n f hForwardExt,
      coevaluation_kernel_rigid X Y n f hRigidX hRigidY,
      coevaluation_kernel_scalar_end X Y n f hReverseExt hEndX,
      kernel_id_ne_zero_of_not_mono e he.2,
      coevaluation_kernel_local_end X Y n f he.2 hReverseExt hEndX⟩

/-- Nonzero old Hom derives the missing forward Ext-zero fact by accepted
pair purity, then constructs the actual left replacement and local End. -/
theorem left_hom_mutation_of_nonzero_hom (X Y : C) (n : ℕ)
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
    (hHom : ∃ g : X ⟶ Y, g ≠ 0) :
    let e := biproduct.lift (f := fun _ : Fin n => Y) (fun j => f j)
    ∃ Q : C,
      ((Mono e ∧ ¬ Epi e ∧ Q = cokernel e) ∨
       (Epi e ∧ ¬ Mono e ∧ Q = kernel e)) ∧
      (∀ g : Q ⟶ Y, g = 0) ∧
      (∀ x : Ext Q Y 1, x = 0) ∧
      (∀ x : Ext Q Q 1, x = 0) ∧
      (∀ d : Q ⟶ Q, ∃ c : K, d = c • 𝟙 Q) ∧
      𝟙 Q ≠ 0 ∧ IsLocalRing (End Q) := by
  letI := local_end_of_scalar_end X hIdX hEndX
  letI := local_end_of_scalar_end Y hIdY hEndY
  exact left_hom_mutation_exists X Y n f hHered hReverseHom hReverseExt
    (extOne_vanishes_of_nonzero_hom_rigid X Y hHered hReverseExt hRigidX hRigidY hHom)
    hRigidX hRigidY hIdX hEndX hEndY

#print axioms left_hom_mutation_exists
#print axioms left_hom_mutation_of_nonzero_hom
end QuiverProofs.MA4RestartArrow20261003.LeftHomMutation
