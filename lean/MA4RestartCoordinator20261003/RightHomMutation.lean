import MA4Coordinator20261003.EvaluationKernel
import MA4Coordinator20261003.PairPurity
import MA4Arrow20261003.AbsentEvaluationFaithful

/-! Construct the right Hom-mutation object from old exceptional-pair data.
The actual evaluation branch, replacement nonzeroness, rigidity, scalar End,
and its reverse Hom/Ext orthogonality are conclusions. A fixed category and
old realized objects are still supplied; no numerical frame realization is claimed. -/
namespace QuiverProofs.MA4RestartRightHomMutation
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open MACompletionEvaluationKernel MACompletionEvaluationCokernel
open MACompletionBiproductHomFaithfulness MACompletionScalarEndomorphisms
open MACompletionPairPurity
open QuiverProofs.MA4Arrow20261003.AbsentEvaluationFaithful
open QuiverProofs.MA4Arrow20261003.AbsentEvaluationBiproduct
open QuiverProofs.MA4Arrow20261003.AbsentEvaluationExt
universe w v u z
variable {K : Type w} [Field K] {C : Type u}
  [Category.{v} C] [Abelian C] [Linear K C] [HasExt.{z} C]
set_option maxHeartbeats 0

omit [HasExt C] in
/-- Reverse Hom orthogonality and a nonzero target exclude isomorphism for
ANY map from finitely many copies, including zero copies. -/
theorem copies_morphism_not_isIso (R V : C) (n : Nat)
    [HasBiproduct (fun _ : Fin n => R)]
    (e : (⨁ fun _ : Fin n => R) ⟶ V)
    (hReverseHom : ∀ f : V ⟶ R, f = 0)
    (hIdV : (𝟙 V : V ⟶ V) ≠ 0) : ¬ IsIso e := by
  intro hIso
  letI := hIso
  have hz : inv e = 0 := by
    apply biproduct.hom_ext (inv e) 0
    intro j
    simpa only [zero_comp] using
      hReverseHom (inv e ≫ biproduct.π (fun _ : Fin n => R) j)
  apply hIdV
  calc
    (𝟙 V : V ⟶ V) = inv e ≫ e := (IsIso.inv_hom_id e).symm
    _ = 0 := by rw [hz, zero_comp]

/-- A full Hom-basis evaluation has an actual mono-or-epi dichotomy from
old scalar End and reverse Ext data. Its source End need not be local. -/
theorem hom_evaluation_mono_or_epi (R V : C) (n : Nat)
    [HasBiproduct (fun _ : Fin n => R)]
    (basis : Module.Basis (Fin n) K (R ⟶ V))
    (hHered : ∀ T : C, HasProjectiveDimensionLT T 2)
    (hReverse : ∀ x : Ext V R 1, x = 0)
    (hEndR : ∀ d : R ⟶ R, ∃ c : K, d = c • 𝟙 R)
    (hEndV : ∀ d : V ⟶ V, ∃ c : K, d = c • 𝟙 V) :
    Mono (biproduct.desc (f := fun _ : Fin n => R) (fun j => basis j)) ∨
    Epi (biproduct.desc (f := fun _ : Fin n => R) (fun j => basis j)) := by
  exact mono_or_epi_of_reverse_extOne_zero _ hHered
    (extOne_biproduct_vanishes V (fun _ : Fin n => R) (fun _ => hReverse))
    (end_postcomp_evaluation_injective R V (fun j => basis j)
      hEndR basis.linearIndependent)
    (end_zero_or_iso_of_scalar_end V hEndV)

/-- Construct an actual strict kernel/cokernel replacement, with all internal
exceptionality facts derived from old Hom/Ext-orthogonal pair data. -/
theorem right_hom_mutation_exists (R V : C) (n : Nat)
    [HasBiproduct (fun _ : Fin n => R)]
    (basis : Module.Basis (Fin n) K (R ⟶ V))
    (hHered : ∀ T : C, HasProjectiveDimensionLT T 2)
    (hReverseHom : ∀ f : V ⟶ R, f = 0)
    (hReverse : ∀ x : Ext V R 1, x = 0)
    (hForward : ∀ x : Ext R V 1, x = 0)
    (hRigidR : ∀ x : Ext R R 1, x = 0)
    (hRigidV : ∀ x : Ext V V 1, x = 0)
    (hIdV : (𝟙 V : V ⟶ V) ≠ 0)
    (hEndR : ∀ d : R ⟶ R, ∃ c : K, d = c • 𝟙 R)
    (hEndV : ∀ d : V ⟶ V, ∃ c : K, d = c • 𝟙 V) :
    let e := biproduct.desc (f := fun _ : Fin n => R) (fun j => basis j)
    ∃ Q : C,
      ((Mono e ∧ ¬ Epi e ∧ Q = cokernel e) ∨
       (Epi e ∧ ¬ Mono e ∧ Q = kernel e)) ∧
      (∀ f : R ⟶ Q, f = 0) ∧
      (∀ x : Ext R Q 1, x = 0) ∧
      (∀ x : Ext Q Q 1, x = 0) ∧
      (∀ d : Q ⟶ Q, ∃ c : K, d = c • 𝟙 Q) ∧
      (𝟙 Q : Q ⟶ Q) ≠ 0 := by
  let e := biproduct.desc (f := fun _ : Fin n => R) (fun j => basis j)
  letI := hHered R
  letI := hHered V
  have hNotIso := copies_morphism_not_isIso R V n e hReverseHom hIdV
  rcases hom_evaluation_mono_or_epi R V n basis hHered hReverse hEndR hEndV with hm | he
  · letI : Mono e := hm
    have hn : ¬ Epi e := by
      intro h
      letI := h
      exact hNotIso (isIso_of_mono_of_epi e)
    let S := ShortComplex.mk e (cokernel.π e) (cokernel.condition e)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel e }
    refine ⟨cokernel e, Or.inl ⟨hm, hn, rfl⟩,
      hom_summand_evaluation_cokernel_zero R V n basis hRigidR,
      extOne_quotient_vanishes R hS hForward,
      evaluation_cokernel_rigid R V n basis hRigidR hRigidV,
      evaluation_cokernel_scalar_end R V n basis hReverse hEndV, ?_⟩
    intro h
    apply hn
    apply epi_of_cokernel_π_eq_zero e
    calc
      cokernel.π e = cokernel.π e ≫ 𝟙 (cokernel e) := (Category.comp_id _).symm
      _ = 0 := by rw [h, comp_zero]
  · letI : Epi e := he
    have hn : ¬ Mono e := by
      intro h
      letI := h
      exact hNotIso (isIso_of_mono_of_epi e)
    refine ⟨kernel e, Or.inr ⟨he, hn, rfl⟩,
      hom_summand_evaluation_kernel_zero R V n basis hEndR,
      extOne_summand_evaluation_kernel_zero R V n basis hRigidR,
      evaluation_kernel_rigid R V n basis hRigidR,
      evaluation_kernel_scalar_end R V n basis hReverse hEndR hEndV, ?_⟩
    intro h
    apply hn
    apply mono_of_kernel_ι_eq_zero e
    calc
      kernel.ι e = 𝟙 (kernel e) ≫ kernel.ι e := (Category.id_comp _).symm
      _ = 0 := by rw [h, zero_comp]

/-- On the positive-Hom branch, forward Ext vanishing is derived from the
old rigid scalar-End pair. Neither a map branch nor new-object facts are supplied. -/
theorem right_hom_mutation_of_nonzero_hom (R V : C) (n : Nat)
    [HasBiproduct (fun _ : Fin n => R)]
    (basis : Module.Basis (Fin n) K (R ⟶ V))
    (hHered : ∀ T : C, HasProjectiveDimensionLT T 2)
    (hReverseHom : ∀ f : V ⟶ R, f = 0)
    (hReverse : ∀ x : Ext V R 1, x = 0)
    (hRigidR : ∀ x : Ext R R 1, x = 0)
    (hRigidV : ∀ x : Ext V V 1, x = 0)
    (hIdR : (𝟙 R : R ⟶ R) ≠ 0)
    (hIdV : (𝟙 V : V ⟶ V) ≠ 0)
    (hEndR : ∀ d : R ⟶ R, ∃ c : K, d = c • 𝟙 R)
    (hEndV : ∀ d : V ⟶ V, ∃ c : K, d = c • 𝟙 V)
    (hHom : ∃ f : R ⟶ V, f ≠ 0) :
    let e := biproduct.desc (f := fun _ : Fin n => R) (fun j => basis j)
    ∃ Q : C,
      ((Mono e ∧ ¬ Epi e ∧ Q = cokernel e) ∨
       (Epi e ∧ ¬ Mono e ∧ Q = kernel e)) ∧
      (∀ f : R ⟶ Q, f = 0) ∧
      (∀ x : Ext R Q 1, x = 0) ∧
      (∀ x : Ext Q Q 1, x = 0) ∧
      (∀ d : Q ⟶ Q, ∃ c : K, d = c • 𝟙 Q) ∧
      (𝟙 Q : Q ⟶ Q) ≠ 0 := by
  letI := local_end_of_scalar_end R hIdR hEndR
  letI := local_end_of_scalar_end V hIdV hEndV
  exact right_hom_mutation_exists R V n basis hHered hReverseHom hReverse
    (extOne_vanishes_of_nonzero_hom_rigid R V hHered hReverse hRigidR hRigidV hHom)
    hRigidR hRigidV hIdV hEndR hEndV

#print axioms copies_morphism_not_isIso
#print axioms hom_evaluation_mono_or_epi
#print axioms right_hom_mutation_exists
#print axioms right_hom_mutation_of_nonzero_hom
end QuiverProofs.MA4RestartRightHomMutation
