import MA4Arrow20261003.AbsentEvaluationBiproduct
import MA4Coordinator20261003.ScalarEndomorphisms
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.CategoryTheory.Linear.Basic

/-! Concrete cokernel branch of exceptional evaluation mutation.
The Hom basis, monicity, rigidity and orthogonality data are supplied; the
actual chosen cokernel is proved rigid with local End. No full-frame object
realization, dimension-vector identification or all-word preservation is proved. -/
namespace QuiverProofs.MACompletionEvaluationCokernel
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open QuiverProofs.MA4Arrow20261003.AbsentEvaluationExt
open QuiverProofs.MA4Arrow20261003.AbsentEvaluationBiproduct
open MACompletionScalarEndomorphisms
universe w v u z
variable {K : Type w} [Field K] {C : Type u}
  [Category.{v} C] [Abelian C] [Linear K C] [HasExt.{z} C]
set_option maxHeartbeats 0

omit [HasExt C] in
/-- The supplied full Hom basis makes the actual evaluation right-universal
for maps from its summand object, with an explicit biproduct lift. -/
theorem hom_basis_evaluation_factor (R V : C) (n : Nat)
    [HasBiproduct (fun _ : Fin n => R)]
    (basis : Module.Basis (Fin n) K (R ⟶ V)) (g : R ⟶ V) :
    ∃ h : R ⟶ (⨁ fun _ : Fin n => R),
      h ≫ biproduct.desc (f := fun _ : Fin n => R) (fun j => basis j) = g := by
  classical
  refine ⟨biproduct.lift (fun j : Fin n => basis.repr g j • 𝟙 R), ?_⟩
  rw [biproduct.lift_desc]
  simpa only [Linear.smul_comp, Category.id_comp] using basis.sum_repr g

/-- Rigidity of the summand and universality of evaluation force Hom from
that summand to the actual cokernel to vanish in the monic branch. -/
theorem hom_summand_evaluation_cokernel_zero (R V : C) (n : Nat)
    [HasBiproduct (fun _ : Fin n => R)]
    (basis : Module.Basis (Fin n) K (R ⟶ V))
    [Mono (biproduct.desc (f := fun _ : Fin n => R) (fun j => basis j))]
    (hRigid : ∀ e : Ext R R 1, e = 0) :
    ∀ f : R ⟶ cokernel (biproduct.desc (f := fun _ : Fin n => R)
      (fun j => basis j)), f = 0 := by
  let e := biproduct.desc (f := fun _ : Fin n => R) (fun j => basis j)
  let q := cokernel.π e
  let S := ShortComplex.mk e q (cokernel.condition e)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel e }
  have hRM : ∀ x : Ext R (⨁ fun _ : Fin n => R) 1, x = 0 :=
    extOne_biproduct_vanishes R (fun _ : Fin n => R) (fun _ => hRigid)
  intro f
  obtain ⟨x, hx⟩ := Ext.covariant_sequence_exact₃ R hS (Ext.mk₀ f)
    (show 0 + 1 = 1 from rfl) (hRM _)
  let g := Ext.homEquiv₀ x
  have hg : g ≫ q = f := by
    apply (Ext.mk₀_bijective R (cokernel e)).injective
    rw [← Ext.mk₀_comp_mk₀, Ext.mk₀_homEquiv₀_apply]
    exact hx
  obtain ⟨a, ha⟩ := hom_basis_evaluation_factor R V n basis g
  rw [← hg, ← ha, Category.assoc]
  change a ≫ (e ≫ cokernel.π e) = 0
  rw [cokernel.condition, comp_zero]

/-- The entire finite source biproduct is Hom-orthogonal to the actual
cokernel, including the zero-copy case. -/
theorem hom_copies_evaluation_cokernel_zero (R V : C) (n : Nat)
    [HasBiproduct (fun _ : Fin n => R)]
    (basis : Module.Basis (Fin n) K (R ⟶ V))
    [Mono (biproduct.desc (f := fun _ : Fin n => R) (fun j => basis j))]
    (hRigid : ∀ e : Ext R R 1, e = 0) :
    ∀ f : (⨁ fun _ : Fin n => R) ⟶
      cokernel (biproduct.desc (f := fun _ : Fin n => R) (fun j => basis j)),
      f = 0 := by
  intro f
  apply biproduct.hom_ext' f 0
  intro j
  simpa only [comp_zero] using hom_summand_evaluation_cokernel_zero R V n
    basis hRigid (biproduct.ι (fun _ : Fin n => R) j ≫ f)

/-- Hereditary exactness and universality prove self-rigidity of the
constructed evaluation cokernel, rather than assuming its next rigidity. -/
theorem evaluation_cokernel_rigid (R V : C) (n : Nat)
    [HasBiproduct (fun _ : Fin n => R)]
    (basis : Module.Basis (Fin n) K (R ⟶ V))
    [Mono (biproduct.desc (f := fun _ : Fin n => R) (fun j => basis j))]
    [HasProjectiveDimensionLT V 2]
    (hRigidR : ∀ e : Ext R R 1, e = 0)
    (hRigidV : ∀ e : Ext V V 1, e = 0) :
    ∀ x : Ext (cokernel (biproduct.desc (f := fun _ : Fin n => R) (fun j => basis j)))
      (cokernel (biproduct.desc (f := fun _ : Fin n => R) (fun j => basis j))) 1,
      x = 0 := by
  let e := biproduct.desc (f := fun _ : Fin n => R) (fun j => basis j)
  let Q := cokernel e
  let q := cokernel.π e
  let S := ShortComplex.mk e q (cokernel.condition e)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel e }
  have hVQ : ∀ x : Ext V Q 1, x = 0 := extOne_quotient_vanishes V hS hRigidV
  have hMQ := hom_copies_evaluation_cokernel_zero R V n basis hRigidR
  intro x
  obtain ⟨y, hy⟩ := Ext.contravariant_sequence_exact₃ hS Q x
    (hVQ _) (show 1 + 0 = 1 from rfl)
  have hy0 : y = 0 := by
    rw [← Ext.mk₀_homEquiv₀_apply y, hMQ (Ext.homEquiv₀ y), Ext.mk₀_zero]
  rw [← hy, hy0, Ext.comp_zero]

/-- Scalar End of the target passes to the actual monic-evaluation
cokernel under reverse Ext orthogonality, via lifting its endomorphisms. -/
theorem evaluation_cokernel_scalar_end (R V : C) (n : Nat)
    [HasBiproduct (fun _ : Fin n => R)]
    (basis : Module.Basis (Fin n) K (R ⟶ V))
    [Mono (biproduct.desc (f := fun _ : Fin n => R) (fun j => basis j))]
    (hReverse : ∀ x : Ext V R 1, x = 0)
    (hEnd : ∀ g : V ⟶ V, ∃ c : K, g = c • 𝟙 V) :
    ∀ g : cokernel (biproduct.desc (f := fun _ : Fin n => R) (fun j => basis j)) ⟶
      cokernel (biproduct.desc (f := fun _ : Fin n => R) (fun j => basis j)),
      ∃ c : K, g = c • 𝟙 _ := by
  let e := biproduct.desc (f := fun _ : Fin n => R) (fun j => basis j)
  let Q := cokernel e
  let q := cokernel.π e
  let S := ShortComplex.mk e q (cokernel.condition e)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel e }
  have hVM : ∀ x : Ext V (⨁ fun _ : Fin n => R) 1, x = 0 :=
    extOne_biproduct_vanishes V (fun _ : Fin n => R) (fun _ => hReverse)
  intro g
  obtain ⟨x, hx⟩ := Ext.covariant_sequence_exact₃ V hS (Ext.mk₀ (q ≫ g))
    (show 0 + 1 = 1 from rfl) (hVM _)
  let d := Ext.homEquiv₀ x
  have hd : d ≫ q = q ≫ g := by
    apply (Ext.mk₀_bijective V Q).injective
    rw [← Ext.mk₀_comp_mk₀, Ext.mk₀_homEquiv₀_apply]
    exact hx
  obtain ⟨c, hc⟩ := hEnd d
  refine ⟨c, (cancel_epi q).mp ?_⟩
  rw [← hd, hc]
  simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp]
  change c • q = c • (q ≫ 𝟙 Q)
  rw [Category.comp_id]

/-- Non-epicity makes the constructed cokernel nonzero; its proved scalar
End then supplies the local ring needed at the next categorical step. -/
theorem evaluation_cokernel_local_end (R V : C) (n : Nat)
    [HasBiproduct (fun _ : Fin n => R)]
    (basis : Module.Basis (Fin n) K (R ⟶ V))
    [Mono (biproduct.desc (f := fun _ : Fin n => R) (fun j => basis j))]
    (hNotEpi : ¬ Epi (biproduct.desc (f := fun _ : Fin n => R) (fun j => basis j)))
    (hReverse : ∀ x : Ext V R 1, x = 0)
    (hEnd : ∀ g : V ⟶ V, ∃ c : K, g = c • 𝟙 V) :
    IsLocalRing (End (cokernel (biproduct.desc (f := fun _ : Fin n => R)
      (fun j => basis j)))) := by
  let e := biproduct.desc (f := fun _ : Fin n => R) (fun j => basis j)
  let Q := cokernel e
  have hId : (𝟙 Q : Q ⟶ Q) ≠ 0 := by
    intro h
    apply hNotEpi
    apply epi_of_cokernel_π_eq_zero e
    calc
      cokernel.π e = cokernel.π e ≫ 𝟙 Q := (Category.comp_id _).symm
      _ = 0 := by rw [h, comp_zero]
  exact local_end_of_scalar_end Q hId
    (evaluation_cokernel_scalar_end R V n basis hReverse hEnd)

#print axioms evaluation_cokernel_rigid
#print axioms evaluation_cokernel_local_end
end QuiverProofs.MACompletionEvaluationCokernel
