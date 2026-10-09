import MA4Coordinator20261003.EvaluationCokernel
import MA4Coordinator20261003.BiproductHomFaithfulness
import QuiverProofs.MACompletionCategoricalTriangles

/-! Concrete kernel branch of exceptional evaluation mutation.
Full Hom basis, scalar End data, epicity and reverse orthogonality remain
explicit. The actual kernel is proved rigid and, when evaluation is not
monic, has local End. No root-frame realization or dimension correspondence. -/
namespace QuiverProofs.MACompletionEvaluationKernel
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open MACompletionEvaluationCokernel MACompletionBiproductHomFaithfulness
open MACompletionCategoricalTriangles
open QuiverProofs.MA4Arrow20261003.AbsentEvaluationBiproduct
universe w v u z
variable {K : Type w} [Field K] {C : Type u}
  [Category.{v} C] [Abelian C] [Linear K C] [HasExt.{z} C]
set_option maxHeartbeats 0

/-- Independence and scalar summand End make evaluation injective on Hom
from the summand object, including every finite number of copies. -/
theorem hom_summand_evaluation_eq_zero (R V : C) (n : Nat)
    [HasBiproduct (fun _ : Fin n => R)]
    (basis : Module.Basis (Fin n) K (R ⟶ V))
    (hEnd : ∀ d : R ⟶ R, ∃ c : K, d = c • 𝟙 R)
    (h : R ⟶ (⨁ fun _ : Fin n => R))
    (hh : h ≫ biproduct.desc (f := fun _ : Fin n => R) (fun j => basis j) = 0) :
    h = 0 := by
  classical
  choose c hc using fun j : Fin n => hEnd (h ≫ biproduct.π (fun _ : Fin n => R) j)
  have hs : ∑ j : Fin n, c j • basis j = 0 := by
    calc
      _ = ∑ j : Fin n, (h ≫ biproduct.π (fun _ : Fin n => R) j) ≫ basis j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hc j]
        simp only [Linear.smul_comp, Category.id_comp]
      _ = h ≫ biproduct.desc (f := fun _ : Fin n => R) (fun j => basis j) := by
        rw [biproduct.desc_eq, CategoryTheory.Preadditive.comp_sum]
        simp only [Category.assoc]
      _ = 0 := hh
  have hcz : ∀ j, c j = 0 := (Fintype.linearIndependent_iff.mp basis.linearIndependent) c hs
  apply biproduct.hom_ext h 0
  intro j
  simp only [zero_comp, hc j, hcz j, zero_smul]

/-- The actual evaluation kernel is Hom-orthogonal from its summand object. -/
theorem hom_summand_evaluation_kernel_zero (R V : C) (n : Nat)
    [HasBiproduct (fun _ : Fin n => R)]
    (basis : Module.Basis (Fin n) K (R ⟶ V))
    (hEnd : ∀ d : R ⟶ R, ∃ c : K, d = c • 𝟙 R) :
    ∀ f : R ⟶ kernel (biproduct.desc (f := fun _ : Fin n => R) (fun j => basis j)),
      f = 0 := by
  let e := biproduct.desc (f := fun _ : Fin n => R) (fun j => basis j)
  intro f
  apply (cancel_mono (kernel.ι e)).mp
  have hz := hom_summand_evaluation_eq_zero R V n basis hEnd (f ≫ kernel.ι e)
    (by rw [Category.assoc, kernel.condition, comp_zero])
  simpa only [zero_comp] using hz

/-- Right-universality makes Ext1 from the summand to the actual epic
basis-evaluation kernel vanish, using only old summand rigidity. -/
theorem extOne_summand_evaluation_kernel_zero (R V : C) (n : Nat)
    [HasBiproduct (fun _ : Fin n => R)]
    (basis : Module.Basis (Fin n) K (R ⟶ V))
    [Epi (biproduct.desc (f := fun _ : Fin n => R) (fun j => basis j))]
    (hRigid : ∀ x : Ext R R 1, x = 0) :
    ∀ x : Ext R (kernel (biproduct.desc (f := fun _ : Fin n => R) (fun j => basis j))) 1,
      x = 0 := by
  let e := biproduct.desc (f := fun _ : Fin n => R) (fun j => basis j)
  let L := kernel e
  let S := ShortComplex.mk (kernel.ι e) e (kernel.condition e)
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel e }
  have hRM : ∀ x : Ext R (⨁ fun _ : Fin n => R) 1, x = 0 :=
    extOne_biproduct_vanishes R (fun _ : Fin n => R) (fun _ => hRigid)
  intro x
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ R hS x (hRM _)
    (show 0 + 1 = 1 from rfl)
  let g := Ext.homEquiv₀ y
  obtain ⟨a, ha⟩ := hom_basis_evaluation_factor R V n basis g
  rw [← hy, ← Ext.mk₀_homEquiv₀_apply y]
  change (Ext.mk₀ g).comp hS.extClass (zero_add 1) = 0
  rw [← ha, ← Ext.mk₀_comp_mk₀,
    Ext.comp_assoc (a₁ := 0) (a₂ := 0) (a₃ := 1)]
  rw [hS.comp_extClass, Ext.comp_zero]
  all_goals rfl

/-- The constructed epic-evaluation kernel is self-rigid under the stated
hereditary bound; next rigidity is a conclusion. -/
theorem evaluation_kernel_rigid (R V : C) (n : Nat)
    [HasBiproduct (fun _ : Fin n => R)]
    (basis : Module.Basis (Fin n) K (R ⟶ V))
    [Epi (biproduct.desc (f := fun _ : Fin n => R) (fun j => basis j))]
    [HasProjectiveDimensionLT V 2]
    (hRigid : ∀ x : Ext R R 1, x = 0) :
    ∀ x : Ext (kernel (biproduct.desc (f := fun _ : Fin n => R) (fun j => basis j)))
      (kernel (biproduct.desc (f := fun _ : Fin n => R) (fun j => basis j))) 1,
      x = 0 := by
  let e := biproduct.desc (f := fun _ : Fin n => R) (fun j => basis j)
  let L := kernel e
  let S := ShortComplex.mk (kernel.ι e) e (kernel.condition e)
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel e }
  have hRL := extOne_summand_evaluation_kernel_zero R V n basis hRigid
  have hML : ∀ x : Ext (⨁ fun _ : Fin n => R) L 1, x = 0 := by
    intro x
    let E := Ext.biproductAddEquiv (biproduct.isBilimit (fun _ : Fin n => R)) L 1
    apply E.injective
    ext j
    simpa only [map_zero, Pi.zero_apply] using hRL (E x j)
  exact extOne_subobject_vanishes L hS hML

/-- Lift an endomorphism of the actual kernel, descend its action to the
old target, then use evaluation faithfulness to prove it scalar. -/
theorem evaluation_kernel_scalar_end (R V : C) (n : Nat)
    [HasBiproduct (fun _ : Fin n => R)]
    (basis : Module.Basis (Fin n) K (R ⟶ V))
    [Epi (biproduct.desc (f := fun _ : Fin n => R) (fun j => basis j))]
    (hReverse : ∀ x : Ext V R 1, x = 0)
    (hEndR : ∀ d : R ⟶ R, ∃ c : K, d = c • 𝟙 R)
    (hEndV : ∀ d : V ⟶ V, ∃ c : K, d = c • 𝟙 V) :
    ∀ d : kernel (biproduct.desc (f := fun _ : Fin n => R) (fun j => basis j)) ⟶
      kernel (biproduct.desc (f := fun _ : Fin n => R) (fun j => basis j)),
      ∃ c : K, d = c • 𝟙 _ := by
  let e := biproduct.desc (f := fun _ : Fin n => R) (fun j => basis j)
  let L := kernel e
  let M : C := ⨁ fun _ : Fin n => R
  let m := kernel.ι e
  let S := ShortComplex.mk m e (kernel.condition e)
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel e }
  have hVM : ∀ x : Ext V M 1, x = 0 :=
    extOne_biproduct_vanishes V (fun _ : Fin n => R) (fun _ => hReverse)
  intro d
  obtain ⟨a, ha⟩ := Ext.contravariant_sequence_exact₁ hS M (Ext.mk₀ (d ≫ m))
    (show 1 + 0 = 1 from rfl) (hVM _)
  let A := Ext.homEquiv₀ a
  have hA : m ≫ A = d ≫ m := by
    apply (Ext.mk₀_bijective L M).injective
    rw [← Ext.mk₀_comp_mk₀, Ext.mk₀_homEquiv₀_apply]
    exact ha
  have hkill : m ≫ (A ≫ e) = 0 := by
    rw [← Category.assoc, hA, Category.assoc, kernel.condition, comp_zero]
  obtain ⟨b, hb⟩ := Ext.contravariant_sequence_exact₂ hS V (Ext.mk₀ (A ≫ e))
    (by rw [Ext.mk₀_comp_mk₀, hkill, Ext.mk₀_zero])
  let B := Ext.homEquiv₀ b
  have hB : e ≫ B = A ≫ e := by
    apply (Ext.mk₀_bijective M V).injective
    rw [← Ext.mk₀_comp_mk₀, Ext.mk₀_homEquiv₀_apply]
    exact hb
  obtain ⟨c, hc⟩ := hEndV B
  have hAc : A = c • 𝟙 M := by
    apply end_postcomp_evaluation_injective R V (fun j : Fin n => basis j)
      hEndR basis.linearIndependent
    change A ≫ e = (c • 𝟙 M) ≫ e
    rw [← hB, hc]
    simp only [Linear.comp_smul, Linear.smul_comp, Category.comp_id, Category.id_comp]
  refine ⟨c, (cancel_mono m).mp ?_⟩
  rw [← hA, hAc]
  simp only [Linear.comp_smul, Linear.smul_comp, Category.id_comp]
  change c • (m ≫ 𝟙 M) = c • m
  rw [Category.comp_id]

/-- Non-monicity makes the actual kernel nonzero, so its proved scalar End
property supplies a local ring for another categorical mutation step. -/
theorem evaluation_kernel_local_end (R V : C) (n : Nat)
    [HasBiproduct (fun _ : Fin n => R)]
    (basis : Module.Basis (Fin n) K (R ⟶ V))
    [Epi (biproduct.desc (f := fun _ : Fin n => R) (fun j => basis j))]
    (hNotMono : ¬ Mono (biproduct.desc (f := fun _ : Fin n => R) (fun j => basis j)))
    (hReverse : ∀ x : Ext V R 1, x = 0)
    (hEndR : ∀ d : R ⟶ R, ∃ c : K, d = c • 𝟙 R)
    (hEndV : ∀ d : V ⟶ V, ∃ c : K, d = c • 𝟙 V) :
    IsLocalRing (End (kernel (biproduct.desc (f := fun _ : Fin n => R)
      (fun j => basis j)))) := by
  let e := biproduct.desc (f := fun _ : Fin n => R) (fun j => basis j)
  let L := kernel e
  have hId : (𝟙 L : L ⟶ L) ≠ 0 := by
    intro h
    apply hNotMono
    apply mono_of_kernel_ι_eq_zero e
    calc
      kernel.ι e = 𝟙 L ≫ kernel.ι e := (Category.id_comp _).symm
      _ = 0 := by rw [h, zero_comp]
  exact MACompletionScalarEndomorphisms.local_end_of_scalar_end L hId
    (evaluation_kernel_scalar_end R V n basis hReverse hEndR hEndV)

#print axioms evaluation_kernel_rigid
#print axioms evaluation_kernel_local_end
end QuiverProofs.MACompletionEvaluationKernel
