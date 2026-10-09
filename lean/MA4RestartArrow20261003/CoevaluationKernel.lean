import MA4RestartArrow20261003.CoevaluationCokernel
import QuiverProofs.MACompletionCategoricalTriangles

/-! Actual epic coevaluation replacement L = ker e, in the tuple (Y,L).
The Hom-mutation premise Ext1(X,Y)=0 is explicit where needed; a zero-copy
Hom basis does not silently assert it. Rigidity, scalar and local End of L
are proved from old pair data, not assumed for the replacement. -/
namespace QuiverProofs.MA4RestartArrow20261003.CoevaluationKernel
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open QuiverProofs.MA4RestartArrow20261003.CoevaluationMap
open QuiverProofs.MA4RestartArrow20261003.CoevaluationCokernel
open QuiverProofs.MACompletionCategoricalTriangles
open QuiverProofs.MACompletionScalarEndomorphisms
universe w v u z
variable {K : Type w} [Field K] {C : Type u}
  [Category.{v} C] [Abelian C] [Linear K C] [HasExt.{z} C]
set_option maxHeartbeats 0

/-- Fullness and old Y-rigidity give Hom(L,Y)=0 in the epic branch. -/
theorem hom_coevaluation_kernel_summand_zero (X Y : C) (n : ℕ)
    [HasBiproduct (fun _ : Fin n => Y)]
    (f : Module.Basis (Fin n) K (X ⟶ Y))
    [Epi (biproduct.lift (f := fun _ : Fin n => Y) (fun j => f j))]
    (hRigidY : ∀ x : Ext Y Y 1, x = 0) :
    ∀ g : kernel (biproduct.lift (f := fun _ : Fin n => Y) (fun j => f j)) ⟶ Y,
      g = 0 := by
  let e := biproduct.lift (f := fun _ : Fin n => Y) (fun j => f j)
  let L := kernel e
  let m := kernel.ι e
  let S := ShortComplex.mk m e (kernel.condition e)
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel e }
  have hMY : ∀ x : Ext (⨁ fun _ : Fin n => Y) Y 1, x = 0 :=
    extOne_biproduct_first_vanishes Y (fun _ : Fin n => Y) (fun _ => hRigidY)
  intro g
  obtain ⟨y, hy⟩ := Ext.contravariant_sequence_exact₁ hS Y (Ext.mk₀ g)
    (show 1 + 0 = 1 from rfl) (hMY _)
  let h : X ⟶ Y := Ext.homEquiv₀ y
  have hh : m ≫ h = g := by
    apply (Ext.mk₀_bijective L Y).injective
    rw [← Ext.mk₀_comp_mk₀, Ext.mk₀_homEquiv₀_apply]
    exact hy
  obtain ⟨a, ha⟩ := hom_basis_coevaluation_factor X Y f h
  rw [← hh, ← ha, ← Category.assoc, kernel.condition, zero_comp]

/-- The internal reverse Ext needed for (Y,L) follows from the forward
Ext-zero Hom branch and hereditary contravariant exactness. -/
theorem extOne_coevaluation_kernel_summand_zero (X Y : C) (n : ℕ)
    [HasBiproduct (fun _ : Fin n => Y)]
    (f : Module.Basis (Fin n) K (X ⟶ Y))
    [Epi (biproduct.lift (f := fun _ : Fin n => Y) (fun j => f j))]
    [HasProjectiveDimensionLT (⨁ fun _ : Fin n => Y) 2]
    (hForwardExt : ∀ x : Ext X Y 1, x = 0) :
    ∀ x : Ext (kernel (biproduct.lift (f := fun _ : Fin n => Y) (fun j => f j))) Y 1,
      x = 0 := by
  let e := biproduct.lift (f := fun _ : Fin n => Y) (fun j => f j)
  let S := ShortComplex.mk (kernel.ι e) e (kernel.condition e)
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel e }
  exact extOne_subobject_vanishes Y hS hForwardExt

/-- Old X/Y rigidity gives rigidity of the actual kernel. The Hom term is
killed by fullness, and the Ext term by hereditary subobject exactness. -/
theorem coevaluation_kernel_rigid (X Y : C) (n : ℕ)
    [HasBiproduct (fun _ : Fin n => Y)]
    (f : Module.Basis (Fin n) K (X ⟶ Y))
    [Epi (biproduct.lift (f := fun _ : Fin n => Y) (fun j => f j))]
    [HasProjectiveDimensionLT (⨁ fun _ : Fin n => Y) 2]
    (hRigidX : ∀ x : Ext X X 1, x = 0)
    (hRigidY : ∀ x : Ext Y Y 1, x = 0) :
    ∀ x : Ext (kernel (biproduct.lift (f := fun _ : Fin n => Y) (fun j => f j)))
      (kernel (biproduct.lift (f := fun _ : Fin n => Y) (fun j => f j))) 1, x = 0 := by
  let e := biproduct.lift (f := fun _ : Fin n => Y) (fun j => f j)
  let L := kernel e
  let S := ShortComplex.mk (kernel.ι e) e (kernel.condition e)
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel e }
  have hLX : ∀ x : Ext L X 1, x = 0 := extOne_subobject_vanishes X hS hRigidX
  have hLY := hom_coevaluation_kernel_summand_zero X Y n f hRigidY
  have hLM : ∀ g : L ⟶ (⨁ fun _ : Fin n => Y), g = 0 := by
    intro g
    apply biproduct.hom_ext g 0
    intro j
    simpa only [zero_comp] using hLY (g ≫ biproduct.π (fun _ : Fin n => Y) j)
  intro x
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ L hS x (hLX _)
    (show 0 + 1 = 1 from rfl)
  have hy0 : y = 0 := by
    rw [← Ext.mk₀_homEquiv₀_apply y, hLM (Ext.homEquiv₀ y), Ext.mk₀_zero]
  rw [← hy, hy0, Ext.zero_comp]

/-- Reverse Ext lifts each End L to old End X, which is scalar. -/
theorem coevaluation_kernel_scalar_end (X Y : C) (n : ℕ)
    [HasBiproduct (fun _ : Fin n => Y)]
    (f : Module.Basis (Fin n) K (X ⟶ Y))
    [Epi (biproduct.lift (f := fun _ : Fin n => Y) (fun j => f j))]
    (hReverseExt : ∀ x : Ext Y X 1, x = 0)
    (hEndX : ∀ g : X ⟶ X, ∃ c : K, g = c • 𝟙 X) :
    ∀ d : kernel (biproduct.lift (f := fun _ : Fin n => Y) (fun j => f j)) ⟶
      kernel (biproduct.lift (f := fun _ : Fin n => Y) (fun j => f j)),
      ∃ c : K, d = c • 𝟙 _ := by
  let e := biproduct.lift (f := fun _ : Fin n => Y) (fun j => f j)
  let L := kernel e
  let m := kernel.ι e
  let S := ShortComplex.mk m e (kernel.condition e)
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel e }
  have hMX : ∀ x : Ext (⨁ fun _ : Fin n => Y) X 1, x = 0 :=
    extOne_biproduct_first_vanishes X (fun _ : Fin n => Y) (fun _ => hReverseExt)
  intro d
  obtain ⟨y, hy⟩ := Ext.contravariant_sequence_exact₁ hS X (Ext.mk₀ (d ≫ m))
    (show 1 + 0 = 1 from rfl) (hMX _)
  let b : X ⟶ X := Ext.homEquiv₀ y
  have hb : m ≫ b = d ≫ m := by
    apply (Ext.mk₀_bijective L X).injective
    rw [← Ext.mk₀_comp_mk₀, Ext.mk₀_homEquiv₀_apply]
    exact hy
  obtain ⟨c, hc⟩ := hEndX b
  refine ⟨c, (cancel_mono m).mp ?_⟩
  rw [← hb, hc]
  simp only [Linear.comp_smul, Linear.smul_comp, Category.id_comp]
  change c • (m ≫ 𝟙 X) = c • m
  rw [Category.comp_id]

omit [HasExt C] in
/-- Non-monicity gives nonzero L through the actual kernel inclusion. -/
theorem kernel_id_ne_zero_of_not_mono {X M : C} (e : X ⟶ M) (hNotMono : ¬ Mono e) :
    𝟙 (kernel e) ≠ 0 := by
  intro hz
  apply hNotMono
  apply mono_of_kernel_ι_eq_zero e
  calc
    kernel.ι e = 𝟙 _ ≫ kernel.ι e := (Category.id_comp _).symm
    _ = 0 := by rw [hz, zero_comp]

/-- The strict epic branch has local End from its proved scalar End and
nonzero actual kernel. -/
theorem coevaluation_kernel_local_end (X Y : C) (n : ℕ)
    [HasBiproduct (fun _ : Fin n => Y)]
    (f : Module.Basis (Fin n) K (X ⟶ Y))
    [Epi (biproduct.lift (f := fun _ : Fin n => Y) (fun j => f j))]
    (hNotMono : ¬ Mono (biproduct.lift (f := fun _ : Fin n => Y) (fun j => f j)))
    (hReverseExt : ∀ x : Ext Y X 1, x = 0)
    (hEndX : ∀ g : X ⟶ X, ∃ c : K, g = c • 𝟙 X) :
    IsLocalRing (End (kernel (biproduct.lift (f := fun _ : Fin n => Y) (fun j => f j)))) :=
  local_end_of_scalar_end _ (kernel_id_ne_zero_of_not_mono _ hNotMono)
    (coevaluation_kernel_scalar_end X Y n f hReverseExt hEndX)

#print axioms coevaluation_kernel_rigid
#print axioms coevaluation_kernel_scalar_end
#print axioms coevaluation_kernel_local_end
end QuiverProofs.MA4RestartArrow20261003.CoevaluationKernel
