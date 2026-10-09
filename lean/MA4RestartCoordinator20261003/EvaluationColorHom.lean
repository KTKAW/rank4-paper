import MA4RestartCoordinator20261003.RightHomMutation

/-! Minimal same-color Hom gates for chosen right evaluation replacements.
The kernel's internal Hom vanishing is derived from the actual full basis.
No next color, whole frame, or Hom vanishing is supplied. -/
namespace QuiverProofs.MA4RestartEvaluationColorHom
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open MACompletionEvaluationKernel
open QuiverProofs.MA4Arrow20261003.AbsentEvaluationBiproduct
universe w v u z
variable {K : Type w} [Field K] {C : Type u}
  [Category.{v} C] [Abelian C] [Linear K C] [HasExt.{z} C]
set_option maxHeartbeats 0

private theorem ext_to_first_zero (T : C) {S : ShortComplex C} (hS : S.ShortExact)
    (h₃ : ∀ f : T ⟶ S.X₃, f = 0)
    (h₂ : ∀ x : Ext T S.X₂ 1, x = 0) : ∀ x : Ext T S.X₁ 1, x = 0 := by
  intro x
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ T hS x (h₂ _)
    (show 0 + 1 = 1 from rfl)
  have hy0 : y = 0 := by
    rw [← Ext.mk₀_homEquiv₀_apply y, h₃ (Ext.homEquiv₀ y), Ext.mk₀_zero]
  rw [← hy, hy0, Ext.zero_comp]

private theorem hom_from_first_zero {S : ShortComplex C} (hS : S.ShortExact) (T : C)
    (h₂ : ∀ f : S.X₂ ⟶ T, f = 0)
    (h₃ : ∀ x : Ext S.X₃ T 1, x = 0) : ∀ f : S.X₁ ⟶ T, f = 0 := by
  intro f
  obtain ⟨y, hy⟩ := Ext.contravariant_sequence_exact₁ hS T (Ext.mk₀ f)
    (show 1 + 0 = 1 from rfl) (h₃ _)
  have hy0 : y = 0 := by
    rw [← Ext.mk₀_homEquiv₀_apply y, h₂ (Ext.homEquiv₀ y), Ext.mk₀_zero]
  apply (Ext.mk₀_bijective S.X₁ T).injective
  rw [Ext.mk₀_zero, ← hy, hy0, Ext.comp_zero]

private theorem hom_to_third_zero (T : C) {S : ShortComplex C} (hS : S.ShortExact)
    (h₂ : ∀ f : T ⟶ S.X₂, f = 0)
    (h₁ : ∀ x : Ext T S.X₁ 1, x = 0) : ∀ f : T ⟶ S.X₃, f = 0 := by
  intro f
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₃ T hS (Ext.mk₀ f)
    (show 0 + 1 = 1 from rfl) (h₁ _)
  have hy0 : y = 0 := by
    rw [← Ext.mk₀_homEquiv₀_apply y, h₂ (Ext.homEquiv₀ y), Ext.mk₀_zero]
  apply (Ext.mk₀_bijective T S.X₃).injective
  rw [Ext.mk₀_zero, ← hy, hy0, Ext.zero_comp]

omit [HasExt C] in
private theorem hom_from_copies_zero (Y T : C) (n : ℕ)
    [HasBiproduct (fun _ : Fin n => Y)] (h : ∀ f : Y ⟶ T, f = 0) :
    ∀ f : (⨁ fun _ : Fin n => Y) ⟶ T, f = 0 := by
  intro f
  apply biproduct.hom_ext' f 0
  intro j
  simpa only [comp_zero] using h (biproduct.ι (fun _ : Fin n => Y) j ≫ f)

omit [HasExt C] in
private theorem hom_to_copies_zero (T Y : C) (n : ℕ)
    [HasBiproduct (fun _ : Fin n => Y)] (h : ∀ f : T ⟶ Y, f = 0) :
    ∀ f : T ⟶ (⨁ fun _ : Fin n => Y), f = 0 := by
  intro f
  apply biproduct.hom_ext f 0
  intro j
  simpa only [zero_comp] using h (f ≫ biproduct.π (fun _ : Fin n => Y) j)

omit [HasExt C] in
private theorem hom_from_middle_zero {S : ShortComplex C} (hS : S.ShortExact) (T : C)
    (h₁ : ∀ f : S.X₁ ⟶ T, f = 0) (h₃ : ∀ f : S.X₃ ⟶ T, f = 0) :
    ∀ f : S.X₂ ⟶ T, f = 0 := by
  intro f
  let a := hS.gIsCokernel.desc (CokernelCofork.ofπ f (h₁ (S.f ≫ f)))
  have ha : S.g ≫ a = f := hS.gIsCokernel.fac _ WalkingParallelPair.one
  rw [h₃ a, comp_zero] at ha
  exact ha.symm

omit [HasExt C] in
private theorem hom_to_middle_zero (T : C) {S : ShortComplex C} (hS : S.ShortExact)
    (h₁ : ∀ f : T ⟶ S.X₁, f = 0) (h₃ : ∀ f : T ⟶ S.X₃, f = 0) :
    ∀ f : T ⟶ S.X₂, f = 0 := by
  intro f
  let a := hS.fIsKernel.lift (KernelFork.ofι f (h₃ (f ≫ S.g)))
  have ha : a ≫ S.f = f := hS.fIsKernel.fac _ WalkingParallelPair.zero
  rw [h₁ a, zero_comp] at ha
  exact ha.symm

/-- Both kernels inherit forward Hom zero. Fullness of the second selected
evaluation derives its internal pivot-to-kernel Hom zero. -/
theorem evaluation_kernels_hom_zero (X X' Y : C) (n m : ℕ)
    [HasBiproduct (fun _ : Fin n => Y)] [HasBiproduct (fun _ : Fin m => Y)]
    (e : (⨁ fun _ : Fin n => Y) ⟶ X)
    (f' : Module.Basis (Fin m) K (Y ⟶ X'))
    [Epi e] [Epi (biproduct.desc (f := fun _ : Fin m => Y) (fun j => f' j))]
    (hEndY : ∀ g : Y ⟶ Y, ∃ c : K, g = c • 𝟙 Y)
    (hXX : ∀ g : X ⟶ X', g = 0) (hXY : ∀ x : Ext X Y 1, x = 0) :
    let e' := biproduct.desc (f := fun _ : Fin m => Y) (fun j => f' j)
    ∀ g : kernel e ⟶ kernel e', g = 0 := by
  let e' := biproduct.desc (f := fun _ : Fin m => Y) (fun j => f' j)
  let S := ShortComplex.mk (kernel.ι e) e (kernel.condition e)
  let S' := ShortComplex.mk (kernel.ι e') e' (kernel.condition e')
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel e }
  have hS' : S'.ShortExact := { exact := ShortComplex.exact_kernel e' }
  have hYQ := hom_summand_evaluation_kernel_zero Y X' m f' hEndY
  have hCopies := extOne_biproduct_vanishes X (fun _ : Fin m => Y) (fun _ => hXY)
  exact hom_from_first_zero hS (kernel e')
    (hom_from_copies_zero Y (kernel e') n hYQ)
    (ext_to_first_zero X hS' hXX hCopies)

/-- The first evaluation map is arbitrary. Only the second map's mono
branch is needed; old reverse Ext and old same-color Hom give the result. -/
theorem evaluation_cokernels_hom_zero (X X' Y : C) (n m : ℕ)
    [HasBiproduct (fun _ : Fin n => Y)] [HasBiproduct (fun _ : Fin m => Y)]
    (e : (⨁ fun _ : Fin n => Y) ⟶ X)
    (e' : (⨁ fun _ : Fin m => Y) ⟶ X') [Mono e']
    (hXX : ∀ g : X ⟶ X', g = 0) (hXY : ∀ x : Ext X Y 1, x = 0) :
    ∀ g : cokernel e ⟶ cokernel e', g = 0 := by
  let S' := ShortComplex.mk e' (cokernel.π e') (cokernel.condition e')
  have hS' : S'.ShortExact := { exact := ShortComplex.exact_cokernel e' }
  have hCopies := extOne_biproduct_vanishes X (fun _ : Fin m => Y) (fun _ => hXY)
  have hXQ := hom_to_third_zero X hS' hXX hCopies
  intro g
  apply (cancel_epi (cokernel.π e)).mp
  simpa only [comp_zero] using hXQ (cokernel.π e ≫ g)

omit [HasExt C] in
/-- Actual universal right-extension middles inherit same-color Hom zero
from old boundaries and the second replacement's proved internal Hom law. -/
theorem right_extensions_hom_zero (X X' Y Q Q' : C) (n m : ℕ)
    [HasBiproduct (fun _ : Fin n => Y)] [HasBiproduct (fun _ : Fin m => Y)]
    (i : X ⟶ Q) (p : Q ⟶ (⨁ fun _ : Fin n => Y)) (wi : i ≫ p = 0)
    (hS : (ShortComplex.mk i p wi).ShortExact)
    (i' : X' ⟶ Q') (p' : Q' ⟶ (⨁ fun _ : Fin m => Y)) (wi' : i' ≫ p' = 0)
    (hS' : (ShortComplex.mk i' p' wi').ShortExact)
    (hXX : ∀ f : X ⟶ X', f = 0) (hXY : ∀ f : X ⟶ Y, f = 0)
    (hYQ : ∀ f : Y ⟶ Q', f = 0) : ∀ f : Q ⟶ Q', f = 0 := by
  have hXQ := hom_to_middle_zero X hS' hXX (hom_to_copies_zero X Y m hXY)
  exact hom_from_middle_zero hS Q' hXQ (hom_from_copies_zero Y Q' n hYQ)

/-- A green right extension followed by a green evaluation kernel has Hom
zero. The kernel's internal Hom law is derived from its chosen full basis. -/
theorem right_extension_to_kernel_hom_zero (X X' Y Q : C) (n m : ℕ)
    [HasBiproduct (fun _ : Fin n => Y)] [HasBiproduct (fun _ : Fin m => Y)]
    (i : X ⟶ Q) (p : Q ⟶ (⨁ fun _ : Fin n => Y)) (wi : i ≫ p = 0)
    (hS : (ShortComplex.mk i p wi).ShortExact)
    (f' : Module.Basis (Fin m) K (Y ⟶ X'))
    (hEndY : ∀ g : Y ⟶ Y, ∃ c : K, g = c • 𝟙 Y)
    (hXY : ∀ g : X ⟶ Y, g = 0) :
    let e' := biproduct.desc (f := fun _ : Fin m => Y) (fun j => f' j)
    ∀ g : Q ⟶ kernel e', g = 0 := by
  let e' := biproduct.desc (f := fun _ : Fin m => Y) (fun j => f' j)
  have hXQ : ∀ g : X ⟶ kernel e', g = 0 := by
    intro g
    apply (cancel_mono (kernel.ι e')).mp
    simpa only [zero_comp] using
      hom_to_copies_zero X Y m hXY (g ≫ kernel.ι e')
  exact hom_from_middle_zero hS (kernel e') hXQ
    (hom_from_copies_zero Y (kernel e') n
      (hom_summand_evaluation_kernel_zero Y X' m f' hEndY))

#print axioms evaluation_kernels_hom_zero
#print axioms evaluation_cokernels_hom_zero
#print axioms right_extensions_hom_zero
#print axioms right_extension_to_kernel_hom_zero
end QuiverProofs.MA4RestartEvaluationColorHom
