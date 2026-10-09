import MA4RestartArrow20261003.CoevaluationExternal
import MA4RestartArrow20261003.CoevaluationCokernel

/-! Actual Hom-only transport for the colored full-sweep frontier.
These weakened SES gates keep exactly the Hom/Ext boundary needed.
The two chosen-kernel/cokernel controls derive same-color Hom zero from
OLD Hom zero and OLD reverse Ext; no NEXT color or ArrowSigns is supplied.
No complete colored pivot preservation is asserted by these local gates. -/
namespace QuiverProofs.MA4RestartArrow20261003.ColoredHomTransport
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open QuiverProofs.MA4RestartArrow20261003.CoevaluationCokernel
open MA4EulerExternalOrthogonality01a0fee4
universe w v u z
variable {K : Type w} [Field K] {C : Type u}
  [Category.{v} C] [Abelian C] [Linear K C] [HasExt.{z} C]
set_option maxHeartbeats 0

theorem hom_to_first_zero (T : C) {S : ShortComplex C} (hS : S.ShortExact)
    (h₂ : ∀ f : T ⟶ S.X₂, f = 0) : ∀ f : T ⟶ S.X₁, f = 0 := by
  letI := hS.mono_f
  intro f
  apply (cancel_mono S.f).mp
  simpa only [zero_comp] using h₂ (f ≫ S.f)

theorem hom_from_third_zero {S : ShortComplex C} (hS : S.ShortExact) (T : C)
    (h₂ : ∀ f : S.X₂ ⟶ T, f = 0) : ∀ f : S.X₃ ⟶ T, f = 0 := by
  letI := hS.epi_g
  intro f
  apply (cancel_epi S.g).mp
  simpa only [comp_zero] using h₂ (S.g ≫ f)

theorem hom_from_first_zero {S : ShortComplex C} (hS : S.ShortExact) (T : C)
    (h₂ : ∀ f : S.X₂ ⟶ T, f = 0)
    (h₃ : ∀ x : Ext S.X₃ T 1, x = 0) : ∀ f : S.X₁ ⟶ T, f = 0 := by
  intro f
  obtain ⟨y, hy⟩ := Ext.contravariant_sequence_exact₁ hS T (Ext.mk₀ f)
    (show 1 + 0 = 1 from rfl) (h₃ _)
  have hy0 : y = 0 := by
    rw [← Ext.mk₀_homEquiv₀_apply y, h₂ (Ext.homEquiv₀ y), Ext.mk₀_zero]
  apply (Ext.mk₀_bijective S.X₁ T).injective
  rw [Ext.mk₀_zero, ← hy, hy0, Ext.comp_zero]

theorem hom_to_third_zero (T : C) {S : ShortComplex C} (hS : S.ShortExact)
    (h₂ : ∀ f : T ⟶ S.X₂, f = 0)
    (h₁ : ∀ x : Ext T S.X₁ 1, x = 0) : ∀ f : T ⟶ S.X₃, f = 0 := by
  intro f
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₃ T hS (Ext.mk₀ f)
    (show 0 + 1 = 1 from rfl) (h₁ _)
  have hy0 : y = 0 := by
    rw [← Ext.mk₀_homEquiv₀_apply y, h₂ (Ext.homEquiv₀ y), Ext.mk₀_zero]
  apply (Ext.mk₀_bijective T S.X₃).injective
  rw [Ext.mk₀_zero, ← hy, hy0, Ext.zero_comp]

theorem ext_from_third_zero {S : ShortComplex C} (hS : S.ShortExact) (T : C)
    (h₁ : ∀ f : S.X₁ ⟶ T, f = 0)
    (h₂ : ∀ x : Ext S.X₂ T 1, x = 0) : ∀ x : Ext S.X₃ T 1, x = 0 := by
  intro x
  obtain ⟨y, hy⟩ := Ext.contravariant_sequence_exact₃ hS T x (h₂ _)
    (show 1 + 0 = 1 from rfl)
  have hy0 : y = 0 := by
    rw [← Ext.mk₀_homEquiv₀_apply y, h₁ (Ext.homEquiv₀ y), Ext.mk₀_zero]
  rw [← hy, hy0, Ext.comp_zero]

theorem hom_from_middle_zero {S : ShortComplex C} (hS : S.ShortExact) (T : C)
    (h₁ : ∀ f : S.X₁ ⟶ T, f = 0) (h₃ : ∀ f : S.X₃ ⟶ T, f = 0) :
    ∀ f : S.X₂ ⟶ T, f = 0 := by
  intro f
  let a := hS.gIsCokernel.desc (CokernelCofork.ofπ f (h₁ (S.f ≫ f)))
  have ha : S.g ≫ a = f := hS.gIsCokernel.fac _ WalkingParallelPair.one
  rw [h₃ a, comp_zero] at ha
  exact ha.symm

theorem hom_to_middle_zero (T : C) {S : ShortComplex C} (hS : S.ShortExact)
    (h₁ : ∀ f : T ⟶ S.X₁, f = 0) (h₃ : ∀ f : T ⟶ S.X₃, f = 0) :
    ∀ f : T ⟶ S.X₂, f = 0 := by
  intro f
  let a := hS.fIsKernel.lift (KernelFork.ofι f (h₃ (f ≫ S.g)))
  have ha : a ≫ S.f = f := hS.fIsKernel.fac _ WalkingParallelPair.zero
  rw [h₁ a, zero_comp] at ha
  exact ha.symm

theorem hom_from_copies_zero (Y T : C) (n : ℕ)
    [HasBiproduct (fun _ : Fin n => Y)] (h : ∀ f : Y ⟶ T, f = 0) :
    ∀ f : (⨁ fun _ : Fin n => Y) ⟶ T, f = 0 := by
  intro f
  apply biproduct.hom_ext' f 0
  intro j
  simpa only [comp_zero] using h (biproduct.ι (fun _ : Fin n => Y) j ≫ f)

theorem hom_to_copies_zero (T Y : C) (n : ℕ)
    [HasBiproduct (fun _ : Fin n => Y)] (h : ∀ f : T ⟶ Y, f = 0) :
    ∀ f : T ⟶ (⨁ fun _ : Fin n => Y), f = 0 := by
  intro f
  apply biproduct.hom_ext f 0
  intro j
  simpa only [zero_comp] using h (f ≫ biproduct.π (fun _ : Fin n => Y) j)

/-- A red cokernel preceding a green kernel has Hom zero directly from
OLD reverse Hom to the fixed pivot. The separate Ext-zero consequence
still needs the full numerical Euler identity and selected sweep. -/
theorem cokernel_to_kernel_hom_zero (X X' Y : C) (n m : ℕ)
    [HasBiproduct (fun _ : Fin n => Y)] [HasBiproduct (fun _ : Fin m => Y)]
    (e : X ⟶ (⨁ fun _ : Fin n => Y))
    (e' : X' ⟶ (⨁ fun _ : Fin m => Y))
    (hYX : ∀ f : Y ⟶ X', f = 0) : ∀ f : cokernel e ⟶ kernel e', f = 0 := by
  intro f
  let h : (⨁ fun _ : Fin n => Y) ⟶ X' := cokernel.π e ≫ f ≫ kernel.ι e'
  have hz := hom_from_copies_zero Y X' n hYX h
  apply (cancel_mono (kernel.ι e')).mp
  apply (cancel_epi (cokernel.π e)).mp
  simpa only [h, Category.assoc, zero_comp, comp_zero] using hz

/-- Two actual universal left-extension middle objects inherit same-color
Hom zero from old same-color Hom, old pivot reverse Hom, and their already
derived internal new-to-pivot Hom zero. -/
theorem left_extensions_hom_zero (X X' Y Q Q' : C) (n m : ℕ)
    [HasBiproduct (fun _ : Fin n => Y)] [HasBiproduct (fun _ : Fin m => Y)]
    (i : (⨁ fun _ : Fin n => Y) ⟶ Q) (p : Q ⟶ X) (wi : i ≫ p = 0)
    (hS : (ShortComplex.mk i p wi).ShortExact)
    (i' : (⨁ fun _ : Fin m => Y) ⟶ Q') (p' : Q' ⟶ X') (wi' : i' ≫ p' = 0)
    (hS' : (ShortComplex.mk i' p' wi').ShortExact)
    (hXX : ∀ f : X ⟶ X', f = 0) (hYX : ∀ f : Y ⟶ X', f = 0)
    (hQY : ∀ f : Q ⟶ Y, f = 0) : ∀ f : Q ⟶ Q', f = 0 := by
  have hQX := hom_from_middle_zero hS X' (hom_from_copies_zero Y X' n hYX) hXX
  exact hom_to_middle_zero Q hS' (hom_to_copies_zero Q Y m hQY) hQX

/-- A red cokernel and a later red universal left extension are the mixed
same-color pair; OLD pivot reverse Hom and actual internal Hom suffice. -/
theorem cokernel_to_left_extension_hom_zero (X X' Y Q' : C) (n m : ℕ)
    [HasBiproduct (fun _ : Fin n => Y)] [HasBiproduct (fun _ : Fin m => Y)]
    (e : X ⟶ (⨁ fun _ : Fin n => Y))
    (i' : (⨁ fun _ : Fin m => Y) ⟶ Q') (p' : Q' ⟶ X') (wi' : i' ≫ p' = 0)
    (hS' : (ShortComplex.mk i' p' wi').ShortExact)
    (hYX : ∀ f : Y ⟶ X', f = 0) (hQY : ∀ f : cokernel e ⟶ Y, f = 0) :
    ∀ f : cokernel e ⟶ Q', f = 0 := by
  have hQX : ∀ f : cokernel e ⟶ X', f = 0 := by
    intro f
    apply (cancel_epi (cokernel.π e)).mp
    simpa only [comp_zero] using
      hom_from_copies_zero Y X' n hYX (cokernel.π e ≫ f)
  exact hom_to_middle_zero (cokernel e) hS'
    (hom_to_copies_zero (cokernel e) Y m hQY) hQX

/-- Both epic coevaluations produce green kernels. Their forward Hom is
zero using only OLD same-color Hom and reverse Ext to the fixed pivot. -/
theorem coevaluation_kernels_hom_zero (X X' Y : C) (n m : ℕ)
    [HasBiproduct (fun _ : Fin n => Y)] [HasBiproduct (fun _ : Fin m => Y)]
    (e : X ⟶ (⨁ fun _ : Fin n => Y))
    (e' : X' ⟶ (⨁ fun _ : Fin m => Y)) [Epi e] [Epi e']
    (hXX : ∀ f : X ⟶ X', f = 0)
    (hYX : ∀ x : Ext Y X' 1, x = 0) :
    ∀ f : kernel e ⟶ kernel e', f = 0 := by
  let S := ShortComplex.mk (kernel.ι e) e (kernel.condition e)
  let S' := ShortComplex.mk (kernel.ι e') e' (kernel.condition e')
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel e }
  have hS' : S'.ShortExact := { exact := ShortComplex.exact_kernel e' }
  have hCopies : ∀ x : Ext (⨁ fun _ : Fin n => Y) X' 1, x = 0 := by
    intro x
    let E := Ext.biproductAddEquiv (biproduct.isBilimit (fun _ : Fin n => Y)) X' 1
    apply E.injective
    ext j
    simpa only [map_zero, Pi.zero_apply] using hYX (E x j)
  exact hom_to_first_zero (kernel e) hS'
    (hom_from_first_zero hS X' hXX hCopies)

/-- Both monic full coevaluations produce red cokernels. Fullness derives
the new-to-pivot Hom zero; no future Hom vanishing is assumed. -/
theorem coevaluation_cokernels_hom_zero (X X' Y : C) (n m : ℕ)
    [HasBiproduct (fun _ : Fin n => Y)] [HasBiproduct (fun _ : Fin m => Y)]
    (f : Module.Basis (Fin n) K (X ⟶ Y))
    (f' : Module.Basis (Fin m) K (X' ⟶ Y))
    [Mono (biproduct.lift (f := fun _ : Fin n => Y) (fun j => f j))]
    [Mono (biproduct.lift (f := fun _ : Fin m => Y) (fun j => f' j))]
    (hEndY : ∀ g : Y ⟶ Y, ∃ c : K, g = c • 𝟙 Y)
    (hXX : ∀ g : X ⟶ X', g = 0)
    (hYX : ∀ x : Ext Y X' 1, x = 0) :
    ∀ g : cokernel (biproduct.lift (f := fun _ : Fin n => Y) (fun j => f j)) ⟶
      cokernel (biproduct.lift (f := fun _ : Fin m => Y) (fun j => f' j)), g = 0 := by
  let e := biproduct.lift (f := fun _ : Fin n => Y) (fun j => f j)
  let e' := biproduct.lift (f := fun _ : Fin m => Y) (fun j => f' j)
  let S := ShortComplex.mk e (cokernel.π e) (cokernel.condition e)
  let S' := ShortComplex.mk e' (cokernel.π e') (cokernel.condition e')
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel e }
  have hS' : S'.ShortExact := { exact := ShortComplex.exact_cokernel e' }
  have hCopies : ∀ x : Ext (⨁ fun _ : Fin n => Y) X' 1, x = 0 := by
    intro x
    let E := Ext.biproductAddEquiv (biproduct.isBilimit (fun _ : Fin n => Y)) X' 1
    apply E.injective
    ext j
    simpa only [map_zero, Pi.zero_apply] using hYX (E x j)
  have hQY : ∀ g : cokernel e ⟶ Y, g = 0 :=
    hom_coevaluation_cokernel_summand_zero X Y n f hEndY
  have hQCopies : ∀ g : cokernel e ⟶ (⨁ fun _ : Fin m => Y), g = 0 := by
    intro g
    apply biproduct.hom_ext g 0
    intro j
    simpa only [zero_comp] using hQY (g ≫ biproduct.π (fun _ : Fin m => Y) j)
  exact hom_to_third_zero (cokernel e) hS' hQCopies
    (ext_from_third_zero hS X' hXX hCopies)

#print axioms coevaluation_kernels_hom_zero
#print axioms coevaluation_cokernels_hom_zero
end QuiverProofs.MA4RestartArrow20261003.ColoredHomTransport
