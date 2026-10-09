import MA4EulerExternalOrthogonality01a0fee4

/-! Direct coevaluation consumers of accepted exact-sequence outside
orthogonality. All unchanged objects and old orthogonality premises are
explicit; no future-frame predicate is supplied. -/
namespace QuiverProofs.MA4RestartArrow20261003.CoevaluationExternal
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open MA4EulerExternalOrthogonality01a0fee4
universe u v w
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
set_option maxHeartbeats 0

/-- Cokernel of an actual monic coevaluation stays orthogonal to every
unchanged target orthogonal to both old objects. -/
theorem coevaluation_cokernel_outside_orthogonality (X Y T : C) (n : ℕ)
    [HasBiproduct (fun _ : Fin n => Y)]
    (e : X ⟶ (⨁ fun _ : Fin n => Y)) [Mono e]
    (hX : (∀ g : X ⟶ T, g = 0) ∧ (∀ x : Ext X T 1, x = 0))
    (hY : (∀ g : Y ⟶ T, g = 0) ∧ (∀ x : Ext Y T 1, x = 0)) :
    (∀ g : cokernel e ⟶ T, g = 0) ∧ (∀ x : Ext (cokernel e) T 1, x = 0) :=
  quotient_outside_orthogonality
    (S := ShortComplex.mk e (cokernel.π e) (cokernel.condition e))
    { exact := ShortComplex.exact_cokernel e } T hX
    (finite_biproduct_outside_orthogonality (fun _ : Fin n => Y) T (fun _ => hY))

/-- The opposite outside direction uses hereditary dimension only on T. -/
theorem coevaluation_cokernel_inside_orthogonality (T X Y : C) (n : ℕ)
    [HasBiproduct (fun _ : Fin n => Y)] [HasProjectiveDimensionLT T 2]
    (e : X ⟶ (⨁ fun _ : Fin n => Y)) [Mono e]
    (hX : (∀ g : T ⟶ X, g = 0) ∧ (∀ x : Ext T X 1, x = 0))
    (hY : (∀ g : T ⟶ Y, g = 0) ∧ (∀ x : Ext T Y 1, x = 0)) :
    (∀ g : T ⟶ cokernel e, g = 0) ∧ (∀ x : Ext T (cokernel e) 1, x = 0) :=
  quotient_inside_orthogonality T
    (S := ShortComplex.mk e (cokernel.π e) (cokernel.condition e))
    { exact := ShortComplex.exact_cokernel e } hX
    (finite_biproduct_inside_orthogonality T (fun _ : Fin n => Y) (fun _ => hY))

/-- Kernel of an actual epic coevaluation stays orthogonal to unchanged
targets, using the hereditary bound on its old target sum. -/
theorem coevaluation_kernel_outside_orthogonality (X Y T : C) (n : ℕ)
    [HasBiproduct (fun _ : Fin n => Y)]
    [HasProjectiveDimensionLT (⨁ fun _ : Fin n => Y) 2]
    (e : X ⟶ (⨁ fun _ : Fin n => Y)) [Epi e]
    (hX : (∀ g : X ⟶ T, g = 0) ∧ (∀ x : Ext X T 1, x = 0))
    (hY : (∀ g : Y ⟶ T, g = 0) ∧ (∀ x : Ext Y T 1, x = 0)) :
    (∀ g : kernel e ⟶ T, g = 0) ∧ (∀ x : Ext (kernel e) T 1, x = 0) :=
  kernel_outside_orthogonality
    (S := ShortComplex.mk (kernel.ι e) e (kernel.condition e))
    { exact := ShortComplex.exact_kernel e } T hX
    (finite_biproduct_outside_orthogonality (fun _ : Fin n => Y) T (fun _ => hY))

/-- Kernel orthogonality in the opposite direction requires no dimension
bound, and every finite multiplicity, including zero, is allowed. -/
theorem coevaluation_kernel_inside_orthogonality (T X Y : C) (n : ℕ)
    [HasBiproduct (fun _ : Fin n => Y)]
    (e : X ⟶ (⨁ fun _ : Fin n => Y)) [Epi e]
    (hX : (∀ g : T ⟶ X, g = 0) ∧ (∀ x : Ext T X 1, x = 0))
    (hY : (∀ g : T ⟶ Y, g = 0) ∧ (∀ x : Ext T Y 1, x = 0)) :
    (∀ g : T ⟶ kernel e, g = 0) ∧ (∀ x : Ext T (kernel e) 1, x = 0) :=
  kernel_inside_orthogonality T
    (S := ShortComplex.mk (kernel.ι e) e (kernel.condition e))
    { exact := ShortComplex.exact_kernel e } hX
    (finite_biproduct_inside_orthogonality T (fun _ : Fin n => Y) (fun _ => hY))

#print axioms coevaluation_cokernel_outside_orthogonality
#print axioms coevaluation_kernel_inside_orthogonality
end QuiverProofs.MA4RestartArrow20261003.CoevaluationExternal
