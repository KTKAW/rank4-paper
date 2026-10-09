import MA4RestartArrow20261003.LeftColorTraceHom

/-! Hom-only outside boundary laws of the same actual left map/SES traces.
Every boundary hypothesis concerns old objects; no future colored law. -/
namespace QuiverProofs.MA4RestartArrow20261003.LeftTraceBoundaryHom
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open QuiverProofs.MA4RestartArrow20261003.ColoredHomTransport
open QuiverProofs.MA4RestartArrow20261003.LeftColorTraceHom
universe w v u z
variable {K : Type w} [Field K] {C : Type u}
  [Category.{v} C] [Abelian C] [Linear K C] [HasExt.{z} C] [HasFiniteBiproducts C]
set_option maxHeartbeats 0

theorem green_trace_old_green (X Y Q : C) (ci : Bool)
    (h : LeftColorTrace (K := K) X Y Q ci true) : ci = true := by
  cases h
  rfl

theorem hom_to_green_trace (T X Y Q : C) (ci : Bool)
    (h : LeftColorTrace (K := K) X Y Q ci true)
    (hTX : ∀ f : T ⟶ X, f = 0) : ∀ f : T ⟶ Q, f = 0 := by
  cases h with
  | kernel n f he hQ =>
    rw [hQ]
    intro g
    apply (cancel_mono (kernel.ι _)).mp
    simpa only [zero_comp] using hTX (g ≫ kernel.ι _)

theorem hom_from_red_trace (X Y Q T : C) (ci : Bool)
    (h : LeftColorTrace (K := K) X Y Q ci false)
    (hYT : ∀ f : Y ⟶ T, f = 0)
    (hXT : ci = false → ∀ f : X ⟶ T, f = 0) : ∀ f : Q ⟶ T, f = 0 := by
  cases h with
  | cokernel n f he hQ =>
    rw [hQ]
    intro g
    apply (cancel_epi (cokernel.π _)).mp
    simpa only [comp_zero] using hom_from_copies_zero Y T n hYT (cokernel.π _ ≫ g)
  | extension n i p wi hS =>
    exact hom_from_middle_zero hS T (hom_from_copies_zero Y T n hYT) (hXT rfl)

theorem hom_to_old_red_trace (T X Y Q : C) (gi : Bool)
    (h : LeftColorTrace (K := K) X Y Q false gi)
    (hTY : ∀ f : T ⟶ Y, f = 0) (hTX : ∀ f : T ⟶ X, f = 0) :
    ∀ f : T ⟶ Q, f = 0 := by
  cases h with
  | extension n i p wi hS =>
    exact hom_to_middle_zero T hS (hom_to_copies_zero T Y n hTY) hTX

#print axioms green_trace_old_green
#print axioms hom_to_green_trace
#print axioms hom_from_red_trace
#print axioms hom_to_old_red_trace
end QuiverProofs.MA4RestartArrow20261003.LeftTraceBoundaryHom
