import MA4RestartArrow20261003.RightTracedReplacement
import MA4RestartArrow20261003.ColoredHomTransport
namespace QuiverProofs.MA4RestartArrow20261003.RightTraceBoundaryHom
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open QuiverProofs.MA4RestartRightColorTraceHom
open QuiverProofs.MA4RestartArrow20261003.ColoredHomTransport
universe w v u z
variable {K : Type w} [Field K] {C : Type u}
  [Category.{v} C] [Abelian C] [Linear K C] [HasExt.{z} C] [HasFiniteBiproducts C]
set_option maxHeartbeats 0

theorem red_trace_old_red (X Y Q : C) (ci : Bool)
    (h : RightColorTrace (K := K) X Y Q ci false) : ci = false := by
  rcases h with ⟨hi,hg,h⟩ | ⟨hi,hg,h⟩ | ⟨hi,hg,h⟩
  · cases hg
  · exact hi
  · cases hg

theorem hom_from_red_trace (X Y Q T : C) (ci : Bool)
    (h : RightColorTrace (K := K) X Y Q ci false)
    (hXT : ∀ f : X ⟶ T, f = 0) : ∀ f : Q ⟶ T, f = 0 := by
  rcases h with ⟨hi,hg,h⟩ | ⟨hi,hg,n,f,hm,hQ⟩ | ⟨hi,hg,h⟩
  · cases hg
  · rw [hQ]
    intro g
    apply (cancel_epi (cokernel.π _)).mp
    simpa only [comp_zero] using hXT (cokernel.π _ ≫ g)
  · cases hg

theorem hom_to_green_trace (T X Y Q : C) (ci : Bool)
    (h : RightColorTrace (K := K) X Y Q ci true)
    (hTY : ∀ f : T ⟶ Y, f = 0)
    (hTX : ci = true → ∀ f : T ⟶ X, f = 0) : ∀ f : T ⟶ Q, f = 0 := by
  rcases h with ⟨hi,hg,n,f,he,hQ⟩ | ⟨hi,hg,h⟩ | ⟨hi,hg,n,i,p,wi,hS⟩
  · rw [hQ]
    intro g
    apply (cancel_mono (kernel.ι _)).mp
    simpa only [zero_comp] using hom_to_copies_zero T Y n hTY (g ≫ kernel.ι _)
  · cases hg
  · exact hom_to_middle_zero T hS (hTX hi) (hom_to_copies_zero T Y n hTY)

theorem hom_from_old_green_trace (X Y Q T : C) (gi : Bool)
    (h : RightColorTrace (K := K) X Y Q true gi)
    (hXT : ∀ f : X ⟶ T, f = 0) (hYT : ∀ f : Y ⟶ T, f = 0) :
    ∀ f : Q ⟶ T, f = 0 := by
  rcases h with ⟨hi,hg,h⟩ | ⟨hi,hg,h⟩ | ⟨hi,hg,n,i,p,wi,hS⟩
  · cases hi
  · cases hi
  · exact hom_from_middle_zero hS T hXT (hom_from_copies_zero Y T n hYT)
#print axioms hom_to_green_trace
end QuiverProofs.MA4RestartArrow20261003.RightTraceBoundaryHom
