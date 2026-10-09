import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! A positive strict-peak shape cannot lie above its admissible proper scalar.
This is a uniform arithmetic theorem, independent of semantic MA and any
triangle or mutation-path theorem. The matrix/scalar bridge is separate. -/
namespace QuiverProofs.Rank4StructureRound2.PositivePeakScalar
set_option maxHeartbeats 4000000

def scalar (a b c d e f : Int) : Int :=
  a^2+b^2+c^2+d^2+e^2+a*b*d+a*c*e+f*(f-b*c-d*(e+a*c))
def pfaffian (a b c d e f : Int) : Int := a*f+b*e-c*d

private theorem quadratic_bound (a b c d e f : Int)
    (ha : 2≤a) (hb : 1≤b) (hc : 1≤c) (hd : 1≤d) (he : 1≤e)
    (hE : e+a*c<f) (hB : b+a*d<f) :
    a^2+b^2+c^2+d^2+e^2+a*b*d+a*c*e≤a^2+2*(f-1)^2 := by
  have ha0 : 0≤a := by omega
  have ha2 : 4≤a^2 := by nlinarith
  have hbd := mul_nonneg (mul_nonneg ha0 (show 0≤b by omega)) (show 0≤d by omega)
  have hce := mul_nonneg (mul_nonneg ha0 (show 0≤c by omega)) (show 0≤e by omega)
  have hd2 := mul_nonneg (show 0≤a^2-1 by omega) (show 0≤d^2 by positivity)
  have hc2 := mul_nonneg (show 0≤a^2-1 by omega) (show 0≤c^2 by positivity)
  have hleft : b^2+d^2+a*b*d≤(b+a*d)^2 := by nlinarith
  have hright : c^2+e^2+a*c*e≤(e+a*c)^2 := by nlinarith
  have hB0 : 0≤b+a*d := by positivity
  have hE0 : 0≤e+a*c := by positivity
  have hBs : (b+a*d)^2≤(f-1)^2 := by nlinarith
  have hEs : (e+a*c)^2≤(f-1)^2 := by nlinarith
  nlinarith

theorem low_pfaffian_forces_negative_scalar (a b c d e f : Int)
    (ha : 2≤a) (hb : 1≤b) (hc : 1≤c) (hd : 1≤d) (he : 1≤e)
    (hE : e+a*c<f) (hB : b+a*d<f)
    (hpf : 2*pfaffian a b c d e f≤f) : scalar a b c d e f<0 := by
  have hK := quadratic_bound a b c d e f ha hb hc hd he hE hB
  have ha0 : 0≤a := by omega
  have ha2 : 4≤a^2 := by nlinarith
  have hac := mul_nonneg ha0 (show 0≤c-1 by omega)
  have hf : a+2≤f := by nlinarith
  have hf0 : 0≤f := by omega
  have habc := mul_nonneg (show 0≤b by omega) (show 0≤c by omega)
  have hade := mul_nonneg (show 0≤d by omega) (show 0≤e by omega)
  have habe := mul_nonneg (mul_nonneg ha0 (show 0≤b by omega)) (show 0≤e by omega)
  have hdrop := mul_nonneg (show 0≤a*b*e+b*c+d*e by omega) hf0
  have hbound : scalar a b c d e f≤
      -(a^2-1)*f^2+a*pfaffian a b c d e f*f+a^2+2*(f-1)^2 := by
    unfold scalar pfaffian
    nlinarith
  have hpfscaled := mul_nonneg (show 0≤f-2*pfaffian a b c d e f by omega)
    (mul_nonneg ha0 hf0)
  have hfinal : 2*scalar a b c d e f≤
      -(2*a^2-a-6)*f^2+2*a^2-8*f+4 := by nlinarith
  by_cases h2 : a=2
  · subst a
    nlinarith
  · have h3 : 3≤a := by omega
    have hp := mul_nonneg (show 0≤a-3 by omega) (show 0≤a+2 by omega)
    have hcoef : a^2≤2*a^2-a-6 := by nlinarith
    have hfsq : 4≤f^2 := by nlinarith
    have hq := mul_nonneg (show 0≤2*a^2-a-6-a^2 by omega) (show 0≤f^2 by positivity)
    have hr := mul_nonneg (show 0≤a^2 by positivity) (show 0≤f^2-4 by omega)
    nlinarith

theorem scalar_exceeds_height (a b c d e f : Int)
    (ha : 2≤a) (hb : 1≤b) (hc : 1≤c) (hd : 1≤d) (he : 1≤e)
    (hE : e+a*c<f) (hB : b+a*d<f)
    (hnecessary : 2*abs (pfaffian a b c d e f)<scalar a b c d e f) :
    f<scalar a b c d e f := by
  have habs : pfaffian a b c d e f≤abs (pfaffian a b c d e f) := le_abs_self _
  have hn : 0≤scalar a b c d e f := by have h := abs_nonneg (pfaffian a b c d e f); omega
  have hp : f<2*pfaffian a b c d e f := by
    by_contra hh
    have hneg := low_pfaffian_forces_negative_scalar a b c d e f
      ha hb hc hd he hE hB (by omega)
    omega
  omega

#print axioms low_pfaffian_forces_negative_scalar
#print axioms scalar_exceeds_height
end QuiverProofs.Rank4StructureRound2.PositivePeakScalar
