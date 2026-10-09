import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! Scalar bound for the mixed two-state flat block. Only the two strict
lower-exit inequalities are needed; no triangle, properness or MA premise.
The relation to a matrix's proper scalar remains a separate obligation. -/
namespace QuiverProofs.Rank4StructureRound2.FlatMixedScalar
set_option maxHeartbeats 4000000

def scalar (a b c d E f : Int) : Int :=
  a^2+b^2+c^2+d^2+E^2+a*b*d-a*c*E+f*(f-b*c-d*(a*c-E))
def pfaffian (a b c d E f : Int) : Int := a*f-b*E-c*d

private theorem pair_bound (a u v : Int) (ha : 2≤a) (hu : 0≤u) (hv : 0≤v) :
    a^2*(u^2+a*u*v+v^2)≤(a*u+(a^2-1)*v)^2 := by
  have ha0 : 0≤a := by omega
  have ha2 : 4≤a^2 := by nlinarith
  have hcoef : 0≤a^4-3*a^2+1 := by
    have hp := mul_nonneg (show 0≤a^2 by positivity) (show 0≤a^2-3 by omega)
    nlinarith
  have hfirst := mul_nonneg (mul_nonneg (mul_nonneg ha0 hu) hv)
    (show 0≤a^2-2 by omega)
  have hsecond := mul_nonneg (show 0≤v^2 by positivity) hcoef
  nlinarith

private theorem initial_quadratic_bound (a b c d E f : Int)
    (ha : 2≤a) (hb : 1≤b) (hd : 0≤d) (hE : 0≤E) (hc : a*E<c)
    (hleft : a*c-E<f) (hright : a*b+(a^2-1)*d<f) :
    a^2+b^2+c^2+d^2+E^2+a*b*d-a*c*E≤f^2 := by
  have ha0 : 0≤a := by omega
  have ha2 : 4≤a^2 := by nlinarith
  have hbd := pair_bound a b d ha (by omega) hd
  have hce := pair_bound a (c-a*E) E ha (by omega) hE
  have hde := mul_nonneg (show 0≤a^2-1 by omega) hd
  have hab := mul_nonneg ha0 (show 0≤b-1 by omega)
  have hfa : a+1≤f := by nlinarith
  have hS0 : 0≤a*b+(a^2-1)*d := by nlinarith
  have hT0 : 0≤a*c-E := by
    have hp := mul_nonneg ha0 (show 0≤c-a*E by omega)
    have he := mul_nonneg (show 0≤a^2-1 by omega) hE
    nlinarith
  have hSsquare : (a*b+(a^2-1)*d)^2≤(f-1)^2 := by nlinarith
  have hTsquare : (a*c-E)^2≤(f-1)^2 := by nlinarith
  have hce' : a^2*(c^2+E^2-a*c*E)≤(a*c-E)^2 := by
    convert hce using 1 <;> ring
  have hsum : a^2*(a^2+b^2+c^2+d^2+E^2+a*b*d-a*c*E)≤a^4+2*(f-1)^2 := by
    nlinarith
  have hfsq : (a+1)^2≤f^2 := by nlinarith
  have hp := mul_nonneg (show 0≤a^2-2 by omega) (show 0≤f^2-(a+1)^2 by omega)
  have hq := mul_nonneg (show 0≤a^2 by positivity) (show 0≤2*a-1 by omega)
  have hlimit : a^4+2*(f-1)^2≤a^2*f^2 := by nlinarith
  nlinarith

theorem low_pfaffian_forces_negative_scalar (a b c d E f : Int)
    (ha : 2≤a) (hb : 1≤b) (hd : 0≤d) (hE : 0≤E) (hc : a*E<c)
    (hleft : a*c-E<f) (hright : a*b+(a^2-1)*d<f)
    (hpf : 2*pfaffian a b c d E f≤f) : scalar a b c d E f<0 := by
  have hK := initial_quadratic_bound a b c d E f ha hb hd hE hc hleft hright
  have ha0 : 0≤a := by omega
  have ha2 : 4≤a^2 := by nlinarith
  have hde := mul_nonneg (show 0≤a^2-1 by omega) hd
  have hab := mul_nonneg ha0 (show 0≤b-1 by omega)
  have hf : 0<f := by nlinarith
  have hbe := mul_nonneg (show 0≤b by omega) hE
  have hx := mul_nonneg (show 0≤c-a*E by omega) hd
  have hR : a*d*E≤b*E+c*d := by nlinarith
  have hRf := mul_nonneg (show 0≤b*E+c*d-a*d*E by omega) (show 0≤f by omega)
  have hbx := mul_nonneg (show 0≤b by omega) (show 0≤c-a*E by omega)
  have hbxaf := mul_nonneg hbx (mul_nonneg ha0 (show 0≤f by omega))
  have hKa := mul_nonneg (show 0≤f^2-(a^2+b^2+c^2+d^2+E^2+a*b*d-a*c*E) by omega) ha0
  have hbound : a*scalar a b c d E f ≤
      -(a^3-3*a)*f^2+(a^2-1)*pfaffian a b c d E f*f := by
    unfold scalar pfaffian
    nlinarith
  have hpfscaled := mul_nonneg (show 0≤f-2*pfaffian a b c d E f by omega)
    (mul_nonneg (show 0≤a^2-1 by omega) (show 0≤f by omega))
  have hcoef : 1≤2*a^3-a^2-6*a+1 := by
    have hp := mul_nonneg (show 0≤a-2 by omega) (show 0≤2*a^2+3*a by nlinarith)
    nlinarith
  have hcoeff := mul_nonneg (show 0≤2*a^3-a^2-6*a by omega)
    (show 0≤f^2 by positivity)
  have hfsq : 0<f^2 := by nlinarith
  nlinarith

theorem scalar_exceeds_height (a b c d E f : Int)
    (ha : 2≤a) (hb : 1≤b) (hd : 0≤d) (hE : 0≤E) (hc : a*E<c)
    (hleft : a*c-E<f) (hright : a*b+(a^2-1)*d<f)
    (hnecessary : 2*abs (pfaffian a b c d E f)<scalar a b c d E f) :
    f<scalar a b c d E f := by
  have habs : pfaffian a b c d E f≤abs (pfaffian a b c d E f) := le_abs_self _
  have hn : 0≤scalar a b c d E f := by have h := abs_nonneg (pfaffian a b c d E f); omega
  have hp : f<2*pfaffian a b c d E f := by
    by_contra hh
    have hneg := low_pfaffian_forces_negative_scalar a b c d E f
      ha hb hd hE hc hleft hright (by omega)
    omega
  omega

#print axioms low_pfaffian_forces_negative_scalar
#print axioms scalar_exceeds_height
end QuiverProofs.Rank4StructureRound2.FlatMixedScalar
