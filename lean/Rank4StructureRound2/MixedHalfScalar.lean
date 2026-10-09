import Rank4StructureRound2.FlatMixedScalar

/-! A mixed scalar barrier for the first strong half-entry. The forward
incident entry may reach f; only b<f and b+ad<=f are required. This is
uniform arithmetic only, with no MA, properness or corridor premise. -/
namespace QuiverProofs.Rank4StructureRound2.MixedHalfScalar
open FlatMixedScalar
set_option maxHeartbeats 4000000

theorem box_quadratic (x y f : Int) (hx : 1≤x) (hy : 1≤y)
    (hxf : x≤f-1) (hyf : y≤f-1) (hf : 0≤f) :
    x^2+y^2-f*x*y≤2-f := by
  have hxx := mul_nonneg (show 0≤x-1 by omega) (show 0≤f-1-x by omega)
  have hyy := mul_nonneg (show 0≤y-1 by omega) (show 0≤f-1-y by omega)
  have hxy := mul_nonneg (show 0≤x-1 by omega) (show 0≤y-1 by omega)
  have hprod := mul_nonneg hf hxy
  nlinarith

theorem low_pfaffian_forces_negative_scalar (a b c d E f : Int)
    (ha : 2≤a) (hb : 1≤b) (hd : 0≤d) (hE : 0≤E)
    (hc : E<c) (hbtop : b<f) (hB : b+a*d≤f) (hC : a*c-E<f)
    (hpf : 2*pfaffian a b c d E f≤f) : scalar a b c d E f<0 := by
  let x := b+(a-1)*d
  let y := c-E
  have hdA := mul_nonneg (show 0≤a-1 by omega) hd
  have hb0 : 0≤b+a*d := by nlinarith [mul_nonneg (show 0≤a by omega) hd]
  have hK1 := mul_nonneg (mul_nonneg (show 0≤a-2 by omega) hd) hb0
  have hc0 : 0≤c := by omega
  have hK2 := mul_nonneg (mul_nonneg (show 0≤a-2 by omega) hc0) hE
  have hL := mul_nonneg (mul_nonneg (show 0≤a-2 by omega) hd) hE
  have hx : 1≤x := by dsimp [x]; nlinarith
  have hy : 1≤y := by dsimp [y]; omega
  have hxf : x≤f-1 := by
    dsimp [x]
    by_cases hd0 : d=0
    · subst d; nlinarith
    · have hd1 : 1≤d := by omega
      nlinarith
  have hyf : y≤f-1 := by dsimp [y]; nlinarith [mul_nonneg (show 0≤a-1 by omega) hc0]
  have haf : a<f := by
    have hc1 : 1≤c-E := by omega
    have hprod := mul_nonneg (show 0≤a-1 by omega) (show 0≤c-1 by omega)
    nlinarith
  have hf : 0≤f := by omega
  have hbox := box_quadratic x y f hx hy hxf hyf hf
  have hK : a^2+b^2+c^2+d^2+E^2+a*b*d-a*c*E≤a^2+x^2+y^2 := by
    dsimp [x,y]
    nlinarith
  have hbound : b*c+d*(a*c-E)≥a*f-pfaffian a b c d E f+x*y := by
    dsimp [x,y]
    unfold pfaffian
    nlinarith
  have hmul := mul_nonneg hf (show 0≤b*c+d*(a*c-E)-
    (a*f-pfaffian a b c d E f+x*y) by omega)
  have hpre : scalar a b c d E f≤a^2+x^2+y^2+f^2-a*f^2+
      f*pfaffian a b c d E f-f*x*y := by
    unfold scalar
    nlinarith
  have hpfmul := mul_nonneg hf (show 0≤f-2*pfaffian a b c d E f by omega)
  have hfinal : 2*scalar a b c d E f≤2*a^2+4-2*f-(2*a-3)*f^2 := by
    nlinarith
  by_cases ha2 : a=2
  · subst a
    have hf3 : 3≤f := by omega
    nlinarith
  · have ha3 : 3≤a := by omega
    have hsquare : a^2≤f^2 := by nlinarith
    have hprod := mul_nonneg (show 0≤a-3 by omega) (sq_nonneg f)
    nlinarith

theorem scalar_exceeds_height (a b c d E f : Int)
    (ha : 2≤a) (hb : 1≤b) (hd : 0≤d) (hE : 0≤E)
    (hc : E<c) (hbtop : b<f) (hB : b+a*d≤f) (hC : a*c-E<f)
    (hadmissible : 2*abs (pfaffian a b c d E f)≤scalar a b c d E f) :
    f<scalar a b c d E f := by
  by_contra hn
  have hle : scalar a b c d E f≤f := by omega
  have habs := le_abs_self (pfaffian a b c d E f)
  have hnegative := low_pfaffian_forces_negative_scalar a b c d E f
    ha hb hd hE hc hbtop hB hC (by omega)
  have hn0 := abs_nonneg (pfaffian a b c d E f)
  omega

#print axioms low_pfaffian_forces_negative_scalar
#print axioms scalar_exceeds_height
end QuiverProofs.Rank4StructureRound2.MixedHalfScalar
