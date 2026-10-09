import Rank4StructureRound2.FlatMixedScalar

/-! Extend the mixed scalar obstruction from c>aE into the adjacent range
(a-1)E<c<=aE. This is scalar arithmetic; the proper-order/MA bridge and
arbitrary corridor assembly are separate statements. -/
namespace Rank4ReviewRound2.StrongPairMixedScalar
open QuiverProofs.Rank4StructureRound2.FlatMixedScalar

private theorem rectangle (u x f : Int) (hu : 1≤u) (hx : 1≤x)
    (huf : u≤f-1) (hxf : x≤f-1) : u^2+x^2-f*u*x≤2-f := by
  have hU := mul_nonneg (show 0≤u-1 by omega) (show 0≤f-1-u by omega)
  have hX := mul_nonneg (show 0≤x-1 by omega) (show 0≤f-1-x by omega)
  have hUX := mul_nonneg (show 0≤u-1 by omega) (show 0≤x-1 by omega)
  have hF := mul_nonneg (show 0≤f by omega) hUX
  nlinarith

private theorem coefficient_bound (a f : Int) (ha : 2≤a) (hf : a<f) :
    2*a^2+4-2*f-(2*a^2-3*a-1)*f^2<0 := by
  by_cases ha2 : a=2
  · subst a
    nlinarith [sq_nonneg (f-3)]
  · have ha3 : 3≤a := by omega
    have hp := mul_nonneg (show 0≤a by omega) (show 0≤a-3 by omega)
    have hcoef : a^2-1≤2*a^2-3*a-1 := by nlinarith
    have hdiff := mul_nonneg (show 0≤2*a^2-3*a-1-(a^2-1) by omega)
      (show 0≤f^2 by positivity)
    have hsmall := mul_nonneg (show 0≤a^2-1 by nlinarith)
      (show 0≤f^2-4 by nlinarith)
    nlinarith

theorem adjacent_mixed_low_pfaffian_negative (a b c d E f : Int)
    (ha : 2≤a) (hb : 1≤b) (hd : 0≤d) (hE : 0≤E) (hf : a<f)
    (hx0 : (a-1)*E<c) (hxE : c≤a*E)
    (hu : b+(a-1)*d<f) (hx : c-(a-1)*E<f)
    (hpf : 2*pfaffian a b c d E f≤f) : scalar a b c d E f<0 := by
  let u := b+(a-1)*d
  let x := c-(a-1)*E
  have hu1 : 1≤u := by
    dsimp [u]
    have h := mul_nonneg (show 0≤a-1 by omega) hd
    nlinarith
  have hx1 : 1≤x := by dsimp [x]; omega
  have hxE' : x≤E := by dsimp [x]; nlinarith
  have hrect := rectangle u x f hu1 hx1 (by dsimp [u]; omega) (by dsimp [x]; omega)
  have hleft := mul_nonneg (show 0≤a-2 by omega)
    (mul_nonneg hd (show 0≤b+a*d by have h:=mul_nonneg (show 0≤a by omega) hd; nlinarith))
  have hright := mul_nonpos_of_nonneg_of_nonpos
    (show 0≤a-2 by omega)
    (mul_nonpos_of_nonpos_of_nonneg (show x-E≤0 by omega)
      (show 0≤E+f*d by have h:=mul_nonneg (show 0≤f by omega) hd; omega))
  have hdecomp : scalar a b c d E f=
      a^2+u^2+x^2-f*u*x-(a^2-a-1)*f^2+(a-1)*f*pfaffian a b c d E f
        -(a-2)*d*(b+a*d)+(a-2)*(x-E)*(E+f*d) := by
    dsimp [scalar,pfaffian,u,x]
    ring
  have hrest : scalar a b c d E f≤
      a^2+2-f-(a^2-a-1)*f^2+(a-1)*f*pfaffian a b c d E f := by
    rw [hdecomp]
    nlinarith
  have hpfMul := mul_nonneg (mul_nonneg (show 0≤a-1 by omega)
    (show 0≤f by omega)) (show 0≤f-2*pfaffian a b c d E f by omega)
  have hcoef := coefficient_bound a f ha hf
  nlinarith

#print axioms adjacent_mixed_low_pfaffian_negative
end Rank4ReviewRound2.StrongPairMixedScalar
