import Rank4ReviewRound2.ZeroDoubleUnitOverflow
import Rank4CoordinatorR2.ZeroScalar

/-! Uniform arithmetic for the entire zero-unit overflow cone. A conditional
MA consumer derives e>d; it does not supply the missing global NMA closure.
Both structural properness bridges remain explicit.
-/
namespace Rank4ReviewRound2.ZeroUnitScalarBounds
open QuiverProofs Rank4Coordinator Rank4Round2 Rank4CoordinatorR2
open ProperOrder ProperWiggle ProperMutation ProperObstructionSoundness

def scalar (d e u v : Int) : Int :=
  d*d+e*e+1-d*e*(u+v)+u*u+u*v+v*v

theorem residual_scalar (c d e u v : Int) (hde : d*e=c+u+v) :
    zeroMarkov 1 c d e (c+u)=scalar d e u v := by
  have hc : c=d*e-u-v := by omega
  rw [hc]
  unfold zeroMarkov scalar
  ring

private theorem ordered_scalar_upper (d e u v : Int)
    (hu : 1≤u) (hv : u≤v) (hde : 2*v<d*e) :
    scalar d e u v≤(d-e)^2+4 := by
  have hp := mul_nonneg (show 0≤d*e-2*v-1 by omega)
    (show 0≤u+v-2 by omega)
  have hq := mul_nonneg (show 0≤u-1 by omega) (show 0≤v-u by omega)
  have hid : (d-e)^2+4-scalar d e u v=
      (d*e-2*v-1)*(u+v-2)+(u-1)^2+3*(u-1)*(v-u)+(v-u)^2 := by
    unfold scalar
    ring
  nlinarith [hid,sq_nonneg (u-1),sq_nonneg (v-u)]

theorem scalar_upper (c d e u v : Int) (hu : 0<u) (hv : 0<v)
    (hde : d*e=c+u+v) (hdu : 2*u<d*e) (hdv : 2*v<d*e) :
    zeroMarkov 1 c d e (c+u)≤(d-e)^2+4 := by
  rw [residual_scalar c d e u v hde]
  by_cases huv : u≤v
  · exact ordered_scalar_upper d e u v (by omega) huv hdv
  · have heq : scalar d e u v=scalar d e v u := by unfold scalar; ring
    rw [heq]
    exact ordered_scalar_upper d e v u (by omega) (by omega) hdu

private theorem small_c_scalar (c d e u v : Int)
    (hc : 2≤c) (he : 2≤e) (hed : e≤d) (hcd : c<d)
    (hde : d*e=c+u+v) (hfu : d<c+u) (hfv : d<c+v) :
    zeroMarkov 1 c d e (c+u)≤2 := by
  have ht : 0≤d-c+1 := by omega
  have hu : d-c+1≤u := by omega
  have hv : d-c+1≤v := by omega
  have hp := mul_nonneg (show 0≤u-(d-c+1) by omega) (show 0≤v by omega)
  have hq := mul_nonneg ht (show 0≤v-(d-c+1) by omega)
  have hmul := Int.mul_le_mul_of_nonneg_right hc (show 0≤d by omega)
  have hprod := mul_nonneg (show 0≤c*d-2*e by omega) (show 0≤e-2 by omega)
  have hM : zeroMarkov 1 c d e (c+u)=
      (d-c)^2+e*e+1-c*d*(e-2)-u*v := by
    have h0 := residual_scalar c d e u v hde
    unfold scalar at h0
    nlinarith [h0,hde]
  nlinarith [hM,hp,hq,hprod,sq_nonneg (e-2)]

private theorem large_c_pfaffian (c d e u v : Int)
    (he : 2≤e) (hed : e≤d) (hcd : d≤c)
    (hM : zeroMarkov 1 c d e (c+u)≤(d-e)^2+4) :
    zeroMarkov 1 c d e (c+u)≤2*|e-c*d| := by
  have hd : 2≤d := by omega
  have hmul := Int.mul_le_mul_of_nonneg_right hcd (show 0≤d by omega)
  have hpos : e-c*d≤0 := by nlinarith
  rw [abs_of_nonpos hpos]
  have hprod := mul_nonneg (show 0≤d-e by omega) (show 0≤d+e by omega)
  have he2 := mul_nonneg (show 0≤e-2 by omega) (show 0≤e+1 by omega)
  nlinarith [hM,hprod,he2]

theorem scalar_admissible_e_gt_d (c d e u v : Int)
    (hc : 2≤c) (hd : 2≤d) (he : 2≤e) (hu : 0<u) (hv : 0<v)
    (hde : d*e=c+u+v) (hdu : 2*u<d*e) (hdv : 2*v<d*e)
    (hfu : d<c+u) (hfv : d<c+v)
    (hM : 3≤zeroMarkov 1 c d e (c+u))
    (hPf : 2*|e-c*d|<zeroMarkov 1 c d e (c+u)) : d<e := by
  by_contra hn
  have hed : e≤d := by omega
  by_cases hcd : c<d
  · have h := small_c_scalar c d e u v hc he hed hcd hde hfu hfv
    omega
  · have h := large_c_pfaffian c d e u v he hed (by omega)
      (scalar_upper c d e u v hu hv hde hdu hdv)
    omega

theorem zeroPeak_MA_strict_pfaffian
    (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4)
    (b c d e f : Int) (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e) (hf : 0<f)
    (hma : MutationAcyclic (zeroPeak b c d e f)) :
    2*|b*e-c*d|<zeroMarkov b c d e f := by
  let B := zeroPeak b c d e f
  have hs : SkewSymmetric B := ofSix_skew _ _ _ _ _ _
  obtain ⟨p,hp⟩ := hExist B hs hma
  have h := connected_MA_totalProper_strict_pfaffian hEnd B hs
    (zeroPeak_connected b c d e f hb hd hf) hma p hp
  have hscalar : orderMarkov B p=zeroMarkov b c d e f :=
    zeroPeak_proper_markov b c d e f hb hc hd he hf p (totalProper_proper B p hp)
  have hpf : matrixPfaffian B=b*e-c*d := by
    change Algebra.pfaffian 0 b (-c) d (-e) f=b*e-c*d
    unfold Algebra.pfaffian
    ring
  rw [hscalar,hpf,Int.natCast_natAbs] at h
  exact h

theorem zero_unit_MA_overflow_e_gt_d
    (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4)
    (c d e f : Int) (H : Nat) (hc : 2≤c) (hd : 0<d) (he : 0<e)
    (h0 : HeightLe (mutate (zeroPeak 1 c d e f) 0) H)
    (h1 : HeightLe (mutate (zeroPeak 1 c d e f) 1) H)
    (hf : (H:Int)<f) (hover : f+(H:Int)<c+d*e)
    (hma : MutationAcyclic (zeroPeak 1 c d e f)) : d<e := by
  have hdH := h0 1 2
  have heH := h0 1 3
  have hcH := h0 0 3
  have huH := h0 2 3
  have hvH := h1 2 3
  rw [zeroPeak_zero 1 c d e f (by decide) (by omega)] at hdH heH hcH huH
  rw [zeroPeak_one 1 c d e f hd he] at hvH
  simp only [ofSix,one_mul] at hdH heH hcH huH hvH
  obtain ⟨u,v,hu,hv,hup,hvp,hd2,he2,_,_,hde,hf',hfu,hfv,_,_,_⟩ :=
    ZeroUnitDecomposition.zero_unit_overflow_decomposition c d e f H (by omega) hd he
      hcH.2 hdH.2 (by omega) huH.2 (by omega) hf hover
  have hdu : 2*u<d*e := by omega
  have hdv : 2*v<d*e := by omega
  have hM := zeroPeak_MA_markov hExist hEnd 1 c d e f
    (by decide) (by omega) hd he (by omega) hma
  have hPf := zeroPeak_MA_strict_pfaffian hExist hEnd 1 c d e f
    (by decide) (by omega) hd he (by omega) hma
  simp only [one_mul] at hPf
  rw [hf'] at hM hPf
  exact scalar_admissible_e_gt_d c d e u v hc hd2 he2 hup hvp hde hdu hdv
    (by omega) (by omega) hM hPf

#print axioms scalar_upper
#print axioms scalar_admissible_e_gt_d
#print axioms zero_unit_MA_overflow_e_gt_d
end Rank4ReviewRound2.ZeroUnitScalarBounds
