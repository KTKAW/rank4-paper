import Rank4CoordinatorR2.ZeroScalar

/-! An actual positive zero peak with bounded incident entries cannot
change its opposite top from F to -F by the other zero-pair mutation.
The whole product wall de=2F has negative proper scalar. -/
namespace Rank4Round2.ZeroOrbitScalar
open QuiverProofs Rank4Coordinator Rank4CoordinatorR2 Rank4Round2
open ProperObstructionSoundness

theorem rectangle_pair (b c F : Int) (hF : 2≤F)
    (hb : 1≤b) (hc : 1≤c) (hbF : b≤F-1) (hcF : c≤F-1) :
    b*b+c*c-F*b*c≤2-F := by
  have hx := mul_nonneg (show 0≤b-1 by omega) (show 0≤F-1-b by omega)
  have hy := mul_nonneg (show 0≤c-1 by omega) (show 0≤F-1-c by omega)
  have hxy := mul_nonneg (show 0≤b-1 by omega) (show 0≤c-1 by omega)
  have hfxy := mul_nonneg (show 0≤F by omega) hxy
  nlinarith

theorem sign_flip_scalar_negative (b c d e F : Int)
    (hb : 1≤b) (hc : 1≤c) (hd : 1≤d) (he : 1≤e)
    (hbF : b≤F-1) (hcF : c≤F-1) (hdF : d≤F-1) (heF : e≤F-1)
    (hprod : d*e=2*F) : zeroMarkov b c d e F<0 := by
  have hd3 : 3≤d := by
    by_contra hn
    have hh := mul_nonneg (show 0≤2-d by omega) (show 0≤e by omega)
    nlinarith
  have he3 : 3≤e := by
    by_contra hn
    have hh := mul_nonneg (show 0≤2-e by omega) (show 0≤d by omega)
    nlinarith
  have hF : 4≤F := by omega
  have hbc := rectangle_pair b c F (by omega) hb hc hbF hcF
  have hdRect := mul_nonneg (show 0≤d-3 by omega) (show 0≤F-1-d by omega)
  have heRect := mul_nonneg (show 0≤e-3 by omega) (show 0≤F-1-e by omega)
  have hdeRect := mul_nonneg (show 0≤d-3 by omega) (show 0≤e-3 by omega)
  have hSum : 3*(d+e)≤2*F+9 := by nlinarith
  have hScale := mul_nonneg (show 0≤F+2 by omega)
    (show 0≤2*F+9-3*(d+e) by omega)
  have hSquares : 3*(d*d+e*e)≤2*F*F-5*F+36 := by nlinarith
  have hNegative : 42-8*F-F*F<0 := by nlinarith
  unfold zeroMarkov
  have hprodF : F*(d*e)=2*F*F := by rw [hprod];ring
  nlinarith

theorem sign_flip_not_MA (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4)
    (b c d e : Int) (H : Nat)
    (hb : 1≤b) (hc : 1≤c) (hd : 1≤d) (he : 1≤e)
    (hbH : b≤(H:Int)) (hcH : c≤(H:Int)) (hdH : d≤(H:Int)) (heH : e≤(H:Int))
    (hprod : d*e=2*((H:Int)+1)) :
    ¬MutationAcyclic (ofSix 0 b (-c) d (-e) ((H:Int)+1)) := by
  intro hma
  have hneg := sign_flip_scalar_negative b c d e ((H:Int)+1)
    hb hc hd he (by omega) (by omega) (by omega) (by omega) hprod
  have hMA := zeroPeak_MA_markov hExist hEnd b c d e ((H:Int)+1)
    (by omega) (by omega) (by omega) (by omega) (by omega) hma
  omega

#print axioms rectangle_pair
#print axioms sign_flip_scalar_negative
#print axioms sign_flip_not_MA
end Rank4Round2.ZeroOrbitScalar
