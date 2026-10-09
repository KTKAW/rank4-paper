import Rank4ReviewRound2.ZeroUnitScalarBounds

/-! Further uniform cone restrictions, conditional on the same MA properness
bridges. Parameter comparisons here are proved inequalities, never an
assumption that d and e can be interchanged by mutation or relabeling.
-/
namespace Rank4ReviewRound2.ZeroUnitDominance
open QuiverProofs Rank4Coordinator Rank4Round2 Rank4CoordinatorR2
open ProperObstructionSoundness ZeroUnitScalarBounds

theorem small_c_scalar (c d e u v : Int)
    (hc : 2≤c) (hd : 2≤d) (hdeOrder : d≤e) (hce : c<e)
    (hde : d*e=c+u+v) (hfu : e<c+u) (hfv : e<c+v) :
    zeroMarkov 1 c d e (c+u)≤2 := by
  have ht : 0≤e-c+1 := by omega
  have hp := mul_nonneg (show 0≤u-(e-c+1) by omega) (show 0≤v by omega)
  have hq := mul_nonneg ht (show 0≤v-(e-c+1) by omega)
  have hmul := Int.mul_le_mul_of_nonneg_right hc (show 0≤e by omega)
  have hprod := mul_nonneg (show 0≤c*e-2*d by omega) (show 0≤d-2 by omega)
  have hM : zeroMarkov 1 c d e (c+u)=
      (e-c)^2+d*d+1-c*e*(d-2)-u*v := by
    have h0 := residual_scalar c d e u v hde
    unfold scalar at h0
    nlinarith [h0,hde]
  nlinarith [hM,hp,hq,hprod,sq_nonneg (d-2)]

theorem equal_c_scalar (d e u v : Int)
    (hd : 2≤d) (hdeOrder : d≤e) (hu : 0<u) (hv : 0<v)
    (hde : d*e=e+u+v) : zeroMarkov 1 e d e (e+u)≤4 := by
  have huv := mul_nonneg (show 0≤u-1 by omega) (show 0≤v-1 by omega)
  have hM : zeroMarkov 1 e d e (e+u)=d*d-(d-2)*e*e+1-u*v := by
    have h0 := residual_scalar e d e u v hde
    unfold scalar at h0
    nlinarith [h0,hde]
  by_cases hd2 : d=2
  · subst d
    nlinarith [hM,huv]
  · have hp := mul_nonneg (show 0≤d-2 by omega) (show 0≤e*e-d*d by nlinarith)
    have hq := mul_nonneg (show 0≤d-3 by omega) (show 0≤d*d by nlinarith)
    nlinarith [hM,hp,hq,huv]

theorem scalar_admissible_c_gt_e (c d e u v : Int)
    (hc : 2≤c) (hd : 2≤d) (hdeOrder : d<e) (hu : 0<u) (hv : 0<v)
    (hde : d*e=c+u+v) (hfu : e<c+u) (hfv : e<c+v)
    (hM : 3≤zeroMarkov 1 c d e (c+u))
    (hPf : 2*|e-c*d|<zeroMarkov 1 c d e (c+u)) : e<c := by
  by_contra hn
  by_cases hce : c<e
  · have h := small_c_scalar c d e u v hc hd (by omega) hce hde hfu hfv
    omega
  · have hce : c=e := by omega
    subst c
    have h := equal_c_scalar d e u v hd (by omega) hu hv hde
    have hmul := Int.mul_le_mul_of_nonneg_right hd (show 0≤e by omega)
    have hneg : e-e*d≤0 := by nlinarith
    rw [abs_of_nonpos hneg] at hPf
    nlinarith [h,hPf,hmul]

theorem zero_unit_MA_overflow_dominance
    (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4)
    (c d e f : Int) (H : Nat) (hc : 2≤c) (hd : 0<d) (he : 0<e)
    (h0 : HeightLe (mutate (zeroPeak 1 c d e f) 0) H)
    (h1 : HeightLe (mutate (zeroPeak 1 c d e f) 1) H)
    (hf : (H:Int)<f) (hover : f+(H:Int)<c+d*e)
    (hma : MutationAcyclic (zeroPeak 1 c d e f)) : d<e ∧ e<c := by
  have hgt := zero_unit_MA_overflow_e_gt_d hExist hEnd c d e f H hc hd he h0 h1 hf hover hma
  have hdH := h0 1 2
  have heH := h0 1 3
  have hcH := h0 0 3
  have huH := h0 2 3
  have hvH := h1 2 3
  rw [zeroPeak_zero 1 c d e f (by decide) (by omega)] at hdH heH hcH huH
  rw [zeroPeak_one 1 c d e f hd he] at hvH
  simp only [ofSix,one_mul] at hdH heH hcH huH hvH
  obtain ⟨u,v,_,_,hup,hvp,hd2,_,_,_,hde,hf',hfu,hfv,_,_,_⟩ :=
    ZeroUnitDecomposition.zero_unit_overflow_decomposition c d e f H (by omega) hd he
      hcH.2 hdH.2 (by omega) huH.2 (by omega) hf hover
  have hM := zeroPeak_MA_markov hExist hEnd 1 c d e f
    (by decide) (by omega) hd he (by omega) hma
  have hPf := zeroPeak_MA_strict_pfaffian hExist hEnd 1 c d e f
    (by decide) (by omega) hd he (by omega) hma
  simp only [one_mul] at hPf
  rw [hf'] at hM hPf
  exact ⟨hgt,scalar_admissible_c_gt_e c d e u v hc hd2 hgt hup hvp hde
    (by omega) (by omega) hM hPf⟩

#print axioms scalar_admissible_c_gt_e
#print axioms zero_unit_MA_overflow_dominance
end Rank4ReviewRound2.ZeroUnitDominance
