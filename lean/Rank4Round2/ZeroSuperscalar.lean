import Rank4Round2.ZeroWeakConsumers

/-! The reviewed dominance reduction also bounds the overflowing edge by
the actual proper scalar. This supplies a superscalar peak exclusion without
closing the residual strip walls. Both foundational bridges remain explicit.
-/
namespace Rank4Round2.ZeroSuperscalar
open QuiverProofs Rank4Coordinator Rank4Round2 Rank4CoordinatorR2
open ProperObstructionSoundness

theorem scalar_dominates_edge (c d e f m : Int)
    (hd : 2≤d) (he : 0≤e) (hec : e<c) (hfde : f<d*e)
    (hPf : 2*|e-c*d|<m) : f<m := by
  have hc : 0≤c := by omega
  have hcd := Int.mul_le_mul_of_nonneg_right hd hc
  have hneg : e-c*d≤0 := by nlinarith
  rw [abs_of_nonpos hneg] at hPf
  have hdelta := Int.mul_le_mul_of_nonneg_left
    (show 1≤c-e by omega) (show 0≤d by omega)
  have hprod := mul_nonneg (show 0≤d-2 by omega) he
  nlinarith [hPf,hdelta,hprod]

theorem zero_unit_MA_overflow_superscalar
    (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4)
    (c d e f : Int) (H : Nat) (hc : 2≤c) (hd : 0<d) (he : 0<e)
    (h0 : HeightLe (mutate (zeroPeak 1 c d e f) 0) H)
    (h1 : HeightLe (mutate (zeroPeak 1 c d e f) 1) H)
    (hf : (H:Int)<f) (hover : f+(H:Int)<c+d*e)
    (hma : MutationAcyclic (zeroPeak 1 c d e f)) :
    f<zeroMarkov 1 c d e f := by
  have ho := Rank4ReviewRound2.ZeroUnitDominance.zero_unit_MA_overflow_dominance
    hExist hEnd c d e f H hc hd he h0 h1 hf hover hma
  have heH := h0 1 3
  have hcH := h0 0 3
  rw [zeroPeak_zero 1 c d e f (by decide) (by omega)] at heH hcH
  simp only [ofSix] at heH hcH
  have hd2 : 2≤d := by
    by_contra hn
    have hd1 : d=1 := by omega
    rw [hd1] at hover
    simp only [one_mul] at hover
    omega
  have hPf := Rank4ReviewRound2.ZeroUnitScalarBounds.zeroPeak_MA_strict_pfaffian
    hExist hEnd 1 c d e f (by decide) (by omega) hd he (by omega) hma
  simp only [one_mul] at hPf
  exact scalar_dominates_edge c d e f _ hd2 (by omega) ho.2
    (by omega) hPf

theorem no_zero_unit_superscalar_overflow
    (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4)
    (c d e f : Int) (H : Nat) (hc : 2≤c) (hd : 0<d) (he : 0<e)
    (h0 : HeightLe (mutate (zeroPeak 1 c d e f) 0) H)
    (h1 : HeightLe (mutate (zeroPeak 1 c d e f) 1) H)
    (hf : (H:Int)<f) (hover : f+(H:Int)<c+d*e)
    (hM : zeroMarkov 1 c d e f≤(H:Int)) :
    ¬MutationAcyclic (zeroPeak 1 c d e f) := by
  intro hma
  have hs := zero_unit_MA_overflow_superscalar
    hExist hEnd c d e f H hc hd he h0 h1 hf hover hma
  omega

#print axioms scalar_dominates_edge
#print axioms zero_unit_MA_overflow_superscalar
#print axioms no_zero_unit_superscalar_overflow
end Rank4Round2.ZeroSuperscalar
