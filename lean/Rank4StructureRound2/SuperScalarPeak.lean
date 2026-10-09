import Rank4StructureRound2.PositivePeakOrder
import Rank4StructureRound2.FlatMixedOrder
import Mathlib.Algebra.Order.Ring.Abs

/-! Actual MA scalar bounds for positive strict peaks and mixed flat blocks.
The endpoint bridge and, when needed, MA total-proper-order existence remain
explicit. No connectedness, hereditary premise or global path bound is used.
-/
namespace QuiverProofs.Rank4StructureRound2.SuperScalarPeak
open Census ProperOrder ProperWiggle ProperMutation ProperObstructionSoundness
set_option maxHeartbeats 4000000

/-- The non-strict Pfaffian bound needs no connectedness assumption. -/
theorem MA_totalProper_pfaffian_bound (hEnd : EndpointTopological4)
    (B : Matrix 4) (hB : SkewSymmetric B) (hMA : MutationAcyclic B)
    (p : CyclicOrder) (hp : TotalProper B p) :
    2*abs (matrixPfaffian B)≤orderMarkov B p := by
  obtain ⟨w,hw⟩ := hMA
  obtain ⟨r,htr,hpr⟩ := totalProper_lifts_word B hB p hp w
  have hC := word_preserves_skew B w hB
  obtain ⟨q,hq,hrq⟩ := hEnd _ hC hw r hpr
  have hM := transport_markov hB htr
  have hMq := ProperWiggleInvariants.markov_wiggle_invariant _ hC hrq
  have htop := Algebra.pfaffian_bound
    ((applyWord B w) (q.toFun 0) (q.toFun 1))
    ((applyWord B w) (q.toFun 0) (q.toFun 2))
    ((applyWord B w) (q.toFun 0) (q.toFun 3))
    ((applyWord B w) (q.toFun 1) (q.toFun 2))
    ((applyWord B w) (q.toFun 1) (q.toFun 3))
    ((applyWord B w) (q.toFun 2) (q.toFun 3))
    hq.1 hq.2.1 hq.2.2.1 hq.2.2.2.1 hq.2.2.2.2.1 hq.2.2.2.2.2
  change 2*((matrixPfaffian (relabel (applyWord B w) q)).natAbs:Int)≤
    orderMarkov (applyWord B w) q at htop
  have hsq := (ClassSeparation.pfaffian_square_relabel _ hC q).trans
    (pfaffian_square_word B w hB)
  have habs : abs (matrixPfaffian (relabel (applyWord B w) q))=abs (matrixPfaffian B) := by
    exact (abs_eq_iff_mul_self_eq).mpr (by simpa only [pow_two] using hsq)
  rw [Int.natCast_natAbs,habs] at htop
  have hscalar : orderMarkov (applyWord B w) q=orderMarkov B p := hMq.symm.trans hM
  rwa [hscalar] at htop

theorem positive_nonstrict_scalar_bound (a b c d e f : Int)
    (ha : 2≤a) (hb : 1≤b) (hc : 1≤c) (hd : 1≤d) (he : 1≤e)
    (hE : e+a*c<f) (hB : b+a*d<f)
    (hnecessary : 2*abs (PositivePeakScalar.pfaffian a b c d e f)≤
      PositivePeakScalar.scalar a b c d e f) :
    f<PositivePeakScalar.scalar a b c d e f := by
  have habs := le_abs_self (PositivePeakScalar.pfaffian a b c d e f)
  have hn : 0≤PositivePeakScalar.scalar a b c d e f := by
    have h := abs_nonneg (PositivePeakScalar.pfaffian a b c d e f); omega
  have hpf : f<2*PositivePeakScalar.pfaffian a b c d e f := by
    by_contra hh
    have hneg := PositivePeakScalar.low_pfaffian_forces_negative_scalar a b c d e f
      ha hb hc hd he hE hB (by omega)
    omega
  omega

theorem positive_totalProper_scalar_bound (hEnd : EndpointTopological4)
    (a b c d e f : Int)
    (ha : 2≤a) (hb : 1≤b) (hc : 1≤c) (hd : 1≤d) (he : 1≤e)
    (hE : e+a*c<f) (hB : b+a*d<f)
    (hma : MutationAcyclic (PositivePeakOrder.peak a b c d e f))
    (p : CyclicOrder) (hp : TotalProper (PositivePeakOrder.peak a b c d e f) p) :
    f<orderMarkov (PositivePeakOrder.peak a b c d e f) p := by
  have hac := mul_nonneg (show 0≤a by omega) (show 0≤c-1 by omega)
  have hf : 0<f := by nlinarith
  have hpr := totalProper_proper _ p hp
  have hn := MA_totalProper_pfaffian_bound hEnd _ (ofSix_skew _ _ _ _ _ _) hma p hp
  change 2*abs (matrixPfaffian (PositivePeakOrder.peak a b c d e f))≤
    orderMarkov (PositivePeakOrder.peak a b c d e f) p at hn
  rw [PositivePeakOrder.matrix_pfaffian] at hn
  rw [PositivePeakOrder.proper_markov a b c d e f (by omega) (by omega) (by omega)
      (by omega) (by omega) hf p hpr] at hn ⊢
  exact positive_nonstrict_scalar_bound a b c d e f ha hb hc hd he hE hB hn

theorem positive_MA_scalar_bound (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4)
    (a b c d e f : Int)
    (ha : 2≤a) (hb : 1≤b) (hc : 1≤c) (hd : 1≤d) (he : 1≤e)
    (hE : e+a*c<f) (hB : b+a*d<f)
    (hma : MutationAcyclic (PositivePeakOrder.peak a b c d e f)) :
    f<PositivePeakScalar.scalar a b c d e f := by
  obtain ⟨p,hp⟩ := hExist _ (ofSix_skew _ _ _ _ _ _) hma
  have h := positive_totalProper_scalar_bound hEnd a b c d e f ha hb hc hd he hE hB hma p hp
  have hac := mul_nonneg (show 0≤a by omega) (show 0≤c-1 by omega)
  have hf : 0<f := by nlinarith
  rwa [PositivePeakOrder.proper_markov a b c d e f (by omega) (by omega) (by omega)
    (by omega) (by omega) hf p (totalProper_proper _ p hp)] at h

theorem mixed_nonstrict_scalar_bound (a b c d E f : Int)
    (ha : 2≤a) (hb : 1≤b) (hd : 0≤d) (hE : 0≤E) (hc : a*E<c)
    (hleft : a*c-E<f) (hright : a*b+(a^2-1)*d<f)
    (hnecessary : 2*abs (FlatMixedScalar.pfaffian a b c d E f)≤
      FlatMixedScalar.scalar a b c d E f) :
    f<FlatMixedScalar.scalar a b c d E f := by
  have habs := le_abs_self (FlatMixedScalar.pfaffian a b c d E f)
  have hn : 0≤FlatMixedScalar.scalar a b c d E f := by
    have h := abs_nonneg (FlatMixedScalar.pfaffian a b c d E f); omega
  have hpf : f<2*FlatMixedScalar.pfaffian a b c d E f := by
    by_contra hh
    have hneg := FlatMixedScalar.low_pfaffian_forces_negative_scalar a b c d E f
      ha hb hd hE hc hleft hright (by omega)
    omega
  omega

theorem mixed_totalProper_scalar_bound (hEnd : EndpointTopological4)
    (a b c d E f : Int)
    (ha : 2≤a) (hb : 1≤b) (hd : 0≤d) (hE : 0≤E) (hc : a*E<c)
    (hleft : a*c-E<f) (hright : a*b+(a^2-1)*d<f)
    (hma : MutationAcyclic (FlatMixedOrder.peak a b c d E f))
    (p : CyclicOrder) (hp : TotalProper (FlatMixedOrder.peak a b c d E f) p) :
    f<orderMarkov (FlatMixedOrder.peak a b c d E f) p := by
  have ha0 : 0≤a := by omega
  have ha2 : 4≤a^2 := by nlinarith
  have hde := mul_nonneg (show 0≤a^2-1 by omega) hd
  have hab := mul_nonneg ha0 (show 0≤b-1 by omega)
  have hc0 : 0<c := by have h := mul_nonneg ha0 hE; omega
  have hf : 0<f := by nlinarith
  have hn := MA_totalProper_pfaffian_bound hEnd _ (ofSix_skew _ _ _ _ _ _) hma p hp
  change 2*abs (matrixPfaffian (FlatMixedOrder.peak a b c d E f))≤
    orderMarkov (FlatMixedOrder.peak a b c d E f) p at hn
  rw [FlatMixedOrder.matrix_pfaffian] at hn
  rw [FlatMixedOrder.proper_markov a b c d E f (by omega) (by omega) hc0 hd hE hf p
      (totalProper_proper _ p hp)] at hn ⊢
  exact mixed_nonstrict_scalar_bound a b c d E f ha hb hd hE hc hleft hright hn

theorem mixed_MA_scalar_bound (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4)
    (a b c d E f : Int)
    (ha : 2≤a) (hb : 1≤b) (hd : 0≤d) (hE : 0≤E) (hc : a*E<c)
    (hleft : a*c-E<f) (hright : a*b+(a^2-1)*d<f)
    (hma : MutationAcyclic (FlatMixedOrder.peak a b c d E f)) :
    f<FlatMixedScalar.scalar a b c d E f := by
  obtain ⟨p,hp⟩ := hExist _ (ofSix_skew _ _ _ _ _ _) hma
  have h := mixed_totalProper_scalar_bound hEnd a b c d E f ha hb hd hE hc hleft hright hma p hp
  have ha0 : 0≤a := by omega
  have ha2 : 4≤a^2 := by nlinarith
  have hde := mul_nonneg (show 0≤a^2-1 by omega) hd
  have hab := mul_nonneg ha0 (show 0≤b-1 by omega)
  have hc0 : 0<c := by have h := mul_nonneg ha0 hE; omega
  have hf : 0<f := by nlinarith
  rwa [FlatMixedOrder.proper_markov a b c d E f (by omega) (by omega) hc0 hd hE hf p
    (totalProper_proper _ p hp)] at h

#print axioms MA_totalProper_pfaffian_bound
#print axioms positive_totalProper_scalar_bound
#print axioms positive_MA_scalar_bound
#print axioms mixed_totalProper_scalar_bound
#print axioms mixed_MA_scalar_bound
end QuiverProofs.Rank4StructureRound2.SuperScalarPeak
