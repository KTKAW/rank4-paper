import Rank4StructureRound2.MixedHalfScalar
import Rank4StructureRound2.PositiveHalfScalar
import Rank4StructureRound2.TwoStateFrame

/-! Above a supplied proper scalar, the first strong half-entry must be
in the stable mixed chamber d>=0 and c<=E. It needs no next fixed-pivot
lookahead. This is the normalized input to later pivot-switch geometry,
not a complete arbitrary-word plateau decomposition. -/
namespace QuiverProofs.Rank4StructureRound2.HalfEntryStable
open Census ProperOrder ProperMutation ProperObstructionSoundness
open Rank4Coordinator Rank4CoordinatorR2.FlatHalfShape TwoStateScalar SuperScalarPeak
set_option maxHeartbeats 4000000

private theorem corr_positive (x y : Int) (hx : 0≤x) (hy : 0≤y) : correction x y=x*y := by
  simp only [correction,max_eq_left hx,max_eq_left hy,
    max_eq_right (show -x≤0 by omega),max_eq_right (show -y≤0 by omega)]
  ring
private theorem corr_negative (x y : Int) (hx : x≤0) (hy : y≤0) : correction x y= -x*y := by
  simp only [correction,max_eq_right hx,max_eq_right hy,
    max_eq_left (show 0≤ -x by omega),max_eq_left (show 0≤ -y by omega)]
  ring

theorem positive_half_totalProper_scalar_bound (hEnd : EndpointTopological4)
    (a b c d e f : Int) (ha : 2≤a) (hb : 1≤b) (hc : 1≤c) (hd : 1≤d) (he : 1≤e)
    (hE : e+a*c<f) (hX : b+(a-1)*d<f) (hf : 0<f)
    (hma : MutationAcyclic (PositivePeakOrder.peak a b c d e f))
    (p : CyclicOrder) (hp : TotalProper (PositivePeakOrder.peak a b c d e f) p) :
    f<orderMarkov (PositivePeakOrder.peak a b c d e f) p := by
  have hm := PositivePeakOrder.proper_markov a b c d e f (by omega) (by omega)
    (by omega) (by omega) (by omega) hf p (totalProper_proper _ p hp)
  have hn := MA_totalProper_pfaffian_bound hEnd _ (ofSix_skew _ _ _ _ _ _) hma p hp
  change 2*abs (matrixPfaffian (PositivePeakOrder.peak a b c d e f))≤
    orderMarkov (PositivePeakOrder.peak a b c d e f) p at hn
  rw [PositivePeakOrder.matrix_pfaffian,hm] at hn
  rw [hm]
  by_contra hout
  have hle : PositivePeakScalar.scalar a b c d e f≤f := by omega
  have habs := le_abs_self (PositivePeakScalar.pfaffian a b c d e f)
  have hnegative := PositiveHalfScalar.low_pfaffian_forces_negative_scalar a b c d e f
    ha hb hc hd he hE hX (by omega)
  have hn0 := abs_nonneg (PositivePeakScalar.pfaffian a b c d e f)
  omega

private theorem sink_impossible (a b c d E f : Int) (H : Nat)
    (ha : 2≤a) (hb : 0≤b) (hc : 0≤c) (hd : d≤0) (hE : E≤0)
    (hf : f=(H:Int)+1) (hn : 2*abs (a*f-b*E-c*d)≤(H:Int)) : False := by
  have hbe := mul_nonpos_of_nonneg_of_nonpos hb hE
  have hcd := mul_nonpos_of_nonneg_of_nonpos hc hd
  have haf := mul_nonneg (show 0≤a-2 by omega) (show 0≤f by omega)
  have habs := le_abs_self (a*f-b*E-c*d)
  nlinarith

theorem normalized_half_entry_forces_stable_chamber (hEnd : EndpointTopological4)
    (a b c d E f : Int) (H : Nat) (ha : 2≤a) (hb : 0<b) (hc : 0<c)
    (hf : f=(H:Int)+1) (hP : HeightLe (Q a b c d E f) (H+1))
    (h0 : HeightLe (mutate (Q a b c d E f) 0) H)
    (h1 : HeightLe (mutate (Q a b c d E f) 1) (H+1))
    (hma : MutationAcyclic (Q a b c d E f))
    (p : CyclicOrder) (hp : TotalProper (Q a b c d E f) p)
    (hM : orderMarkov (Q a b c d E f) p≤(H:Int)) : 0≤d ∧ c≤E := by
  have hf0 : 0<f := by omega
  have hPair : 2≤abs (Q a b c d E f 0 1) := by
    change 2≤abs a
    rwa [abs_of_nonneg (show 0≤a by omega)]
  have hcols := five_edges_below (Q a b c d E f) (ofSix_skew _ _ _ _ _ _) H hP h0 h1 hPair
  have hbH := hcols.2.1.2
  change b≤(H:Int) at hbH
  have hfirst := h0 1 3
  change -(H:Int)≤E+correction (-a) (-c) ∧ E+correction (-a) (-c)≤(H:Int) at hfirst
  rw [corr_negative (-a) (-c) (by omega) (by omega)] at hfirst
  have hC : a*c-E<f := by nlinarith
  have hnPF := MA_totalProper_pfaffian_bound hEnd _ (ofSix_skew _ _ _ _ _ _) hma p hp
  change 2*abs (a*f-b*E+(-c)*d)≤orderMarkov (Q a b c d E f) p at hnPF
  have heq : a*f-b*E+(-c)*d=a*f-b*E-c*d := by ring
  rw [heq] at hnPF
  have hn : 2*abs (a*f-b*E-c*d)≤(H:Int) := hnPF.trans hM
  have hd : 0≤d := by
    by_contra hd
    by_cases hE : E≤0
    · exact sink_impossible a b c d E f H ha (by omega) (by omega)
        (by omega) hE hf hn
    · have hprod := mul_pos (show 0< -d by omega) (show 0<E by omega)
      have hh := (h1 2 3).2
      change f+correction (-d) E≤((H+1:Nat):Int) at hh
      rw [corr_positive (-d) E (by omega) (by omega)] at hh
      simp only [Nat.cast_add,Nat.cast_one] at hh
      omega
  have hB := (h1 0 2).2
  change b+correction a d≤((H+1:Nat):Int) at hB
  rw [corr_positive a d (by omega) hd] at hB
  simp only [Nat.cast_add,Nat.cast_one] at hB
  have hX : b+(a-1)*d<f := by
    by_cases hd0 : d=0
    · subst d; nlinarith
    · have hd1 : 1≤d := by omega
      nlinarith
  refine ⟨hd,?_⟩
  by_contra hcle
  have hcE : E<c := by omega
  by_cases hE : 0≤E
  · have hm := FlatMixedOrder.proper_markov a b c d E f (by omega) hb hc hd hE hf0 p
      (totalProper_proper _ p hp)
    change orderMarkov (Q a b c d E f) p=FlatMixedScalar.scalar a b c d E f at hm
    have hnec : 2*abs (FlatMixedScalar.pfaffian a b c d E f)≤
        FlatMixedScalar.scalar a b c d E f := by
      unfold FlatMixedScalar.pfaffian
      rwa [hm] at hnPF
    have hl := MixedHalfScalar.scalar_exceeds_height a b c d E f ha (by omega) hd hE
      hcE (by omega) (by omega) hC hnec
    rw [←hm] at hl
    omega
  · by_cases hd0 : d=0
    · exact sink_impossible a b c d E f H ha (by omega) (by omega)
        (by omega) (by omega) hf hn
    · have hh := positive_half_totalProper_scalar_bound hEnd a b c d (-E) f ha
        (by omega) (by omega) (by omega) (by omega) (by omega) hX hf0
        (by simpa only [PositivePeakOrder.peak,Q,Int.neg_neg] using hma) p
        (by simpa only [PositivePeakOrder.peak,Q,Int.neg_neg] using hp)
      have hh' : f<orderMarkov (Q a b c d E f) p := by
        simpa only [PositivePeakOrder.peak,Q,Int.neg_neg] using hh
      omega

#print axioms positive_half_totalProper_scalar_bound
#print axioms normalized_half_entry_forces_stable_chamber
end QuiverProofs.Rank4StructureRound2.HalfEntryStable
