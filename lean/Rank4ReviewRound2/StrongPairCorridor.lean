import Rank4ReviewRound2.StrongPairMixedOrder
import Rank4ReviewRound2.StrongPairStable
import Rank4StructureRound2.TwoStateScalar

/-! Constant strong-pair corridors cannot return below H above their
supplied proper scalar. This normalized layer uses actual mutations and
arbitrary length; original-input scalar transport remains a wrapper. -/
namespace Rank4ReviewRound2.StrongPairCorridor
open QuiverProofs Rank4Coordinator Rank4CoordinatorR2
open ProperOrder ProperMutation ProperObstructionSoundness
open QuiverProofs.Rank4StructureRound2
open StrongPairIncident StrongPairStable
set_option maxHeartbeats 4000000

private theorem corr_positive (a d : Int) (ha : 0≤a) (hd : 0≤d) :
    correction a d=a*d := by
  simp only [correction,max_eq_left ha,max_eq_left hd,
    max_eq_right (show -a≤0 by omega),max_eq_right (show -d≤0 by omega)]
  ring
private theorem corr_negative (a d : Int) (ha : a≤0) (hd : d≤0) :
    correction a d= -a*d := by
  simp only [correction,max_eq_right ha,max_eq_right hd,
    max_eq_left (show 0≤ -a by omega),max_eq_left (show 0≤ -d by omega)]
  ring

private theorem sink_impossible (hEnd : EndpointTopological4)
    (a b c d E f : Int) (H : Nat) (ha : 2≤a) (hb : 0≤b) (hc : 0≤c)
    (hd : d≤0) (hE : E≤0) (hf : f=(H:Int)+1)
    (hma : MutationAcyclic (TwoStateScalar.Q a b c d E f))
    (p : CyclicOrder) (hp : TotalProper (TwoStateScalar.Q a b c d E f) p)
    (hM : orderMarkov (TwoStateScalar.Q a b c d E f) p≤(H:Int)) : False := by
  have ht := SuperScalarPeak.MA_totalProper_pfaffian_bound hEnd _
    (ofSix_skew _ _ _ _ _ _) hma p hp
  change 2*abs (a*f-b*E+(-c)*d)≤orderMarkov (TwoStateScalar.Q a b c d E f) p at ht
  have he : a*f-b*E+(-c)*d=a*f-b*E-c*d := by ring
  rw [he] at ht
  have habs := le_abs_self (a*f-b*E-c*d)
  have hbe := mul_nonpos_of_nonneg_of_nonpos hb hE
  have hcd := mul_nonpos_of_nonneg_of_nonpos hc hd
  have haf := mul_nonneg (show 0≤a-2 by omega) (show 0≤f by omega)
  nlinarith

theorem normalized_no_return (hEnd : EndpointTopological4)
    (n : Nat) (hn : 2≤n) (a b c d E f : Int) (H : Nat)
    (ha : 2≤a) (hb : 0<b) (hc : 0<c) (hf : f=(H:Int)+1)
    (hBack : HeightLe (mutate (TwoStateScalar.Q a b c d E f) 0) H)
    (hCeil : ∀ r≤n, HeightLe
      (applyWord (TwoStateScalar.Q a b c d E f) (alternatingWord 0 1 r)) (H+1))
    (hEndState : HeightLe
      (applyWord (TwoStateScalar.Q a b c d E f) (alternatingWord 0 1 n)) H)
    (hma : MutationAcyclic (TwoStateScalar.Q a b c d E f))
    (p : CyclicOrder) (hp : TotalProper (TwoStateScalar.Q a b c d E f) p)
    (hM : orderMarkov (TwoStateScalar.Q a b c d E f) p≤(H:Int)) : False := by
  let P := TwoStateScalar.Q a b c d E f
  have hs : SkewSymmetric P := ofSix_skew _ _ _ _ _ _
  have hPair : 2≤abs (P 0 1) := by
    change 2≤abs a
    rwa [abs_of_nonneg (show 0≤a by omega)]
  have hInit := FlatHalfShape.five_edges_below P hs H (hCeil 0 (by omega))
    hBack (hCeil 1 (by omega)) hPair
  have hStart : IncidentLe P 0 1 H := by
    intro l
    have hl : l=0 ∨ l=1 ∨ l=2 ∨ l=3 := by omega
    rcases hl with rfl|rfl|rfl|rfl
    · have h01 := hInit.1
      change -(H:Int)≤a ∧ a≤(H:Int) at h01
      simp only [P,TwoStateScalar.Q,ofSix]
      omega
    · have h01 := hInit.1
      change -(H:Int)≤a ∧ a≤(H:Int) at h01
      simp only [P,TwoStateScalar.Q,ofSix]
      omega
    · exact ⟨hInit.2.1,hInit.2.2.2.1⟩
    · exact ⟨hInit.2.2.1,hInit.2.2.2.2⟩
  have hAll := all_incident_below n P hs 0 1 (by decide) H hPair hStart hCeil hEndState
  have hFirst := (hAll 1 (by omega) 2).1
  change -(H:Int)≤b+correction a d ∧ b+correction a d≤(H:Int) at hFirst
  have hNext := (hAll 2 hn 2).2
  have hcBound := (hStart 3).1
  change -(H:Int)≤ -c ∧ -c≤(H:Int) at hcBound
  have hA := hInit.1
  change -(H:Int)≤a ∧ a≤(H:Int) at hA
  have hLeft := hBack 1 3
  change -(H:Int)≤E+correction (-a) (-c) ∧
    E+correction (-a) (-c)≤(H:Int) at hLeft
  rw [corr_negative (-a) (-c) (by omega) (by omega)] at hLeft
  by_cases hd : 0≤d
  · rw [corr_positive a d (by omega) hd] at hFirst
    have hRight : a*b+(a^2-1)*d<f := by
      change -(H:Int)≤ -d+correction (-(-a)) (b+correction a d) ∧
        -d+correction (-(-a)) (b+correction a d)≤(H:Int) at hNext
      rw [Int.neg_neg,corr_positive a d (by omega) hd,
        corr_positive a (b+a*d) (by omega)
          (by have h:=mul_nonneg (show 0≤a by omega) hd; nlinarith)] at hNext
      nlinarith
    by_cases hE : 0≤E
    · by_cases hTurn : (a-1)*E<c
      · have hBound := StrongPairMixedOrder.mixed_totalProper_scalar_bound hEnd
          a b c d E f ha (by omega) hc hd hE (by omega) hTurn
          (by omega) (by omega) (by nlinarith) hRight hma p hp
        change f<orderMarkov (TwoStateScalar.Q a b c d E f) p at hBound
        omega
      · have hInitial : ∀ l : Fin 4,0≠l → 1≠l →
          0≤P 1 l ∧ 0≤P 0 l+(P 0 1-1)*P 1 l := by
          intro l h0 h1
          have hl : l=2 ∨ l=3 := by omega
          rcases hl with rfl|rfl <;> simp only [P,TwoStateScalar.Q,ofSix]
          · have h:=mul_nonneg (show 0≤a-1 by omega) hd
            exact ⟨hd,by nlinarith⟩
          · exact ⟨hE,by omega⟩
        have he := initial_word_opposite_fixed n P hs 0 1 (by decide) ha hInitial
          2 3 (by decide) (by decide) (by decide) (by decide)
        have hend := hEndState 2 3
        rw [he] at hend
        change -(H:Int)≤f ∧ f≤(H:Int) at hend
        omega
    · by_cases hd0 : d=0
      · exact sink_impossible hEnd a b c d E f H ha (by omega) (by omega)
          (by omega) (by omega) hf hma p hp hM
      · have hBound := SuperScalarPeak.positive_totalProper_scalar_bound hEnd
          a b c d (-E) f ha (by omega) (by omega) (by omega) (by omega)
          (by nlinarith) (by omega)
          (by simpa only [PositivePeakOrder.peak,TwoStateScalar.Q,Int.neg_neg] using hma) p
          (by simpa only [PositivePeakOrder.peak,TwoStateScalar.Q,Int.neg_neg] using hp)
        have hBound' : f<orderMarkov (TwoStateScalar.Q a b c d E f) p := by
          simpa only [PositivePeakOrder.peak,TwoStateScalar.Q,Int.neg_neg] using hBound
        omega
  · by_cases hE : E≤0
    · exact sink_impossible hEnd a b c d E f H ha (by omega) (by omega)
        (by omega) hE hf hma p hp hM
    · have ht := hCeil 1 (by omega) 2 3
      change -((H+1:Nat):Int)≤f+correction (-d) E ∧
        f+correction (-d) E≤((H+1:Nat):Int) at ht
      rw [corr_positive (-d) E (by omega) (by omega)] at ht
      have hprod := mul_pos (show 0< -d by omega) (show 0<E by omega)
      simp only [Nat.cast_add,Nat.cast_one] at ht
      omega

#print axioms normalized_no_return
end Rank4ReviewRound2.StrongPairCorridor
