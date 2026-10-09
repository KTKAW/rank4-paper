import Rank4StructureRound2.SuperScalarPeak
import Rank4CoordinatorR2.FlatHalfShape

/-! A normalized high-pair two-state flat block lies strictly below its
supplied proper scalar. Zero incident walls are included; no hereditary
triangle premise is used. The endpoint bridge stays explicit. -/
namespace QuiverProofs.Rank4StructureRound2.TwoStateScalar
open Census ProperOrder ProperWiggle ProperMutation ProperObstructionSoundness
open Rank4Coordinator Rank4CoordinatorR2.FlatHalfShape SuperScalarPeak
set_option maxHeartbeats 4000000

def Q (a b c d E f : Int) : Matrix 4 := ofSix a b (-c) d E f

private theorem corr_positive (x y : Int) (hx : 0≤x) (hy : 0≤y) : correction x y=x*y := by
  simp only [correction,max_eq_left hx,max_eq_left hy,
    max_eq_right (show -x≤0 by omega),max_eq_right (show -y≤0 by omega)]
  ring
private theorem corr_negative (x y : Int) (hx : x≤0) (hy : y≤0) : correction x y= -x*y := by
  simp only [correction,max_eq_right hx,max_eq_right hy,
    max_eq_left (show 0≤ -x by omega),max_eq_left (show 0≤ -y by omega)]
  ring
private theorem corr_nonpos_nonneg (x y : Int) (hx : x≤0) (hy : 0≤y) : correction x y=0 := by
  simp only [correction,max_eq_right hx,max_eq_left hy,
    max_eq_right (show -y≤0 by omega)]
  ring

private theorem mutate_one_mixed (a b c d E f : Int)
    (ha : 0≤a) (hd : 0≤d) (hE : 0≤E) :
    mutate (Q a b c d E f) 1=ofSix (-a) (b+a*d) (-c+a*E) (-d) (-E) f := by
  have hrec := (ofSix_reconstruct (mutate (Q a b c d E f) 1)
    (mutation_preserves_skew _ _ (ofSix_skew _ _ _ _ _ _))).symm
  change mutate (Q a b c d E f) 1=ofSix (-a) (b+correction a d)
    (-c+correction a E) (-d) (-E) (f+correction (-d) E) at hrec
  rwa [corr_positive a d ha hd,corr_positive a E ha hE,
    corr_nonpos_nonneg (-d) E (by omega) hE,Int.add_zero] at hrec

private theorem lower_first_column (a b c d E f : Int) (H : Nat)
    (ha : 0≤a) (hc : 0≤c) (h0 : HeightLe (mutate (Q a b c d E f) 0) H) :
    a*c-E≤(H:Int) := by
  have he := h0 1 3
  change -(H:Int)≤E+correction (-a) (-c) ∧ E+correction (-a) (-c)≤(H:Int) at he
  rw [corr_negative (-a) (-c) (by omega) (by omega)] at he
  nlinarith

private theorem sink_scalar_bound (hEnd : EndpointTopological4)
    (a b c d E f : Int) (ha : 2≤a) (hb : 0≤b) (hc : 0≤c)
    (hd : d≤0) (hE : E≤0) (hf : 0<f)
    (hma : MutationAcyclic (Q a b c d E f))
    (p : CyclicOrder) (hp : TotalProper (Q a b c d E f) p) :
    f<orderMarkov (Q a b c d E f) p := by
  have hbe := mul_nonpos_of_nonneg_of_nonpos hb hE
  have hcd := mul_nonpos_of_nonneg_of_nonpos hc hd
  have haf := mul_nonneg (show 0≤a-2 by omega) (show 0≤f by omega)
  have hpf : 2*f≤matrixPfaffian (Q a b c d E f) := by
    unfold matrixPfaffian Q
    simp only [ofSix]
    nlinarith
  have hm := MA_totalProper_pfaffian_bound hEnd _ (ofSix_skew _ _ _ _ _ _) hma p hp
  change 2*abs (matrixPfaffian (Q a b c d E f))≤orderMarkov (Q a b c d E f) p at hm
  have habs := le_abs_self (matrixPfaffian (Q a b c d E f))
  nlinarith

theorem two_state_scalar_exceeds_height (hEnd : EndpointTopological4)
    (a b c d E f : Int) (H : Nat) (ha : 2≤a) (hb : 0<b) (hc : 0<c)
    (hf : f=(H:Int)+1)
    (hP : HeightLe (Q a b c d E f) (H+1))
    (h0 : HeightLe (mutate (Q a b c d E f) 0) H)
    (h1 : HeightLe (mutate (Q a b c d E f) 1) (H+1))
    (h10 : HeightLe (mutate (mutate (Q a b c d E f) 1) 0) H)
    (hma : MutationAcyclic (Q a b c d E f))
    (p : CyclicOrder) (hp : TotalProper (Q a b c d E f) p) :
    f<orderMarkov (Q a b c d E f) p := by
  have hf0 : 0<f := by omega
  have hPair1 : 2≤abs (mutate (Q a b c d E f) 1 0 1) := by
    change 2≤abs (-a)
    simpa only [abs_neg,abs_of_nonneg (show 0≤a by omega)] using ha
  have hreturn : HeightLe (mutate (mutate (Q a b c d E f) 1) 1) (H+1) := by
    simpa only [mutation_involutive] using hP
  have hcols := five_edges_below (mutate (Q a b c d E f) 1)
    (mutation_preserves_skew _ _ (ofSix_skew _ _ _ _ _ _)) H h1 h10 hreturn hPair1
  have hfirst := lower_first_column a b c d E f H (by omega) (by omega) h0
  by_cases hd : 0≤d
  · by_cases hE : 0≤E
    · have hword := mutate_one_mixed a b c d E f (by omega) hd hE
      have hlast := h10 2 3
      rw [hword] at hlast
      change -(H:Int)≤f+correction (-(b+a*d)) (-c+a*E) ∧
        f+correction (-(b+a*d)) (-c+a*E)≤(H:Int) at hlast
      have hs := correction_negative_inputs (-(b+a*d)) (-c+a*E)
        (show correction (-(b+a*d)) (-c+a*E)<0 by omega)
      have hlast12 := h10 1 2
      rw [hword] at hlast12
      change -(H:Int)≤ -d+correction (-(-a)) (b+a*d) ∧
        -d+correction (-(-a)) (b+a*d)≤(H:Int) at hlast12
      have had := mul_nonneg (show 0≤a by omega) hd
      rw [Int.neg_neg,corr_positive a (b+a*d) (by omega) (by omega)] at hlast12
      have hright : a*b+(a^2-1)*d<f := by nlinarith
      exact mixed_totalProper_scalar_bound hEnd a b c d E f ha (by omega) hd hE
        (by omega) (by omega) hright hma p hp
    · have hE' : E≤0 := by omega
      by_cases hd0 : d=0
      · exact sink_scalar_bound hEnd a b c d E f ha (by omega) (by omega)
          (by omega) hE' hf0 hma p hp
      · have hd' : 0<d := by omega
        have hB := hcols.2.1
        change -(H:Int)≤b+correction a d ∧ b+correction a d≤(H:Int) at hB
        rw [corr_positive a d (by omega) hd] at hB
        have hscalar := positive_totalProper_scalar_bound hEnd a b c d (-E) f ha
          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by simpa [PositivePeakOrder.peak,Q] using hma) p
          (by simpa [PositivePeakOrder.peak,Q] using hp)
        simpa [PositivePeakOrder.peak,Q] using hscalar
  · have hd' : d≤0 := by omega
    by_cases hE : E≤0
    · exact sink_scalar_bound hEnd a b c d E f ha (by omega) (by omega)
        hd' hE hf0 hma p hp
    · have hE' : 0<E := by omega
      have hprod := mul_pos (show 0< -d by omega) hE'
      have hh := h1 2 3
      change -((H+1:Nat):Int)≤f+correction (-d) E ∧
        f+correction (-d) E≤((H+1:Nat):Int) at hh
      rw [corr_positive (-d) E (by omega) (by omega)] at hh
      simp only [Nat.cast_add,Nat.cast_one] at hh
      omega

#print axioms two_state_scalar_exceeds_height
end QuiverProofs.Rank4StructureRound2.TwoStateScalar
