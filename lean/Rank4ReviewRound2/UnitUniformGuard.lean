import Rank4ReviewRound2.UnitSideMarkov
import Rank4Round2.UnitPfaffian

/-! All positive incident parameters of a normalized strict unit peak.
Arithmetic and actual word progress are unconditional given the displayed
scalar comparison. Supplying that comparison from semantic MA is separate.
-/
namespace Rank4ReviewRound2.UnitUniformGuard
open QuiverProofs Rank4Coordinator Rank4Round2 UnitSideMarkov

theorem unit_overflow_markov_lt_abs_pfaffian (b c d e f : Int) (H : Nat)
    (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e)
    (hx : b+d≤(H:Int)) (hy : c+e≤(H:Int))
    (hf : (H:Int)<f) (hover : f+(H:Int)<unitCost b c d e) :
    unitMarkov b c d e f < 2*|unitPfaffian b c d e f| := by
  by_cases hc1 : c=1
  · subst c
    have h := c_one_overflow_pfaffian b d e f H hb hd he hx (by omega) hf hover
    rw [abs_of_pos h.1]
    omega
  by_cases hd1 : d=1
  · subst d
    have h := d_one_overflow_pfaffian b c e f H hb hc he (by omega) hy hf hover
    rw [abs_of_pos h.1]
    omega
  have h := unit_mid_large_overflow_markov b c d e f H
    (by omega) (by omega) (by omega) (by omega) hx hy hf hover
  have hab := abs_nonneg (unitPfaffian b c d e f)
  omega

theorem unit_uniform_guard (b c d e f : Int) (H : Nat)
    (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e)
    (h0 : HeightLe (mutate (unitPeak b c d e f) 0) H)
    (h1 : HeightLe (mutate (unitPeak b c d e f) 1) H)
    (hf : (H:Int)<f)
    (hm : 2*|unitPfaffian b c d e f|≤unitMarkov b c d e f) :
    PrefixHeightLe (mutate (unitPeak b c d e f) 0) [1,0,1] H := by
  have hy := h0 1 3
  have hx := h1 0 2
  unfold unitPeak at hy hx
  rw [positivePeak_zero 1 b c d e f (by decide) hb hc] at hy
  rw [positivePeak_one 1 b c d e f (by decide) hd he] at hx
  simp only [ofSix] at hy hx
  apply (unitPeak_detour_iff b c d e f H hb hc hd he h0 h1).mpr
  by_contra hguard
  have hover : f+(H:Int)<unitCost b c d e := by omega
  have h := unit_overflow_markov_lt_abs_pfaffian b c d e f H hb hc hd he
    (by omega) (by omega) hf hover
  omega

theorem unit_uniform_count_decrease (b c d e f : Int) (H : Nat)
    (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e)
    (h0 : HeightLe (mutate (unitPeak b c d e f) 0) H)
    (h1 : HeightLe (mutate (unitPeak b c d e f) 1) H)
    (hf : (H:Int)<f)
    (hm : 2*|unitPfaffian b c d e f|≤unitMarkov b c d e f)
    (tail : List (Fin 4)) :
    overCount (mutate (unitPeak b c d e f) 0)
        ([1,0,1]++tail.map Forks.swap01.invFun) H + 1 =
      overCount (mutate (unitPeak b c d e f) 0) ([0,1]++tail) H := by
  apply strict_peak_overCount _ 0 1 [1,0,1] tail Forks.swap01 H _ h1
    (unitPeak_detour_endpoint b c d e f hb hc hd he)
    (unit_uniform_guard b c d e f H hb hc hd he h0 h1 hf hm)
  intro hP
  have h := (hP 2 3).2
  simp only [unitPeak,positivePeak,ofSix] at h
  omega

#print axioms unit_overflow_markov_lt_abs_pfaffian
#print axioms unit_uniform_guard
#print axioms unit_uniform_count_decrease
end Rank4ReviewRound2.UnitUniformGuard
