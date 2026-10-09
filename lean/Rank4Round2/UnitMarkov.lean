import Rank4Round2.OverHeightCount
import QuiverProofs.Algebra
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! Uniform arithmetic guards for normalized unit-pivot peaks with all
four incident parameters at least two. The scalar hypothesis is explicit;
this file supplies no semantic MA-to-scalar theorem.
-/
namespace Rank4Round2
open QuiverProofs Rank4Coordinator

def unitMarkov (b c d e f : Int) : Int :=
  1+b*b+c*c+d*d+e*e+b*d+c*e+f*f-f*unitCost b c d e

theorem unitMarkov_eq (b c d e f : Int) :
    unitMarkov b c d e f = Algebra.markov 1 b (-c) d (-e) f := by
  unfold unitMarkov unitCost Algebra.markov Algebra.squareSum Algebra.cycleTerms
  ring

private theorem ordered_unit_band (x y T f u v : Int)
    (hxy : y≤x) (hy : 4≤y) (hu : 4≤u) (hv : 4≤v)
    (hT : 2*x+2*y-4≤T) (hf : x<f) (hz : x<T-f) :
    1+x*x+y*y-u-v+f*f-f*T≤-10 := by
  have hprod := mul_nonneg (show 0≤f-x-1 by omega)
    (show 0≤T-f-x-1 by omega)
  have hTprod := mul_nonneg (show 0≤x+1 by omega)
    (show 0≤T-2*x-2*y+4 by omega)
  have hbound : (x+1)*(x+2*y-5)≤f*(T-f) := by
    nlinarith [hprod,hTprod]
  have hrem := mul_nonneg (show 0≤x-y by omega) (show 0≤y-2 by omega)
  have hbase := mul_nonneg (show 0≤y-4 by omega) (show 0≤y+2 by omega)
  have hdiff : 11≤(x+1)*(x+2*y-5)-x*x-y*y+u+v := by
    nlinarith [hrem,hbase]
  nlinarith [hbound,hdiff]

/-- A failed unit detour forces the local scalar at most -10 in this cone.
The endpoint sum inequalities alone suffice for this arithmetic deduction. -/
theorem unit_overflow_markov (b c d e f : Int) (H : Nat)
    (hb : 2≤b) (hc : 2≤c) (hd : 2≤d) (he : 2≤e)
    (hbd : b+d≤(H:Int)) (hce : c+e≤(H:Int))
    (hf : (H:Int)<f) (hover : f+(H:Int)<unitCost b c d e) :
    unitMarkov b c d e f≤-10 := by
  have hbc := mul_nonneg (show 0≤b-2 by omega) (show 0≤c-2 by omega)
  have hdc := mul_nonneg (show 0≤d-2 by omega) (show 0≤c-2 by omega)
  have hde := mul_nonneg (show 0≤d-2 by omega) (show 0≤e-2 by omega)
  have hT : 2*(b+d)+2*(c+e)-4≤unitCost b c d e := by
    unfold unitCost
    nlinarith [hbc,hdc,hde]
  have hbdprod := mul_nonneg (show 0≤b-2 by omega) (show 0≤d-2 by omega)
  have hceprod := mul_nonneg (show 0≤c-2 by omega) (show 0≤e-2 by omega)
  have hu : 4≤b*d := by nlinarith [hbdprod]
  have hv : 4≤c*e := by nlinarith [hceprod]
  have hid : unitMarkov b c d e f =
      1+(b+d)*(b+d)+(c+e)*(c+e)-b*d-c*e+f*f-f*unitCost b c d e := by
    unfold unitMarkov
    ring
  rw [hid]
  rcases le_total (c+e) (b+d) with hxy|hyx
  · exact ordered_unit_band (b+d) (c+e) (unitCost b c d e) f (b*d) (c*e)
      hxy (by omega) hu hv hT (by omega) (by omega)
  · have hT' : 2*(c+e)+2*(b+d)-4≤unitCost b c d e := by omega
    have h := ordered_unit_band (c+e) (b+d) (unitCost b c d e) f (c*e) (b*d)
      hyx (by omega) hv hu hT' (by omega) (by omega)
    nlinarith [h]

theorem unit_guard_of_markov (b c d e f : Int) (H : Nat)
    (hb : 2≤b) (hc : 2≤c) (hd : 2≤d) (he : 2≤e)
    (h0 : HeightLe (mutate (unitPeak b c d e f) 0) H)
    (h1 : HeightLe (mutate (unitPeak b c d e f) 1) H)
    (hf : (H:Int)<f) (hm : -9≤unitMarkov b c d e f) :
    PrefixHeightLe (mutate (unitPeak b c d e f) 0) [1,0,1] H := by
  have hec := h0 1 3
  have hbd := h1 0 2
  unfold unitPeak at hec hbd
  rw [positivePeak_zero 1 b c d e f (by decide) (by omega) (by omega)] at hec
  rw [positivePeak_one 1 b c d e f (by decide) (by omega) (by omega)] at hbd
  simp only [ofSix] at hec hbd
  apply (unitPeak_detour_iff b c d e f H (by omega) (by omega) (by omega)
    (by omega) h0 h1).mpr
  by_contra hguard
  have hover : f+(H:Int)<unitCost b c d e := by omega
  have h := unit_overflow_markov b c d e f H hb hc hd he (show b+d≤(H:Int) by omega)
    (show c+e≤(H:Int) by omega) hf hover
  omega

/-- The arithmetic result supplies an actual strict-peak count decrease
for every suffix. It does not supply the scalar lower bound from MA. -/
theorem unit_markov_count_decrease (b c d e f : Int) (H : Nat)
    (hb : 2≤b) (hc : 2≤c) (hd : 2≤d) (he : 2≤e)
    (h0 : HeightLe (mutate (unitPeak b c d e f) 0) H)
    (h1 : HeightLe (mutate (unitPeak b c d e f) 1) H)
    (hf : (H:Int)<f) (hm : -9≤unitMarkov b c d e f)
    (tail : List (Fin 4)) :
    overCount (mutate (unitPeak b c d e f) 0)
        ([1,0,1]++tail.map Forks.swap01.invFun) H + 1 =
      overCount (mutate (unitPeak b c d e f) 0) ([0,1]++tail) H := by
  apply strict_peak_overCount _ 0 1 [1,0,1] tail Forks.swap01 H _ h1
    (unitPeak_detour_endpoint b c d e f (by omega) (by omega) (by omega) (by omega))
    (unit_guard_of_markov b c d e f H hb hc hd he h0 h1 hf hm)
  intro hP
  have h := (hP 2 3).2
  simp only [unitPeak,positivePeak,ofSix] at h
  omega

#print axioms unit_overflow_markov
#print axioms unit_guard_of_markov
#print axioms unit_markov_count_decrease
end Rank4Round2
