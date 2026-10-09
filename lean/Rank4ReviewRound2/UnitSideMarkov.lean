import Rank4Round2.UnitMarkov

/-! Uniform arithmetic for the b=1 or e=1 sides of a unit peak.
The scalar lower bound used by the guard consumer is explicit; this file
does not assert a semantic MA-to-scalar implication.
-/
namespace Rank4ReviewRound2.UnitSideMarkov
open QuiverProofs Rank4Coordinator Rank4Round2

theorem unit_side_overflow_markov (c d e f : Int) (H : Nat)
    (hc : 2≤c) (hd : 2≤d) (he : 1≤e)
    (hx : d+1≤(H:Int)) (hy : c+e≤(H:Int))
    (hf : (H:Int)<f) (hover : f+(H:Int)<unitCost 1 c d e) :
    unitMarkov 1 c d e f≤-1 := by
  let y := c+e
  let T := c+d*y
  have hT : unitCost 1 c d e = T := by dsimp [T,y,unitCost]; ring
  have hid : unitMarkov 1 c d e f = 2+d*d+d+y*y-c*e-f*(T-f) := by
    dsimp [y,T,unitMarkov,unitCost]
    ring
  have hy3 : 3≤y := by dsimp [y]; omega
  have hce : 2≤c*e := by
    have h := mul_le_mul_of_nonneg_left he (show 0≤c by omega)
    nlinarith
  rw [hT] at hover
  rcases le_total (d+1) y with hxy|hyx
  · have hprod := mul_nonneg (show 0≤f-y-1 by dsimp [y]; omega)
      (show 0≤T-f-y-1 by dsimp [y] at *; omega)
    have hband : (y+1)*(T-y-1)≤f*(T-f) := by nlinarith [hprod]
    have hysq : d*d+3*d+2≤y*y+y := by
      have h := mul_nonneg (show 0≤y-d-1 by omega) (show 0≤y+d+2 by omega)
      nlinarith [h]
    have hC : 10≤c*c+c+2*c*e := by nlinarith [hce]
    have hD := mul_nonneg (show 0≤d-2 by omega)
      (show 0≤y*y+y-(d*d+3*d+2) by omega)
    have hrem := mul_nonneg (show 0≤d-2 by omega)
      (show 0≤d*d+2*d-1 by nlinarith)
    have hbound : 3+d*d+d+y*y-c*e-(y+1)*(T-y-1)≤0 := by
      dsimp [T,y] at *
      nlinarith [hC,hD,hrem]
    nlinarith [hid,hband,hbound]
  · have hprod := mul_nonneg (show 0≤f-d-2 by omega)
      (show 0≤T-f-d-2 by omega)
    have hband : (d+2)*(T-d-2)≤f*(T-f) := by nlinarith [hprod]
    have hysq := mul_nonneg (show 0≤y by omega) (show 0≤d+1-y by omega)
    have hK := mul_nonneg (show 0≤d*d+d-1 by nlinarith) (show 0≤y-3 by omega)
    have hcprod := mul_nonneg (show 0≤d+2 by omega) (show 0≤c-2 by omega)
    have hbound : 3+d*d+d+y*y-c*e-(d+2)*(T-d-2)≤0 := by
      dsimp [T] at *
      nlinarith [hysq,hK,hcprod,hce]
    nlinarith [hid,hband,hbound]

theorem unit_side_symmetry (b c d e f : Int) :
    unitMarkov b c d e f = unitMarkov e d c b f := by
  unfold unitMarkov unitCost
  ring

theorem unit_other_side_overflow_markov (b c d f : Int) (H : Nat)
    (hb : 1≤b) (hc : 2≤c) (hd : 2≤d)
    (hx : b+d≤(H:Int)) (hy : c+1≤(H:Int))
    (hf : (H:Int)<f) (hover : f+(H:Int)<unitCost b c d 1) :
    unitMarkov b c d 1 f≤-1 := by
  rw [unit_side_symmetry]
  apply unit_side_overflow_markov d c b f H hd hc hb (by omega) (by omega) hf
  unfold unitCost at hover ⊢
  nlinarith

theorem unit_side_guard_of_markov (c d e f : Int) (H : Nat)
    (hc : 2≤c) (hd : 2≤d) (he : 1≤e)
    (h0 : HeightLe (mutate (unitPeak 1 c d e f) 0) H)
    (h1 : HeightLe (mutate (unitPeak 1 c d e f) 1) H)
    (hf : (H:Int)<f) (hm : 0≤unitMarkov 1 c d e f) :
    PrefixHeightLe (mutate (unitPeak 1 c d e f) 0) [1,0,1] H := by
  have hy := h0 1 3
  have hx := h1 0 2
  unfold unitPeak at hy hx
  rw [positivePeak_zero 1 1 c d e f (by decide) (by decide) (by omega)] at hy
  rw [positivePeak_one 1 1 c d e f (by decide) (by omega) (by omega)] at hx
  simp only [ofSix] at hy hx
  apply (unitPeak_detour_iff 1 c d e f H (by decide) (by omega) (by omega)
    (by omega) h0 h1).mpr
  by_contra hguard
  have hover : f+(H:Int)<unitCost 1 c d e := by omega
  have h := unit_side_overflow_markov c d e f H hc hd he (by omega) (by omega) hf hover
  omega

/-- Together with the all-four-at-least-two branch, the side lemmas
cover every positive b,e when the two middle parameters are at least two. -/
theorem unit_mid_large_overflow_markov (b c d e f : Int) (H : Nat)
    (hb : 1≤b) (hc : 2≤c) (hd : 2≤d) (he : 1≤e)
    (hx : b+d≤(H:Int)) (hy : c+e≤(H:Int))
    (hf : (H:Int)<f) (hover : f+(H:Int)<unitCost b c d e) :
    unitMarkov b c d e f≤-1 := by
  by_cases hb1 : b=1
  · subst b
    exact unit_side_overflow_markov c d e f H hc hd he (by omega) hy hf hover
  by_cases he1 : e=1
  · subst e
    exact unit_other_side_overflow_markov b c d f H hb hc hd hx (by omega) hf hover
  have h := unit_overflow_markov b c d e f H (by omega) hc hd (by omega) hx hy hf hover
  omega

theorem unit_mid_large_guard_of_markov (b c d e f : Int) (H : Nat)
    (hb : 1≤b) (hc : 2≤c) (hd : 2≤d) (he : 1≤e)
    (h0 : HeightLe (mutate (unitPeak b c d e f) 0) H)
    (h1 : HeightLe (mutate (unitPeak b c d e f) 1) H)
    (hf : (H:Int)<f) (hm : 0≤unitMarkov b c d e f) :
    PrefixHeightLe (mutate (unitPeak b c d e f) 0) [1,0,1] H := by
  have hy := h0 1 3
  have hx := h1 0 2
  unfold unitPeak at hy hx
  rw [positivePeak_zero 1 b c d e f (by decide) (by omega) (by omega)] at hy
  rw [positivePeak_one 1 b c d e f (by decide) (by omega) (by omega)] at hx
  simp only [ofSix] at hy hx
  apply (unitPeak_detour_iff b c d e f H (by omega) (by omega) (by omega)
    (by omega) h0 h1).mpr
  by_contra hguard
  have hover : f+(H:Int)<unitCost b c d e := by omega
  have h := unit_mid_large_overflow_markov b c d e f H hb hc hd he (by omega) (by omega) hf hover
  omega

#print axioms unit_side_overflow_markov
#print axioms unit_other_side_overflow_markov
#print axioms unit_side_guard_of_markov
#print axioms unit_mid_large_overflow_markov
#print axioms unit_mid_large_guard_of_markov
end Rank4ReviewRound2.UnitSideMarkov
