import Rank4Coordinator.PeakShape
import Rank4CoordinatorR2.EndpointBudget
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! At the top integer level H+1, an entry from below H and a bounded
neighbor across a pair of weight at least two force every incident edge
below H. Only the edge opposite the pair can carry the top height. -/
namespace Rank4CoordinatorR2.FlatHalfShape
open QuiverProofs Rank4Coordinator Rank4CoordinatorR2

theorem column_bounded (a b d : Int) (H : Nat) (ha : 2≤abs a)
    (hb : -(H:Int)≤b ∧ b≤(H:Int))
    (hd : -((H+1:Nat):Int)≤d ∧ d≤((H+1:Nat):Int))
    (hl : -(H:Int)≤d+correction (-a) b ∧ d+correction (-a) b≤(H:Int))
    (hr : -((H+1:Nat):Int)≤b+correction a d ∧ b+correction a d≤((H+1:Nat):Int)) :
    -(H:Int)≤d ∧ d≤(H:Int) := by
  by_contra hh
  have hc : d=(H:Int)+1 ∨ d= -(H:Int)-1 := by omega
  rcases hc with hc|hc
  · have hs := correction_negative_inputs (-a) b (show correction (-a) b<0 by omega)
    have ha2 : 2≤a := by rw [abs_of_nonneg (show 0≤a by omega)] at ha; exact ha
    have hd0 : 0≤d := by omega
    have he : correction a d=a*d := by
      simp only [correction,max_eq_left (show 0≤a by omega),max_eq_left hd0,
        max_eq_right (show -a≤0 by omega),max_eq_right (show -d≤0 by omega)]
      ring
    rw [he] at hr
    have hp := mul_nonneg (show 0≤a-2 by omega) hd0
    simp only [Nat.cast_add,Nat.cast_one] at hr
    nlinarith
  · have hs := correction_positive_inputs (-a) b (show 0<correction (-a) b by omega)
    have ha2 : a≤ -2 := by rw [abs_of_nonpos (show a≤0 by omega)] at ha; omega
    have hd0 : d≤0 := by omega
    have he : correction a d= -a*d := by
      simp only [correction,max_eq_right (show a≤0 by omega),max_eq_right hd0,
        max_eq_left (show 0≤ -a by omega),max_eq_left (show 0≤ -d by omega)]
      ring
    rw [he] at hr
    have hp := mul_nonneg (show 0≤ -a-2 by omega) (show 0≤ -d by omega)
    simp only [Nat.cast_add,Nat.cast_one] at hr
    nlinarith

theorem five_edges_below (B : Matrix 4) (hs : SkewSymmetric B) (H : Nat)
    (hB : HeightLe B (H+1)) (h0 : HeightLe (mutate B 0) H)
    (h1 : HeightLe (mutate B 1) (H+1)) (ha : 2≤abs (B 0 1)) :
    (-(H:Int)≤B 0 1 ∧ B 0 1≤(H:Int)) ∧
    (-(H:Int)≤B 0 2 ∧ B 0 2≤(H:Int)) ∧
    (-(H:Int)≤B 0 3 ∧ B 0 3≤(H:Int)) ∧
    (-(H:Int)≤B 1 2 ∧ B 1 2≤(H:Int)) ∧
    (-(H:Int)≤B 1 3 ∧ B 1 3≤(H:Int)) := by
  have h01 := h0 0 1
  have h02 := h0 0 2
  have h03 := h0 0 3
  change -(H:Int)≤ -B 0 1 ∧ -B 0 1≤(H:Int) at h01
  change -(H:Int)≤ -B 0 2 ∧ -B 0 2≤(H:Int) at h02
  change -(H:Int)≤ -B 0 3 ∧ -B 0 3≤(H:Int) at h03
  have hb : -(H:Int)≤B 0 2 ∧ B 0 2≤(H:Int) := by omega
  have hc : -(H:Int)≤B 0 3 ∧ B 0 3≤(H:Int) := by omega
  have h10 : B 1 0= -B 0 1 := hs 1 0
  have hl2 := h0 1 2
  have hl3 := h0 1 3
  have hr2 := h1 0 2
  have hr3 := h1 0 3
  change -(H:Int)≤B 1 2+correction (B 1 0) (B 0 2) ∧
    B 1 2+correction (B 1 0) (B 0 2)≤(H:Int) at hl2
  change -(H:Int)≤B 1 3+correction (B 1 0) (B 0 3) ∧
    B 1 3+correction (B 1 0) (B 0 3)≤(H:Int) at hl3
  change -((H+1:Nat):Int)≤B 0 2+correction (B 0 1) (B 1 2) ∧
    B 0 2+correction (B 0 1) (B 1 2)≤((H+1:Nat):Int) at hr2
  change -((H+1:Nat):Int)≤B 0 3+correction (B 0 1) (B 1 3) ∧
    B 0 3+correction (B 0 1) (B 1 3)≤((H+1:Nat):Int) at hr3
  rw [h10] at hl2 hl3
  have hd := column_bounded (B 0 1) (B 0 2) (B 1 2) H ha hb (hB 1 2) hl2 hr2
  have he := column_bounded (B 0 1) (B 0 3) (B 1 3) H ha hc (hB 1 3) hl3 hr3
  exact ⟨by omega,hb,hc,hd,he⟩

theorem opposite_top (B : Matrix 4) (hs : SkewSymmetric B) (H : Nat)
    (hB : HeightLe B (H+1)) (h0 : HeightLe (mutate B 0) H)
    (h1 : HeightLe (mutate B 1) (H+1)) (ha : 2≤abs (B 0 1))
    (hout : ¬HeightLe B H) : abs (B 2 3)=(H:Int)+1 := by
  obtain ⟨h01,h02,h03,h12,h13⟩ := five_edges_below B hs H hB h0 h1 ha
  have he : ¬ (-(H:Int)≤B 2 3 ∧ B 2 3≤(H:Int)) := by
    intro hh
    apply hout
    rw [←ofSix_reconstruct B hs]
    intro i j
    have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
    have hj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
    rcases hi with rfl|rfl|rfl|rfl <;> rcases hj with rfl|rfl|rfl|rfl <;>
      simp only [ofSix] <;> omega
  have hb := hB 2 3
  rcases le_total 0 (B 2 3) with hp|hn
  · rw [abs_of_nonneg hp]; omega
  · rw [abs_of_nonpos hn]; omega

#print axioms column_bounded
#print axioms five_edges_below
#print axioms opposite_top
end Rank4CoordinatorR2.FlatHalfShape
