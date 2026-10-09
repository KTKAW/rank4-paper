import Rank4Coordinator.HeightBound

/-! Exact normalized strict-peak arithmetic. This module supplies no global
MA/NMA conclusion. Its named consumers are R2-PEAK-GLOBAL and R2-PLATEAU.
-/
namespace Rank4Round2
open QuiverProofs Rank4Coordinator

private theorem four (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega

theorem heightLe_ofSix_iff (a b c d e f : Int) (H : Nat) :
    HeightLe (ofSix a b c d e f) H ↔
      (-(H:Int)≤a ∧ a≤(H:Int)) ∧ (-(H:Int)≤b ∧ b≤(H:Int)) ∧
      (-(H:Int)≤c ∧ c≤(H:Int)) ∧ (-(H:Int)≤d ∧ d≤(H:Int)) ∧
      (-(H:Int)≤e ∧ e≤(H:Int)) ∧ (-(H:Int)≤f ∧ f≤(H:Int)) := by
  constructor
  · intro h
    exact ⟨h 0 1,h 0 2,h 0 3,h 1 2,h 1 3,h 2 3⟩
  · rintro ⟨ha,hb,hc,hd,he,hf⟩ i j
    rcases four i with rfl|rfl|rfl|rfl <;>
      rcases four j with rfl|rfl|rfl|rfl <;> simp only [ofSix] <;> omega

def positivePeak (a b c d e f : Int) : Matrix 4 := ofSix a b (-c) d (-e) f

theorem positivePeak_zero (a b c d e f : Int)
    (ha : 0<a) (hb : 0<b) (hc : 0<c) :
    mutate (positivePeak a b c d e f) 0 =
      ofSix (-a) (-b) c d (-(e+a*c)) (f-b*c) := by
  funext i j
  rcases four i with rfl|rfl|rfl|rfl <;>
    rcases four j with rfl|rfl|rfl|rfl <;>
    simp [positivePeak,mutate,ofSix,correction] <;> grind

theorem positivePeak_one (a b c d e f : Int)
    (ha : 0<a) (hd : 0<d) (he : 0<e) :
    mutate (positivePeak a b c d e f) 1 =
      ofSix (-a) (b+a*d) (-c) (-d) e (f-d*e) := by
  funext i j
  rcases four i with rfl|rfl|rfl|rfl <;>
    rcases four j with rfl|rfl|rfl|rfl <;>
    simp [positivePeak,mutate,ofSix,correction] <;> grind

/-- A reduced equivalent cone: the omitted original coordinates are bounded
by the displayed positive sums. In particular there is no c+a*e bound. -/
theorem positivePeak_children_iff (a b c d e f : Int) (H : Nat)
    (ha : 2≤a) (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e) :
    (HeightLe (mutate (positivePeak a b c d e f) 0) H ∧
      HeightLe (mutate (positivePeak a b c d e f) 1) H) ↔
    a≤(H:Int) ∧ e+a*c≤(H:Int) ∧ b+a*d≤(H:Int) ∧
      (-(H:Int)≤f-b*c ∧ f-b*c≤(H:Int)) ∧
      (-(H:Int)≤f-d*e ∧ f-d*e≤(H:Int)) := by
  rw [positivePeak_zero a b c d e f (by omega) hb hc,
    positivePeak_one a b c d e f (by omega) hd he,
    heightLe_ofSix_iff, heightLe_ofSix_iff]
  have hac : c≤a*c := by
    have h := Int.mul_le_mul_of_nonneg_right (show 1≤a by omega) (show 0≤c by omega)
    simpa using h
  have had : d≤a*d := by
    have h := Int.mul_le_mul_of_nonneg_right (show 1≤a by omega) (show 0≤d by omega)
    simpa using h
  omega

/-- The exact normalized hypotheses for the current strict positive peak
investigation. The final f>H premise is separate from both child checks. -/
def PositivePeakCone (a b c d e f : Int) (H : Nat) : Prop :=
  2≤a ∧ 0<b ∧ 0<c ∧ 0<d ∧ 0<e ∧ (H:Int)<f ∧
    a≤(H:Int) ∧ e+a*c≤(H:Int) ∧ b+a*d≤(H:Int) ∧
      (-(H:Int)≤f-b*c ∧ f-b*c≤(H:Int)) ∧
      (-(H:Int)≤f-d*e ∧ f-d*e≤(H:Int))

theorem positivePeakCone_iff (a b c d e f : Int) (H : Nat) :
    PositivePeakCone a b c d e f H ↔
      2≤a ∧ 0<b ∧ 0<c ∧ 0<d ∧ 0<e ∧ (H:Int)<f ∧
        HeightLe (mutate (positivePeak a b c d e f) 0) H ∧
        HeightLe (mutate (positivePeak a b c d e f) 1) H := by
  unfold PositivePeakCone
  constructor
  · rintro ⟨ha,hb,hc,hd,he,hf,ht⟩
    exact ⟨ha,hb,hc,hd,he,hf,(positivePeak_children_iff a b c d e f H ha hb hc hd he).mpr ht⟩
  · rintro ⟨ha,hb,hc,hd,he,hf,ht⟩
    exact ⟨ha,hb,hc,hd,he,hf,(positivePeak_children_iff a b c d e f H ha hb hc hd he).mp ht⟩

#print axioms positivePeak_zero
#print axioms positivePeak_one
#print axioms positivePeak_children_iff
#print axioms positivePeakCone_iff
end Rank4Round2
