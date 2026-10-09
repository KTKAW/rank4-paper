import Rank4Round2.WordRerouting

/-! The normalized unit-pivot pentagon detour, with exact every-prefix height
guard and the necessary endpoint relabeling. No semantic MA guard supplier
or automatic plateau reduction is asserted.
-/
namespace Rank4Round2
open QuiverProofs Rank4Coordinator

private theorem four (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
def unitPeak (b c d e f : Int) : Matrix 4 := positivePeak 1 b c d e f
def unitCost (b c d e : Int) : Int := b*c+d*e+c*d

theorem unitPeak_01 (b c d e f : Int)
    (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e) :
    applyWord (unitPeak b c d e f) [0,1] =
      ofSix 1 (-b) (-e) (-d) (c+e) (f-unitCost b c d e) := by
  change mutate (mutate (positivePeak 1 b c d e f) 0) 1 = _
  rw [positivePeak_zero 1 b c d e f (by decide) hb hc]
  funext i j
  rcases four i with rfl|rfl|rfl|rfl <;>
    rcases four j with rfl|rfl|rfl|rfl <;>
    simp [mutate,ofSix,correction,unitCost] <;> grind

theorem unitPeak_010 (b c d e f : Int)
    (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e) :
    applyWord (unitPeak b c d e f) [0,1,0] =
      ofSix (-1) b e (-(b+d)) c (f-unitCost b c d e) := by
  change mutate (applyWord (unitPeak b c d e f) [0,1]) 0 = _
  rw [unitPeak_01 b c d e f hb hc hd he]
  funext i j
  rcases four i with rfl|rfl|rfl|rfl <;>
    rcases four j with rfl|rfl|rfl|rfl <;>
    simp [mutate,ofSix,correction] <;> grind

theorem unitPeak_0101 (b c d e f : Int)
    (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e) :
    applyWord (unitPeak b c d e f) [0,1,0,1] =
      relabel (mutate (unitPeak b c d e f) 1) Forks.swap01 := by
  change mutate (applyWord (unitPeak b c d e f) [0,1,0]) 1 = _
  rw [unitPeak_010 b c d e f hb hc hd he]
  unfold unitPeak
  rw [positivePeak_one 1 b c d e f (by decide) hd he]
  funext i j
  rcases four i with rfl|rfl|rfl|rfl <;>
    rcases four j with rfl|rfl|rfl|rfl <;>
    simp [mutate,ofSix,correction,relabel,Forks.swap01,unitCost] <;> grind

theorem unitPeak_detour_endpoint (b c d e f : Int)
    (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e) :
    applyWord (mutate (unitPeak b c d e f) 0) [1,0,1] =
      relabel (mutate (unitPeak b c d e f) 1) Forks.swap01 :=
  unitPeak_0101 b c d e f hb hc hd he

theorem unitPeak_detour_iff (b c d e f : Int) (H : Nat)
    (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e)
    (h0 : HeightLe (mutate (unitPeak b c d e f) 0) H)
    (h1 : HeightLe (mutate (unitPeak b c d e f) 1) H) :
    PrefixHeightLe (mutate (unitPeak b c d e f) 0) [1,0,1] H ↔
      -(H:Int)≤f-unitCost b c d e := by
  have hec := h0 1 3
  have hbd := h1 0 2
  have hfc := h0 2 3
  unfold unitPeak at hec hbd hfc
  rw [positivePeak_zero 1 b c d e f (by decide) hb hc] at hec hfc
  rw [positivePeak_one 1 b c d e f (by decide) hd he] at hbd
  simp only [ofSix] at hec hbd hfc
  have hde : 0≤d*e := Int.mul_nonneg (by omega) (by omega)
  have hcd : 0≤c*d := Int.mul_nonneg (by omega) (by omega)
  have costUpper : f-unitCost b c d e≤(H:Int) := by unfold unitCost; omega
  simp only [prefixHeight_cons,prefixHeight_nil]
  change (HeightLe (mutate (unitPeak b c d e f) 0) H ∧
    HeightLe (applyWord (unitPeak b c d e f) [0,1]) H ∧
    HeightLe (applyWord (unitPeak b c d e f) [0,1,0]) H ∧
    HeightLe (applyWord (unitPeak b c d e f) [0,1,0,1]) H) ↔ _
  rw [unitPeak_01 b c d e f hb hc hd he,unitPeak_010 b c d e f hb hc hd he,
    unitPeak_0101 b c d e f hb hc hd he,heightLe_relabel_iff]
  rw [heightLe_ofSix_iff,heightLe_ofSix_iff]
  constructor
  · intro h
    exact h.2.1.2.2.2.2.2.1
  · intro h
    refine ⟨h0,?_,?_,h1⟩ <;> omega

-- The height guard is real: both children fit H=4, detour interior has height7.
example : HeightLe (mutate (unitPeak 2 2 2 2 5) 0) 4 := by decide
example : HeightLe (mutate (unitPeak 2 2 2 2 5) 1) 4 := by decide
example : ¬ PrefixHeightLe (mutate (unitPeak 2 2 2 2 5) 0) [1,0,1] 4 := by
  rw [unitPeak_detour_iff 2 2 2 2 5 4 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)]
  decide

#print axioms unitPeak_0101
#print axioms unitPeak_detour_iff
end Rank4Round2
