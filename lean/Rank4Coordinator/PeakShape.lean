import Rank4Coordinator.HeightBound

/-! Exact local shape of a height peak at mutations 0 and 1. These necessary
conditions do not assert peak removal or NMA. The consumer is the open
MA-specific height-normalization investigation. -/
namespace Rank4Coordinator
open QuiverProofs

theorem correction_negative_inputs (x y : Int) (h : correction x y < 0) :
    x < 0 ∧ y < 0 := by
  have nonneg : 0 ≤ max x 0 * max y 0 :=
    Int.mul_nonneg (le_max_right x 0) (le_max_right y 0)
  constructor
  · by_contra hx
    have hx' : 0 ≤ x := by omega
    have hz : max (-x) 0 = 0 := max_eq_right (by omega)
    simp only [correction, hz, Int.zero_mul, Int.sub_zero] at h
    omega
  · by_contra hy
    have hy' : 0 ≤ y := by omega
    have hz : max (-y) 0 = 0 := max_eq_right (by omega)
    simp only [correction, hz, Int.mul_zero, Int.sub_zero] at h
    omega

theorem correction_positive_inputs (x y : Int) (h : 0 < correction x y) :
    0 < x ∧ 0 < y := by
  have hn : correction (-x) (-y) < 0 := by rw [correction_neg]; omega
  have hs := correction_negative_inputs (-x) (-y) hn
  constructor <;> omega

theorem five_edges_bounded (B : Matrix 4) (H : Nat)
    (h0 : HeightLe (mutate B 0) H) (h1 : HeightLe (mutate B 1) H) :
    (-(H : Int) ≤ B 0 1 ∧ B 0 1 ≤ (H : Int)) ∧
    (-(H : Int) ≤ B 0 2 ∧ B 0 2 ≤ (H : Int)) ∧
    (-(H : Int) ≤ B 0 3 ∧ B 0 3 ≤ (H : Int)) ∧
    (-(H : Int) ≤ B 1 2 ∧ B 1 2 ≤ (H : Int)) ∧
    (-(H : Int) ≤ B 1 3 ∧ B 1 3 ≤ (H : Int)) := by
  have ha := h0 0 1
  have hb := h0 0 2
  have hc := h0 0 3
  have hd := h1 1 2
  have he := h1 1 3
  simp only [mutate, true_or, ↓reduceIte] at ha hb hc hd he
  constructor <;> omega

/-- The only edge that can exceed both mutated children's height is the edge
opposite the pair of pivots. Skew includes all diagonal and lower entries. -/
theorem opposite_edge_outside (B : Matrix 4) (skew : SkewSymmetric B) (H : Nat)
    (h0 : HeightLe (mutate B 0) H) (h1 : HeightLe (mutate B 1) H)
    (outside : ¬ HeightLe B H) :
    B 2 3 < -(H : Int) ∨ (H : Int) < B 2 3 := by
  by_contra h
  have hf : -(H : Int) ≤ B 2 3 ∧ B 2 3 ≤ (H : Int) := by omega
  obtain ⟨ha, hb, hc, hd, he⟩ := five_edges_bounded B H h0 h1
  apply outside
  rw [← ofSix_reconstruct B skew]
  intro i j
  have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  have hj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
  rcases hi with rfl|rfl|rfl|rfl <;> rcases hj with rfl|rfl|rfl|rfl <;>
    simp only [ofSix] <;> omega

/-- In positive orientation the two pivots both lie on a path 3 → pivot → 2,
closed by the large opposite arrow 2 → 3. -/
theorem positive_peak_paths (B : Matrix 4) (skew : SkewSymmetric B) (H : Nat)
    (h0 : HeightLe (mutate B 0) H) (h1 : HeightLe (mutate B 1) H)
    (large : (H : Int) < B 2 3) :
    0 < B 0 2 ∧ B 0 3 < 0 ∧ 0 < B 1 2 ∧ B 1 3 < 0 := by
  have hf0 := (h0 2 3).2
  have hf1 := (h1 2 3).2
  simp [mutate] at hf0 hf1
  have c0 : correction (B 2 0) (B 0 3) < 0 := by omega
  have c1 : correction (B 2 1) (B 1 3) < 0 := by omega
  have s0 := correction_negative_inputs _ _ c0
  have s1 := correction_negative_inputs _ _ c1
  have b0 := skew 2 0
  have b1 := skew 2 1
  constructor <;> omega

theorem negative_peak_paths (B : Matrix 4) (skew : SkewSymmetric B) (H : Nat)
    (h0 : HeightLe (mutate B 0) H) (h1 : HeightLe (mutate B 1) H)
    (large : B 2 3 < -(H : Int)) :
    B 0 2 < 0 ∧ 0 < B 0 3 ∧ B 1 2 < 0 ∧ 0 < B 1 3 := by
  have hf0 := (h0 2 3).1
  have hf1 := (h1 2 3).1
  simp [mutate] at hf0 hf1
  have c0 : 0 < correction (B 2 0) (B 0 3) := by omega
  have c1 : 0 < correction (B 2 1) (B 1 3) := by omega
  have s0 := correction_positive_inputs _ _ c0
  have s1 := correction_positive_inputs _ _ c1
  have b0 := skew 2 0
  have b1 := skew 2 1
  constructor <;> omega

#print axioms opposite_edge_outside
#print axioms positive_peak_paths
#print axioms negative_peak_paths
end Rank4Coordinator
