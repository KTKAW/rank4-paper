import QuiverProofs.CensusCore
import QuiverProofs.Algebra

/-! Rank-four cyclic-order semantics. No MA-to-total-properness result is assumed. -/
namespace QuiverProofs.ProperOrder

abbrev CyclicOrder := Relabeling 4

/-- Strict clockwise order of three positions in a linear representative. -/
def Clockwise (i j k : Fin 4) : Prop :=
  (i < j ∧ j < k) ∨ (j < k ∧ k < i) ∨ (k < i ∧ i < j)
instance (i j k : Fin 4) : Decidable (Clockwise i j k) := inferInstanceAs (Decidable (_ ∨ _ ∨ _))

def Between (p : CyclicOrder) (u v w : Fin 4) : Prop :=
  Clockwise (p.invFun u) (p.invFun v) (p.invFun w)
instance (p : CyclicOrder) (u v w : Fin 4) : Decidable (Between p u v w) :=
  inferInstanceAs (Decidable (Clockwise _ _ _))

def SameCyclicOrder (p q : CyclicOrder) : Prop :=
  ∀ u v w, Between p u v w ↔ Between q u v w
instance (p q : CyclicOrder) : Decidable (SameCyclicOrder p q) :=
  inferInstanceAs (Decidable (∀ u v w, Between p u v w ↔ Between q u v w))

/-- Canonical representatives (0,1,2,3), (0,1,3,2), ..., (0,3,2,1). -/
def order (k : Fin 6) : CyclicOrder := Census.permutation ⟨k.val, by omega⟩

theorem six_orders_distinct : ∀ i j : Fin 6,
    SameCyclicOrder (order i) (order j) → i = j := by decide

theorem permutation_six_orders : ∀ p : Fin 24,
    ∃ k : Fin 6, SameCyclicOrder (Census.permutation p) (order k) := by decide

private theorem invFun_eq_of_toFun_eq (p q : CyclicOrder)
    (h : p.toFun = q.toFun) : p.invFun = q.invFun := by
  funext i
  apply p.injective
  rw [p.right_inv, h, q.right_inv]

/-- Exhaustiveness over all vertex permutations, not just a supplied list. -/
theorem cyclic_order_exhaustive (p : CyclicOrder) :
    ∃ k : Fin 6, SameCyclicOrder p (order k) := by
  obtain ⟨j, hj⟩ := Census.permutation_exhaustive p
  obtain ⟨k, hk⟩ := permutation_six_orders j
  refine ⟨k, ?_⟩
  have hi := invFun_eq_of_toFun_eq p (Census.permutation j) hj
  simpa only [SameCyclicOrder, Between, hi] using hk

/-- Properness at one vertex in one representative. -/
def ProperVertex (B : Matrix 4) (p : CyclicOrder) (v : Fin 4) : Prop :=
  ∀ u w, 0 < B u v → 0 < B v w → Between p u v w
instance (B : Matrix 4) (p : CyclicOrder) (v : Fin 4) : Decidable (ProperVertex B p v) :=
  inferInstanceAs (Decidable (∀ u w, 0 < B u v → 0 < B v w → Between p u v w))

theorem properVertex_cyclic (B : Matrix 4) (p q : CyclicOrder)
    (hpq : SameCyclicOrder p q) (v : Fin 4) :
    ProperVertex B p v ↔ ProperVertex B q v := by
  constructor
  · intro h u w huv hvw; exact (hpq u v w).mp (h u w huv hvw)
  · intro h u w huv hvw; exact (hpq u v w).mpr (h u w huv hvw)

def orderMarkov (B : Matrix 4) (p : CyclicOrder) : Int :=
  Algebra.markov (B (p.toFun 0) (p.toFun 1)) (B (p.toFun 0) (p.toFun 2))
    (B (p.toFun 0) (p.toFun 3)) (B (p.toFun 1) (p.toFun 2))
    (B (p.toFun 1) (p.toFun 3)) (B (p.toFun 2) (p.toFun 3))

theorem markov_rotate (a b c d e f : Int) :
    Algebra.markov d e (-a) f (-b) (-c) = Algebra.markov a b c d e f := by
  unfold Algebra.markov Algebra.squareSum Algebra.cycleTerms
  grind

theorem markov_wiggle_front (b c d e f : Int) :
    Algebra.markov 0 d e b c f = Algebra.markov 0 b c d e f := by
  unfold Algebra.markov Algebra.squareSum Algebra.cycleTerms
  grind

private theorem correction_nonpos_nonpos (x y : Int) (hx : x ≤ 0) (hy : y ≤ 0) :
    correction x y = -(x*y) := by
  simp only [correction, Int.max_def]
  grind

private theorem correction_nonpos_nonneg (x y : Int) (hx : x ≤ 0) (hy : 0 ≤ y) :
    correction x y = 0 := by
  simp only [correction, Int.max_def]
  grind

private theorem correction_nonneg_nonpos (x y : Int) (hx : 0 ≤ x) (hy : y ≤ 0) :
    correction x y = 0 := by
  simp only [correction, Int.max_def]
  grind

/-- Exact proper transport with outgoing vertices in the initial block.
Zero entries may occur on either side of the cut. -/
theorem markov_proper_cut_zero (a b c d e f : Int)
    (ha : a ≤ 0) (hb : b ≤ 0) (hc : c ≤ 0) :
    orderMarkov (mutate (ofSix a b c d e f) 0) (Census.permutation 0) =
      Algebra.markov a b c d e f := by
  change Algebra.markov (-a) (-b) (-c) (d + correction (-a) b) (e + correction (-a) c) (f + correction (-b) c) = Algebra.markov a b c d e f
  simp only [correction, Int.max_def]
  unfold Algebra.markov Algebra.squareSum Algebra.cycleTerms
  grind

theorem markov_proper_cut_one (a b c d e f : Int)
    (ha : 0 ≤ a) (hb : b ≤ 0) (hc : c ≤ 0) :
    orderMarkov (mutate (ofSix a b c d e f) 0) (Census.permutation 6) =
      Algebra.markov a b c d e f := by
  change Algebra.markov (-(-a)) (d + correction (-a) b) (e + correction (-a) c) (-b) (-c) (f + correction (-b) c) = Algebra.markov a b c d e f
  rw [correction_nonpos_nonpos (-a) b (by omega) hb,
    correction_nonpos_nonpos (-a) c (by omega) hc,
    correction_nonneg_nonpos (-b) c (by omega) hc]
  unfold Algebra.markov Algebra.squareSum Algebra.cycleTerms
  grind

theorem markov_proper_cut_two (a b c d e f : Int)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : c ≤ 0) :
    orderMarkov (mutate (ofSix a b c d e f) 0) (Census.permutation 8) =
      Algebra.markov a b c d e f := by
  change Algebra.markov (d + correction (-a) b) (-(-a)) (e + correction (-a) c) (-(-b)) (f + correction (-b) c) (-c) = Algebra.markov a b c d e f
  rw [correction_nonpos_nonneg (-a) b (by omega) hb,
    correction_nonpos_nonpos (-a) c (by omega) hc,
    correction_nonpos_nonpos (-b) c (by omega) hc]
  unfold Algebra.markov Algebra.squareSum Algebra.cycleTerms
  grind

theorem markov_proper_cut_three (a b c d e f : Int)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    orderMarkov (mutate (ofSix a b c d e f) 0) (Census.permutation 9) =
      Algebra.markov a b c d e f := by
  change Algebra.markov (d + correction (-a) b) (e + correction (-a) c) (-(-a)) (f + correction (-b) c) (-(-b)) (-(-c)) = Algebra.markov a b c d e f
  simp only [correction, Int.max_def]
  unfold Algebra.markov Algebra.squareSum Algebra.cycleTerms
  grind

/-- The incident signs exactly characterize properness at the first vertex. -/
theorem proper_zero_iff (a b c d e f : Int) :
    ProperVertex (ofSix a b c d e f) (Census.permutation 0) 0 ↔
      (a < 0 → b ≤ 0 ∧ c ≤ 0) ∧ (b < 0 → c ≤ 0) := by
  constructor
  · intro h
    have hab : ¬(a < 0 ∧ 0 < b) := by
      rintro ⟨ha, hb⟩
      have hh := h 1 2 (by change 0 < -a; omega) hb
      exact (show ¬Between (Census.permutation 0) 1 0 2 by decide) hh
    have hac : ¬(a < 0 ∧ 0 < c) := by
      rintro ⟨ha, hc⟩
      have hh := h 1 3 (by change 0 < -a; omega) hc
      exact (show ¬Between (Census.permutation 0) 1 0 3 by decide) hh
    have hbc : ¬(b < 0 ∧ 0 < c) := by
      rintro ⟨hb, hc⟩
      have hh := h 2 3 (by change 0 < -b; omega) hc
      exact (show ¬Between (Census.permutation 0) 2 0 3 by decide) hh
    omega
  · intro h u w huv hvw
    have hu : u=0 ∨ u=1 ∨ u=2 ∨ u=3 := by omega
    have hw : w=0 ∨ w=1 ∨ w=2 ∨ w=3 := by omega
    rcases hu with rfl | rfl | rfl | rfl <;>
      rcases hw with rfl | rfl | rfl | rfl <;>
      simp only [ofSix] at huv hvw
    all_goals first | exact (by decide) | exfalso; omega

theorem proper_cut_zero_vertex (a b c d e f : Int)
    (ha : a ≤ 0) (hb : b ≤ 0) (hc : c ≤ 0) :
    ProperVertex (mutate (ofSix a b c d e f) 0) (Census.permutation 0) 0 := by
  intro u w huv hvw
  have hu : u=0 ∨ u=1 ∨ u=2 ∨ u=3 := by omega
  have hw : w=0 ∨ w=1 ∨ w=2 ∨ w=3 := by omega
  rcases hu with rfl | rfl | rfl | rfl <;>
    rcases hw with rfl | rfl | rfl | rfl <;>
    simp [mutate, ofSix] at huv hvw
  all_goals first | exact (by decide) | exfalso; omega

theorem proper_cut_one_vertex (a b c d e f : Int)
    (ha : 0 ≤ a) (hb : b ≤ 0) (hc : c ≤ 0) :
    ProperVertex (mutate (ofSix a b c d e f) 0) (Census.permutation 6) 0 := by
  intro u w huv hvw
  have hu : u=0 ∨ u=1 ∨ u=2 ∨ u=3 := by omega
  have hw : w=0 ∨ w=1 ∨ w=2 ∨ w=3 := by omega
  rcases hu with rfl | rfl | rfl | rfl <;>
    rcases hw with rfl | rfl | rfl | rfl <;>
    simp [mutate, ofSix] at huv hvw
  all_goals first | exact (by decide) | exfalso; omega

theorem proper_cut_two_vertex (a b c d e f : Int)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : c ≤ 0) :
    ProperVertex (mutate (ofSix a b c d e f) 0) (Census.permutation 8) 0 := by
  intro u w huv hvw
  have hu : u=0 ∨ u=1 ∨ u=2 ∨ u=3 := by omega
  have hw : w=0 ∨ w=1 ∨ w=2 ∨ w=3 := by omega
  rcases hu with rfl | rfl | rfl | rfl <;>
    rcases hw with rfl | rfl | rfl | rfl <;>
    simp [mutate, ofSix] at huv hvw
  all_goals first | exact (by decide) | exfalso; omega

theorem proper_cut_three_vertex (a b c d e f : Int)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    ProperVertex (mutate (ofSix a b c d e f) 0) (Census.permutation 9) 0 := by
  intro u w huv hvw
  have hu : u=0 ∨ u=1 ∨ u=2 ∨ u=3 := by omega
  have hw : w=0 ∨ w=1 ∨ w=2 ∨ w=3 := by omega
  rcases hu with rfl | rfl | rfl | rfl <;>
    rcases hw with rfl | rfl | rfl | rfl <;>
    simp [mutate, ofSix] at huv hvw
  all_goals first | exact (by decide) | exfalso; omega

/-- Every proper first vertex admits one of the four outgoing/incoming cuts. -/
theorem proper_zero_has_cut (a b c d e f : Int)
    (h : ProperVertex (ofSix a b c d e f) (Census.permutation 0) 0) :
    (a ≤ 0 ∧ b ≤ 0 ∧ c ≤ 0) ∨
    (0 ≤ a ∧ b ≤ 0 ∧ c ≤ 0) ∨
    (0 ≤ a ∧ 0 ≤ b ∧ c ≤ 0) ∨
    (0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c) := by
  have := (proper_zero_iff a b c d e f).mp h
  omega

/-- A proper mutation at the first vertex has an explicitly transported order
with the same Markov coefficient. This does not assert all vertices are proper. -/
theorem proper_zero_markov_transport (a b c d e f : Int)
    (h : ProperVertex (ofSix a b c d e f) (Census.permutation 0) 0) :
    ∃ p : CyclicOrder,
      orderMarkov (mutate (ofSix a b c d e f) 0) p =
        orderMarkov (ofSix a b c d e f) (Census.permutation 0) := by
  rcases proper_zero_has_cut a b c d e f h with h | h | h | h
  · exact ⟨Census.permutation 0, markov_proper_cut_zero a b c d e f h.1 h.2.1 h.2.2⟩
  · exact ⟨Census.permutation 6, markov_proper_cut_one a b c d e f h.1 h.2.1 h.2.2⟩
  · exact ⟨Census.permutation 8, markov_proper_cut_two a b c d e f h.1 h.2.1 h.2.2⟩
  · exact ⟨Census.permutation 9, markov_proper_cut_three a b c d e f h.1 h.2.1 h.2.2⟩

end QuiverProofs.ProperOrder
