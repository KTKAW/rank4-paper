import Rank4Round6.Coordinator.FiniteBoxReach

/-!
The round-six finite-box search repeats expansion for the full state-count
bound. This implementation stops recursion when one expansion adds no state.
It still uses the same input-dependent finite mutation box and has exactly
the same answer as `boxInvariant`.
-/

namespace Rank4Round8.Reduction

open Rank4Formula QuiverProofs Rank4Round6.Coordinator

/-- The same expansion iteration as `visited`, with an arbitrary initial set. -/
def expandIter (H : Nat) (s : Finset (Matrix 4)) : Nat → Finset (Matrix 4)
  | 0 => s
  | n + 1 => expand H (expandIter H s n)

theorem expandIter_fixed (H : Nat) (s : Finset (Matrix 4))
    (h : expand H s = s) (n : Nat) : expandIter H s n = s := by
  induction n with
  | zero => rfl
  | succ n ih => simp [expandIter, ih, h]

theorem expandIter_front (H : Nat) (s : Finset (Matrix 4))
    (n : Nat) :
    expandIter H s (n + 1) = expandIter H (expand H s) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change expand H (expandIter H s (n + 1)) =
        expand H (expandIter H (expand H s) n)
      exact congrArg (expand H) ih

/-- Early-stopping iteration: a fixed point halts all remaining rounds. -/
def reachUntil (H : Nat) (s : Finset (Matrix 4)) : Nat → Finset (Matrix 4)
  | 0 => s
  | n + 1 =>
      let next := expand H s
      if next = s then s else reachUntil H next n

theorem reachUntil_eq_expandIter (H : Nat) (s : Finset (Matrix 4))
    (n : Nat) : reachUntil H s n = expandIter H s n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      rw [expandIter_front]
      by_cases h : expand H s = s
      · simp [reachUntil, h, expandIter_fixed H s h]
      · simp [reachUntil, h, ih]

theorem reachUntil_fixed (H : Nat) (s : Finset (Matrix 4))
    (h : expand H s = s) (n : Nat) : reachUntil H s (n + 1) = s := by
  simp [reachUntil, h]

theorem expandIter_singleton_eq_visited (B : Matrix 4) (H n : Nat) :
    expandIter H ({B} : Finset (Matrix 4)) n = visited B H n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [expandIter, visited, ih]

theorem reachUntil_card_le_stateCount (q : SixTuple) (n : Nat) :
    (reachUntil (budget q) ({ofTuple q} : Finset (Matrix 4)) n).card ≤
      stateCount q := by
  rw [reachUntil_eq_expandIter, expandIter_singleton_eq_visited]
  change (visited (ofTuple q) (budget q) n).card ≤
    (2 * budget q + 1)^6
  exact visited_card_le_box (ofTuple q) (budget q)
    (ofSix_skew (q 0) (q 1) (q 2) (q 3) (q 4) (q 5))
    (by simpa only [budget] using
      Rank4CoordinatorR2.initial_height_budget (Rank4Round3.certifiedInput q)) n

/-- The complete finite-box decision procedure with fixed-point early exit. -/
def earlyBoxInvariant (q : SixTuple) : Bool :=
  decide (((reachUntil (budget q) ({ofTuple q} : Finset (Matrix 4))
    (stateCount q - 1)).filter
    (fun C => decide (ForkPruning.FiniteAcyclic C))).Nonempty)

theorem earlyBoxInvariant_eq_boxInvariant (q : SixTuple) :
    earlyBoxInvariant q = boxInvariant q := by
  simp only [earlyBoxInvariant, boxInvariant,
    reachUntil_eq_expandIter, expandIter_singleton_eq_visited]

theorem earlyBoxInvariant_MA_iff (q : SixTuple) :
    earlyBoxInvariant q = true ↔ MutationAcyclic (ofTuple q) := by
  rw [earlyBoxInvariant_eq_boxInvariant]
  exact boxInvariant_MA_iff q

theorem earlyBoxInvariant_NMA_iff (q : SixTuple) :
    earlyBoxInvariant q = false ↔ ¬ MutationAcyclic (ofTuple q) := by
  rw [earlyBoxInvariant_eq_boxInvariant]
  exact boxInvariant_NMA_iff q

/-- A positive acyclic hit in the current discovered set. -/
def acyclicFound (s : Finset (Matrix 4)) : Bool :=
  decide ((s.filter (fun C => decide (ForkPruning.FiniteAcyclic C))).Nonempty)

theorem acyclicFound_mono (s t : Finset (Matrix 4))
    (hst : s ⊆ t) (hs : acyclicFound s = true) :
    acyclicFound t = true := by
  simp only [acyclicFound, decide_eq_true_eq] at hs ⊢
  obtain ⟨C, hC⟩ := hs
  obtain ⟨hCs, hAc⟩ := Finset.mem_filter.mp hC
  exact ⟨C, Finset.mem_filter.mpr ⟨hst hCs, hAc⟩⟩

theorem expand_contains (H : Nat) (s : Finset (Matrix 4)) :
    s ⊆ expand H s := by
  intro C hC
  exact Finset.mem_union_left _ hC

theorem reachUntil_contains (H : Nat) (s : Finset (Matrix 4))
    (n : Nat) : s ⊆ reachUntil H s n := by
  induction n generalizing s with
  | zero => exact Finset.Subset.rfl
  | succ n ih =>
      by_cases h : expand H s = s
      · simpa [reachUntil, h] using (Finset.Subset.rfl : s ⊆ s)
      · simpa [reachUntil, h] using
          (expand_contains H s).trans (ih (expand H s))

/-- Stop on an acyclic hit or a saturated component. Both exits avoid the
remaining input-dependent box rounds. -/
def reachAnswer (H : Nat) (s : Finset (Matrix 4)) : Nat → Bool
  | 0 => acyclicFound s
  | n + 1 =>
      if acyclicFound s then true
      else
        let next := expand H s
        if next = s then false else reachAnswer H next n

theorem reachAnswer_eq_reachUntil (H : Nat) (s : Finset (Matrix 4))
    (n : Nat) : reachAnswer H s n = acyclicFound (reachUntil H s n) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      by_cases hfound : acyclicFound s = true
      · have hfuture := acyclicFound_mono s (reachUntil H s (n + 1))
          (reachUntil_contains H s (n + 1)) hfound
        simp [reachAnswer, hfound, hfuture]
      · have hfalse : acyclicFound s = false := by
          cases hb : acyclicFound s <;> simp_all
        by_cases hfix : expand H s = s
        · simp [reachAnswer, reachUntil, hfalse, hfix]
        · simpa [reachAnswer, reachUntil, hfalse, hfix] using
            ih (expand H s)

def earlyAnswerBoxInvariant (q : SixTuple) : Bool :=
  reachAnswer (budget q) ({ofTuple q} : Finset (Matrix 4))
    (stateCount q - 1)

theorem earlyAnswerBoxInvariant_eq_boxInvariant (q : SixTuple) :
    earlyAnswerBoxInvariant q = boxInvariant q := by
  rw [earlyAnswerBoxInvariant, reachAnswer_eq_reachUntil]
  exact earlyBoxInvariant_eq_boxInvariant q

theorem earlyAnswerBoxInvariant_MA_iff (q : SixTuple) :
    earlyAnswerBoxInvariant q = true ↔ MutationAcyclic (ofTuple q) := by
  rw [earlyAnswerBoxInvariant_eq_boxInvariant]
  exact boxInvariant_MA_iff q

theorem earlyAnswerBoxInvariant_NMA_iff (q : SixTuple) :
    earlyAnswerBoxInvariant q = false ↔ ¬ MutationAcyclic (ofTuple q) := by
  rw [earlyAnswerBoxInvariant_eq_boxInvariant]
  exact boxInvariant_NMA_iff q

#print axioms reachUntil_eq_expandIter
#print axioms reachUntil_card_le_stateCount
#print axioms earlyBoxInvariant_eq_boxInvariant
#print axioms earlyBoxInvariant_MA_iff
#print axioms earlyBoxInvariant_NMA_iff
#print axioms reachAnswer_eq_reachUntil
#print axioms earlyAnswerBoxInvariant_eq_boxInvariant
#print axioms earlyAnswerBoxInvariant_MA_iff
#print axioms earlyAnswerBoxInvariant_NMA_iff

end Rank4Round8.Reduction
