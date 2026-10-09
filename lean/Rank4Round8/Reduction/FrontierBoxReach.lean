import Rank4Round8.Reduction.EarlyFixedPointBox

/-!
Finite-box breadth-first expansion using only the new frontier. Each
discovered matrix is expanded at most once. The graph and height bound are
those of the verified round-six `boxInvariant`.
-/

namespace Rank4Round8.Reduction

open Rank4Formula QuiverProofs Rank4Round6.Coordinator

def successorSet (H : Nat) (s : Finset (Matrix 4)) : Finset (Matrix 4) :=
  s.biUnion (successors H)

def frontierStep (H : Nat)
    (state : Finset (Matrix 4) × Finset (Matrix 4)) :
    Finset (Matrix 4) × Finset (Matrix 4) :=
  let fresh := successorSet H state.2 \ state.1
  (state.1 ∪ fresh, fresh)

def frontierIter (H : Nat)
    (state : Finset (Matrix 4) × Finset (Matrix 4)) : Nat →
      Finset (Matrix 4) × Finset (Matrix 4)
  | 0 => state
  | n + 1 => frontierStep H (frontierIter H state n)

def initialFrontier (B : Matrix 4) :
    Finset (Matrix 4) × Finset (Matrix 4) := ({B}, {B})

def frontierStates (B : Matrix 4) (H n : Nat) :
    Finset (Matrix 4) × Finset (Matrix 4) :=
  frontierIter H (initialFrontier B) n

theorem frontierIter_front (H : Nat)
    (state : Finset (Matrix 4) × Finset (Matrix 4)) (n : Nat) :
    frontierIter H state (n + 1) =
      frontierIter H (frontierStep H state) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change frontierStep H (frontierIter H state (n + 1)) =
        frontierStep H (frontierIter H (frontierStep H state) n)
      exact congrArg (frontierStep H) ih

def FrontierInvariant (H : Nat)
    (state : Finset (Matrix 4) × Finset (Matrix 4)) : Prop :=
  state.2 ⊆ state.1 ∧
    successorSet H (state.1 \ state.2) ⊆ state.1

theorem initialFrontier_invariant (B : Matrix 4) (H : Nat) :
    FrontierInvariant H (initialFrontier B) := by
  constructor
  · exact Finset.Subset.rfl
  · simp [successorSet, initialFrontier]

private theorem seen_union_fresh (H : Nat)
    (seen frontier : Finset (Matrix 4)) :
    seen ∪ (successorSet H frontier \ seen) =
      seen ∪ successorSet H frontier := by
  ext C
  simp only [Finset.mem_union, Finset.mem_sdiff]
  tauto

private theorem old_of_step (H : Nat)
    (seen frontier : Finset (Matrix 4)) :
    (frontierStep H (seen, frontier)).1 \
        (frontierStep H (seen, frontier)).2 = seen := by
  ext C
  simp only [frontierStep, Finset.mem_sdiff, Finset.mem_union]
  tauto

theorem frontierStep_seen_eq_expand (H : Nat)
    (state : Finset (Matrix 4) × Finset (Matrix 4))
    (h : FrontierInvariant H state) :
    (frontierStep H state).1 = expand H state.1 := by
  obtain ⟨hsub, hclosed⟩ := h
  rcases state with ⟨seen, frontier⟩
  change seen ∪ (successorSet H frontier \ seen) =
    seen ∪ successorSet H seen
  rw [seen_union_fresh]
  ext C
  simp only [Finset.mem_union]
  constructor
  · rintro (hs | hc)
    · exact Or.inl hs
    · right
      obtain ⟨D, hD, hsucc⟩ := Finset.mem_biUnion.mp hc
      exact Finset.mem_biUnion.mpr ⟨D, hsub hD, hsucc⟩
  · rintro (hs | hc)
    · exact Or.inl hs
    · obtain ⟨D, hD, hsucc⟩ := Finset.mem_biUnion.mp hc
      by_cases hDf : D ∈ frontier
      · exact Or.inr (Finset.mem_biUnion.mpr ⟨D, hDf, hsucc⟩)
      · exact Or.inl (hclosed (Finset.mem_biUnion.mpr
          ⟨D, Finset.mem_sdiff.mpr ⟨hD, hDf⟩, hsucc⟩))

theorem frontierStep_invariant (H : Nat)
    (state : Finset (Matrix 4) × Finset (Matrix 4))
    (h : FrontierInvariant H state) :
    FrontierInvariant H (frontierStep H state) := by
  constructor
  · intro C hC
    exact Finset.mem_union_right _ hC
  · rw [old_of_step, frontierStep_seen_eq_expand H state h]
    intro C hC
    exact Finset.mem_union_right _ hC

theorem frontierIter_invariant (H : Nat)
    (state : Finset (Matrix 4) × Finset (Matrix 4))
    (h : FrontierInvariant H state) (n : Nat) :
    FrontierInvariant H (frontierIter H state n) := by
  induction n with
  | zero => exact h
  | succ n ih => exact frontierStep_invariant H _ ih

theorem frontierStates_seen_eq_visited (B : Matrix 4) (H n : Nat) :
    (frontierStates B H n).1 = visited B H n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (frontierStep H (frontierStates B H n)).1 =
        expand H (visited B H n)
      have hinv : FrontierInvariant H (frontierStates B H n) :=
        frontierIter_invariant H (initialFrontier B)
          (initialFrontier_invariant B H) n
      rw [frontierStep_seen_eq_expand H _ hinv, ih]

theorem frontierStep_seen_card (H : Nat)
    (state : Finset (Matrix 4) × Finset (Matrix 4)) :
    (frontierStep H state).1.card =
      state.1.card + (frontierStep H state).2.card := by
  change (state.1 ∪ (successorSet H state.2 \ state.1)).card =
    state.1.card + (successorSet H state.2 \ state.1).card
  exact Finset.card_union_of_disjoint Finset.disjoint_sdiff

/-- Total number of distinct frontier states presented for expansion in
the first `fuel` rounds. -/
def frontierProcessCount (H : Nat)
    (state : Finset (Matrix 4) × Finset (Matrix 4)) : Nat → Nat
  | 0 => 0
  | n + 1 => frontierProcessCount H state n +
      (frontierIter H state n).2.card

theorem frontierProcessCount_succ_eq_seen (B : Matrix 4) (H n : Nat) :
    frontierProcessCount H (initialFrontier B) (n + 1) =
      (frontierStates B H n).1.card := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change frontierProcessCount H (initialFrontier B) (n + 1) +
          (frontierStates B H (n + 1)).2.card =
        (frontierStates B H (n + 1)).1.card
      rw [ih]
      change (frontierStates B H n).1.card +
          (frontierStep H (frontierStates B H n)).2.card =
        (frontierStep H (frontierStates B H n)).1.card
      exact (frontierStep_seen_card H _).symm

theorem frontierProcessCount_front (H : Nat)
    (state : Finset (Matrix 4) × Finset (Matrix 4)) (n : Nat) :
    frontierProcessCount H state (n + 1) =
      state.2.card + frontierProcessCount H (frontierStep H state) n := by
  induction n with
  | zero => simp [frontierProcessCount, frontierIter]
  | succ n ih =>
      calc
        frontierProcessCount H state (n + 1 + 1) =
            frontierProcessCount H state (n + 1) +
              (frontierIter H state (n + 1)).2.card := rfl
        _ = state.2.card + frontierProcessCount H (frontierStep H state) n +
              (frontierIter H (frontierStep H state) n).2.card := by
              rw [ih, frontierIter_front]
        _ = state.2.card +
              frontierProcessCount H (frontierStep H state) (n + 1) := by
              simp only [frontierProcessCount]
              omega

theorem frontierProcessCount_le_stateCount (q : SixTuple) (fuel : Nat) :
    frontierProcessCount (budget q) (initialFrontier (ofTuple q)) fuel ≤
      stateCount q := by
  cases fuel with
  | zero => exact Nat.zero_le _
  | succ n =>
      rw [frontierProcessCount_succ_eq_seen,
        frontierStates_seen_eq_visited]
      simpa only [reachUntil_eq_expandIter,
        expandIter_singleton_eq_visited] using
        reachUntil_card_le_stateCount q n

def frontierMutationEvals (q : SixTuple) (fuel : Nat) : Nat :=
  4 * frontierProcessCount (budget q) (initialFrontier (ofTuple q)) fuel

theorem frontierMutationEvals_le (q : SixTuple) (fuel : Nat) :
    frontierMutationEvals q fuel ≤ 4 * stateCount q := by
  exact Nat.mul_le_mul_left 4 (frontierProcessCount_le_stateCount q fuel)

theorem frontierStep_seen_contains (H : Nat)
    (state : Finset (Matrix 4) × Finset (Matrix 4)) :
    state.1 ⊆ (frontierStep H state).1 := by
  intro C hC
  exact Finset.mem_union_left _ hC

theorem frontierIter_seen_contains (H : Nat)
    (state : Finset (Matrix 4) × Finset (Matrix 4)) (n : Nat) :
    state.1 ⊆ (frontierIter H state n).1 := by
  induction n with
  | zero => exact Finset.Subset.rfl
  | succ n ih => exact ih.trans (frontierStep_seen_contains H _)

theorem frontierStep_empty (H : Nat)
    (state : Finset (Matrix 4) × Finset (Matrix 4))
    (h : state.2 = ∅) : frontierStep H state = state := by
  rcases state with ⟨seen, frontier⟩
  have hf : frontier = ∅ := h
  subst frontier
  simp [frontierStep, successorSet]

theorem frontierIter_fixed (H : Nat)
    (state : Finset (Matrix 4) × Finset (Matrix 4))
    (h : frontierStep H state = state) (n : Nat) :
    frontierIter H state n = state := by
  induction n with
  | zero => rfl
  | succ n ih => simp [frontierIter, ih, h]

/-- Complete search, stopping on an acyclic hit or an empty frontier. -/
def frontierAnswer (H : Nat)
    (state : Finset (Matrix 4) × Finset (Matrix 4)) : Nat → Bool
  | 0 => acyclicFound state.1
  | fuel + 1 =>
      if acyclicFound state.1 then true
      else if state.2 = ∅ then false
      else frontierAnswer H (frontierStep H state) fuel

theorem frontierAnswer_eq_iter (H : Nat)
    (state : Finset (Matrix 4) × Finset (Matrix 4))
    (fuel : Nat) :
    frontierAnswer H state fuel =
      acyclicFound (frontierIter H state fuel).1 := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      by_cases hfound : acyclicFound state.1 = true
      · have hfuture := acyclicFound_mono state.1
          (frontierIter H state (fuel + 1)).1
          (frontierIter_seen_contains H state (fuel + 1)) hfound
        simp [frontierAnswer, hfound, hfuture]
      · have hfalse : acyclicFound state.1 = false := by
          cases hb : acyclicFound state.1 <;> simp_all
        by_cases hempty : state.2 = ∅
        · have hstep := frontierStep_empty H state hempty
          have hiter := frontierIter_fixed H state hstep (fuel + 1)
          simp [frontierAnswer, hfalse, hempty, hiter]
        · rw [frontierIter_front]
          simpa [frontierAnswer, hfalse, hempty] using
            ih (frontierStep H state)

def frontierBoxInvariant (q : SixTuple) : Bool :=
  frontierAnswer (budget q) (initialFrontier (ofTuple q))
    (stateCount q - 1)

theorem frontierBoxInvariant_eq_boxInvariant (q : SixTuple) :
    frontierBoxInvariant q = boxInvariant q := by
  rw [frontierBoxInvariant, frontierAnswer_eq_iter]
  change acyclicFound
      (frontierStates (ofTuple q) (budget q) (stateCount q - 1)).1 =
    acyclicFound (visited (ofTuple q) (budget q) (stateCount q - 1))
  rw [frontierStates_seen_eq_visited]

theorem frontierBoxInvariant_MA_iff (q : SixTuple) :
    frontierBoxInvariant q = true ↔ MutationAcyclic (ofTuple q) := by
  rw [frontierBoxInvariant_eq_boxInvariant]
  exact boxInvariant_MA_iff q

theorem frontierBoxInvariant_NMA_iff (q : SixTuple) :
    frontierBoxInvariant q = false ↔ ¬ MutationAcyclic (ofTuple q) := by
  rw [frontierBoxInvariant_eq_boxInvariant]
  exact boxInvariant_NMA_iff q

/-- Source-level mutation calls along exactly the branches taken by
`frontierAnswer`: four calls for each member of an expanded frontier. -/
def frontierAnswerMutationEvals (H : Nat)
    (state : Finset (Matrix 4) × Finset (Matrix 4)) : Nat → Nat
  | 0 => 0
  | fuel + 1 =>
      if acyclicFound state.1 then 0
      else if state.2 = ∅ then 0
      else 4 * state.2.card +
        frontierAnswerMutationEvals H (frontierStep H state) fuel

theorem frontierAnswerMutationEvals_le_process (H : Nat)
    (state : Finset (Matrix 4) × Finset (Matrix 4)) (fuel : Nat) :
    frontierAnswerMutationEvals H state fuel ≤
      4 * frontierProcessCount H state fuel := by
  induction fuel generalizing state with
  | zero => simp [frontierAnswerMutationEvals, frontierProcessCount]
  | succ fuel ih =>
      by_cases hfound : acyclicFound state.1 = true
      · simp [frontierAnswerMutationEvals, hfound]
      · have hfalse : acyclicFound state.1 = false := by
          cases hb : acyclicFound state.1 <;> simp_all
        by_cases hempty : state.2 = ∅
        · simp [frontierAnswerMutationEvals, hfalse, hempty]
        · have hrec := ih (frontierStep H state)
          simp only [frontierAnswerMutationEvals, hfalse,
            Bool.false_eq_true, ↓reduceIte, hempty]
          calc
            4 * state.2.card +
                frontierAnswerMutationEvals H (frontierStep H state) fuel ≤
              4 * state.2.card +
                4 * frontierProcessCount H (frontierStep H state) fuel :=
              Nat.add_le_add_left hrec _
            _ = 4 * frontierProcessCount H state (fuel + 1) := by
              rw [frontierProcessCount_front]
              ring

def inputFrontierMutationEvals (q : SixTuple) : Nat :=
  frontierAnswerMutationEvals (budget q) (initialFrontier (ofTuple q))
    (stateCount q - 1)

theorem inputFrontierMutationEvals_le (q : SixTuple) :
    inputFrontierMutationEvals q ≤ 4 * stateCount q := by
  exact (frontierAnswerMutationEvals_le_process (budget q)
    (initialFrontier (ofTuple q)) (stateCount q - 1)).trans
      (frontierMutationEvals_le q (stateCount q - 1))

#print axioms frontierStep_seen_eq_expand
#print axioms frontierStep_invariant
#print axioms frontierStates_seen_eq_visited
#print axioms frontierProcessCount_succ_eq_seen
#print axioms frontierMutationEvals_le
#print axioms frontierAnswer_eq_iter
#print axioms frontierBoxInvariant_eq_boxInvariant
#print axioms frontierBoxInvariant_MA_iff
#print axioms frontierBoxInvariant_NMA_iff
#print axioms frontierAnswerMutationEvals_le_process
#print axioms inputFrontierMutationEvals_le

end Rank4Round8.Reduction
