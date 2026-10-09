import Rank4Round8.Reduction.ChoiceFreeListFrontier

/-!
Deduplicated choice-free list frontier. The mathematical semantics are the
same as the verified finite-set frontier; unlike the initial list variant,
each fresh frontier is a list without repeated matrices.
-/

namespace Rank4Round8.Reduction

open Rank4Formula QuiverProofs Rank4Round6.Coordinator

def dedupMatrixList (xs : List (Matrix 4)) : List (Matrix 4) :=
  letI : DecidableEq (Matrix 4) := explicitMatrixDecEq
  xs.dedup

theorem dedupMatrixList_mem (xs : List (Matrix 4)) (C : Matrix 4) :
    C ∈ dedupMatrixList xs ↔ C ∈ xs := by
  simp [dedupMatrixList]

theorem dedupMatrixList_nodup (xs : List (Matrix 4)) :
    (dedupMatrixList xs).Nodup := by
  letI : DecidableEq (Matrix 4) := explicitMatrixDecEq
  change (List.dedup xs).Nodup
  exact List.nodup_dedup xs

def listFrontierStepDedup (H : Nat)
    (state : List (Matrix 4) × List (Matrix 4)) :
    List (Matrix 4) × List (Matrix 4) :=
  let fresh := dedupMatrixList
    ((listSuccessorSet H state.2).filter
      (fun C => !listMatrixMember C state.1))
  (state.1 ++ fresh, fresh)

theorem listFrontierStepDedup_fresh_nodup (H : Nat)
    (state : List (Matrix 4) × List (Matrix 4)) :
    (listFrontierStepDedup H state).2.Nodup := by
  exact dedupMatrixList_nodup _

theorem listFrontierStepDedup_fresh_not_seen (H : Nat)
    (state : List (Matrix 4) × List (Matrix 4)) (C : Matrix 4)
    (hC : C ∈ (listFrontierStepDedup H state).2) :
    C ∉ state.1 := by
  change C ∈ dedupMatrixList
    ((listSuccessorSet H state.2).filter
      (fun D => !listMatrixMember D state.1)) at hC
  have hf := (dedupMatrixList_mem _ C).mp hC
  have hnot : listMatrixMember C state.1 = false := by
    have hp := (List.mem_filter.mp hf).2
    cases hb : listMatrixMember C state.1 <;> simp_all
  exact (listMatrixMember_false_iff C state.1).mp hnot

theorem listFrontierStepDedup_seen_nodup (H : Nat)
    (state : List (Matrix 4) × List (Matrix 4))
    (hseen : state.1.Nodup) :
    (listFrontierStepDedup H state).1.Nodup := by
  change (state.1 ++ (listFrontierStepDedup H state).2).Nodup
  rw [List.nodup_append]
  refine ⟨hseen, listFrontierStepDedup_fresh_nodup H state, ?_⟩
  intro a ha b hb hab
  subst b
  exact (listFrontierStepDedup_fresh_not_seen H state a hb) ha

theorem listFrontierStepDedup_eq (H : Nat)
    (state : List (Matrix 4) × List (Matrix 4)) :
    listStateFinset (listFrontierStepDedup H state) =
      frontierStep H (listStateFinset state) := by
  calc
    listStateFinset (listFrontierStepDedup H state) =
        listStateFinset (listFrontierStep H state) := by
      apply Prod.ext
      · ext C
        simp [listStateFinset, listFrontierStepDedup, listFrontierStep,
          dedupMatrixList_mem]
      · ext C
        simp [listStateFinset, listFrontierStepDedup, listFrontierStep,
          dedupMatrixList_mem]
    _ = frontierStep H (listStateFinset state) := listFrontierStep_eq H state

def listFrontierIterDedup (H : Nat)
    (state : List (Matrix 4) × List (Matrix 4)) : Nat →
      List (Matrix 4) × List (Matrix 4)
  | 0 => state
  | n + 1 => listFrontierStepDedup H (listFrontierIterDedup H state n)

theorem listFrontierIterDedup_front (H : Nat)
    (state : List (Matrix 4) × List (Matrix 4)) (n : Nat) :
    listFrontierIterDedup H state (n + 1) =
      listFrontierIterDedup H (listFrontierStepDedup H state) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change listFrontierStepDedup H
          (listFrontierIterDedup H state (n + 1)) =
        listFrontierStepDedup H
          (listFrontierIterDedup H (listFrontierStepDedup H state) n)
      rw [ih]

theorem listFrontierIterDedup_eq (H : Nat)
    (state : List (Matrix 4) × List (Matrix 4)) (n : Nat) :
    listStateFinset (listFrontierIterDedup H state n) =
      frontierIter H (listStateFinset state) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change listStateFinset
          (listFrontierStepDedup H (listFrontierIterDedup H state n)) =
        frontierStep H (frontierIter H (listStateFinset state) n)
      rw [listFrontierStepDedup_eq, ih]

theorem listFrontierIterDedup_seen_nodup (H : Nat) (B : Matrix 4)
    (n : Nat) :
    (listFrontierIterDedup H ([B], [B]) n).1.Nodup := by
  induction n with
  | zero => simp [listFrontierIterDedup]
  | succ n ih => exact listFrontierStepDedup_seen_nodup H _ ih

theorem listFrontierIterDedup_frontier_nodup (H : Nat) (B : Matrix 4)
    (n : Nat) :
    (listFrontierIterDedup H ([B], [B]) n).2.Nodup := by
  cases n with
  | zero => simp [listFrontierIterDedup]
  | succ n => exact listFrontierStepDedup_fresh_nodup H _

def listFrontierProcessCountDedup (H : Nat)
    (state : List (Matrix 4) × List (Matrix 4)) : Nat → Nat
  | 0 => 0
  | n + 1 => listFrontierProcessCountDedup H state n +
      (listFrontierIterDedup H state n).2.length

theorem listFrontierProcessCountDedup_succ_eq_seen
    (H : Nat) (B : Matrix 4) (n : Nat) :
    listFrontierProcessCountDedup H ([B], [B]) (n + 1) =
      (listFrontierIterDedup H ([B], [B]) n).1.length := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change listFrontierProcessCountDedup H ([B], [B]) (n + 1) +
          (listFrontierIterDedup H ([B], [B]) (n + 1)).2.length =
        (listFrontierIterDedup H ([B], [B]) (n + 1)).1.length
      rw [ih]
      change (listFrontierIterDedup H ([B], [B]) n).1.length +
          (listFrontierStepDedup H
            (listFrontierIterDedup H ([B], [B]) n)).2.length =
        (listFrontierStepDedup H
          (listFrontierIterDedup H ([B], [B]) n)).1.length
      simp [listFrontierStepDedup]

theorem listFrontierProcessCountDedup_le_stateCount
    (q : SixTuple) (fuel : Nat) :
    listFrontierProcessCountDedup (budget q)
      ([ofTuple q], [ofTuple q]) fuel ≤ stateCount q := by
  cases fuel with
  | zero => exact Nat.zero_le _
  | succ n =>
      rw [listFrontierProcessCountDedup_succ_eq_seen]
      let s := listFrontierIterDedup (budget q)
        ([ofTuple q], [ofTuple q]) n
      have hnodup : s.1.Nodup :=
        listFrontierIterDedup_seen_nodup (budget q) (ofTuple q) n
      have hinitial :
          listStateFinset ([ofTuple q], [ofTuple q]) =
            initialFrontier (ofTuple q) := by
        simp [listStateFinset, initialFrontier]
      have hsem : s.1.toFinset =
          (frontierStates (ofTuple q) (budget q) n).1 := by
        have hh := listFrontierIterDedup_eq (budget q)
          ([ofTuple q], [ofTuple q]) n
        rw [hinitial] at hh
        exact congrArg Prod.fst hh
      have hbound :
          (frontierStates (ofTuple q) (budget q) n).1.card ≤
            stateCount q := by
        simpa only [frontierProcessCount_succ_eq_seen] using
          frontierProcessCount_le_stateCount q (n + 1)
      calc
        s.1.length = s.1.toFinset.card :=
          (List.toFinset_card_of_nodup hnodup).symm
        _ = (frontierStates (ofTuple q) (budget q) n).1.card :=
          congrArg Finset.card hsem
        _ ≤ stateCount q := hbound

theorem listFrontierProcessCountDedup_front (H : Nat)
    (state : List (Matrix 4) × List (Matrix 4)) (n : Nat) :
    listFrontierProcessCountDedup H state (n + 1) =
      state.2.length +
        listFrontierProcessCountDedup H
          (listFrontierStepDedup H state) n := by
  induction n with
  | zero => simp [listFrontierProcessCountDedup, listFrontierIterDedup]
  | succ n ih =>
      calc
        listFrontierProcessCountDedup H state (n + 1 + 1) =
            listFrontierProcessCountDedup H state (n + 1) +
              (listFrontierIterDedup H state (n + 1)).2.length := rfl
        _ = state.2.length +
              listFrontierProcessCountDedup H
                (listFrontierStepDedup H state) n +
              (listFrontierIterDedup H
                (listFrontierStepDedup H state) n).2.length := by
              rw [ih]
              rw [listFrontierIterDedup_front]
        _ = state.2.length +
              listFrontierProcessCountDedup H
                (listFrontierStepDedup H state) (n + 1) := by
              simp only [listFrontierProcessCountDedup]
              omega

/-- Source-level mutation calls along the actual early-exit branches.
Each expanded list element triggers the four listed mutations. -/
def listFrontierAnswerMutationEvalsDedup (H : Nat)
    (state : List (Matrix 4) × List (Matrix 4)) : Nat → Nat
  | 0 => 0
  | fuel + 1 =>
      if listAcyclicFound state.1 then 0
      else if state.2.isEmpty then 0
      else 4 * state.2.length +
        listFrontierAnswerMutationEvalsDedup H
          (listFrontierStepDedup H state) fuel

theorem listFrontierAnswerMutationEvalsDedup_le_process
    (H : Nat) (state : List (Matrix 4) × List (Matrix 4))
    (fuel : Nat) :
    listFrontierAnswerMutationEvalsDedup H state fuel ≤
      4 * listFrontierProcessCountDedup H state fuel := by
  induction fuel generalizing state with
  | zero => simp [listFrontierAnswerMutationEvalsDedup,
      listFrontierProcessCountDedup]
  | succ fuel ih =>
      by_cases hfound : listAcyclicFound state.1 = true
      · simp [listFrontierAnswerMutationEvalsDedup, hfound]
      · have hfalse : listAcyclicFound state.1 = false := by
          cases hb : listAcyclicFound state.1 <;> simp_all
        by_cases hempty : state.2.isEmpty = true
        · simp [listFrontierAnswerMutationEvalsDedup, hfalse, hempty]
        · have hemptyFalse : state.2.isEmpty = false := by
            cases hb : state.2.isEmpty <;> simp_all
          have hrec := ih (listFrontierStepDedup H state)
          simp only [listFrontierAnswerMutationEvalsDedup,
            hfalse, Bool.false_eq_true, ↓reduceIte,
            hemptyFalse] at *
          calc
            4 * state.2.length +
                listFrontierAnswerMutationEvalsDedup H
                  (listFrontierStepDedup H state) fuel ≤
              4 * state.2.length +
                4 * listFrontierProcessCountDedup H
                  (listFrontierStepDedup H state) fuel :=
              Nat.add_le_add_left hrec _
            _ = 4 * listFrontierProcessCountDedup H state (fuel + 1) := by
              rw [listFrontierProcessCountDedup_front]
              ring

def inputListFrontierMutationEvalsDedup (q : SixTuple) : Nat :=
  listFrontierAnswerMutationEvalsDedup (budget q)
    ([ofTuple q], [ofTuple q]) (stateCount q - 1)

theorem inputListFrontierMutationEvalsDedup_le (q : SixTuple) :
    inputListFrontierMutationEvalsDedup q ≤ 4 * stateCount q := by
  exact (listFrontierAnswerMutationEvalsDedup_le_process (budget q)
    ([ofTuple q], [ofTuple q]) (stateCount q - 1)).trans
      (Nat.mul_le_mul_left 4
        (listFrontierProcessCountDedup_le_stateCount q
          (stateCount q - 1)))

def listFrontierAnswerDedup (H : Nat)
    (state : List (Matrix 4) × List (Matrix 4)) : Nat → Bool
  | 0 => listAcyclicFound state.1
  | fuel + 1 =>
      if listAcyclicFound state.1 then true
      else if state.2.isEmpty then false
      else listFrontierAnswerDedup H (listFrontierStepDedup H state) fuel

theorem listFrontierAnswerDedup_eq (H : Nat)
    (state : List (Matrix 4) × List (Matrix 4)) (fuel : Nat) :
    listFrontierAnswerDedup H state fuel =
      frontierAnswer H (listStateFinset state) fuel := by
  induction fuel generalizing state with
  | zero =>
      simpa [listFrontierAnswerDedup, frontierAnswer, listStateFinset] using
        listAcyclicFound_eq state.1
  | succ fuel ih =>
      change (if listAcyclicFound state.1 then true
        else if state.2.isEmpty then false
        else listFrontierAnswerDedup H (listFrontierStepDedup H state) fuel) =
        (if acyclicFound state.1.toFinset then true
        else if state.2.toFinset = ∅ then false
        else frontierAnswer H (frontierStep H (listStateFinset state)) fuel)
      rw [listAcyclicFound_eq]
      by_cases ha : acyclicFound state.1.toFinset = true
      · simp [ha]
      · have haf : acyclicFound state.1.toFinset = false := by
          cases h : acyclicFound state.1.toFinset <;> simp_all
        simp only [haf, Bool.false_eq_true, ↓reduceIte]
        by_cases he : state.2.toFinset = ∅
        · have hle : state.2.isEmpty = true := (listEmpty_iff _).mpr he
          simp [hle, he]
        · have hle : state.2.isEmpty = false := by
            cases h : state.2.isEmpty with
            | false => rfl
            | true => exact False.elim (he ((listEmpty_iff _).mp h))
          simp only [hle, if_neg he]
          rw [ih, listFrontierStepDedup_eq]
          simp

def listFrontierBoxInvariantDedup (q : SixTuple) : Bool :=
  listFrontierAnswerDedup (budget q) ([ofTuple q], [ofTuple q])
    (stateCount q - 1)

theorem listFrontierBoxInvariantDedup_eq (q : SixTuple) :
    listFrontierBoxInvariantDedup q = frontierBoxInvariant q := by
  unfold listFrontierBoxInvariantDedup frontierBoxInvariant
  rw [listFrontierAnswerDedup_eq]
  rfl

theorem listFrontierBoxInvariantDedup_MA_iff (q : SixTuple) :
    listFrontierBoxInvariantDedup q = true ↔
      MutationAcyclic (ofTuple q) := by
  rw [listFrontierBoxInvariantDedup_eq]
  exact frontierBoxInvariant_MA_iff q

theorem listFrontierBoxInvariantDedup_NMA_iff (q : SixTuple) :
    listFrontierBoxInvariantDedup q = false ↔
      ¬ MutationAcyclic (ofTuple q) := by
  rw [listFrontierBoxInvariantDedup_eq]
  exact frontierBoxInvariant_NMA_iff q

#print axioms dedupMatrixList
#print axioms listFrontierStepDedup
#print axioms listFrontierStepDedup_fresh_nodup
#print axioms listFrontierStepDedup_eq
#print axioms listFrontierBoxInvariantDedup
#print axioms listFrontierBoxInvariantDedup_eq
#print axioms listFrontierBoxInvariantDedup_MA_iff
#print axioms listFrontierBoxInvariantDedup_NMA_iff
#print axioms listFrontierProcessCountDedup_le_stateCount
#print axioms listFrontierAnswerMutationEvalsDedup
#print axioms inputListFrontierMutationEvalsDedup
#print axioms inputListFrontierMutationEvalsDedup_le

end Rank4Round8.Reduction
