import Rank4Round8.Reduction.ChoiceFreeEqualityStep

/-!
A list-based version of finite-box frontier expansion. All executable
operations use explicit coordinate comparisons and lists; conversion to
`Finset` is restricted to correctness proofs.
-/

namespace Rank4Round8.Reduction

open Rank4Formula QuiverProofs Rank4Round6.Coordinator

def listMatrixMember (C : Matrix 4) (xs : List (Matrix 4)) : Bool :=
  xs.any (fun D => explicitMatrixEq C D)

theorem listMatrixMember_iff (C : Matrix 4) (xs : List (Matrix 4)) :
    listMatrixMember C xs = true ↔ C ∈ xs := by
  simp only [listMatrixMember, List.any_eq_true, explicitMatrixEq_iff]
  constructor
  · rintro ⟨D, hD, hCD⟩
    simpa [hCD] using hD
  · intro hC
    exact ⟨C, hC, rfl⟩

theorem listMatrixMember_false_iff (C : Matrix 4)
    (xs : List (Matrix 4)) :
    listMatrixMember C xs = false ↔ C ∉ xs := by
  constructor
  · intro hb hm
    have ht := (listMatrixMember_iff C xs).mpr hm
    rw [hb] at ht
    cases ht
  · intro hn
    cases hb : listMatrixMember C xs with
    | false => rfl
    | true => exact False.elim (hn ((listMatrixMember_iff C xs).mp hb))

def listSuccessorSet (H : Nat) (frontier : List (Matrix 4)) :
    List (Matrix 4) :=
  frontier.flatMap (successorsListExplicit H)

theorem listSuccessorSet_mem_iff (H : Nat)
    (frontier : List (Matrix 4)) (C : Matrix 4) :
    C ∈ listSuccessorSet H frontier ↔
      C ∈ successorSet H frontier.toFinset := by
  simp [listSuccessorSet, successorSet, List.mem_flatMap,
    successorsListExplicit_mem_iff]

def listFrontierStep (H : Nat)
    (state : List (Matrix 4) × List (Matrix 4)) :
    List (Matrix 4) × List (Matrix 4) :=
  let fresh := (listSuccessorSet H state.2).filter
    (fun C => !listMatrixMember C state.1)
  (state.1 ++ fresh, fresh)

def listStateFinset
    (state : List (Matrix 4) × List (Matrix 4)) :
    Finset (Matrix 4) × Finset (Matrix 4) :=
  (state.1.toFinset, state.2.toFinset)

theorem listFrontierStep_eq (H : Nat)
    (state : List (Matrix 4) × List (Matrix 4)) :
    listStateFinset (listFrontierStep H state) =
      frontierStep H (listStateFinset state) := by
  apply Prod.ext
  · ext C
    simp [listStateFinset, listFrontierStep,
      listSuccessorSet_mem_iff, listMatrixMember_false_iff,
      frontierStep]
    tauto
  · ext C
    simp [listStateFinset, listFrontierStep,
      listSuccessorSet_mem_iff, listMatrixMember_false_iff,
      frontierStep]

def listFrontierIter (H : Nat)
    (state : List (Matrix 4) × List (Matrix 4)) : Nat →
      List (Matrix 4) × List (Matrix 4)
  | 0 => state
  | n + 1 => listFrontierStep H (listFrontierIter H state n)

theorem listFrontierIter_eq (H : Nat)
    (state : List (Matrix 4) × List (Matrix 4)) (n : Nat) :
    listStateFinset (listFrontierIter H state n) =
      frontierIter H (listStateFinset state) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change listStateFinset (listFrontierStep H (listFrontierIter H state n)) =
        frontierStep H (frontierIter H (listStateFinset state) n)
      rw [listFrontierStep_eq, ih]

def listAcyclicFound (xs : List (Matrix 4)) : Bool :=
  xs.any (fun C => decide (ForkPruning.FiniteAcyclic C))

theorem listAcyclicFound_eq (xs : List (Matrix 4)) :
    listAcyclicFound xs = acyclicFound xs.toFinset := by
  have hiff : listAcyclicFound xs = true ↔
      acyclicFound xs.toFinset = true := by
    simp [listAcyclicFound, acyclicFound, List.any_eq_true, Finset.Nonempty]
  cases h₁ : listAcyclicFound xs <;>
    cases h₂ : acyclicFound xs.toFinset <;>
    simp_all

theorem listEmpty_iff (xs : List (Matrix 4)) :
    xs.isEmpty = true ↔ xs.toFinset = ∅ := by
  cases xs with
  | nil => simp
  | cons x xs => simp

def listFrontierAnswer (H : Nat)
    (state : List (Matrix 4) × List (Matrix 4)) : Nat → Bool
  | 0 => listAcyclicFound state.1
  | fuel + 1 =>
      if listAcyclicFound state.1 then true
      else if state.2.isEmpty then false
      else listFrontierAnswer H (listFrontierStep H state) fuel

theorem listFrontierAnswer_eq (H : Nat)
    (state : List (Matrix 4) × List (Matrix 4)) (fuel : Nat) :
    listFrontierAnswer H state fuel =
      frontierAnswer H (listStateFinset state) fuel := by
  induction fuel generalizing state with
  | zero =>
      simpa [listFrontierAnswer, frontierAnswer, listStateFinset] using
        listAcyclicFound_eq state.1
  | succ fuel ih =>
      change (if listAcyclicFound state.1 then true
        else if state.2.isEmpty then false
        else listFrontierAnswer H (listFrontierStep H state) fuel) =
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
          rw [ih, listFrontierStep_eq]
          simp

def listFrontierBoxInvariant (q : SixTuple) : Bool :=
  listFrontierAnswer (budget q) ([ofTuple q], [ofTuple q])
    (stateCount q - 1)

theorem listFrontierBoxInvariant_eq (q : SixTuple) :
    listFrontierBoxInvariant q = frontierBoxInvariant q := by
  unfold listFrontierBoxInvariant frontierBoxInvariant
  rw [listFrontierAnswer_eq]
  rfl

theorem listFrontierBoxInvariant_MA_iff (q : SixTuple) :
    listFrontierBoxInvariant q = true ↔ MutationAcyclic (ofTuple q) := by
  rw [listFrontierBoxInvariant_eq]
  exact frontierBoxInvariant_MA_iff q

theorem listFrontierBoxInvariant_NMA_iff (q : SixTuple) :
    listFrontierBoxInvariant q = false ↔ ¬ MutationAcyclic (ofTuple q) := by
  rw [listFrontierBoxInvariant_eq]
  exact frontierBoxInvariant_NMA_iff q

#print axioms listMatrixMember
#print axioms listSuccessorSet
#print axioms listFrontierStep
#print axioms listFrontierStep_eq
#print axioms listAcyclicFound
#print axioms listFrontierAnswer
#print axioms listFrontierBoxInvariant
#print axioms listFrontierBoxInvariant_eq
#print axioms listFrontierBoxInvariant_MA_iff
#print axioms listFrontierBoxInvariant_NMA_iff

end Rank4Round8.Reduction
