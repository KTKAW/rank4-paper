import Rank4Round8.Arithmetic.AlternatingLineRecognizer

/-!
The whole integer extension of the alternating affine line. Its negative tail
is acyclic without mutation; its nonnegative tail has the checked parity rule.
-/

namespace Rank4Round8.Arithmetic

open Rank4Formula Rank7Adversarial QuiverProofs

def alternatingLineInt (t : Int) : SixTuple := fun i =>
  match i.val with
  | 0 => -2 | 1 => 2 + t | 2 => t
  | 3 => -t | 4 => 2 - t | _ => 0

theorem alternatingLineInt_negative_acyclic (t : Int) (ht : t < 0) :
    Acyclic (ofTuple (alternatingLineInt t)) := by
  by_cases hs : t ≤ -2
  · refine ⟨(fun i => match i.val with
      | 0 => 2 | 1 => 0 | 2 => 1 | _ => 1), ?_⟩
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [ofTuple, alternatingLineInt, ofSix] at hij ⊢ <;> omega
  · have he : t = -1 := by omega
    subst t
    refine ⟨(fun i => match i.val with
      | 0 => 2 | 1 => 0 | 2 => 3 | _ => 1), ?_⟩
    decide

theorem alternatingLineInt_nonneg (t : Int) (ht : 0 ≤ t) :
    alternatingLineInt t = alternatingLine t.toNat := by
  have hnat : ((t.toNat : Nat) : Int) = t := Int.toNat_of_nonneg ht
  funext i
  fin_cases i <;>
    simp [alternatingLineInt, alternatingLine, hnat]

theorem alternatingLineInt_MA_iff (t : Int) :
    MutationAcyclic (ofTuple (alternatingLineInt t)) ↔
      t < 0 ∨ t.toNat % 2 = 0 := by
  by_cases ht : t < 0
  · have hm : MutationAcyclic (ofTuple (alternatingLineInt t)) :=
      acyclic_is_mutationAcyclic _ (alternatingLineInt_negative_acyclic t ht)
    simp [ht, hm]
  · have hn : 0 ≤ t := by omega
    rw [alternatingLineInt_nonneg t hn, alternatingLine_MA_iff_even]
    simp [ht]

def classifyAlternatingIntegerLine (t : Int) : Bool :=
  decide (t < 0 ∨ t.toNat % 2 = 0)

theorem classifyAlternatingIntegerLine_iff (t : Int) :
    classifyAlternatingIntegerLine t = true ↔
      MutationAcyclic (ofTuple (alternatingLineInt t)) := by
  simpa only [classifyAlternatingIntegerLine, decide_eq_true_eq] using
    (alternatingLineInt_MA_iff t).symm

def OnAlternatingIntegerLine (q : SixTuple) : Prop :=
  q 0 = -2 ∧ q 1 = q 2 + 2 ∧ q 3 = -(q 2) ∧
    q 4 = 2 - q 2 ∧ q 5 = 0

instance (q : SixTuple) : Decidable (OnAlternatingIntegerLine q) := by
  unfold OnAlternatingIntegerLine
  infer_instance

theorem onAlternatingIntegerLine_iff (q : SixTuple) :
    OnAlternatingIntegerLine q ↔
      q = alternatingLineInt (q 2) := by
  constructor
  · rintro ⟨h0, h1, h3, h4, h5⟩
    funext i
    fin_cases i <;>
      simp [alternatingLineInt, h0, h1, h3, h4, h5, add_comm]
  · intro h
    rw [h]
    simp [OnAlternatingIntegerLine, alternatingLineInt, add_comm]

def classifyLineTupleInt (q : SixTuple) : Option Bool :=
  if OnAlternatingIntegerLine q then
    some (classifyAlternatingIntegerLine (q 2))
  else none

theorem classifyLineTupleInt_spec (q : SixTuple) (b : Bool)
    (h : classifyLineTupleInt q = some b) :
    b = true ↔ MutationAcyclic (ofTuple q) := by
  by_cases hOn : OnAlternatingIntegerLine q
  · have hq := (onAlternatingIntegerLine_iff q).mp hOn
    simp [classifyLineTupleInt, hOn] at h
    cases h
    rw [hq]
    exact classifyAlternatingIntegerLine_iff (q 2)
  · simp [classifyLineTupleInt, hOn] at h

#print axioms alternatingLineInt_negative_acyclic
#print axioms alternatingLineInt_MA_iff
#print axioms classifyLineTupleInt_spec

end Rank4Round8.Arithmetic
