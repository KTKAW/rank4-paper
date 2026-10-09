import Rank4Formula.FormulaLanguage
import QuiverProofs.MAHasTotalProper4Completion
import QuiverProofs.FiniteLogic
import QuiverProofs.ForkPruningDecidable
import QuiverProofs.Symmetry
import Mathlib.Tactic.FinCases

/-!
An affine polynomial six-tuple with MA and NMA on two infinite residue
classes. This is a full-language obstruction once the orbit and certified
negative seed are checked.
-/

namespace Rank7Adversarial

set_option maxRecDepth 100000
set_option maxHeartbeats 0

open Rank4Formula QuiverProofs

def alternatingLine (t : Nat) : SixTuple := fun i =>
  match i.val with
  | 0 => -2 | 1 => 2 + (t : Int) | 2 => (t : Int)
  | 3 => -(t : Int) | 4 => 2 - (t : Int) | _ => 0

def negativeSeed : SixTuple := fun i =>
  match i.val with
  | 0 => -2 | 1 => -1 | 2 => -1 | 3 => 1 | 4 => -1 | _ => 1

theorem line_zero_MA : MutationAcyclic (ofTuple (alternatingLine 0)) := by
  refine ⟨[], ?_⟩
  refine ⟨(fun i => match i.val with
    | 0 => 1 | 1 => 0 | 2 => 2 | _ => 2), ?_⟩
  decide

theorem negativeSeed_NMA : ¬ MutationAcyclic (ofTuple negativeSeed) := by
  intro hm
  have hs : SkewSymmetric (ofTuple negativeSeed) := ofSix_skew _ _ _ _ _ _
  obtain ⟨p,hp⟩ := MAHasTotalProper4Completion.maHasTotalProper4 _ hs hm
  obtain ⟨i,hi⟩ := ProperOrder.cyclic_order_exhaustive p
  have hproper := ProperMutation.totalProper_proper _ _ hp
  have htable := (ProperWiggle.properClass_iff_table _ hs p i hi).mp hproper
  have hf : ∀ i : Fin 6, ¬ ProperWiggle.ProperClassTable (ofTuple negativeSeed) i := by decide
  exact hf i htable

theorem seed_to_line_one :
    applyWord (ofTuple negativeSeed) [0, 1] =
      ofTuple (alternatingLine 1) := by decide

theorem line_one_NMA : ¬ MutationAcyclic (ofTuple (alternatingLine 1)) := by
  rw [← seed_to_line_one]
  exact (mutationAcyclic_word_iff _ [0, 1]).not.mpr negativeSeed_NMA

theorem line_step_zero (t : Nat) :
    mutate (ofTuple (alternatingLine t)) 0 =
      ofSix 2 (-2 - (t : Int)) (-(t : Int)) (4 + (t : Int))
        (2 + (t : Int)) 0 := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [mutate, ofTuple, alternatingLine, correction, ofSix] <;> omega

theorem line_step_one (t : Nat) :
    mutate (ofSix 2 (-2 - (t : Int)) (-(t : Int)) (4 + (t : Int))
        (2 + (t : Int)) 0) 1 =
      ofTuple (alternatingLine (t + 4)) := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [mutate, ofTuple, alternatingLine, correction, ofSix] <;> omega

theorem line_translate (t : Nat) :
    applyWord (ofTuple (alternatingLine t)) [0, 1] =
      ofTuple (alternatingLine (t + 4)) := by
  simp only [applyWord, line_step_zero, line_step_one]

theorem line_periodic_MA_iff (t : Nat) :
    MutationAcyclic (ofTuple (alternatingLine (t + 4))) ↔
      MutationAcyclic (ofTuple (alternatingLine t)) := by
  rw [← line_translate t]
  exact mutationAcyclic_word_iff _ [0, 1]

theorem line_four_mul_MA (n : Nat) :
    MutationAcyclic (ofTuple (alternatingLine (4 * n))) := by
  induction n with
  | zero => simpa using line_zero_MA
  | succ n ih =>
      have heq : 4 * (n + 1) = 4 * n + 4 := by omega
      rw [heq]
      exact (line_periodic_MA_iff (4 * n)).mpr ih

theorem line_four_mul_add_one_NMA (n : Nat) :
    ¬ MutationAcyclic (ofTuple (alternatingLine (4 * n + 1))) := by
  induction n with
  | zero => simpa using line_one_NMA
  | succ n ih =>
      have heq : 4 * (n + 1) + 1 = (4 * n + 1) + 4 := by omega
      rw [heq]
      intro hm
      exact ih ((line_periodic_MA_iff (4 * n + 1)).mp hm)

#print axioms line_zero_MA
#print axioms negativeSeed_NMA
#print axioms line_one_NMA
#print axioms line_translate
#print axioms line_four_mul_MA
#print axioms line_four_mul_add_one_NMA

end Rank7Adversarial
