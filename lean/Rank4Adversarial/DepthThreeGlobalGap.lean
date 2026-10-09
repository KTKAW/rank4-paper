import QuiverProofs.FiniteLogic
import Rank4Invariant.OneStepCoverGap

set_option maxRecDepth 10000
set_option maxHeartbeats 0

/-!
An unrestricted MA input needs four mutations before reaching an acyclic
matrix. This only refutes the plain three-step acyclic-target rule globally;
it makes no assertion about a richer target or the bounded-two box.
-/

namespace Rank4Adversarial
open QuiverProofs Rank4Formula

private def HasTriangle (B : Matrix 4) : Prop :=
  ∃ i j k : Fin 4, 0 < B i j ∧ 0 < B j k ∧ 0 < B k i

private instance (B : Matrix 4) : Decidable (HasTriangle B) := by
  unfold HasTriangle
  infer_instance

private theorem hasTriangle_not_acyclic (B : Matrix 4)
    (h : HasTriangle B) : ¬ Acyclic B := by
  obtain ⟨i,j,k,hij,hjk,hki⟩ := h
  exact Rank4Invariant.cyclicTriangle_not_acyclic B i j k hij hjk hki

def depthFourPoint : SixTuple := fun i =>
  match i.val with
  | 0 => -3 | 1 => -1 | 2 => 2 | 3 => -1 | 4 => -2 | _ => -1

theorem depthFourPoint_MA : MutationAcyclic (ofTuple depthFourPoint) := by
  refine ⟨[3, 0, 2, 1], ?_⟩
  refine ⟨(fun i => match i.val with
    | 0 => 0 | 1 => 2 | 2 => 1 | _ => 3), ?_⟩
  decide

theorem depthFourPoint_no_acyclic_word_le_three :
    ¬ ∃ w : List (Fin 4), w.length ≤ 3 ∧
      Acyclic (applyWord (ofTuple depthFourPoint) w) := by
  rintro ⟨w, hw, ha⟩
  have hmem : w ∈ FiniteLogic.wordsUpTo 3 :=
    FiniteLogic.word_mem_wordsUpTo w 3 hw
  have htri : (FiniteLogic.wordsUpTo 3).Forall
      (fun v => HasTriangle (applyWord (ofTuple depthFourPoint) v)) := by decide
  have hv : HasTriangle (applyWord (ofTuple depthFourPoint) w) :=
    (List.forall_iff_forall_mem.mp htri) w hmem
  exact hasTriangle_not_acyclic _ hv ha

#print axioms depthFourPoint_MA
#print axioms depthFourPoint_no_acyclic_word_le_three

end Rank4Adversarial
