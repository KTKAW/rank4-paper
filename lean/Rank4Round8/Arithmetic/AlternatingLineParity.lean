import Rank7Adversarial.PolynomialAlternation

/-!
An exact zero-mutation arithmetic classifier on the one-parameter alternating
line. This is a restricted-family result, not a classifier for all six-tuples.
The rule uses only parity of the parameter after membership in the family is
established. The proof certifies the two previously unresolved residues by an
acyclic witness and a direct proper-order NMA certificate.
-/

namespace Rank4Round8.Arithmetic

set_option maxRecDepth 100000
set_option maxHeartbeats 0

open Rank4Formula Rank7Adversarial QuiverProofs

def oddThreeSeed : SixTuple := fun i =>
  match i.val with
  | 0 => -2 | 1 => 1 | 2 => -1 | 3 => 1 | 4 => 1 | _ => 1

theorem oddThreeSeed_NMA : ¬ MutationAcyclic (ofTuple oddThreeSeed) := by
  intro hm
  have hs : SkewSymmetric (ofTuple oddThreeSeed) := ofSix_skew _ _ _ _ _ _
  obtain ⟨p,hp⟩ := MAHasTotalProper4Completion.maHasTotalProper4 _ hs hm
  obtain ⟨i,hi⟩ := ProperOrder.cyclic_order_exhaustive p
  have hproper := ProperMutation.totalProper_proper _ _ hp
  have htable := (ProperWiggle.properClass_iff_table _ hs p i hi).mp hproper
  have hf : ∀ i : Fin 6, ¬ ProperWiggle.ProperClassTable (ofTuple oddThreeSeed) i := by decide
  exact hf i htable

theorem line_three_to_seed :
    applyWord (ofTuple (alternatingLine 3)) [1, 0] =
      ofTuple oddThreeSeed := by decide

theorem line_three_NMA :
    ¬ MutationAcyclic (ofTuple (alternatingLine 3)) := by
  intro hm
  have hseed : MutationAcyclic (ofTuple oddThreeSeed) := by
    rw [← line_three_to_seed]
    exact (mutationAcyclic_word_iff _ [1, 0]).mpr hm
  exact oddThreeSeed_NMA hseed

theorem line_two_MA : MutationAcyclic (ofTuple (alternatingLine 2)) := by
  refine ⟨[1], ?_⟩
  refine ⟨(fun i => match i.val with
    | 0 => 0 | 1 => 1 | 2 => 2 | _ => 1), ?_⟩
  decide

private theorem line_four_mul_add_iff (r n : Nat) :
    MutationAcyclic (ofTuple (alternatingLine (4 * n + r))) ↔
      MutationAcyclic (ofTuple (alternatingLine r)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hnum : 4 * (n + 1) + r = (4 * n + r) + 4 := by omega
      rw [hnum, line_periodic_MA_iff, ih]

/-- For every nonnegative parameter on this exact affine line, parity decides
MA. Evaluating the rule itself performs no mutation. -/
theorem alternatingLine_MA_iff_even (t : Nat) :
    MutationAcyclic (ofTuple (alternatingLine t)) ↔ t % 2 = 0 := by
  have hres : t % 4 = 0 ∨ t % 4 = 1 ∨ t % 4 = 2 ∨ t % 4 = 3 := by omega
  rcases hres with h0 | h1 | h2 | h3
  · have ht : t = 4 * (t / 4) + 0 := by omega
    rw [ht, line_four_mul_add_iff]
    simp [line_zero_MA] <;> omega
  · have ht : t = 4 * (t / 4) + 1 := by omega
    rw [ht, line_four_mul_add_iff]
    simp [line_one_NMA] <;> omega
  · have ht : t = 4 * (t / 4) + 2 := by omega
    rw [ht, line_four_mul_add_iff]
    simp [line_two_MA] <;> omega
  · have ht : t = 4 * (t / 4) + 3 := by omega
    rw [ht, line_four_mul_add_iff]
    simp [line_three_NMA] <;> omega

def classifyAlternatingLine (t : Nat) : Bool := decide (t % 2 = 0)

theorem classifyAlternatingLine_iff (t : Nat) :
    classifyAlternatingLine t = true ↔
      MutationAcyclic (ofTuple (alternatingLine t)) := by
  simpa only [classifyAlternatingLine, decide_eq_true_eq] using
    (alternatingLine_MA_iff_even t).symm

#print axioms oddThreeSeed_NMA
#print axioms line_two_MA
#print axioms line_three_NMA
#print axioms alternatingLine_MA_iff_even
#print axioms classifyAlternatingLine_iff

end Rank4Round8.Arithmetic
