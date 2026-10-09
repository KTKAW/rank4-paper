import Rank4Invariant.OneStepCoverSyntax
import QuiverProofs.BoundedClassificationCompletion

/-!
A fixed finite polynomial-sign classifier for the box of rank-four integer
quivers whose six upper entries have absolute value at most two.  The syntax
uses the certified acyclic/MA target and repeatedly pulls it back through
all four mutations and all 729 exact input sign chambers.  The lower
triangle is fixed by skew-symmetry.  No input-dependent search appears in
the syntax.

The true answer is sound on every six-tuple.  The false answer is sound only
under `BoxTwo`, through the archived bounded-classification theorem.
-/

namespace Rank4Round4.Formula
open Rank4Formula Rank4Invariant QuiverProofs QuiverProofs.Census

/-- The explicit admissible domain for this restricted classifier. -/
def BoxTwo (q : SixTuple) : Prop :=
  ∀ i : Fin 6, -2 ≤ q i ∧ q i ≤ 2

theorem boxTwo_boundedTwo (q : SixTuple) (hq : BoxTwo q) :
    BoundedTwo (ofTuple q) := by
  intro i j
  have h0 := hq 0
  have h1 := hq 1
  have h2 := hq 2
  have h3 := hq 3
  have h4 := hq 4
  have h5 := hq 5
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases hi with rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl <;>
      simp [ofTuple, ofSix] <;> omega

theorem boundedTwo_boxTwo (q : SixTuple)
    (hq : BoundedTwo (ofTuple q)) : BoxTwo q := by
  intro i
  have h0 : -2 ≤ q 0 ∧ q 0 ≤ 2 := by simpa [ofTuple, ofSix] using hq 0 1
  have h1 : -2 ≤ q 1 ∧ q 1 ≤ 2 := by simpa [ofTuple, ofSix] using hq 0 2
  have h2 : -2 ≤ q 2 ∧ q 2 ≤ 2 := by simpa [ofTuple, ofSix] using hq 0 3
  have h3 : -2 ≤ q 3 ∧ q 3 ≤ 2 := by simpa [ofTuple, ofSix] using hq 1 2
  have h4 : -2 ≤ q 4 ∧ q 4 ≤ 2 := by simpa [ofTuple, ofSix] using hq 1 3
  have h5 : -2 ≤ q 5 ∧ q 5 ≤ 2 := by simpa [ofTuple, ofSix] using hq 2 3
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

/-- A finite polynomial-sign formula. Its construction depends only on the
literal natural number `depth`, never on the input tuple. -/
def depthSyntax : Nat → Formula
  | 0 => targetSyntax
  | n + 1 => .or targetSyntax (oneStepPullbackSyntax (depthSyntax n))

theorem depthSyntax_sound (n : Nat) (q : SixTuple)
    (h : (depthSyntax n).eval q = true) :
    MutationAcyclic (ofTuple q) := by
  induction n generalizing q with
  | zero =>
      exact target_sound q ((targetSyntax_eval q).mp h)
  | succ n ih =>
      change (targetSyntax.eval q ||
        (oneStepPullbackSyntax (depthSyntax n)).eval q) = true at h
      simp only [Bool.or_eq_true] at h
      rcases h with ht | hp
      · exact target_sound q ((targetSyntax_eval q).mp ht)
      · obtain ⟨k, hk⟩ :=
          (oneStepPullbackSyntax_eval (depthSyntax n) q).mp hp
        have hm := ih (Rank4Round3.mutatedUpper q k) hk
        rw [Rank4Round3.mutatedUpper_matrix] at hm
        exact (mutationAcyclic_iff (ofTuple q) k).mp hm

theorem depthSyntax_complete_of_short (n : Nat) :
    ∀ (q : SixTuple) (w : List (Fin 4)),
      w.length ≤ n → Acyclic (applyWord (ofTuple q) w) →
        (depthSyntax n).eval q = true := by
  induction n with
  | zero =>
      intro q w hw ha
      have he : w = [] := List.length_eq_zero_iff.mp (by omega)
      subst w
      exact (targetSyntax_eval q).mpr (Or.inl ha)
  | succ n ih =>
      intro q w hw ha
      change (targetSyntax.eval q ||
        (oneStepPullbackSyntax (depthSyntax n)).eval q) = true
      cases w with
      | nil =>
          simp only [Bool.or_eq_true]
          exact Or.inl ((targetSyntax_eval q).mpr (Or.inl ha))
      | cons k rest =>
          have hrest : Acyclic
              (applyWord (ofTuple (Rank4Round3.mutatedUpper q k)) rest) := by
            rw [Rank4Round3.mutatedUpper_matrix]
            exact ha
          have htail := ih (Rank4Round3.mutatedUpper q k) rest
            (by simpa using hw) hrest
          simp only [Bool.or_eq_true]
          exact Or.inr
            ((oneStepPullbackSyntax_eval (depthSyntax n) q).mpr
              ⟨k, htail⟩)

/-- The exact finite formula on the six-coordinate box `[-2,2]^6`. -/
def boundedTwoDepthThreeSyntax : Formula := depthSyntax 3

/-- The MA label is sound without a box hypothesis. -/
theorem boundedTwoDepthThree_true_sound (q : SixTuple)
    (h : boundedTwoDepthThreeSyntax.eval q = true) :
    MutationAcyclic (ofTuple q) :=
  depthSyntax_sound 3 q h

/-- On the bounded input domain, every MA input satisfies the formula. -/
theorem boundedTwoDepthThree_MA_complete (q : SixTuple)
    (hq : BoxTwo q) (hm : MutationAcyclic (ofTuple q)) :
    boundedTwoDepthThreeSyntax.eval q = true := by
  have hs : SkewSymmetric (ofTuple q) :=
    ofSix_skew (q 0) (q 1) (q 2) (q 3) (q 4) (q 5)
  obtain ⟨w, hw, ha⟩ :=
    (BoundedClassification.bounded_MA_iff_three_mutations
      (ofTuple q) hs (boxTwo_boundedTwo q hq)).mp hm
  exact depthSyntax_complete_of_short 3 q w hw ha

theorem boundedTwoDepthThree_MA_iff (q : SixTuple) (hq : BoxTwo q) :
    boundedTwoDepthThreeSyntax.eval q = true ↔
      MutationAcyclic (ofTuple q) :=
  ⟨boundedTwoDepthThree_true_sound q,
    boundedTwoDepthThree_MA_complete q hq⟩

/-- Under the box restriction, a false answer has a proved NMA meaning. -/
theorem boundedTwoDepthThree_false_sound (q : SixTuple)
    (hq : BoxTwo q)
    (h : boundedTwoDepthThreeSyntax.eval q = false) :
    ¬ MutationAcyclic (ofTuple q) := by
  intro hm
  have ht := boundedTwoDepthThree_MA_complete q hq hm
  rw [h] at ht
  contradiction

theorem boundedTwoDepthThree_NMA_iff (q : SixTuple) (hq : BoxTwo q) :
    boundedTwoDepthThreeSyntax.eval q = false ↔
      ¬ MutationAcyclic (ofTuple q) := by
  constructor
  · exact boundedTwoDepthThree_false_sound q hq
  · intro hn
    cases hv : boundedTwoDepthThreeSyntax.eval q with
    | false => rfl
    | true => exact False.elim (hn (boundedTwoDepthThree_true_sound q hv))

/-- One level of this hierarchy is exactly the earlier one-step cover. -/
theorem depthSyntax_one_eq_oneStepCoverSyntax :
    depthSyntax 1 = oneStepCoverSyntax := rfl

/-- The published gap is an exact strict extension at depth two. -/
theorem gap_depth_one_false : (depthSyntax 1).eval gap = false := by
  rw [depthSyntax_one_eq_oneStepCoverSyntax]
  cases h : oneStepCoverSyntax.eval gap with
  | false => rfl
  | true =>
      exact False.elim
        (gap_outside_oneStepCover ((oneStepCoverSyntax_eval gap).mp h))

theorem gap_depth_two_true : (depthSyntax 2).eval gap = true := by
  apply depthSyntax_complete_of_short 2 gap [0, 3] (by decide)
  refine ⟨(fun i => match i.val with
    | 0 => 0 | 1 => 3 | 2 => 1 | _ => 2), ?_⟩
  decide

#print axioms boxTwo_boundedTwo
#print axioms boundedTwo_boxTwo
#print axioms depthSyntax_sound
#print axioms depthSyntax_complete_of_short
#print axioms boundedTwoDepthThree_true_sound
#print axioms boundedTwoDepthThree_MA_complete
#print axioms boundedTwoDepthThree_MA_iff
#print axioms boundedTwoDepthThree_false_sound
#print axioms boundedTwoDepthThree_NMA_iff
#print axioms gap_depth_one_false
#print axioms gap_depth_two_true

end Rank4Round4.Formula
