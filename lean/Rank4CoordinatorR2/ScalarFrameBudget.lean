import Rank4CoordinatorR2.EndpointBudget
import Rank4ReviewRound2.PeakNormalization
import Mathlib.Tactic.Ring

/-! Every scalar in every signed vertex frame is bounded by the original
input's six computable cyclic scalars. No proper-class covariance is assumed. -/
namespace Rank4CoordinatorR2.ScalarFrameBudget
open QuiverProofs Rank4Coordinator Rank4CoordinatorR2
open Census ProperOrder Rank4ReviewRound2.PeakNormalization

def reflectOrder : Relabeling 4 :=
  ⟨fun i => ⟨3-i.val,by omega⟩,fun i => ⟨3-i.val,by omega⟩,
   by intro i; apply Fin.ext; simp; omega,
   by intro i; apply Fin.ext; simp; omega⟩

theorem reverse_markov (B : Matrix 4) (hs : SkewSymmetric B) (q : CyclicOrder) :
    orderMarkov (reverse B) q=orderMarkov B (q.trans reflectOrder) := by
  change Algebra.markov (-B (q.toFun 0) (q.toFun 1))
    (-B (q.toFun 0) (q.toFun 2)) (-B (q.toFun 0) (q.toFun 3))
    (-B (q.toFun 1) (q.toFun 2)) (-B (q.toFun 1) (q.toFun 3))
    (-B (q.toFun 2) (q.toFun 3))=
    Algebra.markov (B (q.toFun 3) (q.toFun 2)) (B (q.toFun 3) (q.toFun 1))
    (B (q.toFun 3) (q.toFun 0)) (B (q.toFun 2) (q.toFun 1))
    (B (q.toFun 2) (q.toFun 0)) (B (q.toFun 1) (q.toFun 0))
  rw [hs (q.toFun 3) (q.toFun 2),hs (q.toFun 3) (q.toFun 1),
    hs (q.toFun 3) (q.toFun 0),hs (q.toFun 2) (q.toFun 1),
    hs (q.toFun 2) (q.toFun 0),hs (q.toFun 1) (q.toFun 0)]
  unfold Algebra.markov Algebra.squareSum Algebra.cycleTerms
  ring

theorem signed_frame_scalar_budget_bound (B : Matrix 4) (hs : SkewSymmetric B)
    (p : Relabeling 4) (r : Bool) (q : CyclicOrder) :
    (orderMarkov (signedFrame B p r) q).natAbs≤scalarBudget B := by
  cases r
  · change (orderMarkov B (p.trans q)).natAbs≤scalarBudget B
    exact cyclic_scalar_budget B hs _
  · change (orderMarkov (reverse (relabel B p)) q).natAbs≤scalarBudget B
    rw [reverse_markov (relabel B p) (relabel_skew B p hs) q]
    change (orderMarkov B (p.trans (q.trans reflectOrder))).natAbs≤scalarBudget B
    exact cyclic_scalar_budget B hs _

#print axioms reflectOrder
#print axioms reverse_markov
#print axioms signed_frame_scalar_budget_bound
end Rank4CoordinatorR2.ScalarFrameBudget
