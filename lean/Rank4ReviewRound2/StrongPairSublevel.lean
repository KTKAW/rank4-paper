import Rank4ReviewRound2.StrongPairBudget

/-! Every prefix of a bounded-end constant alternating strong-pair word lies
below H, provided the word stays in H+1 and H bounds the original scalar
budget. No minimality or maximal-block decomposition is assumed. -/
namespace Rank4ReviewRound2.StrongPairSublevel
open QuiverProofs Rank4Coordinator Rank4CoordinatorR2 Rank4Round2
open ProperObstructionSoundness StrongPairIncident StrongPairBudget

theorem bounded_alternating_prefixes
    (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4)
    (n : Nat) (Q : Rank4Input) (hma : MutationAcyclic Q.val)
    (lead : List (Fin 4)) (i j : Fin 4) (hij : i≠j) (H : Nat)
    (hBudget : scalarBudget Q.val≤H)
    (hStart : HeightLe (applyWord Q.val lead) H)
    (hCeil : ∀ k≤n,HeightLe
      (applyWord (applyWord Q.val lead) (alternatingWord i j k)) (H+1))
    (hEndState : HeightLe
      (applyWord (applyWord Q.val lead) (alternatingWord i j n)) H)
    (hPair : 2≤abs (applyWord Q.val lead i j)) :
    PrefixHeightLe (applyWord Q.val lead) (alternatingWord i j n) H := by
  induction n generalizing lead i j with
  | zero => exact (prefixHeight_nil _ H).mpr hStart
  | succ n ih =>
    let P := applyWord Q.val lead
    let nextLead := lead++[j]
    have heq : applyWord Q.val nextLead=mutate P j := by
      simp only [nextLead,applyWord_append,applyWord];rfl
    have hsP : SkewSymmetric P := word_preserves_skew Q.val lead Q.property
    have hNextPair : 2≤abs (applyWord Q.val nextLead j i) := by
      rw [heq]
      simp only [mutate,true_or,if_true,hsP j i,Int.neg_neg]
      exact hPair
    have hBack : HeightLe (mutate (applyWord Q.val nextLead) j) H := by
      rw [heq,mutation_involutive]
      exact hStart
    have hTailCeil : ∀ k≤n,HeightLe
        (applyWord (applyWord Q.val nextLead) (alternatingWord j i k)) (H+1) := by
      intro k hk
      rw [heq]
      exact hCeil (k+1) (by omega)
    have hTailEnd : HeightLe
        (applyWord (applyWord Q.val nextLead) (alternatingWord j i n)) H := by
      rw [heq]
      exact hEndState
    have hNext := actual_lead_strong_pair_return_parent_bound hExist hEnd
      Q.val Q.property hma nextLead j i (Ne.symm hij) H n hBudget
      hBack hTailCeil hTailEnd hNextPair
    have hTail := ih nextLead j i (Ne.symm hij) hNext hTailCeil hTailEnd hNextPair
    change PrefixHeightLe P (j::alternatingWord j i n) H
    apply (prefixHeight_cons P j _ H).mpr
    refine ⟨hStart,?_⟩
    rwa [heq] at hTail

#print axioms bounded_alternating_prefixes
end Rank4ReviewRound2.StrongPairSublevel
