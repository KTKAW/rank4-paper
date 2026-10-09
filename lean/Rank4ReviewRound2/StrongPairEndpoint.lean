import Rank4ReviewRound2.StrongPairSublevel
import Rank4CoordinatorR2.EndpointFoundation

/-! Discharge the endpoint bridge using the audited existing unconditional
foundation proof. MA-to-total-proper existence remains explicit. -/
namespace Rank4ReviewRound2.StrongPairEndpoint
open QuiverProofs Rank4Coordinator Rank4CoordinatorR2
open ProperObstructionSoundness StrongPairIncident

theorem bounded_alternating_prefixes
    (hExist : MAHasTotalProper4)
    (n : Nat) (Q : Rank4Input) (hma : MutationAcyclic Q.val)
    (lead : List (Fin 4)) (i j : Fin 4) (hij : i≠j) (H : Nat)
    (hBudget : scalarBudget Q.val≤H)
    (hStart : HeightLe (applyWord Q.val lead) H)
    (hCeil : ∀ k≤n,HeightLe
      (applyWord (applyWord Q.val lead) (alternatingWord i j k)) (H+1))
    (hEndState : HeightLe
      (applyWord (applyWord Q.val lead) (alternatingWord i j n)) H)
    (hPair : 2≤abs (applyWord Q.val lead i j)) :
    PrefixHeightLe (applyWord Q.val lead) (alternatingWord i j n) H :=
  StrongPairSublevel.bounded_alternating_prefixes hExist EndpointFoundation.endpoint_bridge
    n Q hma lead i j hij H hBudget hStart hCeil hEndState hPair

#print axioms bounded_alternating_prefixes
end Rank4ReviewRound2.StrongPairEndpoint
