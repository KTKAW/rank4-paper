import QuiverProofs.ProperEndpoint
import Rank4CoordinatorR2.EndpointBudget
import Rank4StructureRound2.SuperScalarPeak

/-! Reuse of the existing unconditional rank-four endpoint bridge. The
31 additional frozen source dependencies were rebuilt privately. This
removes the endpoint premise from the live scalar route; it does not prove
MAHasTotalProper4 or any bound on intermediate states. -/
namespace Rank4CoordinatorR2.EndpointFoundation
open QuiverProofs Rank4Coordinator Rank4CoordinatorR2
open ProperOrder ProperMutation ProperObstructionSoundness

theorem endpoint_bridge : EndpointTopological4 :=
  ProperEndpoint.endpointTopological4

theorem acyclic_endpoint_budget (hExist : MAHasTotalProper4)
    (Q : Rank4Input) (w : List (Fin 4))
    (ha : Acyclic (applyWord Q.val w)) :
    HeightLe (applyWord Q.val w) (endpointHeightBudget Q) :=
  Rank4CoordinatorR2.acyclic_endpoint_budget hExist endpoint_bridge Q w ha

theorem MA_totalProper_pfaffian_bound (B : Matrix 4)
    (hs : SkewSymmetric B) (hma : MutationAcyclic B)
    (p : CyclicOrder) (hp : TotalProper B p) :
    2*abs (matrixPfaffian B)≤orderMarkov B p :=
  QuiverProofs.Rank4StructureRound2.SuperScalarPeak.MA_totalProper_pfaffian_bound
    endpoint_bridge B hs hma p hp

#check endpoint_bridge
#print axioms ProperEndpoint.acyclic_oneStep_endpoint
#print axioms endpoint_bridge
#print axioms acyclic_endpoint_budget
#print axioms MA_totalProper_pfaffian_bound
end Rank4CoordinatorR2.EndpointFoundation
