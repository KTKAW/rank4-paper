import QuiverProofs.MAHasTotalProper4Completion
import Rank4CoordinatorR2.ConstantPairMinimal
import Rank4CoordinatorR2.FirstStrongEntry
import Rank4CoordinatorR2.FramedNonzeroExit

/-! Instantiate the live classification-route foundations with the audited
unconditional project theorem. The new import closure is pinned in
foundation-closure-integration-manifest.json; its dependencies are borrowed
from the separately reviewed canonical build, and the final source was
freshly compiled in this team's private build. No path bound follows here.
-/
namespace Rank4CoordinatorR2.Foundation
open QuiverProofs Rank4Coordinator Rank4CoordinatorR2 Rank4Round2
open ProperObstructionSoundness Rank4ReviewRound2.StrongPairIncident

theorem ma_existence : MAHasTotalProper4 :=
  MAHasTotalProper4Completion.maHasTotalProper4

theorem acyclic_endpoint_budget (Q : Rank4Input) (w : List (Fin 4))
    (ha : Acyclic (applyWord Q.val w)) :
    HeightLe (applyWord Q.val w) (endpointHeightBudget Q) :=
  EndpointFoundation.acyclic_endpoint_budget ma_existence Q w ha

theorem bounded_alternating_prefixes
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
  Rank4ReviewRound2.StrongPairEndpoint.bounded_alternating_prefixes ma_existence
    n Q hma lead i j hij H hBudget hStart hCeil hEndState hPair

theorem constant_pair_has_zero_overCount
    (Q : Rank4Input) (M : Nat) (w : List (Fin 4))
    (ha : Acyclic (applyWord Q.val w)) (hh : PrefixHeightLe Q.val w M)
    (hcount : ∀ v, Acyclic (applyWord Q.val v) → PrefixHeightLe Q.val v M →
      overCount Q.val w (M-1)≤overCount Q.val v (M-1))
    (hlength : ∀ v, Acyclic (applyWord Q.val v) → PrefixHeightLe Q.val v M →
      overCount Q.val v (M-1)=overCount Q.val w (M-1) → w.length≤v.length)
    (hBudget : endpointHeightBudget Q≤M-1)
    (lead old tail : List (Fin 4)) (i j : Fin 4) (hij : i≠j)
    (hw : w=lead++(old++tail)) (hp : ∀ k∈old,k=i ∨ k=j)
    (hLeft : HeightLe (applyWord Q.val lead) (M-1))
    (hRight : HeightLe (applyWord Q.val (lead++old)) (M-1)) :
    overCount (applyWord Q.val lead) old (M-1)=0 :=
  ConstantPairMinimal.constant_pair_has_zero_overCount ma_existence Q M w ha hh
    hcount hlength hBudget lead old tail i j hij hw hp hLeft hRight

theorem third_pivot_in_high_excursion
    (Q : Rank4Input) (M : Nat) (w : List (Fin 4))
    (ha : Acyclic (applyWord Q.val w)) (hh : PrefixHeightLe Q.val w M)
    (hcount : ∀ v, Acyclic (applyWord Q.val v) → PrefixHeightLe Q.val v M →
      overCount Q.val w (M-1)≤overCount Q.val v (M-1))
    (hlength : ∀ v, Acyclic (applyWord Q.val v) → PrefixHeightLe Q.val v M →
      overCount Q.val v (M-1)=overCount Q.val w (M-1) → w.length≤v.length)
    (hBudget : endpointHeightBudget Q≤M-1)
    (lead old tail : List (Fin 4)) (i j : Fin 4) (hij : i≠j)
    (hw : w=lead++(old++tail))
    (hLeft : HeightLe (applyWord Q.val lead) (M-1))
    (hRight : HeightLe (applyWord Q.val (lead++old)) (M-1))
    (hover : 0<overCount (applyWord Q.val lead) old (M-1)) :
    ∃ k∈old,k≠i ∧ k≠j :=
  ConstantPairMinimal.third_pivot_in_high_excursion ma_existence Q M w ha hh
    hcount hlength hBudget lead old tail i j hij hw hLeft hRight hover

#print axioms ma_existence
#print axioms acyclic_endpoint_budget
#print axioms bounded_alternating_prefixes
#print axioms constant_pair_has_zero_overCount
#print axioms third_pivot_in_high_excursion
end Rank4CoordinatorR2.Foundation
