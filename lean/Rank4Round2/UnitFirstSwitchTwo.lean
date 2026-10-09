import Rank4Round2.UnitFirstSwitchEscape
import Rank4CoordinatorR2.UnitThreeActual

/-! Eliminate the three-letter phase in actual corrected residual packets.
The remaining first outside pivot follows exactly the two entering labels;
its triangle and later return geometry are still separate obligations. -/
namespace Rank4Round2.UnitFirstSwitchTwo
open QuiverProofs Rank4Coordinator Rank4CoordinatorR2 Rank4Round2
open ResidualUnitExcursion UnitFirstSwitchPhase UnitFirstSwitchEscape

theorem packet_no_three_phase (Q : Rank4Input) (H : Nat)
    (w lead : List (Fin 4)) (i j k : Fin 4) (mid post tail : List (Fin 4))
    (hp : Packet Q H w lead i j mid tail)
    (he : (i::j::mid)=[i,j,i]++k::post) : False := by
  have hOut := packet_three_phase_escape Q H w lead i j k mid post tail hp he
  have hw : w=lead++([i,j,i]++((k::post)++tail)) := by
    rw [hp.split,he,List.append_assoc]
  have hWhole : PrefixHeightLe Q.val (lead++([i,j,i]++((k::post)++tail))) (H+1) := by
    rw [←hw]
    exact hp.ceiling
  have hSuffix := (prefixHeight_append_iff Q.val lead _ (H+1)).mp hWhole
  have hPath := ((prefixHeight_append_iff (applyWord Q.val lead) [i,j,i]
    ((k::post)++tail) (H+1)).mp hSuffix.2).1
  have hThird : ¬HeightLe (applyWord (applyWord Q.val lead) [i,j,i]) H :=
    proper_block_high Q H w lead i j mid tail hp [i,j,i] (k::post) he (by simp) (by simp)
  have hUnit : abs (applyWord Q.val lead i j)=1 := by
    have hh := hp.unit
    simpa [mutate] using hh
  have hBudget : scalarBudget Q.val≤H := by
    have hh := hp.budget
    unfold endpointHeightBudget at hh
    omega
  have hma : MutationAcyclic Q.val := ⟨w,hp.acyclic⟩
  have hBound := UnitThreeActual.actual_unit_three_alternative_bounded Q hma lead i j
    hp.distinct H hBudget hp.lowLeft hPath hp.highFirst hThird hUnit
  exact hOut hBound

theorem packet_first_switch_two_only (Q : Rank4Input) (H : Nat)
    (w lead : List (Fin 4)) (i j : Fin 4) (mid tail : List (Fin 4))
    (hp : Packet Q H w lead i j mid tail) :
    ∃ k post,(i::j::mid)=[i,j]++k::post ∧ k≠i ∧ k≠j := by
  obtain ⟨k,post,hki,hkj,hPhase⟩ := packet_two_phases_with_escape Q H w lead i j mid tail hp
  rcases hPhase with hTwo|hThree
  · exact ⟨k,post,hTwo,hki,hkj⟩
  · exact False.elim (packet_no_three_phase Q H w lead i j k mid post tail hp hThree.1)

#print axioms packet_no_three_phase
#print axioms packet_first_switch_two_only
end Rank4Round2.UnitFirstSwitchTwo
