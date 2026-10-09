import Rank4Round2.UnitFirstSwitchPhase
import Rank4ReviewRound2.UnitThreePrefixMinimal

/-! The three-letter actual unit phase additionally forces its alternative
first child above the full ceiling. This is necessary profile geometry;
it does not assert a scalar barrier or eliminate that phase. -/
namespace Rank4Round2.UnitFirstSwitchEscape
open QuiverProofs Rank4Coordinator Rank4CoordinatorR2 Rank4Round2
open ResidualUnitExcursion UnitFirstSwitchPhase

theorem packet_three_phase_escape (Q : Rank4Input) (H : Nat)
    (w lead : List (Fin 4)) (i j k : Fin 4) (mid post tail : List (Fin 4))
    (hp : Packet Q H w lead i j mid tail)
    (he : (i::j::mid)=[i,j,i]++k::post) :
    ¬HeightLe (mutate (applyWord Q.val lead) j) (H+1) := by
  have hw : w=lead++([i,j,i]++((k::post)++tail)) := by
    rw [hp.split,he,List.append_assoc]
  have hu : abs (applyWord Q.val lead i j)=1 := by
    have hh := hp.unit
    simpa [mutate] using hh
  have hCount : ∀ v,Acyclic (applyWord Q.val v) → PrefixHeightLe Q.val v (H+1) →
      overCount Q.val w ((H+1)-1)≤overCount Q.val v ((H+1)-1) := by
    simpa only [Nat.add_sub_cancel] using hp.countMinimum
  have hHigh : ∀ u v,[i,j,i]=u++v → u≠[] →
      ¬HeightLe (applyWord (applyWord Q.val lead) u) H := by
    intro u v huv hu
    apply proper_block_high Q H w lead i j mid tail hp u (v++k::post)
    · rw [he,huv,List.append_assoc]
    · exact hu
    · simp
  have hc : overCount (applyWord Q.val lead) [i,j,i] ((H+1)-1)=3 := by
    simp only [Nat.add_sub_cancel]
    have hh := Rank4ReviewRound2.UnitPrefixMinimal.overCount_eq_length_of_high_prefixes
      (applyWord Q.val lead) [i,j,i] H hHigh
    simpa only [List.length_cons,List.length_nil] using hh
  exact Rank4ReviewRound2.UnitThreePrefixMinimal.three_high_unit_prefix_other_step_escapes
    Q (H+1) w hp.acyclic hp.ceiling hCount lead ((k::post)++tail) i j hp.distinct hw hu hc

theorem packet_two_phases_with_escape (Q : Rank4Input) (H : Nat)
    (w lead : List (Fin 4)) (i j : Fin 4) (mid tail : List (Fin 4))
    (hp : Packet Q H w lead i j mid tail) :
    ∃ k post,k≠i ∧ k≠j ∧
      ((i::j::mid)=[i,j]++k::post ∨
       ((i::j::mid)=[i,j,i]++k::post ∧
        ¬HeightLe (mutate (applyWord Q.val lead) j) (H+1))) := by
  obtain ⟨pre,k,post,he,hki,hkj,hpre⟩ := packet_first_switch_two_phases Q H w lead i j mid tail hp
  refine ⟨k,post,hki,hkj,?_⟩
  rcases hpre with hpre|hpre
  · exact Or.inl (by rwa [hpre] at he)
  · have he' : (i::j::mid)=[i,j,i]++k::post := by rwa [hpre] at he
    exact Or.inr ⟨he',packet_three_phase_escape Q H w lead i j k mid post tail hp he'⟩

#print axioms packet_three_phase_escape
#print axioms packet_two_phases_with_escape
end Rank4Round2.UnitFirstSwitchEscape
