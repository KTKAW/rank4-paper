import Rank4CoordinatorR2.Foundation
import Rank4CoordinatorR2.UnitBlock

/-! A profile-minimal actual witness cannot spend four high reached states
inside any constant unit pair, even if the unit block ends high. This uses
short routing at the full ceiling, with exact permutation of the tail.
It does not assert that a unit excursion stays in that pair. -/
namespace Rank4ReviewRound2.UnitPrefixMinimal
open QuiverProofs Rank4Coordinator Rank4CoordinatorR2 Rank4Round2
open ProperObstructionSoundness

 theorem overCount_le_length (B : Matrix 4) (w : List (Fin 4)) (H : Nat) :
    overCount B w H≤w.length := by
  induction w generalizing B with
  | nil => simp only [overCount,List.length_nil];omega
  | cons k w ih =>
    have ht := ih (mutate B k)
    simp only [overCount,List.length_cons]
    unfold overBit
    split_ifs <;> omega

theorem overCount_eq_length_of_high_prefixes
    (B : Matrix 4) (w : List (Fin 4)) (H : Nat)
    (hHigh : ∀ u v,w=u++v → u≠[] → ¬HeightLe (applyWord B u) H) :
    overCount B w H=w.length := by
  induction w generalizing B with
  | nil => rfl
  | cons k w ih =>
    have hk := hHigh [k] w rfl (by simp)
    change ¬HeightLe (mutate B k) H at hk
    have ht : ∀ u v,w=u++v → u≠[] →
        ¬HeightLe (applyWord (mutate B k) u) H := by
      intro u v he _hu
      have hh := hHigh (k::u) v (by simpa only [List.cons_append] using congrArg (List.cons k) he)
        (by simp)
      exact hh
    simp only [overCount,overBit,if_neg hk,ih (mutate B k) ht,List.length_cons]
    omega

/-- Count minimality bounds every unit block by three high reached states.
No low block endpoint or pair-only whole excursion premise is used. -/
theorem constant_unit_block_overCount_le_three
    (Q : Rank4Input) (M : Nat) (w : List (Fin 4))
    (ha : Acyclic (applyWord Q.val w)) (hh : PrefixHeightLe Q.val w M)
    (hCount : ∀ v,Acyclic (applyWord Q.val v) → PrefixHeightLe Q.val v M →
      overCount Q.val w (M-1)≤overCount Q.val v (M-1))
    (lead old tail : List (Fin 4)) (i j : Fin 4) (hij : i≠j)
    (hw : w=lead++(old++tail)) (hu : abs (applyWord Q.val lead i j)=1)
    (hp : ∀ k∈old,k=i ∨ k=j) :
    overCount (applyWord Q.val lead) old (M-1)≤3 := by
  let B := applyWord Q.val lead
  change overCount B old (M-1)≤3
  have hWhole : PrefixHeightLe Q.val (lead++(old++tail)) M := by rwa [←hw]
  obtain ⟨hLead,hSuffix⟩ := (prefixHeight_append_iff Q.val lead (old++tail) M).mp hWhole
  obtain ⟨hOld,hTail⟩ := (prefixHeight_append_iff B old tail M).mp hSuffix
  have hStart : HeightLe B M := hLead lead [] (by simp)
  have hEnd : HeightLe (applyWord B old) M := hOld old [] (by simp)
  have hsB := word_preserves_skew Q.val lead Q.property
  have hmaB : MutationAcyclic B := (mutationAcyclic_word_iff Q.val lead).mpr ⟨w,ha⟩
  obtain ⟨new,p,hLength,hNew,he⟩ := UnitBlock.arbitrary_unit_pair_route
    Foundation.ma_existence EndpointFoundation.endpoint_bridge B hsB hmaB
    i j hij hu M hStart old hp hEnd
  have hNewSuffix := reroute_prefixHeight B old new tail p M he hNew hTail
  have hNewWhole : PrefixHeightLe Q.val (lead++(new++tail.map p.invFun)) M :=
    prefixHeight_append Q.val lead _ M hLead hNewSuffix
  have hOldAcyclic : Acyclic (applyWord B (old++tail)) := by
    rwa [hw,applyWord_append] at ha
  have hNewAcyclic : Acyclic (applyWord Q.val (lead++(new++tail.map p.invFun))) := by
    rw [applyWord_append,reroute_endpoint B old new tail p he]
    exact (acyclic_relabel_iff _ p).mpr hOldAcyclic
  have hCompare := hCount (lead++(new++tail.map p.invFun)) hNewAcyclic hNewWhole
  have hNewCount := overCount_le_length B new (M-1)
  simp only [hw,overCount_append] at hCompare
  change overCount Q.val lead (M-1)+(overCount B old (M-1)+
      overCount (applyWord B old) tail (M-1))≤
    overCount Q.val lead (M-1)+(overCount B new (M-1)+
      overCount (applyWord B new) (tail.map p.invFun) (M-1)) at hCompare
  rw [he,overCount_relabel] at hCompare
  omega

/-- A wholly high constant-unit prefix in such a witness has at most three
letters. The next pivot may leave the pair; this is a finite phase bound. -/
theorem high_constant_unit_block_length_le_three
    (Q : Rank4Input) (M : Nat) (w : List (Fin 4))
    (ha : Acyclic (applyWord Q.val w)) (hh : PrefixHeightLe Q.val w M)
    (hCount : ∀ v,Acyclic (applyWord Q.val v) → PrefixHeightLe Q.val v M →
      overCount Q.val w (M-1)≤overCount Q.val v (M-1))
    (lead old tail : List (Fin 4)) (i j : Fin 4) (hij : i≠j)
    (hw : w=lead++(old++tail)) (hu : abs (applyWord Q.val lead i j)=1)
    (hp : ∀ k∈old,k=i ∨ k=j)
    (hHigh : ∀ u v,old=u++v → u≠[] →
      ¬HeightLe (applyWord (applyWord Q.val lead) u) (M-1)) :
    old.length≤3 := by
  have hBound := constant_unit_block_overCount_le_three Q M w ha hh hCount
    lead old tail i j hij hw hu hp
  rwa [overCount_eq_length_of_high_prefixes _ old (M-1) hHigh] at hBound

#print axioms overCount_le_length
#print axioms overCount_eq_length_of_high_prefixes
#print axioms constant_unit_block_overCount_le_three
#print axioms high_constant_unit_block_length_le_three
end Rank4ReviewRound2.UnitPrefixMinimal
