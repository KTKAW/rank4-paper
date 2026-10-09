import Rank4ReviewRound2.UnitPrefixMinimal
import Rank4Round2.MixedUnitRelation

/-! If three unit-pair reached states are high in a count-minimal actual
witness, the first step of the alternate two-letter arc exceeds the full
ceiling. Otherwise its exact swapped endpoint and at most two high states
supply a strictly better complete witness. No pair-only excursion is assumed. -/
namespace Rank4ReviewRound2.UnitThreePrefixMinimal
open QuiverProofs Rank4Coordinator Rank4CoordinatorR2 Rank4Round2
open Rank4Round2.MixedUnitRelation Rank4ReviewRound2.PeakNormalization

theorem unit_three_two_01 (B : Matrix 4) (hs : SkewSymmetric B)
    (hu : abs (B 0 1)=1) :
    applyWord B [1,0]=relabel (applyWord B [0,1,0]) Forks.swap01 := by
  have hu' : abs (relabel B Forks.swap01 0 1)=1 := by
    change abs (B 1 0)=1
    rw [hs 1 0,abs_neg]
    exact hu
  have h := unit_two_three (relabel B Forks.swap01)
    (relabel_skew B Forks.swap01 hs) hu'
  rw [word_relabel,word_relabel] at h
  have hp0 : Forks.swap01.toFun 0=1 := rfl
  have hp1 : Forks.swap01.toFun 1=0 := rfl
  simp only [List.map_cons,List.map_nil,hp0,hp1,relabel_inverse] at h
  have hh := congrArg (fun X => relabel X Forks.swap01) h
  dsimp only at hh
  simp only [Rank4CoordinatorR2.UnitCycle.swap_twice] at hh
  exact hh

theorem unit_three_two_at (B : Matrix 4) (hs : SkewSymmetric B)
    (i j : Fin 4) (hij : i≠j) (hu : abs (B i j)=1) :
    ∃ p : Relabeling 4,applyWord B [j,i]=relabel (applyWord B [i,j,i]) p := by
  let p := pivotFrame i j
  have hp := pivotFrame_slots i j hij
  have hp0 : p.toFun 0=i := hp.1
  have hp1 : p.toFun 1=j := hp.2
  have hu' : abs (relabel B p 0 1)=1 := by
    change abs (B (p.toFun 0) (p.toFun 1))=1
    rwa [hp0,hp1]
  have h := unit_three_two_01 (relabel B p) (relabel_skew B p hs) hu'
  have hh := congrArg (fun X => relabel X p.symm) h
  rw [word_relabel,word_relabel] at hh
  change relabel (relabel (applyWord B ([1,0].map p.toFun)) p) p.symm=
    relabel (relabel (relabel (applyWord B ([0,1,0].map p.toFun)) p)
      Forks.swap01) p.symm at hh
  rw [relabel_inverse] at hh
  refine ⟨(p.trans Forks.swap01).trans p.symm,?_⟩
  simpa only [List.map_cons,List.map_nil,hp0,hp1,←relabel_trans] using hh

/-- The alternate first step must leave the whole ceiling. This is a
necessary condition for the three-letter phase, not a global unit reduction. -/
theorem three_high_unit_prefix_other_step_escapes
    (Q : Rank4Input) (M : Nat) (w : List (Fin 4))
    (ha : Acyclic (applyWord Q.val w)) (hh : PrefixHeightLe Q.val w M)
    (hCount : ∀ v,Acyclic (applyWord Q.val v) → PrefixHeightLe Q.val v M →
      overCount Q.val w (M-1)≤overCount Q.val v (M-1))
    (lead tail : List (Fin 4)) (i j : Fin 4) (hij : i≠j)
    (hw : w=lead++([i,j,i]++tail)) (hu : abs (applyWord Q.val lead i j)=1)
    (hHigh : overCount (applyWord Q.val lead) [i,j,i] (M-1)=3) :
    ¬HeightLe (mutate (applyWord Q.val lead) j) M := by
  intro hOther
  let B := applyWord Q.val lead
  have hOldCount : overCount B [i,j,i] (M-1)=3 := hHigh
  have hWhole : PrefixHeightLe Q.val (lead++([i,j,i]++tail)) M := by rwa [←hw]
  obtain ⟨hLead,hSuffix⟩ := (prefixHeight_append_iff Q.val lead ([i,j,i]++tail) M).mp hWhole
  obtain ⟨hOld,hTail⟩ := (prefixHeight_append_iff B [i,j,i] tail M).mp hSuffix
  have hStart : HeightLe B M := hLead lead [] (by simp)
  have hEnd : HeightLe (applyWord B [i,j,i]) M := hOld [i,j,i] [] (by simp)
  obtain ⟨p,he⟩ := unit_three_two_at B (word_preserves_skew Q.val lead Q.property)
    i j hij hu
  have hNewEnd : HeightLe (applyWord B [j,i]) M := by
    rw [he,heightLe_relabel_iff]
    exact hEnd
  have hNew : PrefixHeightLe B [j,i] M := by
    simp only [prefixHeight_cons,prefixHeight_nil]
    exact ⟨hStart,hOther,hNewEnd⟩
  have hNewSuffix := reroute_prefixHeight B [i,j,i] [j,i] tail p M he hNew hTail
  have hNewWhole : PrefixHeightLe Q.val (lead++([j,i]++tail.map p.invFun)) M :=
    prefixHeight_append Q.val lead _ M hLead hNewSuffix
  have hOldAcyclic : Acyclic (applyWord B ([i,j,i]++tail)) := by
    rwa [hw,applyWord_append] at ha
  have hNewAcyclic : Acyclic (applyWord Q.val (lead++([j,i]++tail.map p.invFun))) := by
    rw [applyWord_append,reroute_endpoint B [i,j,i] [j,i] tail p he]
    exact (acyclic_relabel_iff _ p).mpr hOldAcyclic
  have hCompare := hCount (lead++([j,i]++tail.map p.invFun)) hNewAcyclic hNewWhole
  have hNewCount := UnitPrefixMinimal.overCount_le_length B [j,i] (M-1)
  simp only [List.length_cons,List.length_nil] at hNewCount
  simp only [hw,overCount_append] at hCompare
  change overCount Q.val lead (M-1)+(overCount B [i,j,i] (M-1)+
      overCount (applyWord B [i,j,i]) tail (M-1))≤
    overCount Q.val lead (M-1)+(overCount B [j,i] (M-1)+
      overCount (applyWord B [j,i]) (tail.map p.invFun) (M-1)) at hCompare
  rw [he,overCount_relabel,hOldCount] at hCompare
  omega

#print axioms unit_three_two_01
#print axioms unit_three_two_at
#print axioms three_high_unit_prefix_other_step_escapes
end Rank4ReviewRound2.UnitThreePrefixMinimal
