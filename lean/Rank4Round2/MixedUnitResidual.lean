import Rank4Round2.MixedUnitGuard
import Rank4CoordinatorR2.ResidualUnitExcursion

/-! A concrete proved branch of the corrected live unit-profile obligation.
The actual triangle frame and five-letter return pattern remain explicit. -/
namespace Rank4Round2.MixedUnitResidual
open QuiverProofs Rank4Coordinator Rank4CoordinatorR2 Rank4Round2
open MixedUnitRelation MixedUnitFrame ResidualUnitExcursion
open Rank4ReviewRound2.PeakNormalization

theorem pattern_lowering (Q : Rank4Input) (H : Nat)
    (w lead : List (Fin 4)) (i j k : Fin 4) (mid tail : List (Fin 4))
    (hp : Packet Q H w lead i j mid tail) (hmid : mid=[k,i,k])
    (p : Relabeling 4) (r : Bool) (c e f : Int)
    (h0 : p.toFun 0=i) (h1 : p.toFun 1=j) (h2 : p.toFun 2=k)
    (hrep : signedFrame (applyWord Q.val lead) p r=R c e f) :
    ∃ v,Acyclic (applyWord Q.val v) ∧ PrefixHeightLe Q.val v (H+1) ∧
      overCount Q.val v H<overCount Q.val w H ∧ v.length+2=w.length := by
  have hletters : old.map p.toFun=[i,j,k,i,k] := by
    simp only [old,List.map_cons,List.map_nil,h0,h1,h2]
  have hw : w=lead++oldFrame p tail := by
    rw [oldFrame_eq,hletters]
    simpa only [hmid,List.cons_append,List.nil_append] using hp.split
  have hEnd : HeightLe (applyWord (applyWord Q.val lead) (old.map p.toFun)) H := by
    rw [hletters]
    change HeightLe (applyWord (mutate (applyWord Q.val lead) i) [j,k,i,k]) H
    simpa only [hmid] using hp.lowReturn
  have hHigh : ¬HeightLe (mutate (applyWord Q.val lead) (p.toFun 0)) H := by
    simpa only [h0] using hp.highFirst
  have hWhole : PrefixHeightLe Q.val (lead++oldFrame p tail) (H+1) := by
    rw [←hw]
    exact hp.ceiling
  have ha : Acyclic (applyWord Q.val (lead++oldFrame p tail)) := by
    rw [←hw]
    exact hp.acyclic
  obtain ⟨hn,han,hc,hl⟩ := MixedUnitGuard.whole_witness_progress Q.val Q.property
    lead tail p r c e f H hrep hp.lowLeft hHigh hEnd hWhole ha
  refine ⟨lead++newFrame p tail,han,hn,?_,?_⟩
  · rwa [←hw] at hc
  · rwa [←hw] at hl

theorem pattern_impossible (Q : Rank4Input) (H : Nat)
    (w lead : List (Fin 4)) (i j k : Fin 4) (mid tail : List (Fin 4))
    (hp : Packet Q H w lead i j mid tail) (hmid : mid=[k,i,k])
    (p : Relabeling 4) (r : Bool) (c e f : Int)
    (h0 : p.toFun 0=i) (h1 : p.toFun 1=j) (h2 : p.toFun 2=k)
    (hrep : signedFrame (applyWord Q.val lead) p r=R c e f) : False := by
  obtain ⟨v,hav,hv,hc,_⟩ := pattern_lowering Q H w lead i j k mid tail hp hmid
    p r c e f h0 h1 h2 hrep
  have hm := hp.countMinimum v hav hv
  omega

#print axioms pattern_lowering
#print axioms pattern_impossible
end Rank4Round2.MixedUnitResidual
