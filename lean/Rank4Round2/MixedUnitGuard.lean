import Rank4Round2.MixedUnitFrame
import Rank4StructureRound2.MixedUnitHeight

/-! The general fourth-row height guard combined with the two-pentagon
identity supplies actual complete-witness count progress. The five-letter
pattern and its low endpoint remain explicit; no global pattern coverage
is asserted. -/
namespace Rank4Round2.MixedUnitGuard
open QuiverProofs Rank4Coordinator Rank4Round2 MixedUnitRelation MixedUnitFrame
open Rank4ReviewRound2.PeakNormalization

theorem local_progress (c e f : Int) (H : Nat)
    (hR : HeightLe (R c e f) H) (hHigh : ¬HeightLe (mutate (R c e f) 0) H)
    (hOld : PrefixHeightLe (R c e f) old (H+1))
    (hEnd : HeightLe (applyWord (R c e f) old) H) :
    PrefixHeightLe (R c e f) new H ∧ 0<overCount (R c e f) old H := by
  refine ⟨QuiverProofs.Rank4StructureRound2.MixedUnitHeight.guarded_new_prefix_below
    c e f H hR hHigh hOld hEnd,?_⟩
  simp only [old,overCount,overBit,if_neg hHigh]
  omega

theorem framed_tail_progress (B : Matrix 4) (hs : SkewSymmetric B)
    (p : Relabeling 4) (r : Bool) (c e f : Int) (H : Nat)
    (hrep : signedFrame B p r=R c e f)
    (hR : HeightLe B H) (hHigh : ¬HeightLe (mutate B (p.toFun 0)) H)
    (hEnd : HeightLe (applyWord B (old.map p.toFun)) H)
    (tail : List (Fin 4)) (hOld : PrefixHeightLe B (oldFrame p tail) (H+1))
    (ha : Acyclic (applyWord B (oldFrame p tail))) :
    PrefixHeightLe B (newFrame p tail) (H+1) ∧
    Acyclic (applyWord B (newFrame p tail)) ∧
    overCount B (newFrame p tail) H<overCount B (oldFrame p tail) H ∧
    (newFrame p tail).length+2=(oldFrame p tail).length := by
  have hRN : HeightLe (R c e f) H := by
    rw [←hrep,signedFrame_height]
    exact hR
  have hHighN : ¬HeightLe (mutate (R c e f) 0) H := by
    rw [←hrep,signedFrame_mutate,signedFrame_height]
    exact hHigh
  have hEndN : HeightLe (applyWord (R c e f) old) H := by
    rw [←hrep,signedFrame_word,signedFrame_height]
    exact hEnd
  have hOldN : PrefixHeightLe (R c e f) old (H+1) := by
    rw [←hrep]
    apply (signedFrame_forward_prefix B p r old (H+1)).mpr
    rw [oldFrame_eq] at hOld
    exact ((prefixHeight_append_iff B (old.map p.toFun) tail (H+1)).mp hOld).1
  obtain ⟨hNewN,hPosN⟩ := local_progress c e f H hRN hHighN hOldN hEndN
  have hNew : PrefixHeightLe B (new.map p.toFun) H := by
    apply (signedFrame_forward_prefix B p r new H).mp
    rwa [hrep]
  have hPos : 0<overCount B (old.map p.toFun) H := by
    rw [←signedFrame_forward_count B p r old H,hrep]
    exact hPosN
  have hZero : overCount B (new.map p.toFun) H=0 := overCount_eq_zero _ _ _ hNew
  refine ⟨prefix_bound B p r c e f hrep (H+1) tail
    (prefixHeight_mono _ _ H (H+1) (by omega) hNew) hOld,
    acyclic B hs p r c e f hrep tail ha,?_,length_drop p tail⟩
  have hCount := count B p r c e f hrep H tail
  rw [hZero,Nat.add_zero] at hCount
  omega

theorem whole_witness_progress (Q : Matrix 4) (hs : SkewSymmetric Q)
    (lead tail : List (Fin 4)) (p : Relabeling 4) (r : Bool) (c e f : Int) (H : Nat)
    (hrep : signedFrame (applyWord Q lead) p r=R c e f)
    (hR : HeightLe (applyWord Q lead) H)
    (hHigh : ¬HeightLe (mutate (applyWord Q lead) (p.toFun 0)) H)
    (hEnd : HeightLe (applyWord (applyWord Q lead) (old.map p.toFun)) H)
    (hOld : PrefixHeightLe Q (lead++oldFrame p tail) (H+1))
    (ha : Acyclic (applyWord Q (lead++oldFrame p tail))) :
    PrefixHeightLe Q (lead++newFrame p tail) (H+1) ∧
    Acyclic (applyWord Q (lead++newFrame p tail)) ∧
    overCount Q (lead++newFrame p tail) H<overCount Q (lead++oldFrame p tail) H ∧
    (lead++newFrame p tail).length+2=(lead++oldFrame p tail).length := by
  have ht := (prefixHeight_append_iff Q lead (oldFrame p tail) (H+1)).mp hOld
  have ha' : Acyclic (applyWord (applyWord Q lead) (oldFrame p tail)) := by
    rwa [applyWord_append] at ha
  obtain ⟨hn,han,hc,hl⟩ := framed_tail_progress (applyWord Q lead)
    (word_preserves_skew Q lead hs) p r c e f H hrep hR hHigh hEnd tail ht.2 ha'
  refine ⟨prefixHeight_append Q lead (newFrame p tail) (H+1) ht.1 hn,?_,?_,?_⟩
  · rwa [applyWord_append]
  · rw [overCount_append,overCount_append]
    omega
  · simp only [List.length_append]
    omega

theorem count_minimal_excludes_pattern (Q : Matrix 4) (hs : SkewSymmetric Q)
    (lead tail : List (Fin 4)) (p : Relabeling 4) (r : Bool) (c e f : Int) (H : Nat)
    (hrep : signedFrame (applyWord Q lead) p r=R c e f)
    (hR : HeightLe (applyWord Q lead) H)
    (hHigh : ¬HeightLe (mutate (applyWord Q lead) (p.toFun 0)) H)
    (hEnd : HeightLe (applyWord (applyWord Q lead) (old.map p.toFun)) H)
    (hOld : PrefixHeightLe Q (lead++oldFrame p tail) (H+1))
    (ha : Acyclic (applyWord Q (lead++oldFrame p tail)))
    (hmin : ∀ w,PrefixHeightLe Q w (H+1) → Acyclic (applyWord Q w) →
      overCount Q (lead++oldFrame p tail) H≤overCount Q w H) : False := by
  obtain ⟨hn,han,hc,_⟩ := whole_witness_progress Q hs lead tail p r c e f H
    hrep hR hHigh hEnd hOld ha
  have hm := hmin (lead++newFrame p tail) hn han
  omega

#print axioms local_progress
#print axioms framed_tail_progress
#print axioms whole_witness_progress
#print axioms count_minimal_excludes_pattern
end Rank4Round2.MixedUnitGuard
