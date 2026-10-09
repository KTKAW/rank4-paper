import Rank4Round2.MixedUnitRelation
import Rank4Round2.UnitFrameProgress

/-! The mixed-unit relation in an arbitrary signed vertex frame. The actual
continuation is pulled into the frame, transported through the endpoint
cycle, and pushed back to the original labels. -/
namespace Rank4Round2.MixedUnitFrame
open QuiverProofs Rank4Coordinator Rank4Round2
open Rank4ReviewRound2.PeakNormalization MixedUnitRelation

def oldFrame (p : Relabeling 4) (tail : List (Fin 4)) : List (Fin 4) :=
  (old++tail.map p.invFun).map p.toFun
def newFrame (p : Relabeling 4) (tail : List (Fin 4)) : List (Fin 4) :=
  (new++(tail.map p.invFun).map cycle.invFun).map p.toFun

theorem oldFrame_eq (p : Relabeling 4) (tail : List (Fin 4)) :
    oldFrame p tail=old.map p.toFun++tail := by
  simp only [oldFrame,List.map_append,map_inverse_word]

theorem newFrame_eq (p : Relabeling 4) (tail : List (Fin 4)) :
    newFrame p tail=new.map p.toFun++
      ((tail.map p.invFun).map cycle.invFun).map p.toFun := by
  simp only [newFrame,List.map_append]

theorem endpoint (B : Matrix 4) (p : Relabeling 4) (r : Bool)
    (c e f : Int) (hrep : signedFrame B p r=R c e f) (tail : List (Fin 4)) :
    signedFrame (applyWord B (newFrame p tail)) p r=
      relabel (signedFrame (applyWord B (oldFrame p tail)) p r) cycle := by
  have h := literal_tail_endpoint c e f (tail.map p.invFun)
  rw [←hrep,signedFrame_word,signedFrame_word] at h
  exact h

theorem count (B : Matrix 4) (p : Relabeling 4) (r : Bool)
    (c e f : Int) (hrep : signedFrame B p r=R c e f)
    (H : Nat) (tail : List (Fin 4)) :
    overCount B (newFrame p tail) H+overCount B (old.map p.toFun) H=
      overCount B (oldFrame p tail) H+overCount B (new.map p.toFun) H := by
  have h := literal_tail_count c e f H (tail.map p.invFun)
  rw [←hrep,signedFrame_forward_count,signedFrame_forward_count,
    signedFrame_forward_count,signedFrame_forward_count] at h
  exact h

theorem prefix_bound (B : Matrix 4) (p : Relabeling 4) (r : Bool)
    (c e f : Int) (hrep : signedFrame B p r=R c e f)
    (K : Nat) (tail : List (Fin 4))
    (hNew : PrefixHeightLe B (new.map p.toFun) K)
    (hOld : PrefixHeightLe B (oldFrame p tail) K) :
    PrefixHeightLe B (newFrame p tail) K := by
  apply (signedFrame_forward_prefix B p r _ K).mp
  rw [hrep]
  apply literal_tail_prefix c e f K (tail.map p.invFun)
  · rw [←hrep]
    exact (signedFrame_forward_prefix B p r new K).mpr hNew
  · rw [←hrep]
    exact (signedFrame_forward_prefix B p r _ K).mpr hOld

theorem acyclic (B : Matrix 4) (hs : SkewSymmetric B)
    (p : Relabeling 4) (r : Bool) (c e f : Int)
    (hrep : signedFrame B p r=R c e f) (tail : List (Fin 4))
    (ha : Acyclic (applyWord B (oldFrame p tail))) :
    Acyclic (applyWord B (newFrame p tail)) := by
  apply (signedFrame_forward_acyclic B hs p r _).mp
  rw [hrep]
  apply literal_tail_acyclic c e f (tail.map p.invFun)
  rw [←hrep]
  exact (signedFrame_forward_acyclic B hs p r _).mpr ha

theorem length_drop (p : Relabeling 4) (tail : List (Fin 4)) :
    (newFrame p tail).length+2=(oldFrame p tail).length := by
  simp [newFrame,oldFrame,new,old]

#print axioms endpoint
#print axioms count
#print axioms prefix_bound
#print axioms acyclic
#print axioms length_drop
end Rank4Round2.MixedUnitFrame
