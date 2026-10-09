import Rank4Round2.UnitMAGuard
import Rank4ReviewRound2.PeakNormalization

/-! Actual strict unit-peak progress in the computed signed normalization.
The ordered pivots are the two original pivots, possibly exchanged by the
computed frame. Every suffix is transformed by the actual permutation.
The two structural properness bridges remain explicit.
-/
namespace Rank4Round2
open QuiverProofs Rank4Coordinator Census ProperObstructionSoundness
open Rank4ReviewRound2.PeakNormalization

theorem signedFrame_forward_prefix (B : Matrix 4) (p : Relabeling 4) (r : Bool)
    (w : List (Fin 4)) (H : Nat) :
    PrefixHeightLe (signedFrame B p r) w H ↔ PrefixHeightLe B (w.map p.toFun) H := by
  have h := signedFrame_prefix B p r (w.map p.toFun) H
  rw [show (w.map p.toFun).map p.invFun=w from map_inverse_word w p.symm] at h
  exact h

theorem signedFrame_forward_count (B : Matrix 4) (p : Relabeling 4) (r : Bool)
    (w : List (Fin 4)) (H : Nat) :
    overCount (signedFrame B p r) w H = overCount B (w.map p.toFun) H := by
  have h := signedFrame_count B p r (w.map p.toFun) H
  rw [show (w.map p.toFun).map p.invFun=w from map_inverse_word w p.symm] at h
  exact h

theorem signedFrame_forward_acyclic (B : Matrix 4) (hs : SkewSymmetric B)
    (p : Relabeling 4) (r : Bool) (w : List (Fin 4)) :
    Acyclic (applyWord (signedFrame B p r) w) ↔ Acyclic (applyWord B (w.map p.toFun)) := by
  have h := signedFrame_acyclic_word B hs p r (w.map p.toFun)
  rw [show (w.map p.toFun).map p.invFun=w from map_inverse_word w p.symm] at h
  exact h

def unitFrameWord (p : Relabeling 4) (tail : List (Fin 4)) : List (Fin 4) :=
  ([1,0,1]++(tail.map p.invFun).map Forks.swap01.invFun).map p.toFun

/-- On any strict unit pivot, the computed frame supplies an actual bounded
replacement and exact count progress, for all continuations and orientations.
The original pivots may be exchanged; that exchange is explicit in the output.
-/
theorem unit_strict_peak_frame_progress
    (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4)
    (B : Matrix 4) (hs : SkewSymmetric B) (hma : MutationAcyclic B)
    (i j : Fin 4) (hij : i≠j) (H : Nat)
    (hi : HeightLe (mutate B i) H) (hj : HeightLe (mutate B j) H)
    (hout : ¬HeightLe B H) (hunit : |B i j|=1) :
    ∃ (p : Relabeling 4) (r : Bool),
      (p,r)=normalizationFrame B i j ∧
      ((p.toFun 0=i ∧ p.toFun 1=j) ∨ (p.toFun 0=j ∧ p.toFun 1=i)) ∧
      PrefixHeightLe (mutate B (p.toFun 0)) ([1,0,1].map p.toFun) H ∧
      ∀ tail : List (Fin 4),
        overCount (mutate B (p.toFun 0)) (unitFrameWord p tail) H + 1 =
          overCount (mutate B (p.toFun 0)) ([p.toFun 0,p.toFun 1]++tail) H ∧
        (Acyclic (applyWord (mutate B (p.toFun 0)) ([p.toFun 0,p.toFun 1]++tail)) →
          Acyclic (applyWord (mutate B (p.toFun 0)) (unitFrameWord p tail))) := by
  obtain ⟨p,r,a,b,c,d,e,f,hframe,hslots,ha,_,hb,hc,hd,he,hf,hrep,h0,h1⟩ :=
    strict_peak_normalization B hs i j hij H hi hj hout
  have ha1 : a=1 := ha.trans hunit
  rw [ha1] at hrep h0 h1
  have hQ : signedFrame B p r=unitPeak b c d e f := hrep
  have hL : signedFrame (mutate B (p.toFun 0)) p r=mutate (unitPeak b c d e f) 0 := by
    rw [←signedFrame_mutate,hQ]
  have hmaQ : MutationAcyclic (unitPeak b c d e f) := by
    rw [←hQ]
    exact (signedFrame_MA B hs p r).mpr hma
  have hsL := mutation_preserves_skew B (p.toFun 0) hs
  refine ⟨p,r,hframe,hslots,?_,?_⟩
  · apply (signedFrame_forward_prefix (mutate B (p.toFun 0)) p r [1,0,1] H).mp
    rw [hL]
    exact unit_ma_uniform_guard hExist hEnd b c d e f H hb hc hd he h0 h1 hf hmaQ
  · intro tail
    have hold : ([0,1]++tail.map p.invFun).map p.toFun=[p.toFun 0,p.toFun 1]++tail := by
      simp only [List.map_append,List.map_cons,List.map_nil,map_inverse_word]
    have hcount := unit_ma_uniform_count_decrease hExist hEnd b c d e f H
      hb hc hd he h0 h1 hf hmaQ (tail.map p.invFun)
    rw [←hL,signedFrame_forward_count,signedFrame_forward_count,hold] at hcount
    refine ⟨hcount,?_⟩
    intro ha
    have haN : Acyclic (applyWord (mutate (unitPeak b c d e f) 0)
        ([0,1]++tail.map p.invFun)) := by
      rw [←hL]
      apply (signedFrame_forward_acyclic (mutate B (p.toFun 0)) hsL p r _).mpr
      rwa [hold]
    have hnew := (unit_ma_uniform_acyclic_reroute hExist hEnd b c d e f H
      hb hc hd he h0 h1 hf (tail.map p.invFun) haN).1
    rw [←hL] at hnew
    exact (signedFrame_forward_acyclic (mutate B (p.toFun 0)) hsL p r _).mp hnew

#print axioms unitFrameWord
#print axioms unit_strict_peak_frame_progress
end Rank4Round2
