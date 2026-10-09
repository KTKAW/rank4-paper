import Rank4Round2.UnitOrderedProgress
import Rank4Round2.WordBounds

/-! Ordered strict unit reroutes preserve every supplied whole-path ceiling
K >= the local child ceiling H. The actual continuation word is transformed.
The two properness bridges remain explicit.
-/
namespace Rank4Round2
open QuiverProofs Rank4Coordinator Census ProperObstructionSoundness
open Rank4ReviewRound2.PeakNormalization

theorem unit_strict_peak_ordered_bounded_progress
    (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4)
    (B : Matrix 4) (hs : SkewSymmetric B) (hma : MutationAcyclic B)
    (i j : Fin 4) (hij : i≠j) (H : Nat)
    (hi : HeightLe (mutate B i) H) (hj : HeightLe (mutate B j) H)
    (hout : ¬HeightLe B H) (hunit : |B i j|=1) :
    ∃ (p : Relabeling 4) (r : Bool),
      (p,r)=normalizationFrame B i j ∧
      PrefixHeightLe (mutate B i) ((orderedUnitLocal p i).map p.toFun) H ∧
      ∀ tail : List (Fin 4),
        overCount (mutate B i) (orderedUnitWord p i tail) H + 1 =
          overCount (mutate B i) ([i,j]++tail) H ∧
        (Acyclic (applyWord (mutate B i) ([i,j]++tail)) →
          Acyclic (applyWord (mutate B i) (orderedUnitWord p i tail))) ∧
        ∀ K : Nat, H≤K → PrefixHeightLe (mutate B i) ([i,j]++tail) K →
          PrefixHeightLe (mutate B i) (orderedUnitWord p i tail) K := by
  obtain ⟨p,r,a,b,c,d,e,f,hframe,hslots,ha,_,hb,hc,hd,he,hf,hrep,h0,h1⟩ :=
    strict_peak_normalization B hs i j hij H hi hj hout
  have ha1 : a=1 := ha.trans hunit
  rw [ha1] at hrep h0 h1
  have hQ : signedFrame B p r=unitPeak b c d e f := hrep
  have hmaQ : MutationAcyclic (unitPeak b c d e f) := by
    rw [←hQ]
    exact (signedFrame_MA B hs p r).mpr hma
  let s : Fin 4 := if p.toFun 0=i then 0 else 1
  let t : Fin 4 := if p.toFun 0=i then 1 else 0
  have hsi : p.toFun s=i := by
    rcases hslots with hp|hp
    · simp [s,hp.1]
    · have hne : p.toFun 0≠i := by rw [hp.1]; exact hij.symm
      simp [s,hne,hp.2]
  have htj : p.toFun t=j := by
    rcases hslots with hp|hp
    · simp [t,hp.1,hp.2]
    · have hne : p.toFun 0≠i := by rw [hp.1]; exact hij.symm
      simp only [t,if_neg hne,hp.1]
  have hL : signedFrame (mutate B i) p r=mutate (unitPeak b c d e f) s := by
    rw [←hsi,←signedFrame_mutate,hQ]
  have hR : HeightLe (mutate (unitPeak b c d e f) t) H := by
    dsimp only [t]
    split
    · exact h1
    · exact h0
  have hend : applyWord (mutate (unitPeak b c d e f) s) (orderedUnitLocal p i)=
      relabel (mutate (unitPeak b c d e f) t) Forks.swap01 := by
    by_cases hp : p.toFun 0=i
    · simp only [s,t,orderedUnitLocal,if_pos hp]
      exact unitPeak_detour_endpoint b c d e f hb hc hd he
    · simp only [s,t,orderedUnitLocal,if_neg hp]
      exact unitPeak_backward_endpoint b c d e f hb hc hd he
  have hn : PrefixHeightLe (mutate (unitPeak b c d e f) s) (orderedUnitLocal p i) H := by
    by_cases hp : p.toFun 0=i
    · simp only [s,orderedUnitLocal,if_pos hp]
      exact unit_ma_uniform_guard hExist hEnd b c d e f H hb hc hd he h0 h1 hf hmaQ
    · simp only [s,orderedUnitLocal,if_neg hp]
      exact unit_ma_backward_guard hExist hEnd b c d e f H hb hc hd he h0 h1 hf hmaQ
  have hP : ¬HeightLe (unitPeak b c d e f) H := by
    intro h
    have h := (h 2 3).2
    change f≤(H:Int) at h
    omega
  have hsL := mutation_preserves_skew B i hs
  refine ⟨p,r,hframe,?_,?_⟩
  · apply (signedFrame_forward_prefix (mutate B i) p r (orderedUnitLocal p i) H).mp
    rwa [hL]
  · intro tail
    have hold : ([s,t]++tail.map p.invFun).map p.toFun=[i,j]++tail := by
      simp only [List.map_append,List.map_cons,List.map_nil,map_inverse_word,hsi,htj]
    have hcount := strict_peak_overCount (unitPeak b c d e f) s t
      (orderedUnitLocal p i) (tail.map p.invFun) Forks.swap01 H hP hR hend hn
    rw [←hL,signedFrame_forward_count,signedFrame_forward_count,hold] at hcount
    refine ⟨hcount,?_,?_⟩
    · intro ha
      have haN : Acyclic (applyWord (mutate (unitPeak b c d e f) s)
          ([s,t]++tail.map p.invFun)) := by
        rw [←hL]
        apply (signedFrame_forward_acyclic (mutate B i) hsL p r _).mpr
        rwa [hold]
      have hnew := (strict_peak_reroute (unitPeak b c d e f) s t (orderedUnitLocal p i)
        (tail.map p.invFun) Forks.swap01 H hP hR hend hn haN).1
      rw [←hL] at hnew
      exact (signedFrame_forward_acyclic (mutate B i) hsL p r _).mp hnew
    · intro K hHK hOld
      have hOldN : PrefixHeightLe (mutate (unitPeak b c d e f) s)
          ([s,t]++tail.map p.invFun) K := by
        rw [←hL]
        apply (signedFrame_forward_prefix (mutate B i) p r _ K).mpr
        rwa [hold]
      have htN := (prefixHeight_append_iff _ [s,t] (tail.map p.invFun) K).mp hOldN
      have hendOld : applyWord (mutate (unitPeak b c d e f) s) [s,t]=
          mutate (unitPeak b c d e f) t := by
        simp only [applyWord,mutation_involutive]
      have hendpoint : applyWord (mutate (unitPeak b c d e f) s) (orderedUnitLocal p i)=
          relabel (applyWord (mutate (unitPeak b c d e f) s) [s,t]) Forks.swap01 := by
        rwa [hendOld]
      have hnewK := reroute_prefixHeight (mutate (unitPeak b c d e f) s) [s,t]
        (orderedUnitLocal p i) (tail.map p.invFun) Forks.swap01 K hendpoint
        (prefixHeight_mono _ _ H K hHK hn) htN.2
      rw [←hL] at hnewK
      exact (signedFrame_forward_prefix (mutate B i) p r _ K).mp hnewK

#print axioms unit_strict_peak_ordered_bounded_progress
end Rank4Round2
