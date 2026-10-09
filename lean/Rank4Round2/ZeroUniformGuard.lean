import Rank4Round2.ZeroSuperscalar
import Rank4Round2.ZeroFrameGuard
import Rank4Round2.ZeroStripEntry
import Rank4ReviewRound2.ZeroDoubleUnitOverflow

/-! A positive zero-pivot square guard above the proper scalar, with all
incident-unit positions covered by actual signed permutations. The arbitrary
label consumer uses the computable normalization frame and retains its scalar
budget as an explicit hypothesis. No global budget supplier is manufactured.
-/
namespace Rank4Round2.ZeroUniformGuard
open QuiverProofs Rank4Coordinator Rank4Round2 Rank4CoordinatorR2
open ProperObstructionSoundness ProperOrder
open Rank4ReviewRound2.PeakNormalization

private theorem four (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega

theorem last_swap_shape (b c d e f : Int) :
    reverse (relabel (zeroPeak b c d e f) ZeroStripEntry.swap23) =
      zeroPeak c b e d f := by
  funext i j
  rcases four i with rfl|rfl|rfl|rfl <;>
    rcases four j with rfl|rfl|rfl|rfl <;>
    simp [reverse,relabel,ZeroStripEntry.swap23,zeroPeak,ofSix]

theorem pivot_swap_shape (b c d e f : Int) :
    relabel (zeroPeak b c d e f) Forks.swap01 = zeroPeak d e b c f := by
  funext i j
  rcases four i with rfl|rfl|rfl|rfl <;>
    rcases four j with rfl|rfl|rfl|rfl <;>
    simp [relabel,Forks.swap01,zeroPeak,ofSix]

theorem last_swap_scalar (b c d e f : Int) :
    zeroMarkov c b e d f=zeroMarkov b c d e f := by unfold zeroMarkov; ring

theorem pivot_swap_scalar (b c d e f : Int) :
    zeroMarkov d e b c f=zeroMarkov b c d e f := by unfold zeroMarkov; ring

theorem first_unit_overflow_NMA
    (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4)
    (c d e f : Int) (H : Nat) (hc : 0<c) (hd : 0<d) (he : 0<e)
    (h0 : HeightLe (mutate (zeroPeak 1 c d e f) 0) H)
    (h1 : HeightLe (mutate (zeroPeak 1 c d e f) 1) H)
    (hf : (H:Int)<f) (hover : f+(H:Int)<c+d*e)
    (hM : zeroMarkov 1 c d e f≤(H:Int)) :
    ¬MutationAcyclic (zeroPeak 1 c d e f) := by
  by_cases hc1 : c=1
  · subst c
    exact Rank4ReviewRound2.ZeroDoubleUnitOverflow.double_unit_zero_overflow_NMA
      hExist hEnd d e f H hd he h0 h1 hf hover
  · exact ZeroSuperscalar.no_zero_unit_superscalar_overflow
      hExist hEnd c d e f H (by omega) hd he h0 h1 hf hover hM

theorem first_pair_unit_overflow_NMA
    (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4)
    (b c d e f : Int) (H : Nat)
    (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e) (hu : b=1 ∨ c=1)
    (h0 : HeightLe (mutate (zeroPeak b c d e f) 0) H)
    (h1 : HeightLe (mutate (zeroPeak b c d e f) 1) H)
    (hf : (H:Int)<f) (hover : f+(H:Int)<b*c+d*e)
    (hM : zeroMarkov b c d e f≤(H:Int)) :
    ¬MutationAcyclic (zeroPeak b c d e f) := by
  rcases hu with rfl|rfl
  · exact first_unit_overflow_NMA hExist hEnd c d e f H hc hd he h0 h1 hf
      (by simpa only [one_mul] using hover) hM
  · have h0' : HeightLe (mutate (zeroPeak 1 b e d f) 0) H := by
      rw [←last_swap_shape,mutate_reverse,mutate_relabel,
        heightLe_reverse_iff,heightLe_relabel_iff]
      exact h0
    have h1' : HeightLe (mutate (zeroPeak 1 b e d f) 1) H := by
      rw [←last_swap_shape,mutate_reverse,mutate_relabel,
        heightLe_reverse_iff,heightLe_relabel_iff]
      exact h1
    have hn := first_unit_overflow_NMA hExist hEnd b e d f H hb he hd h0' h1' hf
      (by simpa only [mul_one,Int.mul_comm] using hover)
      (by simpa only [last_swap_scalar] using hM)
    intro hma
    apply hn
    rw [←last_swap_shape]
    exact (MA_reverse_iff _ (relabel_skew _ _ (ofSix_skew _ _ _ _ _ _))).mpr
      ((MA_relabel_iff _ _).mpr hma)

theorem any_unit_overflow_NMA
    (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4)
    (b c d e f : Int) (H : Nat)
    (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e)
    (hu : b=1 ∨ c=1 ∨ d=1 ∨ e=1)
    (h0 : HeightLe (mutate (zeroPeak b c d e f) 0) H)
    (h1 : HeightLe (mutate (zeroPeak b c d e f) 1) H)
    (hf : (H:Int)<f) (hover : f+(H:Int)<b*c+d*e)
    (hM : zeroMarkov b c d e f≤(H:Int)) :
    ¬MutationAcyclic (zeroPeak b c d e f) := by
  by_cases hbc : b=1 ∨ c=1
  · exact first_pair_unit_overflow_NMA hExist hEnd b c d e f H hb hc hd he hbc
      h0 h1 hf hover hM
  · have hde : d=1 ∨ e=1 := by omega
    have h0' : HeightLe (mutate (zeroPeak d e b c f) 0) H := by
      rw [←pivot_swap_shape,mutate_relabel,heightLe_relabel_iff]
      exact h1
    have h1' : HeightLe (mutate (zeroPeak d e b c f) 1) H := by
      rw [←pivot_swap_shape,mutate_relabel,heightLe_relabel_iff]
      exact h0
    have hn := first_pair_unit_overflow_NMA hExist hEnd d e b c f H hd he hb hc hde
      h0' h1' hf (by simpa only [add_comm] using hover)
      (by simpa only [pivot_swap_scalar] using hM)
    intro hma
    apply hn
    rw [←pivot_swap_shape]
    exact (MA_relabel_iff _ _).mpr hma

theorem positive_square_guard
    (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4)
    (b c d e f : Int) (H : Nat)
    (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e)
    (h0 : HeightLe (mutate (zeroPeak b c d e f) 0) H)
    (h1 : HeightLe (mutate (zeroPeak b c d e f) 1) H)
    (hf : (H:Int)<f) (hM : zeroMarkov b c d e f≤(H:Int))
    (hma : MutationAcyclic (zeroPeak b c d e f)) :
    PrefixHeightLe (mutate (zeroPeak b c d e f) 0) [1,0] H := by
  by_cases hMin : 2≤b ∧ 2≤c ∧ 2≤d ∧ 2≤e
  · exact zero_ma_square_guard hExist hEnd b c d e f H
      hMin.1 hMin.2.1 hMin.2.2.1 hMin.2.2.2 h0 h1 hf hma
  · have hu : b=1 ∨ c=1 ∨ d=1 ∨ e=1 := by omega
    apply (zeroPeak_detour_iff b c d e f H hb hc hd he h0 h1).mpr
    have hF := h0 2 3
    rw [zeroPeak_zero b c d e f hb hc] at hF
    simp only [ofSix] at hF
    have hde := mul_nonneg (show 0≤d by omega) (show 0≤e by omega)
    refine ⟨?_,by omega⟩
    by_contra hn
    have hover : f+(H:Int)<b*c+d*e := by omega
    exact any_unit_overflow_NMA hExist hEnd b c d e f H hb hc hd he hu
      h0 h1 hf hover hM hma

def normalizedScalar (B : Matrix 4) (i j : Fin 4) : Int :=
  let pr := normalizationFrame B i j
  orderMarkov (signedFrame B pr.1 pr.2) (order 0)

theorem arbitrary_zero_strict_guard
    (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4)
    (B : Matrix 4) (hs : SkewSymmetric B) (hma : MutationAcyclic B)
    (i j : Fin 4) (hij : i≠j) (H : Nat)
    (hi : HeightLe (mutate B i) H) (hj : HeightLe (mutate B j) H)
    (hout : ¬HeightLe B H) (hz : B i j=0)
    (hScalar : normalizedScalar B i j≤(H:Int)) :
    PrefixHeightLe (mutate B i) [j,i] H := by
  obtain ⟨p,r,a,b,c,d,e,f,hpr,hslots,ha,_,hb,hc,hd,he,hf,hrep,h0,h1⟩ :=
    strict_peak_normalization B hs i j hij H hi hj hout
  have ha0 : a=0 := by simpa [hz] using ha
  rw [ha0] at hrep h0 h1
  have hQ : signedFrame B p r=zeroPeak b c d e f := hrep
  have hM : zeroMarkov b c d e f≤(H:Int) := by
    unfold normalizedScalar at hScalar
    rw [←hpr] at hScalar
    change orderMarkov (signedFrame B p r) (order 0)≤_ at hScalar
    rw [hQ] at hScalar
    rw [zeroMarkov_eq]
    exact hScalar
  have hmaQ : MutationAcyclic (zeroPeak b c d e f) := by
    rw [←hQ]
    exact (signedFrame_MA B hs p r).mpr hma
  have hn := positive_square_guard hExist hEnd b c d e f H hb hc hd he h0 h1 hf hM hmaQ
  rcases hslots with hp|hp
  · have hL : signedFrame (mutate B i) p r=mutate (zeroPeak b c d e f) 0 := by
      rw [←hp.1,←signedFrame_mutate,hQ]
    have h := (signedFrame_forward_prefix (mutate B i) p r [1,0] H).mp (by rwa [hL])
    simpa only [List.map_cons,List.map_nil,hp.1,hp.2] using h
  · have hL : signedFrame (mutate B i) p r=mutate (zeroPeak b c d e f) 1 := by
      rw [←hp.2,←signedFrame_mutate,hQ]
    have hrev := prefixHeight_reverse_word _ [1,0] H hn
    rw [zero_square_endpoint (zeroPeak b c d e f) (ofSix_skew _ _ _ _ _ _) rfl] at hrev
    have h := (signedFrame_forward_prefix (mutate B i) p r [0,1] H).mp (by rwa [hL])
    simpa only [List.map_cons,List.map_nil,hp.1,hp.2] using h

#print axioms any_unit_overflow_NMA
#print axioms positive_square_guard
#print axioms normalizedScalar
#print axioms arbitrary_zero_strict_guard
end Rank4Round2.ZeroUniformGuard
