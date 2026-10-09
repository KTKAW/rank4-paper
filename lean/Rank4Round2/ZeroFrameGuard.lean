import Rank4Round2.ZeroMAGuard
import Rank4Round2.UnitOrderedBounds

/-! Actual min-2 zero-pivot strict-square guard in arbitrary vertex labels
and arrow orientation. The incident lower bounds are on the original matrix.
-/
namespace Rank4Round2
open QuiverProofs Rank4Coordinator Census ProperObstructionSoundness
open Rank4ReviewRound2.PeakNormalization

theorem signedFrame_abs (B : Matrix 4) (p : Relabeling 4) (r : Bool) (k l : Fin 4) :
    |signedFrame B p r k l|=|B (p.toFun k) (p.toFun l)| := by
  cases r <;> simp [signedFrame,reverse,relabel,abs_neg]

theorem frame_incident_lower (B : Matrix 4) (p : Relabeling 4) (r : Bool)
    (i j : Fin 4)
    (hslots : (p.toFun 0=i ∧ p.toFun 1=j) ∨ (p.toFun 0=j ∧ p.toFun 1=i))
    (hInc : ∀ l : Fin 4, l≠i → l≠j → 2≤|B i l| ∧ 2≤|B j l|)
    (k l : Fin 4) (hk : k=0 ∨ k=1) (hl : l=2 ∨ l=3) :
    2≤|signedFrame B p r k l| := by
  have hn0 : p.toFun l≠p.toFun 0 := by
    intro heq
    have h := p.injective heq
    rcases hl with hl|hl <;> omega
  have hn1 : p.toFun l≠p.toFun 1 := by
    intro heq
    have h := p.injective heq
    rcases hl with hl|hl <;> omega
  rw [signedFrame_abs]
  rcases hslots with hp|hp
  · have h := hInc (p.toFun l) (by rwa [←hp.1]) (by rwa [←hp.2])
    rcases hk with rfl|rfl
    · rw [hp.1]; exact h.1
    · rw [hp.2]; exact h.2
  · have h := hInc (p.toFun l) (by rwa [←hp.2]) (by rwa [←hp.1])
    rcases hk with rfl|rfl
    · rw [hp.1]; exact h.2
    · rw [hp.2]; exact h.1

theorem mutate_zero_commute_at (B : Matrix 4) (hs : SkewSymmetric B)
    (i j : Fin 4) (hij : i≠j) (hz : B i j=0) :
    mutate (mutate B i) j=mutate (mutate B j) i := by
  let p := pivotFrame i j
  have hp := pivotFrame_slots i j hij
  have hzero : relabel B p 0 1=0 := by simpa [relabel,p,hp.1,hp.2] using hz
  have h := mutate_zero_commute (relabel B p) (relabel_skew B p hs) hzero
  simp only [mutate_relabel] at h
  have h0 : p.toFun 0=i := hp.1
  have h1 : p.toFun 1=j := hp.2
  rw [h0,h1] at h
  have h := congrArg (fun Q => relabel Q p.symm) h
  dsimp only at h
  simpa only [relabel_inverse] using h

theorem zero_square_endpoint_at (B : Matrix 4) (hs : SkewSymmetric B)
    (i j : Fin 4) (hij : i≠j) (hz : B i j=0) :
    applyWord (mutate B i) [j,i]=mutate B j := by
  simp only [applyWord]
  rw [mutate_zero_commute_at B hs i j hij hz,mutation_involutive]

theorem zero_min2_strict_guard
    (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4)
    (B : Matrix 4) (hs : SkewSymmetric B) (hma : MutationAcyclic B)
    (i j : Fin 4) (hij : i≠j) (H : Nat)
    (hi : HeightLe (mutate B i) H) (hj : HeightLe (mutate B j) H)
    (hout : ¬HeightLe B H) (hz : B i j=0)
    (hInc : ∀ l : Fin 4, l≠i → l≠j → 2≤|B i l| ∧ 2≤|B j l|) :
    PrefixHeightLe (mutate B i) [j,i] H := by
  obtain ⟨p,r,a,b,c,d,e,f,_,hslots,ha,_,hb,hc,hd,he,hf,hrep,h0,h1⟩ :=
    strict_peak_normalization B hs i j hij H hi hj hout
  have ha0 : a=0 := by simpa [hz] using ha
  rw [ha0] at hrep h0 h1
  have hQ : signedFrame B p r=zeroPeak b c d e f := hrep
  have hb2 := frame_incident_lower B p r i j hslots hInc 0 2 (Or.inl rfl) (Or.inl rfl)
  have hc2 := frame_incident_lower B p r i j hslots hInc 0 3 (Or.inl rfl) (Or.inr rfl)
  have hd2 := frame_incident_lower B p r i j hslots hInc 1 2 (Or.inr rfl) (Or.inl rfl)
  have he2 := frame_incident_lower B p r i j hslots hInc 1 3 (Or.inr rfl) (Or.inr rfl)
  rw [hQ] at hb2 hc2 hd2 he2
  simp only [zeroPeak,ofSix,abs_neg,abs_of_pos hb,abs_of_pos hc,abs_of_pos hd,abs_of_pos he]
    at hb2 hc2 hd2 he2
  have hmaQ : MutationAcyclic (zeroPeak b c d e f) := by
    rw [←hQ]
    exact (signedFrame_MA B hs p r).mpr hma
  have hn := zero_ma_square_guard hExist hEnd b c d e f H hb2 hc2 hd2 he2 h0 h1 hf hmaQ
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

#print axioms frame_incident_lower
#print axioms mutate_zero_commute_at
#print axioms zero_min2_strict_guard
end Rank4Round2
