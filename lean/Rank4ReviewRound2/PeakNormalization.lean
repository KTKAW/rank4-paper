import Rank4Coordinator.PeakShape
import Rank4Round2.SignedTransport
import Mathlib.Tactic.Linarith

/-! Computable signed frames for arbitrary strict height peaks. The
normalization supplies no MA-specific exclusion of the resulting cone.
All continuation words are transported by the actual permutation map.
-/
namespace Rank4ReviewRound2.PeakNormalization
open QuiverProofs Rank4Coordinator Rank4Round2

def vertexSwap (i j : Fin 4) : Relabeling 4 :=
  ⟨Equiv.swap i j,Equiv.swap i j,(Equiv.swap i j).left_inv,(Equiv.swap i j).right_inv⟩

def pivotFrame (i j : Fin 4) : Relabeling 4 :=
  let s := vertexSwap 0 i
  s.trans (vertexSwap 1 (s.invFun j))

theorem pivotFrame_slots : ∀ i j : Fin 4, i≠j →
    (pivotFrame i j).toFun 0=i ∧ (pivotFrame i j).toFun 1=j := by decide

def signedFrame (B : Matrix 4) (p : Relabeling 4) (r : Bool) : Matrix 4 :=
  if r then reverse (relabel B p) else relabel B p

theorem signedFrame_skew (B : Matrix 4) (hs : SkewSymmetric B)
    (p : Relabeling 4) (r : Bool) : SkewSymmetric (signedFrame B p r) := by
  cases r
  · exact relabel_skew B p hs
  · exact reverse_skew _ (relabel_skew B p hs)

theorem signedFrame_height (B : Matrix 4) (p : Relabeling 4) (r : Bool) (H : Nat) :
    HeightLe (signedFrame B p r) H ↔ HeightLe B H := by
  cases r <;> simp only [signedFrame,Bool.false_eq_true,↓reduceIte,
    heightLe_reverse_iff,heightLe_relabel_iff]

theorem signedFrame_mutate (B : Matrix 4) (p : Relabeling 4) (r : Bool) (k : Fin 4) :
    mutate (signedFrame B p r) k = signedFrame (mutate B (p.toFun k)) p r := by
  cases r <;> simp only [signedFrame,Bool.false_eq_true,↓reduceIte,
    mutate_reverse,mutate_relabel]

theorem signedFrame_word (B : Matrix 4) (p : Relabeling 4) (r : Bool)
    (w : List (Fin 4)) :
    applyWord (signedFrame B p r) w = signedFrame (applyWord B (w.map p.toFun)) p r := by
  cases r <;> simp only [signedFrame,Bool.false_eq_true,↓reduceIte,word_reverse,word_relabel]

theorem signedFrame_MA (B : Matrix 4) (hs : SkewSymmetric B)
    (p : Relabeling 4) (r : Bool) :
    MutationAcyclic (signedFrame B p r) ↔ MutationAcyclic B := by
  cases r
  · exact MA_relabel_iff B p
  · exact (MA_reverse_iff _ (relabel_skew B p hs)).trans (MA_relabel_iff B p)

theorem signedFrame_prefix (B : Matrix 4) (p : Relabeling 4) (r : Bool)
    (w : List (Fin 4)) (H : Nat) :
    PrefixHeightLe (signedFrame B p r) (w.map p.invFun) H ↔ PrefixHeightLe B w H := by
  cases r <;> simp only [signedFrame,Bool.false_eq_true,↓reduceIte,
    prefixHeight_reverse_iff,prefixHeight_relabel_iff]

theorem signedFrame_count (B : Matrix 4) (p : Relabeling 4) (r : Bool)
    (w : List (Fin 4)) (H : Nat) :
    overCount (signedFrame B p r) (w.map p.invFun) H = overCount B w H := by
  cases r <;> simp only [signedFrame,Bool.false_eq_true,↓reduceIte,
    overCount_reverse,overCount_relabel]

theorem signedFrame_acyclic_word (B : Matrix 4) (hs : SkewSymmetric B)
    (p : Relabeling 4) (r : Bool) (w : List (Fin 4)) :
    Acyclic (applyWord (signedFrame B p r) (w.map p.invFun)) ↔ Acyclic (applyWord B w) := by
  rw [signedFrame_word,map_inverse_word]
  cases r
  · exact acyclic_relabel_iff _ p
  · exact (acyclic_reverse_iff _ (relabel_skew _ p (word_preserves_skew B w hs))).trans
      (acyclic_relabel_iff _ p)

def orderPivots (D : Matrix 4) : Relabeling 4 :=
  if 0≤D 0 1 then .identity 4 else Forks.swap01

theorem orderPivots_slots (D : Matrix 4) :
    ((orderPivots D).toFun 0=0 ∧ (orderPivots D).toFun 1=1) ∨
    ((orderPivots D).toFun 0=1 ∧ (orderPivots D).toFun 1=0) := by
  unfold orderPivots
  split <;> simp [Relabeling.identity,Forks.swap01]

theorem orderPivots_last (D : Matrix 4) :
    (orderPivots D).toFun 2=2 ∧ (orderPivots D).toFun 3=3 := by
  unfold orderPivots
  split <;> simp [Relabeling.identity,Forks.swap01]

theorem orderPivots_edge (D : Matrix 4) (hs : SkewSymmetric D) :
    relabel D (orderPivots D) 0 1=|D 0 1| := by
  unfold orderPivots
  split
  · simpa [relabel,Relabeling.identity] using (abs_of_nonneg ‹0≤D 0 1›).symm
  · have h := hs 1 0
    simp only [relabel,Forks.swap01]
    rw [abs_of_neg (show D 0 1<0 by omega)]
    exact h

theorem orderPivots_children (D : Matrix 4) (H : Nat)
    (h0 : HeightLe (mutate D 0) H) (h1 : HeightLe (mutate D 1) H) :
    HeightLe (mutate (relabel D (orderPivots D)) 0) H ∧
      HeightLe (mutate (relabel D (orderPivots D)) 1) H := by
  rw [mutate_relabel,mutate_relabel,heightLe_relabel_iff,heightLe_relabel_iff]
  rcases orderPivots_slots D with h|h
  · simpa [h.1,h.2] using And.intro h0 h1
  · simpa [h.1,h.2] using And.intro h1 h0

theorem signedFrame_relabel (B : Matrix 4) (p q : Relabeling 4) (r : Bool) :
    relabel (signedFrame B p r) q = signedFrame B (p.trans q) r := by
  cases r <;> rfl

def normalizationFrame (B : Matrix 4) (i j : Fin 4) : Relabeling 4 × Bool :=
  let s := pivotFrame i j
  let C := relabel B s
  let r : Bool := if C 2 3<0 then true else false
  let D := signedFrame B s r
  (s.trans (orderPivots D),r)

/-- Every strict peak has an actual signed frame in the positive cone.
The pivot parameter is exactly the absolute original pivot entry. No
positivity of this parameter is assumed: the zero case remains included. -/
theorem strict_peak_normalization (B : Matrix 4) (hs : SkewSymmetric B)
    (i j : Fin 4) (hij : i≠j) (H : Nat)
    (hi : HeightLe (mutate B i) H) (hj : HeightLe (mutate B j) H)
    (hout : ¬HeightLe B H) :
    ∃ (p : Relabeling 4) (r : Bool) (a b c d e f : Int),
      (p,r)=normalizationFrame B i j ∧
      ((p.toFun 0=i ∧ p.toFun 1=j) ∨ (p.toFun 0=j ∧ p.toFun 1=i)) ∧
      a=|B i j| ∧ 0≤a ∧ 0<b ∧ 0<c ∧ 0<d ∧ 0<e ∧ (H:Int)<f ∧
      signedFrame B p r = positivePeak a b c d e f ∧
      HeightLe (mutate (positivePeak a b c d e f) 0) H ∧
      HeightLe (mutate (positivePeak a b c d e f) 1) H := by
  let s := pivotFrame i j
  let C := relabel B s
  have hslots := pivotFrame_slots i j hij
  have hC : SkewSymmetric C := relabel_skew B s hs
  have hC0 : HeightLe (mutate C 0) H := by
    change HeightLe (mutate (relabel B s) 0) H
    rw [mutate_relabel,heightLe_relabel_iff]
    simpa [s,hslots.1] using hi
  have hC1 : HeightLe (mutate C 1) H := by
    change HeightLe (mutate (relabel B s) 1) H
    rw [mutate_relabel,heightLe_relabel_iff]
    simpa [s,hslots.2] using hj
  have hCo : ¬HeightLe C H := fun h => hout ((heightLe_relabel_iff B s H).mp h)
  have hop := opposite_edge_outside C hC H hC0 hC1 hCo
  have hC01 : C 0 1=B i j := by
    change B (s.toFun 0) (s.toFun 1)=B i j
    simp [s,hslots.1,hslots.2]
  let r : Bool := if C 2 3<0 then true else false
  let D := signedFrame B s r
  have oriented : (H:Int)<D 2 3 ∧ HeightLe (mutate D 0) H ∧
      HeightLe (mutate D 1) H ∧ |D 0 1|=|B i j| := by
    by_cases hn : C 2 3<0
    · have heq : D=reverse C := by
        change (if r then reverse C else C)=reverse C
        simp [r,hn]
      have hf : C 2 3< -(H:Int) := by omega
      rw [heq]
      refine ⟨?_,?_,?_,?_⟩
      · change (H:Int)< -C 2 3
        omega
      · rw [mutate_reverse,heightLe_reverse_iff]
        exact hC0
      · rw [mutate_reverse,heightLe_reverse_iff]
        exact hC1
      · change |-C 0 1|=|B i j|
        rw [abs_neg,hC01]
    · have heq : D=C := by
        change (if r then reverse C else C)=C
        simp [r,hn]
      rw [heq]
      exact ⟨by omega,hC0,hC1,by rw [hC01]⟩
  let q := orderPivots D
  let E := relabel D q
  have hD : SkewSymmetric D := signedFrame_skew B hs s r
  have hE : SkewSymmetric E := relabel_skew D q hD
  have hEc := orderPivots_children D H oriented.2.1 oriented.2.2.1
  have hEl : (H:Int)<E 2 3 := by
    change (H:Int)<D (q.toFun 2) (q.toFun 3)
    rw [(orderPivots_last D).1,(orderPivots_last D).2]
    exact oriented.1
  have hpaths := positive_peak_paths E hE H hEc.1 hEc.2 hEl
  have hEa : E 0 1=|B i j| :=
    (orderPivots_edge D hD).trans oriented.2.2.2
  have hrep : E=positivePeak |B i j| (E 0 2) (-E 0 3) (E 1 2) (-E 1 3) (E 2 3) := by
    unfold positivePeak
    simpa only [hEa,Int.neg_neg] using (ofSix_reconstruct E hE).symm
  refine ⟨s.trans q,r,|B i j|,E 0 2,-E 0 3,E 1 2,-E 1 3,E 2 3,
    rfl,?_,rfl,abs_nonneg _,hpaths.1,by omega,hpaths.2.2.1,by omega,hEl,?_,?_,?_⟩
  · rcases orderPivots_slots D with hq|hq
    · left
      change s.toFun (q.toFun 0)=i ∧ s.toFun (q.toFun 1)=j
      simpa [q,hq.1,hq.2,s] using hslots
    · right
      change s.toFun (q.toFun 0)=j ∧ s.toFun (q.toFun 1)=i
      simpa [q,hq.1,hq.2,s] using And.intro hslots.2 hslots.1
  · rw [← signedFrame_relabel]
    exact hrep
  · rw [←hrep]
    exact hEc.1
  · rw [←hrep]
    exact hEc.2

theorem strong_normalized_high_cone (a b c d e f : Int) (H : Nat)
    (ha : 2≤a) (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e)
    (hf : (H:Int)<f)
    (h0 : HeightLe (mutate (positivePeak a b c d e f) 0) H)
    (h1 : HeightLe (mutate (positivePeak a b c d e f) 1) H) :
    e+a*c<f ∧ b+a*d<f ∧ b*c<2*f ∧ d*e<2*f := by
  have hec := h0 1 3
  have hbd := h1 0 2
  have hbc := h0 2 3
  have hde := h1 2 3
  rw [positivePeak_zero a b c d e f (by omega) hb hc] at hec hbc
  rw [positivePeak_one a b c d e f (by omega) hd he] at hbd hde
  simp only [ofSix] at hec hbd hbc hde
  omega

#print axioms pivotFrame
#print axioms normalizationFrame
#print axioms strict_peak_normalization
#print axioms signedFrame_word
#print axioms signedFrame_prefix
#print axioms signedFrame_MA
#print axioms strong_normalized_high_cone
end Rank4ReviewRound2.PeakNormalization
