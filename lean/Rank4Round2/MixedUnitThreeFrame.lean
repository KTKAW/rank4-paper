import Rank4Round2.MixedUnitActualEndpoint

/-! Computable frames for three distinct actual pivots. Positive unit01
orientation and representation expose, rather than supply, the remaining
two signed triangle equalities needed by the mixed-unit guard. -/
namespace Rank4Round2.MixedUnitThreeFrame
open QuiverProofs Rank4Coordinator Rank4Round2 MixedUnitRelation
open Rank4ReviewRound2.PeakNormalization

def tripleFrame (i j k : Fin 4) : Relabeling 4 :=
  let p := pivotFrame i j
  p.trans (vertexSwap 2 (p.invFun k))

theorem triple_slots : ∀ i j k : Fin 4,i≠j → k≠i → k≠j →
    (tripleFrame i j k).toFun 0=i ∧ (tripleFrame i j k).toFun 1=j ∧
    (tripleFrame i j k).toFun 2=k := by decide

def flip (B : Matrix 4) (i j : Fin 4) : Bool := if 0≤B i j then false else true

theorem unit_positive (B : Matrix 4) (i j k : Fin 4)
    (hij : i≠j) (hki : k≠i) (hkj : k≠j) (hu : abs (B i j)=1) :
    signedFrame B (tripleFrame i j k) (flip B i j) 0 1=1 := by
  obtain ⟨h0,h1,_⟩ := triple_slots i j k hij hki hkj
  by_cases h : 0≤B i j
  · have hab := hu
    rw [abs_of_nonneg h] at hab
    simpa only [flip,h,↓reduceIte,signedFrame,Bool.false_eq_true,↓reduceIte,
      relabel,h0,h1] using hab
  · have hab := hu
    rw [abs_of_neg (show B i j<0 by omega)] at hab
    simpa only [flip,h,↓reduceIte,signedFrame,↓reduceIte,reverse,relabel,h0,h1] using hab

private theorem four (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega

theorem triangle_rep (B : Matrix 4) (hs : SkewSymmetric B)
    (h01 : B 0 1=1) (h02 : B 0 2= -2) (h12 : B 1 2=1) :
    B=R (B 0 3) (B 1 3) (B 2 3) := by
  funext i j
  have hsk := hs i j
  rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
    simp only [R,ofSix] <;> first | rfl | omega

theorem computed_rep (B : Matrix 4) (hs : SkewSymmetric B) (i j k : Fin 4)
    (hij : i≠j) (hki : k≠i) (hkj : k≠j) (hu : abs (B i j)=1)
    (h02 : signedFrame B (tripleFrame i j k) (flip B i j) 0 2= -2)
    (h12 : signedFrame B (tripleFrame i j k) (flip B i j) 1 2=1) :
    signedFrame B (tripleFrame i j k) (flip B i j)=
      R (signedFrame B (tripleFrame i j k) (flip B i j) 0 3)
        (signedFrame B (tripleFrame i j k) (flip B i j) 1 3)
        (signedFrame B (tripleFrame i j k) (flip B i j) 2 3) :=
  triangle_rep _ (signedFrame_skew B hs _ _)
    (unit_positive B i j k hij hki hkj hu) h02 h12

theorem old_word (i j k : Fin 4) (hij : i≠j) (hki : k≠i) (hkj : k≠j) :
    old.map (tripleFrame i j k).toFun=[i,j,k,i,k] := by
  obtain ⟨h0,h1,h2⟩ := triple_slots i j k hij hki hkj
  simp only [old,List.map_cons,List.map_nil,h0,h1,h2]

theorem new_word (i j k : Fin 4) (hij : i≠j) (hki : k≠i) (hkj : k≠j) :
    new.map (tripleFrame i j k).toFun=[j,i,k] := by
  obtain ⟨h0,h1,h2⟩ := triple_slots i j k hij hki hkj
  simp only [new,List.map_cons,List.map_nil,h0,h1,h2]

#print axioms triple_slots
#print axioms unit_positive
#print axioms computed_rep
#print axioms old_word
end Rank4Round2.MixedUnitThreeFrame
