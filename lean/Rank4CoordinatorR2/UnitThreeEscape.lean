import Rank4CoordinatorR2.UnitThreePositive

/-! Both opposite-edge orientations of a three-high unit prefix. Scalar
bounds for every relabeled proper order are supplied explicitly here;
the actual-input scalar-budget consumer is separate. -/
namespace Rank4CoordinatorR2.UnitThreeEscape
open QuiverProofs Rank4Coordinator Rank4CoordinatorR2 Rank4Round2
open ProperOrder ProperMutation ProperObstructionSoundness UnitThreeGeometry
set_option maxHeartbeats 4000000
private theorem four (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
def swap23 : Relabeling 4 :=
  ⟨fun i => match i.val with | 0=>0 | 1=>1 | 2=>3 | _=>2,
   fun i => match i.val with | 0=>0 | 1=>1 | 2=>3 | _=>2,by decide,by decide⟩

theorem other_column (x y d E f : Int) :
    applyWord (R x y d E f) [0,1,0] 1 3=E+neg y-pos (g y (-E)) := by
  simp [R,applyWord,mutate,ofSix,correction,g,pos,neg]
  ring

theorem alternate_matrix (x y d E f : Int) :
    mutate (R x y d E f) 1=
      ofSix (-1) (x+pos d) (y+pos (-E)) (-d) E (f+correction (-d) (-E)) := by
  funext i j
  rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
    simp [R,mutate,ofSix,correction,pos] <;> ring

theorem alternate_opposite_outside (x y d E f : Int) (H : Nat)
    (hR : HeightLe (R x y d E f) H)
    (hT : HeightLe (applyWord (R x y d E f) [0,1,0]) (H+1))
    (hOut : ¬HeightLe (mutate (R x y d E f) 1) (H+1)) :
    ¬(-((H:Int)+1)≤f+correction (-d) (-E) ∧ f+correction (-d) (-E)≤(H:Int)+1) := by
  intro hOpp
  have hx := hR 0 2
  have hy := hR 0 3
  have hd := hR 1 2
  have he := hR 1 3
  have hOne := hR 0 1
  simp only [R,ofSix] at hx hy hd he hOne
  have hTx := hT 1 2
  have hTy := hT 1 3
  rw [(three_column x y d E f).2] at hTx
  rw [other_column] at hTy
  simp only [Nat.cast_add,Nat.cast_one] at hTx hTy
  have hX := alternate_column_bounded x d ((H:Int)+1) (by omega) (by omega) hTx
  have hY := alternate_column_bounded y (-E) ((H:Int)+1) (by omega) (by omega)
    (by simpa only [neg_neg] using hTy)
  apply hOut
  rw [alternate_matrix]
  intro i j
  rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
    simp only [ofSix,Nat.cast_add,Nat.cast_one] <;> omega

theorem negative_opposite_impossible (B : Matrix 4) (hs : SkewSymmetric B)
    (h01 : B 0 1=1) (H : Nat)
    (hB : HeightLe B H) (hPath : PrefixHeightLe B [0,1,0] (H+1))
    (hFirst : ¬HeightLe (mutate B 0) H)
    (hThird : ¬HeightLe (applyWord B [0,1,0]) H)
    (hOpp : mutate B 1 2 3< -((H:Int)+1))
    (hScalars : ∀ p,TotalProper B p → orderMarkov B p≤(H:Int)) : ¬MutationAcyclic B := by
  let x := B 0 2
  let y := B 0 3
  let d := B 1 2
  let E := -B 1 3
  let f := B 2 3
  have hrep : B=R x y d E f := by
    rw [←ofSix_reconstruct B hs,h01]
    simp [R,x,y,d,E,f]
  have hAlt : mutate B 1 2 3=f+correction (-d) (-E) := by
    rw [hrep,alternate_matrix];rfl
  have hf := (hB 2 3).1
  change -(H:Int)≤f at hf
  have hCorr : correction (-d) (-E)<0 := by rw [hAlt] at hOpp;omega
  obtain ⟨hd,hE⟩ := correction_negative_inputs (-d) (-E) hCorr
  have hDE : correction (-d) (-E)= -d*E := by
    simp [correction,max_eq_right (show -d≤0 by omega),
      max_eq_right (show -E≤0 by omega),max_eq_left (show 0≤d by omega),
      max_eq_left (show 0≤E by omega)]
  rw [hAlt,hDE] at hOpp
  rw [hrep] at hB hPath hFirst hThird hScalars ⊢
  exact UnitThreePositive.positive_escape_MA_impossible x y d E f H (by omega) (by omega)
    hB hPath hFirst hThird (by nlinarith) hScalars

theorem positive_unit_alternative_bounded (B : Matrix 4) (hs : SkewSymmetric B)
    (hma : MutationAcyclic B) (h01 : B 0 1=1) (H : Nat)
    (hB : HeightLe B H) (hPath : PrefixHeightLe B [0,1,0] (H+1))
    (hFirst : ¬HeightLe (mutate B 0) H)
    (hThird : ¬HeightLe (applyWord B [0,1,0]) H)
    (hScalars : ∀ p q,TotalProper (relabel B p) q → orderMarkov (relabel B p) q≤(H:Int)) :
    HeightLe (mutate B 1) (H+1) := by
  by_contra hn
  have hrep : B=R (B 0 2) (B 0 3) (B 1 2) (-B 1 3) (B 2 3) := by
    calc
      B=ofSix (B 0 1) (B 0 2) (B 0 3) (B 1 2) (B 1 3) (B 2 3) :=
        (ofSix_reconstruct B hs).symm
      _=R (B 0 2) (B 0 3) (B 1 2) (-B 1 3) (B 2 3) := by simp [R,h01]
  have hAlt := alternate_opposite_outside _ _ _ _ _ H
    (by rwa [←hrep]) (by rw [←hrep];exact hPath [0,1,0] [] (by simp)) (by rwa [←hrep])
  have hCell : mutate B 1 2 3=B 2 3+correction (-(B 1 2)) (B 1 3) := by
    simp [mutate,hs 2 1]
  have hOpp : ¬(-((H:Int)+1)≤mutate B 1 2 3 ∧ mutate B 1 2 3≤(H:Int)+1) := by
    simpa only [hCell,neg_neg] using hAlt
  rcases lt_or_ge (mutate B 1 2 3) (-((H:Int)+1)) with hNeg|hNonneg
  · exact negative_opposite_impossible B hs h01 H hB hPath hFirst hThird hNeg
      (by intro q hq;simpa only [relabel_identity] using hScalars (.identity 4) q hq) hma
  · have hPos : (H:Int)+1<mutate B 1 2 3 := by omega
    let C := relabel B swap23
    have hsC := relabel_skew B swap23 hs
    have h01C : C 0 1=1 := h01
    have hBC : HeightLe C H := (heightLe_relabel_iff B swap23 H).mpr hB
    have hPC : PrefixHeightLe C [0,1,0] (H+1) := by
      have h := (prefixHeight_relabel_iff B swap23 [0,1,0] (H+1)).mpr hPath
      exact h
    have hFC : ¬HeightLe (mutate C 0) H := by
      change ¬HeightLe (mutate (relabel B swap23) 0) H
      rw [mutate_relabel,heightLe_relabel_iff];exact hFirst
    have hTC : ¬HeightLe (applyWord C [0,1,0]) H := by
      change ¬HeightLe (applyWord (relabel B swap23) [0,1,0]) H
      rw [word_relabel,heightLe_relabel_iff];exact hThird
    have hOppC : mutate C 1 2 3< -((H:Int)+1) := by
      change mutate (relabel B swap23) 1 2 3<_
      rw [mutate_relabel]
      change mutate B 1 3 2<_
      rw [mutation_preserves_skew B 1 hs 3 2]
      omega
    have hSC : ∀ q,TotalProper C q → orderMarkov C q≤(H:Int) := by
      intro q hq
      exact hScalars swap23 q hq
    have hmaC : MutationAcyclic C := (MA_relabel_iff B swap23).mpr hma
    exact negative_opposite_impossible C hsC h01C H hBC hPC hFC hTC hOppC hSC hmaC

#print axioms alternate_opposite_outside
#print axioms negative_opposite_impossible
#print axioms positive_unit_alternative_bounded
end Rank4CoordinatorR2.UnitThreeEscape
