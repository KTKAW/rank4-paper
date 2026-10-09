import Rank4CoordinatorR2.FlatHalfShape

/-! An incident top entry cannot persist for two forward strong-pair steps.
This is integer mutation geometry, with no MA or properness hypothesis. -/
namespace Rank4ReviewRound2.StrongPairColumn
open QuiverProofs Rank4Coordinator Rank4CoordinatorR2

theorem column_survival (a b d : Int) (H : Nat) (ha : 2≤abs a)
    (hb : -(H:Int)≤b ∧ b≤(H:Int))
    (hd : -(H:Int)≤d ∧ d≤(H:Int))
    (hx : -((H+1:Nat):Int)≤b+correction a d ∧
      b+correction a d≤((H+1:Nat):Int))
    (hy : -((H+1:Nat):Int)≤ -d+correction a (b+correction a d) ∧
      -d+correction a (b+correction a d)≤((H+1:Nat):Int)) :
    -(H:Int)≤b+correction a d ∧ b+correction a d≤(H:Int) := by
  by_contra hn
  have hc : b+correction a d=(H:Int)+1 ∨
      b+correction a d= -(H:Int)-1 := by omega
  rcases hc with hc|hc
  · obtain ⟨haPos,hdPos⟩ := correction_positive_inputs a d
      (show 0<correction a d by omega)
    have ha2 : 2≤a := by rwa [abs_of_pos haPos] at ha
    have he : correction a (b+correction a d)=a*((H:Int)+1) := by
      rw [hc]
      simp only [correction,max_eq_left (show 0≤a by omega),
        max_eq_left (show 0≤(H:Int)+1 by omega),
        max_eq_right (show -a≤0 by omega),max_eq_right (show -((H:Int)+1)≤0 by omega)]
      ring
    rw [he] at hy
    have hp := mul_nonneg (show 0≤a-2 by omega) (show 0≤(H:Int)+1 by omega)
    simp only [Nat.cast_add,Nat.cast_one] at hy
    nlinarith
  · obtain ⟨haNeg,hdNeg⟩ := correction_negative_inputs a d
      (show correction a d<0 by omega)
    have ha2 : a≤ -2 := by rw [abs_of_neg haNeg] at ha; omega
    have he : correction a (b+correction a d)= -a*(-((H:Int)+1)) := by
      rw [hc]
      simp only [correction,max_eq_right (show a≤0 by omega),
        max_eq_right (show -(H:Int)-1≤0 by omega),
        max_eq_left (show 0≤ -a by omega),max_eq_left (show 0≤ -(-(H:Int)-1) by omega)]
      ring
    rw [he] at hy
    have hp := mul_nonneg (show 0≤ -a-2 by omega) (show 0≤(H:Int)+1 by omega)
    simp only [Nat.cast_add,Nat.cast_one] at hy
    nlinarith

theorem frozen_column_survives (B : Matrix 4) (hs : SkewSymmetric B)
    (i j l : Fin 4) (hij : i≠j) (hil : i≠l) (hjl : j≠l)
    (H : Nat) (ha : 2≤abs (B i j))
    (hb : -(H:Int)≤B i l ∧ B i l≤(H:Int))
    (hd : -(H:Int)≤B j l ∧ B j l≤(H:Int))
    (hFirst : HeightLe (mutate B j) (H+1))
    (hNext : HeightLe (mutate (mutate B j) i) (H+1)) :
    -(H:Int)≤mutate B j i l ∧ mutate B j i l≤(H:Int) := by
  have hcol : mutate B j i l=B i l+correction (B i j) (B j l) := by
    simp only [mutate,if_neg (show ¬(i=j ∨ l=j) by omega)]
  have hback : mutate (mutate B j) i j l=
      -B j l+correction (B i j) (B i l+correction (B i j) (B j l)) := by
    simp only [mutate,if_neg (show ¬(j=i ∨ l=i) by omega),
      if_pos (show j=j ∨ l=j from Or.inl rfl),
      if_pos (show j=j ∨ i=j from Or.inl rfl),
      if_neg (show ¬(i=j ∨ l=j) by omega),hs j i,Int.neg_neg,or_true,true_or,if_true]
  have hx := hFirst i l
  have hy := hNext j l
  rw [hcol] at hx
  rw [hback] at hy
  rw [hcol]
  exact column_survival (B i j) (B i l) (B j l) H ha hb hd hx hy

#print axioms column_survival
#print axioms frozen_column_survives
end Rank4ReviewRound2.StrongPairColumn
