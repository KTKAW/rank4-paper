import Rank4ReviewRound2.StrongPairIncident
import Rank4ReviewRound2.StrongPairRecurrence

/-! The stable rank-two cone keeps all opposite entries fixed for an
arbitrary alternating word. These are actual labeled mutations. -/
namespace Rank4ReviewRound2.StrongPairStable
open QuiverProofs StrongPairIncident StrongPairRecurrence

def StableColumns (B : Matrix 4) (i j : Fin 4) : Prop :=
  ∀ l, i≠l → j≠l → B i l≤0 ∧ 0≤B j l ∧ 0≤B i l+B j l

private theorem correction_product (a d : Int) (ha : 0≤a) (hd : 0≤d) :
    correction a d=a*d := by
  simp only [correction,max_eq_left ha,max_eq_left hd,
    max_eq_right (show -a≤0 by omega),max_eq_right (show -d≤0 by omega)]
  ring

theorem stable_step (B : Matrix 4) (i j : Fin 4) (hij : i≠j)
    (ha : 2≤B i j) (hStable : StableColumns B i j) :
    StableColumns (mutate B j) j i := by
  intro l hjl hil
  have ht := hStable l hil hjl
  have hp := mul_nonneg (show 0≤B i j-2 by omega) ht.2.1
  have he := actual_column_step B i j l hij hil hjl
  have hleft : mutate B j j l= -B j l := by simp [mutate]
  have hright : mutate B j i l=B i l+correction (B i j) (B j l) := by
    simp only [mutate,if_neg (show ¬(i=j ∨ l=j) by omega)]
  rw [hleft,hright,correction_product _ _ (by omega) ht.2.1]
  exact ⟨by omega,by nlinarith,by nlinarith⟩

theorem initial_step_stable (B : Matrix 4) (i j : Fin 4) (hij : i≠j)
    (ha : 2≤B i j)
    (hInitial : ∀ l,i≠l → j≠l → 0≤B j l ∧ 0≤B i l+(B i j-1)*B j l) :
    StableColumns (mutate B j) j i := by
  intro l hjl hil
  have ht := hInitial l hil hjl
  have hleft : mutate B j j l= -B j l := by simp [mutate]
  have hright : mutate B j i l=B i l+correction (B i j) (B j l) := by
    simp only [mutate,if_neg (show ¬(i=j ∨ l=j) by omega)]
  rw [hleft,hright,correction_product _ _ (by omega) ht.1]
  exact ⟨by omega,by nlinarith,by nlinarith⟩

theorem opposite_step_fixed (B : Matrix 4) (hs : SkewSymmetric B)
    (j k l : Fin 4) (hjk : j≠k) (hjl : j≠l)
    (hk : 0≤B j k) (hl : 0≤B j l) : mutate B j k l=B k l := by
  simp only [mutate,if_neg (show ¬(k=j ∨ l=j) by omega)]
  have he : correction (B k j) (B j l)=0 := by
    rw [hs k j]
    simp only [correction,max_eq_right (show -B j k≤0 by omega),
      max_eq_left hl,max_eq_right (show -B j l≤0 by omega)]
    ring
  rw [he,Int.add_zero]

theorem stable_word_opposite_fixed (n : Nat) (B : Matrix 4) (hs : SkewSymmetric B)
    (i j : Fin 4) (hij : i≠j) (ha : 2≤B i j) (hStable : StableColumns B i j)
    (k l : Fin 4) (hik : i≠k) (hjk : j≠k) (hil : i≠l) (hjl : j≠l) :
    applyWord B (alternatingWord i j n) k l=B k l := by
  induction n generalizing B i j with
  | zero => rfl
  | succ n ih =>
    have hpair : mutate B j j i=B i j := by simp only [mutate,true_or,if_true,hs j i,Int.neg_neg]
    have hnext := stable_step B i j hij ha hStable
    change applyWord (mutate B j) (alternatingWord j i n) k l=B k l
    rw [ih (mutate B j) (mutation_preserves_skew B j hs) j i (Ne.symm hij)
      (by rwa [hpair]) hnext hjk hik hjl hil]
    exact opposite_step_fixed B hs j k l hjk hjl (hStable k hik hjk).2.1
      (hStable l hil hjl).2.1

theorem initial_word_opposite_fixed (n : Nat) (B : Matrix 4) (hs : SkewSymmetric B)
    (i j : Fin 4) (hij : i≠j) (ha : 2≤B i j)
    (hInitial : ∀ l,i≠l → j≠l → 0≤B j l ∧ 0≤B i l+(B i j-1)*B j l)
    (k l : Fin 4) (hik : i≠k) (hjk : j≠k) (hil : i≠l) (hjl : j≠l) :
    applyWord B (alternatingWord i j n) k l=B k l := by
  cases n with
  | zero => rfl
  | succ n =>
    have hpair : mutate B j j i=B i j := by simp only [mutate,true_or,if_true,hs j i,Int.neg_neg]
    change applyWord (mutate B j) (alternatingWord j i n) k l=B k l
    rw [stable_word_opposite_fixed n (mutate B j) (mutation_preserves_skew B j hs)
      j i (Ne.symm hij) (by rwa [hpair]) (initial_step_stable B i j hij ha hInitial)
      k l hjk hik hjl hil]
    exact opposite_step_fixed B hs j k l hjk hjl (hInitial k hik hjk).1
      (hInitial l hil hjl).1

#print axioms stable_word_opposite_fixed
#print axioms initial_word_opposite_fixed
end Rank4ReviewRound2.StrongPairStable
