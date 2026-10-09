import Rank4StructureRound2.TwoStateScalar
import Rank4ReviewRound2.StrongPairIncident

/-! Exact arbitrary-length alternating words. A mixed first high state
with c≤E has two aligned frozen columns after the first forward mutation;
its opposite entry is then constant forever. Hence a bounded exit forces
E<c. No MA, properness, or prefix ceiling is needed for this implication. -/
namespace QuiverProofs.Rank4StructureRound2.MixedExitGeometry
open Rank4Coordinator Rank4ReviewRound2.StrongPairIncident TwoStateScalar
set_option maxHeartbeats 4000000

private theorem corr_positive (x y : Int) (hx : 0≤x) (hy : 0≤y) :
    correction x y=x*y := by
  simp only [correction,max_eq_left hx,max_eq_left hy,
    max_eq_right (show -x≤0 by omega),max_eq_right (show -y≤0 by omega)]
  ring

private theorem corr_nonpos_nonneg (x y : Int) (hx : x≤0) (hy : 0≤y) :
    correction x y=0 := by
  simp only [correction,max_eq_right hx,max_eq_left hy,
    max_eq_right (show -y≤0 by omega)]
  ring

def Aligned (B : Matrix 4) (i j : Fin 4) : Prop :=
  ∀ l, l≠i → l≠j → B i l≤0 ∧ 0≤B j l ∧ -B i l≤B j l

theorem aligned_step (B : Matrix 4) (hs : SkewSymmetric B)
    (i j : Fin 4) (hij : i≠j) (ha : 2≤B i j) (hc : Aligned B i j) :
    Aligned (mutate B j) j i := by
  intro l hlj hli
  obtain ⟨hl0,hl1,hl2⟩ := hc l hli hlj
  have hmul := mul_nonneg (show 0≤B i j-2 by omega) hl1
  have hi : mutate B j i l=B i l+B i j*B j l := by
    simp only [mutate,if_neg (show ¬(i=j ∨ l=j) by omega)]
    rw [corr_positive _ _ (by omega) hl1]
  have hj : mutate B j j l= -B j l := by simp [mutate]
  rw [hi,hj]
  constructor
  · omega
  constructor <;> nlinarith

theorem aligned_opposite_step (B : Matrix 4) (hs : SkewSymmetric B)
    (i j l m : Fin 4) (hij : i≠j) (hli : l≠i) (hlj : l≠j)
    (hmi : m≠i) (hmj : m≠j) (hc : Aligned B i j) :
    mutate B j l m=B l m := by
  have hl := (hc l hli hlj).2.1
  have hm := (hc m hmi hmj).2.1
  have hlj' : B l j≤0 := by rw [hs l j]; omega
  simp only [mutate,if_neg (show ¬(l=j ∨ m=j) by omega)]
  rw [corr_nonpos_nonneg _ _ hlj' hm,Int.add_zero]

theorem aligned_opposite_constant (n : Nat) (B : Matrix 4) (hs : SkewSymmetric B)
    (i j l m : Fin 4) (hij : i≠j) (hli : l≠i) (hlj : l≠j)
    (hmi : m≠i) (hmj : m≠j) (ha : 2≤B i j) (hc : Aligned B i j) :
    applyWord B (alternatingWord i j n) l m=B l m := by
  induction n generalizing B i j with
  | zero => rfl
  | succ n ih =>
      have hs' := mutation_preserves_skew B j hs
      have ha' : 2≤mutate B j j i := by
        simp only [mutate,true_or,if_true,hs j i,Int.neg_neg]
        exact ha
      change applyWord (mutate B j) (alternatingWord j i n) l m=B l m
      rw [ih (mutate B j) hs' j i (Ne.symm hij) hlj hli hmj hmi ha'
        (aligned_step B hs i j hij ha hc)]
      exact aligned_opposite_step B hs i j l m hij hli hlj hmi hmj hc

theorem mixed_first_aligned (a b c d E f : Int) (ha : 2≤a)
    (hb : 0≤b) (hd : 0≤d) (hE : 0≤E) (hc : c≤E) :
    Aligned (mutate (Q a b c d E f) 1) 1 0 := by
  intro l hl1 hl0
  have hl : l=2 ∨ l=3 := by omega
  rcases hl with rfl | rfl
  · change -d≤0 ∧ 0≤b+correction a d ∧ -(-d)≤b+correction a d
    rw [corr_positive a d (by omega) hd]
    have hm := mul_nonneg (show 0≤a-1 by omega) hd
    constructor
    · omega
    constructor <;> nlinarith
  · change -E≤0 ∧ 0≤ -c+correction a E ∧ -(-E)≤ -c+correction a E
    rw [corr_positive a E (by omega) hE]
    have hm := mul_nonneg (show 0≤a-2 by omega) hE
    constructor
    · omega
    constructor <;> nlinarith

theorem mixed_bounded_exit_forces_c_gt_E (a b c d E f : Int) (H n : Nat)
    (ha : 2≤a) (hb : 0≤b) (hd : 0≤d) (hE : 0≤E) (hf : f=(H:Int)+1)
    (hend : HeightLe (applyWord (Q a b c d E f) (alternatingWord 0 1 n)) H) :
    E<c := by
  by_contra hn
  have hc : c≤E := by omega
  have hlast := (hend 2 3).2
  cases n with
  | zero => change f≤(H:Int) at hlast; omega
  | succ n =>
      let B := mutate (Q a b c d E f) 1
      have hsB : SkewSymmetric B := mutation_preserves_skew _ _ (ofSix_skew _ _ _ _ _ _)
      have haB : 2≤B 1 0 := by change 2≤ -(-a); omega
      have hcB : Aligned B 1 0 := mixed_first_aligned a b c d E f ha hb hd hE hc
      have heq := aligned_opposite_constant n B hsB 1 0 2 3 (by decide)
        (by decide) (by decide) (by decide) (by decide) haB hcB
      change applyWord B (alternatingWord 1 0 n) 2 3≤(H:Int) at hlast
      rw [heq] at hlast
      change f+correction (-d) E≤(H:Int) at hlast
      rw [corr_nonpos_nonneg (-d) E (by omega) hE] at hlast
      omega

#print axioms aligned_opposite_constant
#print axioms mixed_bounded_exit_forces_c_gt_E
end QuiverProofs.Rank4StructureRound2.MixedExitGeometry
