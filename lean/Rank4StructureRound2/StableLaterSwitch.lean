import Rank4StructureRound2.MixedExitGeometry

/-! Later pivot-switch geometry in the stable cone. One further fixed-pair
mutation makes the incoming row strictly negative and the other row strictly
positive at both frozen vertices. Such a state cannot mutate either frozen
vertex inside its opposite-edge ceiling. No MA or scalar premise is needed. -/
namespace QuiverProofs.Rank4StructureRound2.StableLaterSwitch
open Rank4Coordinator MixedExitGeometry
set_option maxHeartbeats 4000000

private theorem corr_positive (x y : Int) (hx : 0≤x) (hy : 0≤y) : correction x y=x*y := by
  simp only [correction,max_eq_left hx,max_eq_left hy,
    max_eq_right (show -x≤0 by omega),max_eq_right (show -y≤0 by omega)]
  ring
private theorem corr_negative (x y : Int) (hx : x≤0) (hy : y≤0) : correction x y= -x*y := by
  simp only [correction,max_eq_right hx,max_eq_right hy,
    max_eq_left (show 0≤ -x by omega),max_eq_left (show 0≤ -y by omega)]
  ring

theorem aligned_positive_step_strict (B : Matrix 4) (i j : Fin 4) (hij : i≠j)
    (ha : 2≤B i j) (hc : Aligned B i j)
    (hpos : ∀ l,l≠i → l≠j → 0<B j l) :
    ∀ l,l≠i → l≠j → mutate B j j l<0 ∧ 0<mutate B j i l := by
  intro l hli hlj
  have ht := hc l hli hlj
  have hp := hpos l hli hlj
  have hmul := mul_nonneg (show 0≤B i j-2 by omega) (show 0≤B j l by omega)
  have hi : mutate B j i l=B i l+B i j*B j l := by
    simp only [mutate,if_neg (show ¬(i=j ∨ l=j) by omega)]
    rw [corr_positive _ _ (by omega) (by omega)]
  have hj : mutate B j j l= -B j l := by simp [mutate]
  rw [hi,hj]
  constructor
  · omega
  · nlinarith

theorem strict_rows_opposite_ceiling_no_third (B : Matrix 4) (hs : SkewSymmetric B)
    (i j k l : Fin 4) (hik : i≠k) (hil : i≠l) (hjk : j≠k) (hjl : j≠l)
    (hkl : k≠l) (H : Nat) (hf : B k l=(H:Int)+1)
    (hikNeg : B i k<0) (hilNeg : B i l<0) (hjkPos : 0<B j k) (hjlPos : 0<B j l) :
    ¬HeightLe (mutate B k) (H+1) ∧ ¬HeightLe (mutate B l) (H+1) := by
  have hF : 0<(H:Int)+1 := by omega
  constructor
  · intro hk
    have h := (hk j l).2
    simp only [mutate,if_neg (show ¬(j=k ∨ l=k) by omega)] at h
    rw [hf,corr_positive _ _ (by omega) (by omega)] at h
    have hprod := mul_nonneg (show 0≤B j k-1 by omega) hF.le
    simp only [Nat.cast_add,Nat.cast_one] at h
    nlinarith
  · intro hl
    have h := (hl i k).1
    simp only [mutate,if_neg (show ¬(i=l ∨ k=l) by omega)] at h
    have hlk : B l k= -((H:Int)+1) := by rw [hs l k,hf]
    rw [hlk,corr_negative _ _ (by omega) (by omega)] at h
    have hprod := mul_nonneg (show 0≤ -B i l-1 by omega) hF.le
    simp only [Nat.cast_add,Nat.cast_one] at h
    nlinarith

#print axioms aligned_positive_step_strict
#print axioms strict_rows_opposite_ceiling_no_third
end QuiverProofs.Rank4StructureRound2.StableLaterSwitch
