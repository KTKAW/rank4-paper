import Rank4Round2.AllFrameUnitBridge

/-! Opposite-top strong-pair exit geometry. Two incident bounds at the
actual preceding state are enough to reduce every nonzero connector to a
unit edge or a scalar/acyclic branch. No whole preceding H bound is used.+-/
namespace Rank4Round2.NonzeroExitGeometry
open QuiverProofs Rank4Coordinator Rank4CoordinatorR2 Rank4Round2
open FlatUnitBridge

private theorem corr_pos (x y : Int) (hx : 0≤x) (hy : 0≤y) : correction x y=x*y := by
  simp only [correction,max_eq_left hx,max_eq_left hy,
    max_eq_right (show -x≤0 by omega),max_eq_right (show -y≤0 by omega)]
  ring
private theorem corr_neg (x y : Int) (hx : x≤0) (hy : y≤0) : correction x y= -x*y := by
  simp only [correction,max_eq_right hx,max_eq_right hy,
    max_eq_left (show 0≤ -x by omega),max_eq_left (show 0≤ -y by omega)]
  ring
private theorem corr_mixed (x y : Int) (hx : 0≤x) (hy : y≤0) : correction x y=0 := by
  simp only [correction,max_eq_left hx,max_eq_right hy,
    max_eq_right (show -x≤0 by omega)]
  ring

theorem exit_geometry (A b C d E : Int) (H : Nat) (hb : b≠0)
    (h0 : HeightLe (mutate (unitShape A b C d E H) 0) (H+1))
    (h2 : HeightLe (mutate (unitShape A b C d E H) 2) (H+1))
    (h03 : -(H:Int)≤mutate (unitShape A b C d E H) 0 0 3 ∧
      mutate (unitShape A b C d E H) 0 0 3≤(H:Int))
    (h13 : -(H:Int)≤mutate (unitShape A b C d E H) 0 1 3 ∧
      mutate (unitShape A b C d E H) 0 1 3≤(H:Int)) :
    C≤0 ∧ -(H:Int)≤C ∧ -(H:Int)≤E ∧
      (0<b → b=1) ∧ d≤1 ∧ (d=1 → E≤0) := by
  have hF : 0≤(H:Int)+1 := by omega
  have hC : C≤0 := by
    by_cases hp : 0<b
    · have h := (h2 0 3).2
      change C+correction b ((H:Int)+1)≤((H+1:Nat):Int) at h
      rw [corr_pos b _ (by omega) hF] at h
      simp only [Nat.cast_add,Nat.cast_one] at h
      have hprod := mul_nonneg (show 0≤b-1 by omega) hF
      nlinarith
    · have hn : b<0 := by omega
      by_contra hc
      have h := (h0 2 3).2
      change (H:Int)+1+correction (-b) C≤((H+1:Nat):Int) at h
      rw [corr_pos (-b) C (by omega) (by omega)] at h
      simp only [Nat.cast_add,Nat.cast_one] at h
      have hprod := mul_pos (show 0< -b by omega) (show 0<C by omega)
      nlinarith
  change -(H:Int)≤ -C ∧ -C≤(H:Int) at h03
  have hCorr : correction (-A) C≤0 := by
    simp only [correction,max_eq_right hC,mul_zero,zero_sub]
    exact neg_nonpos.mpr (mul_nonneg (le_max_right _ _) (le_max_right _ _))
  change -(H:Int)≤E+correction (-A) C ∧ E+correction (-A) C≤(H:Int) at h13
  have hE : -(H:Int)≤E := by omega
  have hUnit : 0<b → b=1 := by
    intro hp
    have h := (h2 0 3).2
    change C+correction b ((H:Int)+1)≤((H+1:Nat):Int) at h
    rw [corr_pos b _ (by omega) hF] at h
    simp only [Nat.cast_add,Nat.cast_one] at h
    by_contra hn
    have hb2 : 2≤b := by omega
    have hprod := mul_nonneg (show 0≤b-2 by omega) hF
    nlinarith
  have hd : d≤1 := by
    by_contra hn
    have hd2 : 2≤d := by omega
    have h := (h2 1 3).2
    change E+correction d ((H:Int)+1)≤((H+1:Nat):Int) at h
    rw [corr_pos d _ (by omega) hF] at h
    simp only [Nat.cast_add,Nat.cast_one] at h
    have hprod := mul_nonneg (show 0≤d-2 by omega) hF
    nlinarith
  refine ⟨hC,by omega,hE,hUnit,hd,?_⟩
  intro hd1
  have h := (h2 1 3).2
  change E+correction d ((H:Int)+1)≤((H+1:Nat):Int) at h
  rw [hd1,corr_pos 1 _ (by decide) hF] at h
  simp only [Nat.cast_add,Nat.cast_one,one_mul] at h
  omega

theorem alternate_neighbor (A b C E : Int) (H : Nat)
    (hA : 2≤A) (hb : b<0) (hE : E≤0)
    (hP : HeightLe (unitShape A b C 1 E H) (H+1)) :
    HeightLe (mutate (unitShape A b C 1 E H) 1) (H+1) := by
  have hrec := (ofSix_reconstruct (mutate (unitShape A b C 1 E H) 1)
    (mutation_preserves_skew _ _ (ofSix_skew _ _ _ _ _ _))).symm
  change mutate (unitShape A b C 1 E H) 1=
    ofSix (-A) (b+correction A 1) (C+correction A E) (-1) (-E)
      ((H:Int)+1+correction (-1) E) at hrec
  rw [corr_pos A 1 (by omega) (by decide),corr_mixed A E (by omega) hE,
    corr_neg (-1) E (by decide) hE] at hrec
  rw [hrec]
  have ha := hP 0 1
  have hb0 := hP 0 2
  have hc := hP 0 3
  have he := hP 1 3
  change -((H+1:Nat):Int)≤A ∧ A≤((H+1:Nat):Int) at ha
  change -((H+1:Nat):Int)≤b ∧ b≤((H+1:Nat):Int) at hb0
  change -((H+1:Nat):Int)≤C ∧ C≤((H+1:Nat):Int) at hc
  change -((H+1:Nat):Int)≤E ∧ E≤((H+1:Nat):Int) at he
  intro i j
  have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  have hj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
  rcases hi with rfl|rfl|rfl|rfl <;> rcases hj with rfl|rfl|rfl|rfl <;>
    simp only [ofSix] <;> omega

#print axioms exit_geometry
#print axioms alternate_neighbor
end Rank4Round2.NonzeroExitGeometry
