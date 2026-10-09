import Rank4Round2.FlatUnitCeiling

/-! With the high pair and opposite top edge both positively oriented,
any unit connection between the entering pivot and a top-edge endpoint
forces a Pfaffian at least the full ceiling. Both adjacent states may be
at that ceiling. This does not supply the signed normalization of every
pivot-switching corridor or deal with a negatively oriented high pair.
-/
namespace Rank4Round2.FlatUnitBridge
open QuiverProofs Rank4Coordinator Rank4CoordinatorR2 Rank4Round2
open ProperOrder ProperMutation ProperObstructionSoundness
open Rank4ReviewRound2.PeakNormalization

def minusShape (A c d E : Int) (H : Nat) : Matrix 4 :=
  ofSix A (-1) (-c) d E ((H:Int)+1)

theorem negative_unit_pfaffian (A c d E : Int) (H : Nat) (hA : 2≤A)
    (h0 : HeightLe (mutate (minusShape A c d E H) 0) (H+1))
    (h2 : HeightLe (mutate (minusShape A c d E H) 2) (H+1)) :
    (H:Int)+1≤matrixPfaffian (minusShape A c d E H) := by
  have hF : 0<(H:Int)+1 := by omega
  have htop := (h0 2 3).2
  change (H:Int)+1+correction 1 (-c)≤((H+1:Nat):Int) at htop
  have hc : 0≤c := by
    have hm := le_max_left (-c) (0:Int)
    simp [correction] at htop
    omega
  have hE := (h0 1 3).1
  change -((H+1:Nat):Int)≤E+correction (-A) (-c) at hE
  have he : correction (-A) (-c)= -A*c := by
    simp only [correction,max_eq_right (show -A≤0 by omega),max_eq_right (show -c≤0 by omega),
      Int.neg_neg,max_eq_left (show 0≤A by omega),max_eq_left hc]
    ring
  rw [he] at hE
  simp only [Nat.cast_add,Nat.cast_one] at hE
  have hAc := mul_nonneg (show 0≤A by omega) hc
  have hdA : d≤A := by
    by_contra hn
    have hd : 3≤d := by omega
    have hb := (h2 1 3).2
    change E+correction d ((H:Int)+1)≤((H+1:Nat):Int) at hb
    have he2 : correction d ((H:Int)+1)=d*((H:Int)+1) := by
      simp only [correction,max_eq_left (show 0≤d by omega),max_eq_left (show 0≤(H:Int)+1 by omega),
        max_eq_right (show -d≤0 by omega),max_eq_right (show -((H:Int)+1)≤0 by omega)]
      ring
    rw [he2] at hb
    simp only [Nat.cast_add,Nat.cast_one] at hb
    have hprod := mul_nonneg (show 0≤d-3 by omega) (show 0≤(H:Int)+1 by omega)
    nlinarith
  have hp := mul_nonneg (show 0≤A-2 by omega) (show 0≤(H:Int)+1 by omega)
  have hcd := mul_nonneg hc (show 0≤A-d by omega)
  have hpf : matrixPfaffian (minusShape A c d E H)=A*((H:Int)+1)+E+(-c)*d := by
    simp [matrixPfaffian,minusShape,ofSix]
  rw [hpf]
  nlinarith

def unitShape (A b C d E : Int) (H : Nat) : Matrix 4 :=
  ofSix A b C d E ((H:Int)+1)

theorem unit_pfaffian_ge_ceiling (A b C d E : Int) (H : Nat)
    (hA : 2≤A) (hb : abs b=1)
    (hP : HeightLe (unitShape A b C d E H) (H+1))
    (h0 : HeightLe (mutate (unitShape A b C d E H) 0) (H+1))
    (h2 : HeightLe (mutate (unitShape A b C d E H) 2) (H+1)) :
    (H:Int)+1≤matrixPfaffian (unitShape A b C d E H) := by
  rcases le_total 0 b with hp|hn
  · rw [abs_of_nonneg hp] at hb
    subst b
    have h03 := (h2 0 3).2
    change C+correction 1 ((H:Int)+1)≤((H+1:Nat):Int) at h03
    have hF : 0≤(H:Int)+1 := by omega
    simp [correction,max_eq_left hF] at h03
    have hc : 0≤ -C := by omega
    have hcF := (hP 0 3).1
    have hEF := (hP 1 3).2
    change -((H+1:Nat):Int)≤C at hcF
    change E≤((H+1:Nat):Int) at hEF
    have heq : FlatUnitPfaffian.shape A (-C) d E H=unitShape A 1 C d E H := by
      simp [FlatUnitPfaffian.shape,unitShape]
    have hs : HeightLe (mutate (FlatUnitPfaffian.shape A (-C) d E H) 2) (H+1) := by
      rwa [heq]
    have h := FlatUnitCeiling.pfaffian_ge_ceiling A (-C) d E H hA hc
      (by simp only [Nat.cast_add,Nat.cast_one] at hcF; omega)
      (by simpa only [Nat.cast_add,Nat.cast_one] using hEF) hs
    rwa [heq] at h
  · rw [abs_of_nonpos hn] at hb
    have he : b= -1 := by omega
    subst b
    have heq : minusShape A (-C) d E H=unitShape A (-1) C d E H := by
      simp [minusShape,unitShape]
    have hs0 : HeightLe (mutate (minusShape A (-C) d E H) 0) (H+1) := by
      rwa [heq]
    have hs2 : HeightLe (mutate (minusShape A (-C) d E H) 2) (H+1) := by
      rwa [heq]
    have h := negative_unit_pfaffian A (-C) d E H hA hs0 hs2
    rwa [heq] at h

theorem no_low_totalProper_scalar_switch
    (hEnd : EndpointTopological4) (A b C d E : Int) (H : Nat)
    (hA : 2≤A) (hb : abs b=1)
    (hP : HeightLe (unitShape A b C d E H) (H+1))
    (h0 : HeightLe (mutate (unitShape A b C d E H) 0) (H+1))
    (h2 : HeightLe (mutate (unitShape A b C d E H) 2) (H+1))
    (q : CyclicOrder) (hq : TotalProper (unitShape A b C d E H) q)
    (hM : orderMarkov (unitShape A b C d E H) q≤(H:Int)) :
    ¬MutationAcyclic (unitShape A b C d E H) := by
  intro hma
  have hpf := unit_pfaffian_ge_ceiling A b C d E H hA hb hP h0 h2
  have hm := QuiverProofs.Rank4StructureRound2.SuperScalarPeak.MA_totalProper_pfaffian_bound
    hEnd (unitShape A b C d E H) (ofSix_skew _ _ _ _ _ _) hma q hq
  have habs := le_abs_self (matrixPfaffian (unitShape A b C d E H))
  omega

theorem no_initial_scalar_budget_switch
    (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4)
    (Q : Rank4Input) (lead : List (Fin 4)) (p : Relabeling 4) (r : Bool)
    (A b C d E : Int) (H : Nat) (hBudget : scalarBudget Q.val≤H)
    (hrep : signedFrame (applyWord Q.val lead) p r=unitShape A b C d E H)
    (hA : 2≤A) (hb : abs b=1)
    (hP : HeightLe (unitShape A b C d E H) (H+1))
    (h0 : HeightLe (mutate (unitShape A b C d E H) 0) (H+1))
    (h2 : HeightLe (mutate (unitShape A b C d E H) 2) (H+1)) :
    ¬MutationAcyclic Q.val := by
  intro hma
  have hmaP : MutationAcyclic (unitShape A b C d E H) := by
    rw [←hrep]
    exact (signedFrame_MA _ (word_preserves_skew Q.val lead Q.property) p r).mpr
      ((mutationAcyclic_word_iff Q.val lead).mpr hma)
  obtain ⟨q,hq⟩ := hExist _ (ofSix_skew _ _ _ _ _ _) hmaP
  have hq' : TotalProper (signedFrame (applyWord Q.val lead) p r) q := by
    rwa [hrep]
  have hscalar := ScalarPathBudget.lead_totalProper_scalar_budget Q.val Q.property lead p r q hq'
  rw [hrep] at hscalar
  have hle := Int.le_natAbs (a:=orderMarkov (unitShape A b C d E H) q)
  have hM : orderMarkov (unitShape A b C d E H) q≤(H:Int) := by omega
  exact no_low_totalProper_scalar_switch hEnd A b C d E H hA hb hP h0 h2 q hq hM hmaP

#print axioms negative_unit_pfaffian
#print axioms unit_pfaffian_ge_ceiling
#print axioms no_initial_scalar_budget_switch
end Rank4Round2.FlatUnitBridge
