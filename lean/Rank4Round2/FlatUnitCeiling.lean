import Rank4Round2.FlatUnitPfaffian

/-! A stronger normalized unit-switch obstruction permits incident edges
at the full ceiling H+1. No lower neighbor at H is required. The orientation
and signed-frame representation stay explicit; arbitrary flat-corridor
normalization and decomposition are separate obligations.
-/
namespace Rank4Round2.FlatUnitCeiling
open QuiverProofs Rank4Coordinator Rank4CoordinatorR2 Rank4Round2
open ProperOrder ProperMutation ProperObstructionSoundness
open FlatUnitPfaffian
open Rank4ReviewRound2.PeakNormalization

theorem pfaffian_ge_ceiling (A c d E : Int) (H : Nat)
    (hA : 2≤A) (hc : 0≤c) (hcF : c≤(H:Int)+1) (hEF : E≤(H:Int)+1)
    (h2 : HeightLe (mutate (shape A c d E H) 2) (H+1)) :
    (H:Int)+1≤matrixPfaffian (shape A c d E H) := by
  have hF : 0≤(H:Int)+1 := by omega
  have hp := mul_nonneg (show 0≤A-2 by omega) hF
  have heq : matrixPfaffian (shape A c d E H)=A*((H:Int)+1)-E+(-c)*d := by
    simp [matrixPfaffian,shape,ofSix]
  rw [heq]
  by_cases hd : d≤0
  · have hcd := mul_nonneg (show 0≤ -d by omega) hc
    nlinarith
  · have hd0 : 0≤d := by omega
    have h := (h2 1 3).2
    change E+correction d ((H:Int)+1)≤((H+1:Nat):Int) at h
    have he : correction d ((H:Int)+1)=d*((H:Int)+1) := by
      simp only [correction,max_eq_left hd0,max_eq_left hF,
        max_eq_right (show -d≤0 by omega),max_eq_right (show -((H:Int)+1)≤0 by omega)]
      ring
    rw [he] at h
    simp only [Nat.cast_add,Nat.cast_one] at h
    have hcd := mul_nonneg (show 0≤(H:Int)+1-c by omega) hd0
    nlinarith

theorem no_low_totalProper_scalar_switch
    (hEnd : EndpointTopological4) (A c d E : Int) (H : Nat)
    (hA : 2≤A) (hc : 0≤c) (hcF : c≤(H:Int)+1) (hEF : E≤(H:Int)+1)
    (h2 : HeightLe (mutate (shape A c d E H) 2) (H+1))
    (q : CyclicOrder) (hq : TotalProper (shape A c d E H) q)
    (hM : orderMarkov (shape A c d E H) q≤(H:Int)) :
    ¬MutationAcyclic (shape A c d E H) := by
  intro hma
  have hpf := pfaffian_ge_ceiling A c d E H hA hc hcF hEF h2
  have hm := QuiverProofs.Rank4StructureRound2.SuperScalarPeak.MA_totalProper_pfaffian_bound
    hEnd (shape A c d E H) (ofSix_skew _ _ _ _ _ _) hma q hq
  have habs := le_abs_self (matrixPfaffian (shape A c d E H))
  omega

theorem no_initial_scalar_budget_switch
    (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4)
    (Q : Rank4Input) (lead : List (Fin 4)) (p : Relabeling 4) (r : Bool)
    (A c d E : Int) (H : Nat) (hBudget : scalarBudget Q.val≤H)
    (hrep : signedFrame (applyWord Q.val lead) p r=shape A c d E H)
    (hA : 2≤A) (hc : 0≤c) (hcF : c≤(H:Int)+1) (hEF : E≤(H:Int)+1)
    (h2 : HeightLe (mutate (shape A c d E H) 2) (H+1)) :
    ¬MutationAcyclic Q.val := by
  intro hma
  have hmaP : MutationAcyclic (shape A c d E H) := by
    rw [←hrep]
    exact (signedFrame_MA _ (word_preserves_skew Q.val lead Q.property) p r).mpr
      ((mutationAcyclic_word_iff Q.val lead).mpr hma)
  obtain ⟨q,hq⟩ := hExist (shape A c d E H) (ofSix_skew _ _ _ _ _ _) hmaP
  have hq' : TotalProper (signedFrame (applyWord Q.val lead) p r) q := by
    rwa [hrep]
  have hb := ScalarPathBudget.lead_totalProper_scalar_budget Q.val Q.property lead p r q hq'
  rw [hrep] at hb
  have hle := Int.le_natAbs (a:=orderMarkov (shape A c d E H) q)
  have hM : orderMarkov (shape A c d E H) q≤(H:Int) := by omega
  exact no_low_totalProper_scalar_switch hEnd A c d E H hA hc hcF hEF h2 q hq hM hmaP

#print axioms pfaffian_ge_ceiling
#print axioms no_low_totalProper_scalar_switch
#print axioms no_initial_scalar_budget_switch
end Rank4Round2.FlatUnitCeiling
