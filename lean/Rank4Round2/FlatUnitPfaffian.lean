import Rank4CoordinatorR2.ScalarPathBudget
import Rank4StructureRound2.SuperScalarPeak

/-! The refined high-pair entry/unit-switch shape has Pfaffian larger than
its top height. It is therefore excluded above a supplied total-proper scalar
or the original scalar budget. This does not assert the refuted broad weak
unit detour, and does not decompose arbitrary pivot-switching plateaus.
-/
namespace Rank4Round2.FlatUnitPfaffian
open QuiverProofs Rank4Coordinator Rank4CoordinatorR2 Rank4Round2
open ProperOrder ProperMutation ProperObstructionSoundness
open Rank4ReviewRound2.PeakNormalization

def shape (A c d E : Int) (H : Nat) : Matrix 4 :=
  ofSix A 1 (-c) d E ((H:Int)+1)

theorem bounded_two_d_le_one (A c d E : Int) (H : Nat)
    (hE : -(H:Int)≤E) (h2 : HeightLe (mutate (shape A c d E H) 2) (H+1)) : d≤1 := by
  have h := (h2 1 3).2
  change E+correction d ((H:Int)+1)≤((H+1:Nat):Int) at h
  by_contra hn
  have hd : 2≤d := by omega
  have hF : 0≤(H:Int)+1 := by omega
  have he : correction d ((H:Int)+1)=d*((H:Int)+1) := by
    simp only [correction,max_eq_left (show 0≤d by omega),max_eq_left hF,
      max_eq_right (show -d≤0 by omega),max_eq_right (show -((H:Int)+1)≤0 by omega)]
    ring
  rw [he] at h
  have hp := mul_nonneg (show 0≤d-2 by omega) hF
  simp only [Nat.cast_add,Nat.cast_one] at h
  nlinarith

theorem bounded_two_d_one_E_nonpositive (A c E : Int) (H : Nat)
    (h2 : HeightLe (mutate (shape A c 1 E H) 2) (H+1)) : E≤0 := by
  have h := (h2 1 3).2
  change E+correction 1 ((H:Int)+1)≤((H+1:Nat):Int) at h
  have hF : 0≤(H:Int)+1 := by omega
  simp [correction,max_eq_left hF,max_eq_right (show -((H:Int)+1)≤0 by omega)] at h
  omega

theorem pfaffian_gt_height (A c d E : Int) (H : Nat)
    (hA : 2≤A) (hc : 0≤c) (hcH : c≤(H:Int))
    (hElo : -(H:Int)≤E) (hEhi : E≤(H:Int))
    (h2 : HeightLe (mutate (shape A c d E H) 2) (H+1)) :
    (H:Int)+1<matrixPfaffian (shape A c d E H) := by
  have hd := bounded_two_d_le_one A c d E H hElo h2
  have hp := mul_nonneg (show 0≤A-2 by omega) (show 0≤(H:Int)+1 by omega)
  have heq : matrixPfaffian (shape A c d E H)=A*((H:Int)+1)-E+(-c)*d := by
    simp [matrixPfaffian,shape,ofSix]
  rw [heq]
  by_cases hd0 : d≤0
  · have hcd := mul_nonneg (show 0≤ -d by omega) hc
    nlinarith
  · have hd1 : d=1 := by omega
    subst d
    have hE := bounded_two_d_one_E_nonpositive A c E H h2
    nlinarith

theorem no_low_totalProper_scalar_switch
    (hEnd : EndpointTopological4) (A c d E : Int) (H : Nat)
    (hA : 2≤A) (hc : 0≤c) (hcH : c≤(H:Int))
    (hElo : -(H:Int)≤E) (hEhi : E≤(H:Int))
    (h2 : HeightLe (mutate (shape A c d E H) 2) (H+1))
    (q : CyclicOrder) (hq : TotalProper (shape A c d E H) q)
    (hM : orderMarkov (shape A c d E H) q≤(H:Int)) :
    ¬MutationAcyclic (shape A c d E H) := by
  intro hma
  have hpf := pfaffian_gt_height A c d E H hA hc hcH hElo hEhi h2
  have hm := QuiverProofs.Rank4StructureRound2.SuperScalarPeak.MA_totalProper_pfaffian_bound
    hEnd (shape A c d E H) (ofSix_skew _ _ _ _ _ _) hma q hq
  have habs := le_abs_self (matrixPfaffian (shape A c d E H))
  omega

theorem no_initial_scalar_budget_switch
    (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4)
    (Q : Rank4Input) (lead : List (Fin 4)) (p : Relabeling 4) (r : Bool)
    (A c d E : Int) (H : Nat) (hBudget : scalarBudget Q.val≤H)
    (hrep : signedFrame (applyWord Q.val lead) p r=shape A c d E H)
    (hA : 2≤A) (hc : 0≤c) (hcH : c≤(H:Int))
    (hElo : -(H:Int)≤E) (hEhi : E≤(H:Int))
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
  exact no_low_totalProper_scalar_switch hEnd A c d E H hA hc hcH hElo hEhi h2 q hq hM hmaP

#print axioms pfaffian_gt_height
#print axioms no_low_totalProper_scalar_switch
#print axioms no_initial_scalar_budget_switch
end Rank4Round2.FlatUnitPfaffian
