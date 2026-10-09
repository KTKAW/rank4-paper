import Rank4Round2.NegativeUnitScalar

/-! Every sign of the high pair is covered for the supplied actual unit
switch configuration. Both neighbors may reach the full ceiling. No
arbitrary flat-block decomposition or unit-connection supplier is asserted.+-/
namespace Rank4Round2.AllSignUnitBridge
open QuiverProofs Rank4Coordinator Rank4CoordinatorR2 Rank4Round2
open ProperOrder ProperWiggle ProperMutation ProperObstructionSoundness
open Rank4ReviewRound2.PeakNormalization
open FlatUnitBridge

def negativeShape (a b c d E : Int) (H : Nat) : Matrix 4 :=
  unitShape (-a) b (-c) d E H

private theorem four (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega

theorem negative_minus_acyclic (a c d E : Int) (H : Nat)
    (ha : 2≤a) (hc : 0≤c) (hd : d<0) :
    Acyclic (negativeShape a (-1) c d E H) := by
  by_cases hE : 0≤E
  · refine ⟨fun i => match i.val with | 0=>3 | 1=>1 | 2=>0 | _=>2,?_⟩
    intro i j h
    rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
      simp [negativeShape,unitShape,ofSix] at * <;> omega
  · refine ⟨fun i => match i.val with | 0=>3 | 1=>2 | 2=>0 | _=>1,?_⟩
    intro i j h
    rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
      simp [negativeShape,unitShape,ofSix] at * <;> omega

theorem no_negative_low_scalar
    (hEnd : EndpointTopological4) (a b c d E : Int) (H : Nat)
    (ha : 2≤a) (hc : 0≤c) (hb : b=1 ∨ b= -1)
    (hP : HeightLe (negativeShape a b c d E H) (H+1))
    (p : CyclicOrder) (hp : TotalProper (negativeShape a b c d E H) p)
    (hM : orderMarkov (negativeShape a b c d E H) p≤(H:Int)) :
    ¬MutationAcyclic (negativeShape a b c d E H) := by
  intro hma
  let B := negativeShape a b c d E H
  have hF : 0<(H:Int)+1 := by omega
  have hn := QuiverProofs.Rank4StructureRound2.SuperScalarPeak.MA_totalProper_pfaffian_bound
    hEnd B (ofSix_skew _ _ _ _ _ _) hma p hp
  have hElo := (hP 1 3).1
  have hEhi := (hP 1 3).2
  have hcF := (hP 0 3).1
  change -((H+1:Nat):Int)≤E at hElo
  change E≤((H+1:Nat):Int) at hEhi
  change -((H+1:Nat):Int)≤ -c at hcF
  simp only [Nat.cast_add,Nat.cast_one] at hElo hEhi hcF
  by_cases hd : 0≤d
  · have hcd := mul_nonneg hc hd
    have haf := mul_nonneg (show 0≤a-2 by omega) (show 0≤(H:Int)+1 by omega)
    have hpf : matrixPfaffian B≤ -((H:Int)+1) := by
      rcases hb with rfl|rfl <;>
        simp [B,negativeShape,unitShape,matrixPfaffian,ofSix] <;> nlinarith
    have habs := neg_le_abs (matrixPfaffian B)
    change orderMarkov B p≤(H:Int) at hM
    omega
  · have hd' : 1≤ -d := by omega
    rcases hb with rfl|rfl
    · by_cases hE : 0≤E
      · have heq : NegativeUnitScalar.Q a c (-d) E ((H:Int)+1) false=B := by
          simp [NegativeUnitScalar.Q,B,negativeShape,unitShape]
        have h := NegativeUnitScalar.negative_totalProper_scalar_exceeds_height hEnd
          a c (-d) E ((H:Int)+1) false ha hc hd' hE (by omega) hEhi hF
          (by rwa [heq]) p (by rwa [heq])
        rw [heq] at h
        change orderMarkov B p≤(H:Int) at hM
        omega
      · have heq : NegativeUnitScalar.Q a c (-d) (-E) ((H:Int)+1) true=B := by
          simp [NegativeUnitScalar.Q,B,negativeShape,unitShape]
        have h := NegativeUnitScalar.negative_totalProper_scalar_exceeds_height hEnd
          a c (-d) (-E) ((H:Int)+1) true ha hc hd' (by omega) (by omega) (by omega) hF
          (by rwa [heq]) p (by rwa [heq])
        rw [heq] at h
        change orderMarkov B p≤(H:Int) at hM
        omega
    · have haB : Acyclic B := negative_minus_acyclic a c d E H ha hc (by omega)
      obtain ⟨q,hq,hpq⟩ := hEnd B (ofSix_skew _ _ _ _ _ _) haB p hp
      have heq := ProperWiggleInvariants.markov_wiggle_invariant B (ofSix_skew _ _ _ _ _ _) hpq
      have hh := topological_height_budget B (ofSix_skew _ _ _ _ _ _) q hq
      have htop := (hh 2 3).2
      change (H:Int)+1≤((orderMarkov B q).natAbs:Int) at htop
      rw [←heq] at htop
      have hnonneg : 0≤orderMarkov B p := by
        have habs := abs_nonneg (matrixPfaffian B)
        omega
      rw [Int.natCast_natAbs,abs_of_nonneg hnonneg] at htop
      change orderMarkov B p≤(H:Int) at hM
      omega

theorem no_low_totalProper_scalar_switch
    (hEnd : EndpointTopological4) (A b C d E : Int) (H : Nat)
    (hA : 2≤abs A) (hb : abs b=1)
    (hP : HeightLe (unitShape A b C d E H) (H+1))
    (h0 : HeightLe (mutate (unitShape A b C d E H) 0) (H+1))
    (h2 : HeightLe (mutate (unitShape A b C d E H) 2) (H+1))
    (p : CyclicOrder) (hp : TotalProper (unitShape A b C d E H) p)
    (hM : orderMarkov (unitShape A b C d E H) p≤(H:Int)) :
    ¬MutationAcyclic (unitShape A b C d E H) := by
  by_cases hpos : 2≤A
  · exact FlatUnitBridge.no_low_totalProper_scalar_switch hEnd A b C d E H hpos hb hP h0 h2 p hp hM
  · have hneg : A≤ -2 := by
      by_cases hn : 0≤A
      · rw [abs_of_nonneg hn] at hA; omega
      · rw [abs_of_nonpos (show A≤0 by omega)] at hA; omega
    have hb' : b=1 ∨ b= -1 := by
      rcases le_total 0 b with hh|hh
      · rw [abs_of_nonneg hh] at hb; exact Or.inl hb
      · rw [abs_of_nonpos hh] at hb; exact Or.inr (by omega)
    have hc : 0≤ -C := by
      rcases hb' with hh|hh
      · have h := (h2 0 3).2
        change C+correction b ((H:Int)+1)≤((H+1:Nat):Int) at h
        rw [hh] at h
        simp [correction,max_eq_left (show 0≤(H:Int)+1 by omega)] at h
        omega
      · have h := (h0 2 3).2
        change (H:Int)+1+correction (-b) C≤((H+1:Nat):Int) at h
        rw [hh] at h
        have hm := le_max_left C (0:Int)
        simp [correction] at h
        omega
    have heq : negativeShape (-A) b (-C) d E H=unitShape A b C d E H := by
      simp [negativeShape,unitShape]
    exact no_negative_low_scalar hEnd (-A) b (-C) d E H (by omega) hc hb'
      (by rwa [heq]) p (by rwa [heq]) (by rwa [heq]) ∘
      (fun hma => by rwa [heq])

theorem no_initial_scalar_budget_switch
    (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4)
    (Q : Rank4Input) (lead : List (Fin 4)) (p : Relabeling 4) (r : Bool)
    (A b C d E : Int) (H : Nat) (hBudget : scalarBudget Q.val≤H)
    (hrep : signedFrame (applyWord Q.val lead) p r=unitShape A b C d E H)
    (hA : 2≤abs A) (hb : abs b=1)
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
  have hq' : TotalProper (signedFrame (applyWord Q.val lead) p r) q := by rwa [hrep]
  have hscalar := ScalarPathBudget.lead_totalProper_scalar_budget Q.val Q.property lead p r q hq'
  rw [hrep] at hscalar
  have hle := Int.le_natAbs (a:=orderMarkov (unitShape A b C d E H) q)
  have hM : orderMarkov (unitShape A b C d E H) q≤(H:Int) := by omega
  exact no_low_totalProper_scalar_switch hEnd A b C d E H hA hb hP h0 h2 q hq hM hmaP

#print axioms no_negative_low_scalar
#print axioms no_low_totalProper_scalar_switch
#print axioms no_initial_scalar_budget_switch
end Rank4Round2.AllSignUnitBridge
