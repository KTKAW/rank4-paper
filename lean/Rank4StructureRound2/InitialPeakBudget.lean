import Rank4StructureRound2.SuperScalarPeak
import Rank4CoordinatorR2.ScalarPathBudget

/-! All labels, all signs, every actual mutation prefix. Above the six-scalar
budget of the original input, a strict peak cannot join pivots of magnitude
at least two. Both external properness bridges remain explicit. This is a
local strict-peak exclusion, not a path-height supplier or classifier.+-/
namespace QuiverProofs.Rank4StructureRound2.InitialPeakBudget
open Census ProperOrder ProperWiggle ProperMutation ProperObstructionSoundness
open Rank4Coordinator Rank4CoordinatorR2 Rank4Round2
open Rank4ReviewRound2.PeakNormalization Rank4CoordinatorR2.ScalarPathBudget
open SuperScalarPeak
set_option maxHeartbeats 4000000

theorem actual_lead_strong_peak_parent_bound
    (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4)
    (B : Matrix 4) (hs : SkewSymmetric B) (hma : MutationAcyclic B)
    (lead : List (Fin 4)) (i j : Fin 4) (hij : i≠j) (H : Nat)
    (hbudget : scalarBudget B≤H)
    (hi : HeightLe (mutate (applyWord B lead) i) H)
    (hj : HeightLe (mutate (applyWord B lead) j) H)
    (hpair : 2≤abs (applyWord B lead i j)) : HeightLe (applyWord B lead) H := by
  by_contra hout
  let C := applyWord B lead
  have hC : SkewSymmetric C := word_preserves_skew B lead hs
  have hmaC : MutationAcyclic C := (mutationAcyclic_word_iff B lead).mpr hma
  obtain ⟨p,r,a,b,c,d,e,f,_,_,ha,ha0,hb,hc,hd,he,hf,heq,h0,h1⟩ :=
    strict_peak_normalization C hC i j hij H hi hj hout
  have ha2 : 2≤a := by rw [ha]; exact hpair
  have hcone := strong_normalized_high_cone a b c d e f H ha2 hb hc hd he hf h0 h1
  have hmap : MutationAcyclic (positivePeak a b c d e f) := by
    rw [←heq]
    exact (signedFrame_MA C hC p r).mpr hmaC
  obtain ⟨q,hq⟩ := hExist (positivePeak a b c d e f) (ofSix_skew _ _ _ _ _ _) hmap
  have hqframe : TotalProper (signedFrame (applyWord B lead) p r) q := by
    change TotalProper (signedFrame C p r) q
    rwa [heq]
  have hscalarbudget := lead_totalProper_scalar_budget B hs lead p r q hqframe
  have habs : (orderMarkov (positivePeak a b c d e f) q).natAbs≤H := by
    rw [heq] at hscalarbudget
    exact hscalarbudget.trans hbudget
  have hM : orderMarkov (positivePeak a b c d e f) q≤(H:Int) := by
    have hcast : ((orderMarkov (positivePeak a b c d e f) q).natAbs:Int)≤(H:Int) := by
      exact_mod_cast habs
    exact (Int.le_natAbs (a:=orderMarkov (positivePeak a b c d e f) q)).trans hcast
  have hl := positive_totalProper_scalar_bound hEnd a b c d e f ha2 (by omega)
    (by omega) (by omega) (by omega) hcone.1 hcone.2.1 hmap q hq
  change f<orderMarkov (positivePeak a b c d e f) q at hl
  omega

theorem actual_lead_strict_peak_pair_small
    (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4)
    (B : Matrix 4) (hs : SkewSymmetric B) (hma : MutationAcyclic B)
    (lead : List (Fin 4)) (i j : Fin 4) (hij : i≠j) (H : Nat)
    (hbudget : scalarBudget B≤H)
    (hi : HeightLe (mutate (applyWord B lead) i) H)
    (hj : HeightLe (mutate (applyWord B lead) j) H)
    (hout : ¬HeightLe (applyWord B lead) H) : abs (applyWord B lead i j)≤1 := by
  by_contra hnot
  exact hout (actual_lead_strong_peak_parent_bound hExist hEnd B hs hma lead i j hij H
    hbudget hi hj (by omega))

theorem endpoint_budget_strict_peak_pair_small
    (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4)
    (Q : Rank4Input) (hma : MutationAcyclic Q.val) (lead : List (Fin 4))
    (i j : Fin 4) (hij : i≠j) (H : Nat) (hbudget : endpointHeightBudget Q≤H)
    (hi : HeightLe (mutate (applyWord Q.val lead) i) H)
    (hj : HeightLe (mutate (applyWord Q.val lead) j) H)
    (hout : ¬HeightLe (applyWord Q.val lead) H) : abs (applyWord Q.val lead i j)≤1 := by
  apply actual_lead_strict_peak_pair_small hExist hEnd Q.val Q.property hma lead i j hij H
    (by unfold endpointHeightBudget at hbudget; omega) hi hj hout

#print axioms actual_lead_strong_peak_parent_bound
#print axioms actual_lead_strict_peak_pair_small
#print axioms endpoint_budget_strict_peak_pair_small
end QuiverProofs.Rank4StructureRound2.InitialPeakBudget
