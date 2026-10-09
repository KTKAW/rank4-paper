import Rank4ReviewRound2.StrongPairCorridor
import Rank4StructureRound2.TwoStateFrame
import Rank4StructureRound2.InitialPeakBudget

/-! All signs, vertex labels, and original scalar budgets: a constant
alternating strong-pair excursion entered from below H cannot return below
H while keeping ceiling H+1. Proper-existence and endpoint bridges stay
explicit. No decomposition of switched-pair blocks is supplied here. -/
namespace Rank4ReviewRound2.StrongPairBudget
open QuiverProofs Rank4Coordinator Rank4CoordinatorR2 Rank4Round2
open ProperOrder ProperMutation ProperObstructionSoundness
open QuiverProofs.Rank4StructureRound2
open PeakNormalization ScalarPathBudget StrongPairIncident

private theorem alternating_map (p : Relabeling 4) (i j : Fin 4) (n : Nat) :
    (alternatingWord i j n).map p.toFun=alternatingWord (p.toFun i) (p.toFun j) n := by
  induction n generalizing i j with
  | zero => rfl
  | succ n ih => simp only [alternatingWord,List.map_cons,ih]

theorem actual_lead_strong_pair_return_parent_bound
    (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4)
    (B : Matrix 4) (hs : SkewSymmetric B) (hma : MutationAcyclic B)
    (lead : List (Fin 4)) (i j : Fin 4) (hij : i≠j) (H n : Nat)
    (hbudget : scalarBudget B≤H)
    (hBack : HeightLe (mutate (applyWord B lead) i) H)
    (hCeil : ∀ k≤n, HeightLe
      (applyWord (applyWord B lead) (alternatingWord i j k)) (H+1))
    (hEndState : HeightLe
      (applyWord (applyWord B lead) (alternatingWord i j n)) H)
    (hpair : 2≤abs (applyWord B lead i j)) : HeightLe (applyWord B lead) H := by
  by_cases hn : 2≤n
  · by_contra hout
    let P := applyWord B lead
    let pp := pivotFrame i j
    let R := relabel P pp
    have hsP : SkewSymmetric P := word_preserves_skew B lead hs
    have hsR : SkewSymmetric R := relabel_skew P pp hsP
    have hmaP : MutationAcyclic P := (mutationAcyclic_word_iff B lead).mpr hma
    have hmaR : MutationAcyclic R := (MA_relabel_iff P pp).mpr hmaP
    have hslots := pivotFrame_slots i j hij
    have hpp0 : pp.toFun 0=i := hslots.1
    have hpp1 : pp.toFun 1=j := hslots.2
    have hRP : HeightLe R (H+1) := (heightLe_relabel_iff P pp (H+1)).mpr (hCeil 0 (by omega))
    have hR0 : HeightLe (mutate R 0) H := by
      change HeightLe (mutate (relabel P pp) 0) H
      rw [mutate_relabel,heightLe_relabel_iff,hpp0];exact hBack
    have hR1 : HeightLe (mutate R 1) (H+1) := by
      change HeightLe (mutate (relabel P pp) 1) (H+1)
      rw [mutate_relabel,heightLe_relabel_iff,hpp1]
      exact hCeil 1 (by omega)
    have hRpair : 2≤abs (R 0 1) := by
      change 2≤abs (P (pp.toFun 0) (pp.toFun 1))
      rw [hpp0,hpp1];exact hpair
    have hRo : ¬HeightLe R H := fun h=>hout ((heightLe_relabel_iff P pp H).mp h)
    obtain ⟨p,r,a,b,c,d,E,f,hp0,hp1,ha,hb,hc,hf,heq⟩ :=
      TwoStateFrame.half_peak_normalization R hsR H hRP hR0 hR1 hRo hRpair
    let frame := pp.trans p
    have hframe : signedFrame P frame r=TwoStateScalar.Q a b c d E f := heq
    have hf0 : frame.toFun 0=i := by change pp.toFun (p.toFun 0)=i;rw [hp0,hpp0]
    have hf1 : frame.toFun 1=j := by change pp.toFun (p.toFun 1)=j;rw [hp1,hpp1]
    have hmap : MutationAcyclic (TwoStateScalar.Q a b c d E f) := by
      rw [←hframe]
      exact (signedFrame_MA P hsP frame r).mpr hmaP
    obtain ⟨q,hq⟩ := hExist _ (ofSix_skew _ _ _ _ _ _) hmap
    have hqframe : TotalProper (signedFrame (applyWord B lead) frame r) q := by
      change TotalProper (signedFrame P frame r) q
      rwa [hframe]
    have hqb := lead_totalProper_scalar_budget B hs lead frame r q hqframe
    rw [hframe] at hqb
    have habs : (orderMarkov (TwoStateScalar.Q a b c d E f) q).natAbs≤H := hqb.trans hbudget
    have hM : orderMarkov (TwoStateScalar.Q a b c d E f) q≤(H:Int) := by
      have hcast : ((orderMarkov (TwoStateScalar.Q a b c d E f) q).natAbs:Int)≤(H:Int) := by
        exact_mod_cast habs
      exact (Int.le_natAbs (a:=orderMarkov (TwoStateScalar.Q a b c d E f) q)).trans hcast
    have hword : ∀ k, applyWord (TwoStateScalar.Q a b c d E f) (alternatingWord 0 1 k)=
        signedFrame (applyWord P (alternatingWord i j k)) frame r := by
      intro k
      rw [←hframe,signedFrame_word,alternating_map,hf0,hf1]
    have hQ0 : HeightLe (mutate (TwoStateScalar.Q a b c d E f) 0) H := by
      rw [←hframe,signedFrame_mutate,hf0,signedFrame_height]
      exact hBack
    have hQCeil : ∀ k≤n,HeightLe
        (applyWord (TwoStateScalar.Q a b c d E f) (alternatingWord 0 1 k)) (H+1) := by
      intro k hk
      rw [hword,signedFrame_height]
      exact hCeil k hk
    have hQEnd : HeightLe
        (applyWord (TwoStateScalar.Q a b c d E f) (alternatingWord 0 1 n)) H := by
      rw [hword,signedFrame_height]
      exact hEndState
    exact StrongPairCorridor.normalized_no_return hEnd n hn a b c d E f H
      ha hb hc hf hQ0 hQCeil hQEnd hmap q hq hM
  · have hn' : n=0 ∨ n=1 := by omega
    rcases hn' with rfl|rfl
    · exact hEndState
    · exact InitialPeakBudget.actual_lead_strong_peak_parent_bound hExist hEnd B hs hma
        lead i j hij H hbudget hBack hEndState hpair

theorem endpoint_budget_strong_pair_return_parent_bound
    (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4)
    (Q : Rank4Input) (hma : MutationAcyclic Q.val) (lead : List (Fin 4))
    (i j : Fin 4) (hij : i≠j) (H n : Nat) (hbudget : endpointHeightBudget Q≤H)
    (hBack : HeightLe (mutate (applyWord Q.val lead) i) H)
    (hCeil : ∀ k≤n, HeightLe
      (applyWord (applyWord Q.val lead) (alternatingWord i j k)) (H+1))
    (hEndState : HeightLe
      (applyWord (applyWord Q.val lead) (alternatingWord i j n)) H)
    (hpair : 2≤abs (applyWord Q.val lead i j)) : HeightLe (applyWord Q.val lead) H :=
  actual_lead_strong_pair_return_parent_bound hExist hEnd Q.val Q.property hma lead i j hij H n
    (by unfold endpointHeightBudget at hbudget;omega) hBack hCeil hEndState hpair

#print axioms actual_lead_strong_pair_return_parent_bound
#print axioms endpoint_budget_strong_pair_return_parent_bound
end Rank4ReviewRound2.StrongPairBudget
