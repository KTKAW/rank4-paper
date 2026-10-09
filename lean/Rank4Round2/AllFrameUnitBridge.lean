import Rank4Round2.AllSignUnitBridge

/-! Actual arbitrary-label unit-switch exclusion. The sign of the opposite
top edge is normalized computationally, and the complete matrix is
reconstructed from its actual entries. No separate shape supplier is needed.+-/
namespace Rank4Round2.AllFrameUnitBridge
open QuiverProofs Rank4Coordinator Rank4CoordinatorR2 Rank4Round2
open ProperObstructionSoundness
open Rank4ReviewRound2.PeakNormalization

theorem normalized_actual_switch
    (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4)
    (Q : Rank4Input) (lead : List (Fin 4)) (p : Relabeling 4) (r : Bool)
    (H : Nat) (hBudget : scalarBudget Q.val≤H)
    (hF : signedFrame (applyWord Q.val lead) p r 2 3=(H:Int)+1)
    (hA : 2≤abs (signedFrame (applyWord Q.val lead) p r 0 1))
    (hb : abs (signedFrame (applyWord Q.val lead) p r 0 2)=1)
    (hP : HeightLe (signedFrame (applyWord Q.val lead) p r) (H+1))
    (h0 : HeightLe (mutate (signedFrame (applyWord Q.val lead) p r) 0) (H+1))
    (h2 : HeightLe (mutate (signedFrame (applyWord Q.val lead) p r) 2) (H+1)) :
    ¬MutationAcyclic Q.val := by
  let S := signedFrame (applyWord Q.val lead) p r
  have hs : SkewSymmetric S := signedFrame_skew _ (word_preserves_skew Q.val lead Q.property) p r
  have hrep : S=FlatUnitBridge.unitShape (S 0 1) (S 0 2) (S 0 3) (S 1 2) (S 1 3) H := by
    unfold FlatUnitBridge.unitShape
    rw [←hF]
    exact (ofSix_reconstruct S hs).symm
  exact AllSignUnitBridge.no_initial_scalar_budget_switch hExist hEnd Q lead p r
    (S 0 1) (S 0 2) (S 0 3) (S 1 2) (S 1 3) H hBudget hrep hA hb
    (by rwa [←hrep]) (by rwa [←hrep]) (by rwa [←hrep])

theorem arbitrary_label_unit_switch
    (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4)
    (Q : Rank4Input) (lead : List (Fin 4)) (p : Relabeling 4)
    (H : Nat) (hBudget : scalarBudget Q.val≤H)
    (hA : 2≤abs (applyWord Q.val lead (p.toFun 0) (p.toFun 1)))
    (hb : abs (applyWord Q.val lead (p.toFun 0) (p.toFun 2))=1)
    (hF : abs (applyWord Q.val lead (p.toFun 2) (p.toFun 3))=(H:Int)+1)
    (hP : HeightLe (applyWord Q.val lead) (H+1))
    (h0 : HeightLe (mutate (applyWord Q.val lead) (p.toFun 0)) (H+1))
    (h2 : HeightLe (mutate (applyWord Q.val lead) (p.toFun 2)) (H+1)) :
    ¬MutationAcyclic Q.val := by
  let B := applyWord Q.val lead
  let r := decide (B (p.toFun 2) (p.toFun 3)<0)
  have htop : signedFrame B p r 2 3=(H:Int)+1 := by
    by_cases hs : 0≤B (p.toFun 2) (p.toFun 3)
    · have hn : ¬B (p.toFun 2) (p.toFun 3)<0 := by omega
      have hf := hF
      change abs (B (p.toFun 2) (p.toFun 3))=(H:Int)+1 at hf
      rw [abs_of_nonneg hs] at hf
      simpa [r,signedFrame,relabel,hn] using hf
    · have hn : B (p.toFun 2) (p.toFun 3)<0 := by omega
      have hf := hF
      change abs (B (p.toFun 2) (p.toFun 3))=(H:Int)+1 at hf
      rw [abs_of_neg hn] at hf
      simpa [r,signedFrame,relabel,reverse,hn] using hf
  have hp : HeightLe (signedFrame B p r) (H+1) := (signedFrame_height B p r _).mpr hP
  have hm0 : HeightLe (mutate (signedFrame B p r) 0) (H+1) := by
    rw [signedFrame_mutate]
    exact (signedFrame_height _ p r _).mpr h0
  have hm2 : HeightLe (mutate (signedFrame B p r) 2) (H+1) := by
    rw [signedFrame_mutate]
    exact (signedFrame_height _ p r _).mpr h2
  have hab : ∀ i j, abs (signedFrame B p r i j)=abs (B (p.toFun i) (p.toFun j)) := by
    intro i j
    cases r <;> simp [signedFrame,relabel,reverse,abs_neg]
  apply normalized_actual_switch hExist hEnd Q lead p r H hBudget htop
  · rw [hab]; exact hA
  · rw [hab]; exact hb
  · exact hp
  · exact hm0
  · exact hm2

#print axioms normalized_actual_switch
#print axioms arbitrary_label_unit_switch
end Rank4Round2.AllFrameUnitBridge
