import Rank4Round2.NonzeroExitConsumer
import Rank4CoordinatorR2.EndpointFoundation
import Rank4ReviewRound2.StrongPairIncident

/-! The nonzero-exit obstruction is applied to actual entries and labels.
The whole preceding state need not lie below H; its two strong-pair rows
do. The endpoint bridge is discharged, leaving only MA existence explicit.
-/
namespace Rank4CoordinatorR2.FramedNonzeroExit
open QuiverProofs Rank4Coordinator Rank4CoordinatorR2 Rank4Round2
open ProperObstructionSoundness Rank4ReviewRound2.PeakNormalization
open Rank4ReviewRound2.StrongPairIncident

theorem signed_entry_interval (B : Matrix 4) (p : Relabeling 4) (r : Bool)
    (u v : Fin 4) (H : Nat)
    (h : -(H:Int)≤B (p.toFun u) (p.toFun v) ∧ B (p.toFun u) (p.toFun v)≤(H:Int)) :
    -(H:Int)≤signedFrame B p r u v ∧ signedFrame B p r u v≤(H:Int) := by
  cases r
  · exact h
  · change -(H:Int)≤ -B (p.toFun u) (p.toFun v) ∧
      -B (p.toFun u) (p.toFun v)≤(H:Int)
    omega

theorem actual_framed_nonzero_exit
    (hExist : MAHasTotalProper4) (Q : Rank4Input)
    (hma : MutationAcyclic Q.val) (lead : List (Fin 4)) (p : Relabeling 4)
    (H : Nat) (hBudget : scalarBudget Q.val≤H)
    (hA : 2≤abs (applyWord Q.val lead (p.toFun 0) (p.toFun 1)))
    (hb : applyWord Q.val lead (p.toFun 0) (p.toFun 2)≠0)
    (hF : abs (applyWord Q.val lead (p.toFun 2) (p.toFun 3))=(H:Int)+1)
    (hP : HeightLe (applyWord Q.val lead) (H+1))
    (h0 : HeightLe (mutate (applyWord Q.val lead) (p.toFun 0)) (H+1))
    (h2 : HeightLe (mutate (applyWord Q.val lead) (p.toFun 2)) (H+1))
    (hPrev : IncidentLe (mutate (applyWord Q.val lead) (p.toFun 0))
      (p.toFun 0) (p.toFun 1) H) : False := by
  let B := applyWord Q.val lead
  let r := decide (B (p.toFun 2) (p.toFun 3)<0)
  let C := signedFrame B p r
  have htop : C 2 3=(H:Int)+1 := by
    by_cases hpos : 0≤B (p.toFun 2) (p.toFun 3)
    · have hn : ¬B (p.toFun 2) (p.toFun 3)<0 := by omega
      have hf := hF
      change abs (B (p.toFun 2) (p.toFun 3))=(H:Int)+1 at hf
      rw [abs_of_nonneg hpos] at hf
      simpa [C,r,signedFrame,relabel,hn] using hf
    · have hn : B (p.toFun 2) (p.toFun 3)<0 := by omega
      have hf := hF
      change abs (B (p.toFun 2) (p.toFun 3))=(H:Int)+1 at hf
      rw [abs_of_neg hn] at hf
      simpa [C,r,signedFrame,relabel,reverse,hn] using hf
  have hsC : SkewSymmetric C := signedFrame_skew B
    (word_preserves_skew Q.val lead Q.property) p r
  have hab : ∀ u v,abs (C u v)=abs (B (p.toFun u) (p.toFun v)) := by
    intro u v
    change abs (signedFrame B p r u v)=abs (B (p.toFun u) (p.toFun v))
    cases r <;> simp [signedFrame,relabel,reverse,abs_neg]
  have hCA : 2≤abs (C 0 1) := by rw [hab];exact hA
  have hCb : C 0 2≠0 := by
    intro hz
    have ha0 := hab 0 2
    rw [hz,abs_zero] at ha0
    exact hb (abs_eq_zero.mp ha0.symm)
  have hCP : HeightLe C (H+1) := (signedFrame_height B p r _).mpr hP
  have hC0 : HeightLe (mutate C 0) (H+1) := by
    rw [show C=signedFrame B p r from rfl,signedFrame_mutate,signedFrame_height]
    exact h0
  have hC2 : HeightLe (mutate C 2) (H+1) := by
    rw [show C=signedFrame B p r from rfl,signedFrame_mutate,signedFrame_height]
    exact h2
  have h03 : -(H:Int)≤mutate C 0 0 3 ∧ mutate C 0 0 3≤(H:Int) := by
    rw [show C=signedFrame B p r from rfl,signedFrame_mutate]
    exact signed_entry_interval _ p r 0 3 H (hPrev (p.toFun 3)).1
  have h13 : -(H:Int)≤mutate C 0 1 3 ∧ mutate C 0 1 3≤(H:Int) := by
    rw [show C=signedFrame B p r from rfl,signedFrame_mutate]
    exact signed_entry_interval _ p r 1 3 H (hPrev (p.toFun 3)).2
  let S := FlatUnitBridge.unitShape (C 0 1) (C 0 2) (C 0 3) (C 1 2) (C 1 3) H
  have heq : C=S := by
    simpa only [S,FlatUnitBridge.unitShape,htop] using (ofSix_reconstruct C hsC).symm
  have hno := NonzeroExitConsumer.no_nonzero_exit hExist EndpointFoundation.endpoint_bridge
    Q lead p r (C 0 1) (C 0 2) (C 0 3) (C 1 2) (C 1 3) H hBudget heq hCA hCb
    (by change HeightLe S (H+1);rwa [←heq])
    (by change HeightLe (mutate S 0) (H+1);rwa [←heq])
    (by change HeightLe (mutate S 2) (H+1);rwa [←heq])
    (by change -(H:Int)≤mutate S 0 0 3 ∧ mutate S 0 0 3≤(H:Int);rwa [←heq])
    (by change -(H:Int)≤mutate S 0 1 3 ∧ mutate S 0 1 3≤(H:Int);rwa [←heq])
  exact hno hma

#print axioms signed_entry_interval
#print axioms actual_framed_nonzero_exit
end Rank4CoordinatorR2.FramedNonzeroExit
