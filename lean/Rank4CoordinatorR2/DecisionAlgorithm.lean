import Rank4CoordinatorR2.PartialStageKlein
import Rank4CoordinatorR2.EndpointBudget

/-!
Executable final decision mechanism. Every computation is finite: a sound
shortcut stage at depth three, followed by the explicit finite word bound.
This module proves positive soundness and certificate self-verification.
The exhausted branch's semantic soundness is supplied only by the separate
global coverage proof; this file does not assert that missing theorem.
-/
namespace Rank4Classification
open QuiverProofs Rank4C7A41E
namespace Shortcut
abbrev Evidence := Rank4CoordinatorR2.PartialStageKlein.NegativeEvidence
abbrev stage := Rank4CoordinatorR2.PartialStageKlein.classifyStage
abbrev verify := Rank4CoordinatorR2.PartialStageKlein.verifyNegative
end Shortcut

abbrev Input := Rank4Input

/-- Number of labelled matrices in the proved height box, minus one. -/
def wordBound (Q : Input) : Nat :=
  Rank4Coordinator.lengthBound Rank4CoordinatorR2.endpointHeightBudget Q

inductive NegativeCertificate where
  | shortcut (evidence : Shortcut.Evidence)
  | exhausted

/-- The exhausted certificate asks a finite verifier to rerun the bounded
search. It is not justified merely by an unsuccessful resource cutoff. -/
def verifyNegative (Q : Input) : NegativeCertificate → Bool
  | .shortcut c => Shortcut.verify Q c
  | .exhausted => (findPositive Q (wordBound Q)).isNone

inductive DecisionCertificate where
  | ma (word : List (Fin 4))
  | nma (certificate : NegativeCertificate)

def verifyCertificate (Q : Input) : DecisionCertificate → Bool
  | .ma w => checkPositive Q w
  | .nma c => verifyNegative Q c

def certificateFromStage (Q : Input)
    (outcome : Rank4CoordinatorR2.PartialStageKlein.Outcome) : DecisionCertificate :=
  match outcome with
  | .ma w => .ma w
  | .nma c => .nma (.shortcut c)
  | .unknown =>
    match findPositive Q (wordBound Q) with
    | some w => .ma w
    | none => .nma .exhausted

def classifyCertificate (Q : Input) : DecisionCertificate :=
  certificateFromStage Q (Shortcut.stage Q 3 [])

def DecisionCertificate.isMA : DecisionCertificate → Bool
  | .ma _ => true
  | .nma _ => false

def classify4 (Q : Input) : Bool :=
  (classifyCertificate Q).isMA

theorem certificateFromStage_verified (Q : Input)
    (outcome : Rank4CoordinatorR2.PartialStageKlein.Outcome)
    (hs : Rank4CoordinatorR2.PartialStageKlein.Outcome.Sound Q outcome) :
    verifyCertificate Q (certificateFromStage Q outcome) = true := by
  cases outcome with
  | ma w =>
    change Acyclic (applyWord Q.val w) at hs
    simpa only [certificateFromStage, verifyCertificate] using
      (checkPositive_iff Q w).mpr hs
  | nma c =>
    simpa only [certificateFromStage, verifyCertificate, verifyNegative,
      Shortcut.verify] using hs.1
  | unknown =>
    cases hp : findPositive Q (wordBound Q) with
    | some w =>
      have ha := (findPositive_some Q (wordBound Q) w hp).2
      simpa only [certificateFromStage, hp, verifyCertificate] using
        (checkPositive_iff Q w).mpr ha
    | none => simp only [certificateFromStage, hp, verifyCertificate,
        verifyNegative, Option.isNone]

theorem classifyCertificate_verified (Q : Input) :
    verifyCertificate Q (classifyCertificate Q) = true :=
  certificateFromStage_verified Q _
    (Rank4CoordinatorR2.PartialStageKlein.classifyStage_sound Q 3 [])

theorem classifyCertificate_ma_sound (Q : Input) (w : List (Fin 4))
    (h : classifyCertificate Q = .ma w) : Acyclic (applyWord Q.val w) := by
  have hv := classifyCertificate_verified Q
  rw [h] at hv
  exact (checkPositive_iff Q w).mp hv

theorem verified_certificate_true_sound (Q : Input) (c : DecisionCertificate)
    (hv : verifyCertificate Q c = true) (h : c.isMA = true) :
    MutationAcyclic Q.val := by
  cases c with
  | ma w => exact ⟨w, (checkPositive_iff Q w).mp hv⟩
  | nma c => simp only [DecisionCertificate.isMA, Bool.false_eq_true] at h

theorem classify4_true_sound (Q : Input) (h : classify4 Q = true) :
    MutationAcyclic Q.val :=
  verified_certificate_true_sound Q _ (classifyCertificate_verified Q) h

#print axioms wordBound
#print axioms verifyNegative
#print axioms classifyCertificate
#print axioms classify4
#print axioms classifyCertificate_verified
#print axioms classify4_true_sound
end Rank4Classification
