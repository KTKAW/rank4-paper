import Rank4C7A41E.BoundedConsumer
import Rank4C7A41E.GraphCoreCertificate

/-! An explicitly partial, certificate-producing finite stage. Positive
words are exhaustively enumerated through depth. Negative certificates are
the supplied finite candidate list; no exhaustive negative enumerator or
all-input covering theorem is claimed.
-/
namespace Rank4C7A41E
open QuiverProofs

inductive NegativeEvidence where
  | regionOrBounded (c : NmaCertificate)
  | graphCore (c : GraphCoreCertificate)

def verifyNegative (Q : Rank4Input) : NegativeEvidence → Bool
  | .regionOrBounded c => checkNmaCertificate Q c
  | .graphCore c => checkGraphCore Q c

theorem verifyNegative_sound (Q : Rank4Input) (c : NegativeEvidence)
    (h : verifyNegative Q c = true) : ¬ MutationAcyclic Q.val := by
  cases c with
  | regionOrBounded c => exact checkNmaCertificate_sound Q c h
  | graphCore c => exact checkGraphCore_sound Q c h

inductive Outcome where
  | ma (w : List (Fin 4))
  | nma (c : NegativeEvidence)
  | unknown

def classifyStage (Q : Rank4Input) (depth : Nat) (negatives : List NegativeEvidence) : Outcome :=
  match findPositive Q depth with
  | some w => .ma w
  | none => match CertificateSearch.searchStage (verifyNegative Q) negatives with
    | some c => .nma c
    | none => .unknown

def Outcome.Sound (Q : Rank4Input) : Outcome → Prop
  | .ma w => Acyclic (applyWord Q.val w)
  | .nma c => verifyNegative Q c = true ∧ ¬ MutationAcyclic Q.val
  | .unknown => True

theorem classifyStage_sound (Q : Rank4Input) (depth : Nat)
    (negatives : List NegativeEvidence) : Outcome.Sound Q (classifyStage Q depth negatives) := by
  cases hp : findPositive Q depth with
  | some w =>
    simpa only [classifyStage, hp, Outcome.Sound] using (findPositive_some Q depth w hp).2
  | none =>
    cases hn : CertificateSearch.searchStage (verifyNegative Q) negatives with
    | none => simp only [classifyStage, hp, hn, Outcome.Sound]
    | some c =>
      have hc := (CertificateSearch.searchStage_some_accepted (verifyNegative Q) negatives c hn).2
      simpa only [classifyStage, hp, hn, Outcome.Sound] using
        And.intro hc (verifyNegative_sound Q c hc)

theorem classifyStage_unknown_excludes_short_words (Q : Rank4Input) (depth : Nat)
    (negatives : List NegativeEvidence) (h : classifyStage Q depth negatives = .unknown) :
    ∀ w : List (Fin 4), w.length ≤ depth → ¬ Acyclic (applyWord Q.val w) := by
  have hp : findPositive Q depth = none := by
    cases hp : findPositive Q depth with
    | none => rfl
    | some w => simp [classifyStage, hp] at h
  exact (findPositive_none_iff Q depth).mp hp

#print axioms classifyStage
#print axioms verifyNegative_sound
#print axioms classifyStage_sound
end Rank4C7A41E
