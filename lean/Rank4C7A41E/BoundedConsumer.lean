import Rank4C7A41E.BoundDecision
import QuiverProofs.BoundedClassificationCompletion

/-! Restricted, unconditional consumer of the audited bounded-two theorem.
Negative certificates may carry a word reaching that bounded domain. They
therefore verify arbitrary input weights when such a certificate is present.
No statement says every NMA input possesses this certificate.
-/
namespace Rank4C7A41E
open QuiverProofs QuiverProofs.Census

def classifyBounded (Q : Rank4Input) : Bool :=
  classifyWithBound (fun _ => 3) Q

theorem classifyBounded_ma_iff (Q : Rank4Input) (hb : BoundedTwo Q.val) :
    classifyBounded Q = true ↔ MutationAcyclic Q.val := by
  unfold classifyBounded
  rw [classifyWithBound_true_iff_witness]
  exact (BoundedClassification.bounded_MA_iff_three_mutations Q.val Q.property hb).symm

theorem classifyBounded_nma_iff (Q : Rank4Input) (hb : BoundedTwo Q.val) :
    classifyBounded Q = false ↔ ¬ MutationAcyclic Q.val := by
  have hm := classifyBounded_ma_iff Q hb
  cases hc : classifyBounded Q <;> simp_all

def boundedMADecidable (Q : Rank4Input) (hb : BoundedTwo Q.val) :
    Decidable (MutationAcyclic Q.val) :=
  if h : classifyBounded Q = true then .isTrue ((classifyBounded_ma_iff Q hb).mp h)
  else .isFalse (fun hm => h ((classifyBounded_ma_iff Q hb).mpr hm))

def boundedBool (B : Matrix 4) : Bool :=
  decide (∀ i j, -2 ≤ B i j ∧ B i j ≤ 2)

theorem boundedBool_iff (B : Matrix 4) : boundedBool B = true ↔ BoundedTwo B := by
  simp only [boundedBool, decide_eq_true_eq, BoundedTwo]

def endpointInput (Q : Rank4Input) (w : List (Fin 4)) : Rank4Input :=
  ⟨applyWord Q.val w, word_preserves_skew Q.val w Q.property⟩

def checkBoundedNegative (Q : Rank4Input) (w : List (Fin 4)) : Bool :=
  boundedBool (applyWord Q.val w) && !(classifyBounded (endpointInput Q w))

theorem checkBoundedNegative_sound (Q : Rank4Input) (w : List (Fin 4))
    (h : checkBoundedNegative Q w = true) : ¬ MutationAcyclic Q.val := by
  have hc : boundedBool (applyWord Q.val w) = true ∧
      classifyBounded (endpointInput Q w) = false := by
    simpa only [checkBoundedNegative, Bool.and_eq_true, Bool.not_eq_true'] using h
  have hb := (boundedBool_iff _).mp hc.1
  have hn := (classifyBounded_nma_iff (endpointInput Q w) hb).mp hc.2
  exact fun hm => hn ((mutationAcyclic_word_iff Q.val w).mpr hm)

theorem checkBoundedNegative_iff (Q : Rank4Input) (w : List (Fin 4)) :
    checkBoundedNegative Q w = true ↔
      BoundedTwo (applyWord Q.val w) ∧ ¬ MutationAcyclic Q.val := by
  constructor
  · intro h
    refine ⟨?_, checkBoundedNegative_sound Q w h⟩
    have hc : boundedBool (applyWord Q.val w) = true ∧
        classifyBounded (endpointInput Q w) = false := by
      simpa only [checkBoundedNegative, Bool.and_eq_true, Bool.not_eq_true'] using h
    exact (boundedBool_iff _).mp hc.1
  · rintro ⟨hb, hn⟩
    have he : ¬ MutationAcyclic (endpointInput Q w).val :=
      fun hm => hn ((mutationAcyclic_word_iff Q.val w).mp hm)
    simp only [checkBoundedNegative, Bool.and_eq_true, Bool.not_eq_true']
    exact ⟨(boundedBool_iff _).mpr hb, (classifyBounded_nma_iff (endpointInput Q w) hb).mpr he⟩

/-- An unconditional finite negative language with two existing consumers. -/
inductive NmaCertificate where
  | region (c : NegativeCertificate)
  | boundedEntry (w : List (Fin 4))

def checkNmaCertificate (Q : Rank4Input) : NmaCertificate → Bool
  | .region c => checkNegative Q c
  | .boundedEntry w => checkBoundedNegative Q w

theorem checkNmaCertificate_sound (Q : Rank4Input) (c : NmaCertificate)
    (h : checkNmaCertificate Q c = true) : ¬ MutationAcyclic Q.val := by
  cases c with
  | region c => exact checkNegative_sound Q c h
  | boundedEntry w => exact checkBoundedNegative_sound Q w h

end Rank4C7A41E
