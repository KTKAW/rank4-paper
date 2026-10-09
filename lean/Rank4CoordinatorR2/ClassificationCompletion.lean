import Rank4CoordinatorR2.DecisionAlgorithm
import Rank4Round2.UnitResidualAssembly
import Rank4C7A41E.HeightConsumer

/-!
Unconditional unrestricted four-mutable-vertex MA/NMA decision theorem.
The actual residual excursion is impossible in every normalized sign case.
Consequently every MA input has an acyclic mutation path in its computed
height box. Finite labelled-state loop erasure supplies the executable word
bound used by DecisionAlgorithm. No external completeness premise remains.
-/
namespace Rank4Classification
open QuiverProofs Rank4C7A41E Rank4Coordinator Rank4CoordinatorR2

theorem heightCoverage : HeightCoverage endpointHeightBudget := by
  intro Q hma
  by_contra hn
  obtain ⟨H,w,lead,i,j,mid,tail,hp⟩ :=
    ResidualUnitExcursion.exists_packet_of_no_bounded_witness Q hma hn
  exact Rank4Round2.UnitResidualAssembly.packet_impossible Q H w lead i j mid tail hp

theorem effectiveWordBound : WitnessBound wordBound :=
  witnessBound_of_heightCoverage endpointHeightBudget heightCoverage

/-- The finite negative verifier is sound for the original, unbounded
existential mutation semantics, including its exhausted-search branch. -/
theorem verifyNegative_sound (Q : Input) (c : NegativeCertificate)
    (h : verifyNegative Q c = true) : ¬MutationAcyclic Q.val := by
  cases c with
  | shortcut e =>
    exact Rank4CoordinatorR2.PartialStageKlein.verifyNegative_sound Q e h
  | exhausted =>
    change (findPositive Q (wordBound Q)).isNone = true at h
    have hn : findPositive Q (wordBound Q) = none := by
      cases hp : findPositive Q (wordBound Q) with
      | none => rfl
      | some w => simp only [hp,Option.isNone,Bool.false_eq_true] at h
    intro hma
    obtain ⟨w,hl,ha⟩ := effectiveWordBound Q hma
    exact (findPositive_none_iff Q (wordBound Q)).mp hn w hl ha

def DecisionCertificate.Sound (Q : Input) : DecisionCertificate → Prop
  | .ma w => Acyclic (applyWord Q.val w)
  | .nma c => ¬MutationAcyclic Q.val

theorem verifyCertificate_sound (Q : Input) (c : DecisionCertificate)
    (h : verifyCertificate Q c = true) : c.Sound Q := by
  cases c with
  | ma w => exact (checkPositive_iff Q w).mp h
  | nma e => exact verifyNegative_sound Q e h

theorem classifyCertificate_sound (Q : Input) :
    (classifyCertificate Q).Sound Q :=
  verifyCertificate_sound Q _ (classifyCertificate_verified Q)

theorem verified_certificate_ma_iff (Q : Input) (c : DecisionCertificate)
    (hv : verifyCertificate Q c = true) : c.isMA = true ↔ MutationAcyclic Q.val := by
  cases c with
  | ma w =>
    exact ⟨fun _ => ⟨w,(checkPositive_iff Q w).mp hv⟩,fun _ => rfl⟩
  | nma e =>
    have hn := verifyNegative_sound Q e hv
    constructor
    · intro hf
      exact Bool.noConfusion hf
    · intro hm
      exact False.elim (hn hm)

theorem classify4_ma_iff (Q : Input) :
    classify4 Q = true ↔ MutationAcyclic Q.val :=
  verified_certificate_ma_iff Q _ (classifyCertificate_verified Q)

private theorem false_iff_not_true (b : Bool) : b = false ↔ ¬b = true := by
  cases b <;> simp

theorem classify4_nma_iff (Q : Input) :
    classify4 Q = false ↔ ¬MutationAcyclic Q.val := by
  rw [false_iff_not_true,classify4_ma_iff]

/-- The proof arguments are erased; the decision computes classify4 Q. -/
def decidableMA (Q : Input) : Decidable (MutationAcyclic Q.val) :=
  if h : classify4 Q = true then
    .isTrue ((classify4_ma_iff Q).mp h)
  else
    .isFalse (fun hm => h ((classify4_ma_iff Q).mpr hm))

instance instDecidableMA (Q : Input) : Decidable (MutationAcyclic Q.val) :=
  decidableMA Q

theorem verified_certificate_positive_complete (Q : Input)
    (c : DecisionCertificate) (hv : verifyCertificate Q c = true)
    (hm : MutationAcyclic Q.val) :
    ∃ w,c = .ma w ∧ Acyclic (applyWord Q.val w) := by
  cases c with
  | ma w => exact ⟨w,rfl,(checkPositive_iff Q w).mp hv⟩
  | nma e => exact False.elim (verifyNegative_sound Q e hv hm)

theorem classifyCertificate_positive_complete (Q : Input)
    (hm : MutationAcyclic Q.val) :
    ∃ w,classifyCertificate Q = .ma w ∧ Acyclic (applyWord Q.val w) :=
  verified_certificate_positive_complete Q _ (classifyCertificate_verified Q) hm

theorem verified_certificate_negative_complete (Q : Input)
    (c : DecisionCertificate) (hv : verifyCertificate Q c = true)
    (hn : ¬MutationAcyclic Q.val) :
    ∃ e,c = .nma e ∧ verifyNegative Q e = true := by
  cases c with
  | ma w => exact False.elim (hn ⟨w,(checkPositive_iff Q w).mp hv⟩)
  | nma e => exact ⟨e,rfl,hv⟩

theorem classifyCertificate_negative_complete (Q : Input)
    (hn : ¬MutationAcyclic Q.val) :
    ∃ e,classifyCertificate Q = .nma e ∧ verifyNegative Q e = true :=
  verified_certificate_negative_complete Q _ (classifyCertificate_verified Q) hn

theorem negative_certificate_iff (Q : Input) :
    (∃ c,verifyNegative Q c = true) ↔ ¬MutationAcyclic Q.val := by
  constructor
  · rintro ⟨c,hc⟩
    exact verifyNegative_sound Q c hc
  · intro hn
    obtain ⟨c,_,hc⟩ := classifyCertificate_negative_complete Q hn
    exact ⟨c,hc⟩

#print axioms heightCoverage
#print axioms effectiveWordBound
#print axioms verifyNegative_sound
#print axioms classifyCertificate_sound
#print axioms classify4_ma_iff
#print axioms classify4_nma_iff
#print axioms decidableMA
#print axioms classifyCertificate_positive_complete
#print axioms classifyCertificate_negative_complete
#print axioms negative_certificate_iff
end Rank4Classification
