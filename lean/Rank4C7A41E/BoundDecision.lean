import QuiverProofs.ForkPruningDecidable
import QuiverProofs.CertificateSearch

/-!
Executable finite search in the original mutation semantics. The global
mathematics is the explicit `WitnessBound` premise. This module does not
assert that an unrestricted computable bound has been established.
Existing finite word enumeration and finite-stage search are reused.
-/
namespace Rank4C7A41E
open QuiverProofs

abbrev Rank4Input := { B : Matrix 4 // SkewSymmetric B }

def ofSixInput (a b c d e f : Int) : Rank4Input :=
  ⟨ofSix a b c d e f, ofSix_skew a b c d e f⟩

def checkPositive (Q : Rank4Input) (w : List (Fin 4)) : Bool :=
  decide (ForkPruning.FiniteAcyclic (applyWord Q.val w))

theorem checkPositive_iff (Q : Rank4Input) (w : List (Fin 4)) :
    checkPositive Q w = true ↔ Acyclic (applyWord Q.val w) := by
  rw [checkPositive, decide_eq_true_eq]
  exact ForkPruning.finiteAcyclic_iff _ (word_preserves_skew Q.val w Q.property)

theorem checkPositive_sound (Q : Rank4Input) (w : List (Fin 4))
    (h : checkPositive Q w = true) : MutationAcyclic Q.val :=
  ⟨w, (checkPositive_iff Q w).mp h⟩

theorem wordsUpTo_length {w : List (Fin 4)} {depth : Nat}
    (h : w ∈ FiniteLogic.wordsUpTo depth) : w.length ≤ depth := by
  induction depth generalizing w with
  | zero =>
    have he : w = [] := by simpa only [FiniteLogic.wordsUpTo, List.mem_singleton] using h
    subst w
    simp
  | succ depth ih =>
    simp only [FiniteLogic.wordsUpTo, List.mem_cons, List.mem_flatMap, List.mem_map] at h
    rcases h with rfl | ⟨k, _, tail, ht, rfl⟩
    · simp
    · have := ih ht
      simp only [List.length_cons]
      omega

def findPositive (Q : Rank4Input) (depth : Nat) : Option (List (Fin 4)) :=
  CertificateSearch.searchStage (checkPositive Q) (FiniteLogic.wordsUpTo depth)

theorem findPositive_some (Q : Rank4Input) (depth : Nat) (w : List (Fin 4))
    (h : findPositive Q depth = some w) :
    w.length ≤ depth ∧ Acyclic (applyWord Q.val w) := by
  obtain ⟨hm, ha⟩ := CertificateSearch.searchStage_some_accepted
    (checkPositive Q) (FiniteLogic.wordsUpTo depth) w h
  exact ⟨wordsUpTo_length hm, (checkPositive_iff Q w).mp ha⟩

theorem findPositive_exists_iff (Q : Rank4Input) (depth : Nat) :
    (∃ w, findPositive Q depth = some w) ↔
      ∃ w : List (Fin 4), w.length ≤ depth ∧ Acyclic (applyWord Q.val w) := by
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w, findPositive_some Q depth w hw⟩
  · rintro ⟨w, hl, ha⟩
    exact CertificateSearch.searchStage_finds (checkPositive Q)
      (FiniteLogic.wordsUpTo depth) w (FiniteLogic.word_mem_wordsUpTo w depth hl)
      ((checkPositive_iff Q w).mpr ha)

theorem findPositive_none_iff (Q : Rank4Input) (depth : Nat) :
    findPositive Q depth = none ↔
      ∀ w : List (Fin 4), w.length ≤ depth → ¬ Acyclic (applyWord Q.val w) := by
  constructor
  · intro hn w hl ha
    obtain ⟨v, hv⟩ := (findPositive_exists_iff Q depth).mpr ⟨w, hl, ha⟩
    rw [hn] at hv
    contradiction
  · intro hn
    cases hv : findPositive Q depth with
    | none => rfl
    | some v =>
      obtain ⟨hl, ha⟩ := findPositive_some Q depth v hv
      exact False.elim (hn v hl ha)

theorem mutationAcyclic_iff_eventual_find (Q : Rank4Input) :
    MutationAcyclic Q.val ↔ ∃ depth w, findPositive Q depth = some w := by
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨v, hv⟩ := (findPositive_exists_iff Q w.length).mpr ⟨w, Nat.le_refl _, hw⟩
    exact ⟨w.length, v, hv⟩
  · rintro ⟨depth, w, hw⟩
    exact ⟨w, (findPositive_some Q depth w hw).2⟩

/-- The OPEN all-input mathematical obligation, not an asserted theorem. -/
def WitnessBound (F : Rank4Input → Nat) : Prop :=
  ∀ Q, MutationAcyclic Q.val →
    ∃ w : List (Fin 4), w.length ≤ F Q ∧ Acyclic (applyWord Q.val w)

/-- An executable finite computation for every supplied executable F. -/
def classifyWithBound (F : Rank4Input → Nat) (Q : Rank4Input) : Bool :=
  (findPositive Q (F Q)).isSome

theorem classifyWithBound_true_iff_witness (F : Rank4Input → Nat) (Q : Rank4Input) :
    classifyWithBound F Q = true ↔
      ∃ w : List (Fin 4), w.length ≤ F Q ∧ Acyclic (applyWord Q.val w) := by
  rw [← findPositive_exists_iff]
  unfold classifyWithBound
  cases findPositive Q (F Q) <;> simp

/-- Conditional infrastructure: hBound is still required. -/
theorem classifyWithBound_ma_iff (F : Rank4Input → Nat) (hBound : WitnessBound F)
    (Q : Rank4Input) : classifyWithBound F Q = true ↔ MutationAcyclic Q.val := by
  rw [classifyWithBound_true_iff_witness]
  exact ⟨fun ⟨w, _, ha⟩ => ⟨w, ha⟩, hBound Q⟩

theorem classifyWithBound_nma_iff (F : Rank4Input → Nat) (hBound : WitnessBound F)
    (Q : Rank4Input) : classifyWithBound F Q = false ↔ ¬ MutationAcyclic Q.val := by
  have hm := classifyWithBound_ma_iff F hBound Q
  cases hc : classifyWithBound F Q <;> simp_all

/-- Constructive decision from the Boolean computation and explicit bound law.
The proof parameter is erased and never supplies the computed Boolean. -/
def decidableWithBound (F : Rank4Input → Nat) (hBound : WitnessBound F)
    (Q : Rank4Input) : Decidable (MutationAcyclic Q.val) :=
  if h : classifyWithBound F Q = true then
    .isTrue ((classifyWithBound_ma_iff F hBound Q).mp h)
  else .isFalse (fun hm => h ((classifyWithBound_ma_iff F hBound Q).mpr hm))

/-- Existing sound negative region certificates; no covering claim. -/
abbrev NegativeCertificate := CertificateSearch.RegionCertificate

def checkNegative (Q : Rank4Input) (c : NegativeCertificate) : Bool :=
  CertificateSearch.acceptCertificate Q.val c

theorem checkNegative_sound (Q : Rank4Input) (c : NegativeCertificate)
    (h : checkNegative Q c = true) : ¬ MutationAcyclic Q.val :=
  CertificateSearch.acceptCertificate_NMA Q.val c h

end Rank4C7A41E
