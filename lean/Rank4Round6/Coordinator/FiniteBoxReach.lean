import Rank4Round6.ExecutableMAInvariant
import Rank4CoordinatorR2.ClassificationCompletion

/-!
Finite-state exploration inside the archive's proved height box. This is a
second, input-dependent evaluation rule. It does not give a fixed polynomial
sign formula.
-/

namespace Rank4Round6.Coordinator

open Rank4Formula QuiverProofs Rank4Coordinator Rank4CoordinatorR2 Rank4Round6.Foundations
  Rank4Round3 Rank4Classification

/-- The matrix satisfies the six-coordinate height limit. -/
def insideBox (H : Nat) (B : Matrix 4) : Bool :=
  decide (HeightLe B H)

/-- One-step successors retained inside the finite height box. -/
def successors (H : Nat) (B : Matrix 4) : Finset (Matrix 4) :=
  ((Finset.univ : Finset (Fin 4)).image (mutate B)).filter
    (fun C => insideBox H C)

/-- Expand an already visited set by all admissible one-step mutations. -/
def expand (H : Nat) (s : Finset (Matrix 4)) : Finset (Matrix 4) :=
  s ∪ s.biUnion (successors H)

/-- States found after at most `n` finite-box mutation steps. -/
def visited (B : Matrix 4) (H : Nat) : Nat → Finset (Matrix 4)
  | 0 => {B}
  | n + 1 => expand H (visited B H n)

def budget (q : SixTuple) : Nat := endpointHeightBudget (certifiedInput q)

def stateCount (q : SixTuple) : Nat := (2 * budget q + 1)^6

/-- An executable finite graph search for an acyclic member. -/
def boxInvariant (q : SixTuple) : Bool :=
  decide (((visited (ofTuple q) (budget q) (stateCount q - 1)).filter
    (fun C => decide (ForkPruning.FiniteAcyclic C))).Nonempty)

theorem visited_sound (B : Matrix 4) (H n : Nat) (C : Matrix 4)
    (hC : C ∈ visited B H n) : ∃ w : List (Fin 4), applyWord B w = C := by
  induction n generalizing C with
  | zero =>
    have h : C = B := by simpa only [visited, Finset.mem_singleton] using hC
    subst C
    exact ⟨[], rfl⟩
  | succ n ih =>
    change C ∈ expand H (visited B H n) at hC
    rcases Finset.mem_union.mp hC with hold | hnext
    · exact ih C hold
    · obtain ⟨D, hD, hsucc⟩ := Finset.mem_biUnion.mp hnext
      obtain ⟨himage, _⟩ := Finset.mem_filter.mp hsucc
      obtain ⟨k, _, hk⟩ := Finset.mem_image.mp himage
      obtain ⟨w, hw⟩ := ih D hD
      refine ⟨w ++ [k], ?_⟩
      rw [applyWord_append, hw]
      simpa only [applyWord] using hk

theorem visited_inside (B : Matrix 4) (H : Nat)
    (hB : HeightLe B H) (n : Nat) (C : Matrix 4)
    (hC : C ∈ visited B H n) : HeightLe C H := by
  induction n generalizing C with
  | zero =>
    have h : C = B := by simpa only [visited, Finset.mem_singleton] using hC
    subst C
    exact hB
  | succ n ih =>
    change C ∈ expand H (visited B H n) at hC
    rcases Finset.mem_union.mp hC with hold | hnext
    · exact ih C hold
    · obtain ⟨D, _, hsucc⟩ := Finset.mem_biUnion.mp hnext
      have hbox := (Finset.mem_filter.mp hsucc).2
      exact of_decide_eq_true hbox

theorem visited_mem_matrixBox (B : Matrix 4) (H : Nat)
    (hskew : SkewSymmetric B) (hB : HeightLe B H)
    (n : Nat) (C : Matrix 4) (hC : C ∈ visited B H n) :
    C ∈ ForkPruning.matrixBox H := by
  obtain ⟨w, hw⟩ := visited_sound B H n C hC
  have hskewC : SkewSymmetric C := by
    rw [← hw]
    exact word_preserves_skew B w hskew
  exact height_mem_box C hskewC H (visited_inside B H hB n C hC)

theorem visited_card_le_box (B : Matrix 4) (H : Nat)
    (hskew : SkewSymmetric B) (hB : HeightLe B H) (n : Nat) :
    (visited B H n).card ≤ (2 * H + 1)^6 := by
  have hsub : visited B H n ⊆ (ForkPruning.matrixBox H).toFinset := by
    intro C hC
    exact List.mem_toFinset.mpr
      (visited_mem_matrixBox B H hskew hB n C hC)
  have hcard := Finset.card_le_card hsub
  have hbox := List.toFinset_card_le (l := ForkPruning.matrixBox H)
  rw [matrixBox_length] at hbox
  omega

theorem visited_mutate (B : Matrix 4) (H n : Nat) (D : Matrix 4)
    (k : Fin 4) (hD : D ∈ visited B H n)
    (hbox : HeightLe (mutate D k) H) :
    mutate D k ∈ visited B H (n + 1) := by
  change mutate D k ∈ expand H (visited B H n)
  apply Finset.mem_union_right
  apply Finset.mem_biUnion.mpr
  refine ⟨D, hD, ?_⟩
  apply Finset.mem_filter.mpr
  constructor
  · exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
  · simp [insideBox, hbox]

theorem visited_word (B : Matrix 4) (H : Nat) :
    ∀ w : List (Fin 4), PrefixHeightLe B w H →
      applyWord B w ∈ visited B H w.length := by
  intro w
  induction w using List.reverseRecOn with
  | nil =>
    intro _
    simp only [applyWord, List.length_nil, visited, Finset.mem_singleton]
  | append_singleton w k ih =>
    intro hbound
    have hprefix : PrefixHeightLe B w H := by
      intro u v huv
      apply hbound u (v ++ [k])
      simp [huv, List.append_assoc]
    have hw := ih hprefix
    have hend : HeightLe (applyWord B (w ++ [k])) H := by
      apply hbound (w ++ [k]) []
      simp
    have hm := visited_mutate B H w.length (applyWord B w) k hw
      (by simpa only [applyWord_append, applyWord] using hend)
    simpa only [List.length_append, List.length_singleton,
      applyWord_append, applyWord] using hm

theorem visited_mono_step (B : Matrix 4) (H n : Nat) :
    visited B H n ⊆ visited B H (n + 1) := by
  intro C hC
  exact Finset.mem_union_left _ hC

theorem visited_subset_add (B : Matrix 4) (H n k : Nat) :
    visited B H n ⊆ visited B H (n + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    simpa only [Nat.add_succ] using ih.trans (visited_mono_step B H (n + k))

theorem visited_mono (B : Matrix 4) (H n m : Nat) (h : n ≤ m) :
    visited B H n ⊆ visited B H m := by
  have heq : n + (m - n) = m := by omega
  simpa only [heq] using visited_subset_add B H n (m - n)

theorem boxInvariant_MA_sound (q : SixTuple)
    (h : boxInvariant q = true) : MutationAcyclic (ofTuple q) := by
  have hn : ((visited (ofTuple q) (budget q) (stateCount q - 1)).filter
      (fun C => decide (ForkPruning.FiniteAcyclic C))).Nonempty := by
    exact of_decide_eq_true h
  obtain ⟨C, hC⟩ := hn
  obtain ⟨hvisit, hac⟩ := Finset.mem_filter.mp hC
  obtain ⟨w, hw⟩ := visited_sound (ofTuple q) (budget q)
    (stateCount q - 1) C hvisit
  refine ⟨w, ?_⟩
  rw [hw]
  exact (ForkPruning.finiteAcyclic_iff C
    (hw ▸ word_preserves_skew (ofTuple q) w
      (ofSix_skew (q 0) (q 1) (q 2) (q 3) (q 4) (q 5)))).mp
    (of_decide_eq_true hac)

theorem boxInvariant_MA_complete (q : SixTuple)
    (hma : MutationAcyclic (ofTuple q)) : boxInvariant q = true := by
  let Q : Rank4Input := certifiedInput q
  have hmaQ : MutationAcyclic Q.val := hma
  obtain ⟨w, hac, hprefix⟩ := heightCoverage Q hmaQ
  obtain ⟨v, hv, hshort, hvbox⟩ :=
    bounded_height_short_word Q.val Q.property w (budget q) hprefix
  have hacyclic : Acyclic (applyWord Q.val v) := by
    rw [hv]
    exact hac
  have hmem0 : applyWord Q.val v ∈ visited Q.val (budget q) v.length :=
    visited_word Q.val (budget q) v hvbox
  have hlen : v.length ≤ stateCount q - 1 := by
    unfold stateCount
    omega
  have hmem := visited_mono Q.val (budget q) v.length
    (stateCount q - 1) hlen hmem0
  have hfinite : ForkPruning.FiniteAcyclic (applyWord Q.val v) :=
    (ForkPruning.finiteAcyclic_iff _
      (word_preserves_skew Q.val v Q.property)).mpr hacyclic
  unfold boxInvariant
  simp only [decide_eq_true_eq]
  refine ⟨applyWord Q.val v, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
  · exact hmem
  · simp [hfinite]

theorem boxInvariant_MA_iff (q : SixTuple) :
    boxInvariant q = true ↔ MutationAcyclic (ofTuple q) :=
  ⟨boxInvariant_MA_sound q, boxInvariant_MA_complete q⟩

theorem boxInvariant_NMA_iff (q : SixTuple) :
    boxInvariant q = false ↔ ¬ MutationAcyclic (ofTuple q) := by
  constructor
  · intro hf hm
    have ht := (boxInvariant_MA_iff q).mpr hm
    rw [hf] at ht
    cases ht
  · intro hn
    cases hb : boxInvariant q with
    | false => rfl
    | true => exact False.elim (hn ((boxInvariant_MA_iff q).mp hb))

private theorem bool_eq_of_true_iff {a b : Bool}
    (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

theorem boxInvariant_eq_maInvariant (q : SixTuple) :
    boxInvariant q = maInvariant q := by
  apply bool_eq_of_true_iff
  rw [boxInvariant_MA_iff, maInvariant_MA_iff]

theorem boxInvariant_mutation (q : SixTuple) (k : Fin 4) :
    boxInvariant (mutatedUpper q k) = boxInvariant q := by
  rw [boxInvariant_eq_maInvariant, boxInvariant_eq_maInvariant]
  exact maInvariant_mutation q k

theorem boxInvariant_word (q : SixTuple) (w : List (Fin 4)) :
    boxInvariant (wordSix q w) = boxInvariant q := by
  rw [boxInvariant_eq_maInvariant, boxInvariant_eq_maInvariant]
  exact maInvariant_word q w

theorem boxInvariant_relabel (q : SixTuple) (p : Relabeling 4) :
    boxInvariant (relabelSix q p) = boxInvariant q := by
  rw [boxInvariant_eq_maInvariant, boxInvariant_eq_maInvariant]
  exact maInvariant_relabel q p

theorem boxInvariant_reverse (q : SixTuple) :
    boxInvariant (reverseSix q) = boxInvariant q := by
  rw [boxInvariant_eq_maInvariant, boxInvariant_eq_maInvariant]
  exact maInvariant_reverse q

#print axioms boxInvariant
#print axioms visited_card_le_box
#print axioms boxInvariant_MA_iff
#print axioms boxInvariant_NMA_iff
#print axioms boxInvariant_mutation
#print axioms boxInvariant_word
#print axioms boxInvariant_relabel
#print axioms boxInvariant_reverse

end Rank4Round6.Coordinator
