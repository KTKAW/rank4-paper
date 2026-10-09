import QuiverProofs.ForkPruningDecidable
import Mathlib.Data.Fintype.Card

/-! Finite-height reduction only. No unrestricted height ceiling is asserted.
All computations use the original integer mutation semantics. Classical
reasoning is confined to erased existence proofs for cycle deletion. -/
namespace Rank4Coordinator
open QuiverProofs

def trace (B : Matrix 4) : List (Fin 4) → List (Matrix 4)
  | [] => [B]
  | k :: w => B :: trace (mutate B k) w

theorem trace_length (B : Matrix 4) (w : List (Fin 4)) :
    (trace B w).length = w.length + 1 := by
  induction w generalizing B with
  | nil => rfl
  | cons k w ih => simp [trace, ih]

theorem mem_trace_iff (B C : Matrix 4) (w : List (Fin 4)) :
    C ∈ trace B w ↔ ∃ u v, w = u ++ v ∧ applyWord B u = C := by
  induction w generalizing B with
  | nil => simp [trace, applyWord, eq_comm]
  | cons k w ih =>
    constructor
    · intro h
      rcases List.mem_cons.mp h with h | h
      · exact ⟨[], k :: w, rfl, h.symm⟩
      · obtain ⟨u, v, hw, hc⟩ := (ih (mutate B k)).mp h
        exact ⟨k :: u, v, congrArg (List.cons k) hw, hc⟩
    · rintro ⟨u, v, hw, hc⟩
      cases u with
      | nil =>
        simp only [applyWord] at hc
        simp [trace, hc]
      | cons a u =>
        have ha : k = a := (List.cons.inj hw).1
        subst a
        have ht : w = u ++ v := (List.cons.inj hw).2
        exact List.mem_cons_of_mem B ((ih (mutate B k)).mpr ⟨u, v, ht, hc⟩)

theorem trace_suffix_sublist (B : Matrix 4) (u v : List (Fin 4)) :
    List.Sublist (trace (applyWord B u) v) (trace B (u ++ v)) := by
  induction u generalizing B with
  | nil => exact List.Sublist.refl _
  | cons k u ih => exact List.Sublist.cons _ (ih (mutate B k))

/-- Repeated labeled matrices can be deleted without adding any new state. -/
theorem erase_loops (B : Matrix 4) (w : List (Fin 4)) :
    ∃ v, applyWord B v = applyWord B w ∧ (trace B v).Nodup ∧
      trace B v ⊆ trace B w := by
  classical
  induction w generalizing B with
  | nil => exact ⟨[], rfl, by simp [trace], fun _ h => h⟩
  | cons k w ih =>
    obtain ⟨v, hv, hn, hs⟩ := ih (mutate B k)
    by_cases hb : B ∈ trace (mutate B k) v
    · obtain ⟨u, s, hvs, hu⟩ := (mem_trace_iff (mutate B k) B v).mp hb
      have sub := trace_suffix_sublist (mutate B k) u s
      rw [hu, ← hvs] at sub
      refine ⟨s, ?_, hn.sublist sub, ?_⟩
      · calc
          applyWord B s = applyWord (mutate B k) (u ++ s) := by
            rw [applyWord_append, hu]
          _ = applyWord (mutate B k) w := by rw [← hvs, hv]
          _ = applyWord B (k :: w) := rfl
      · intro C hc
        exact List.mem_cons_of_mem B (hs (sub.subset hc))
    · refine ⟨k :: v, hv, List.nodup_cons.mpr ⟨hb, hn⟩, ?_⟩
      intro C hc
      rcases List.mem_cons.mp hc with hc | hc
      · exact List.mem_cons.mpr (Or.inl hc)
      · exact List.mem_cons_of_mem B (hs hc)

def HeightLe (B : Matrix 4) (H : Nat) : Prop :=
  ∀ i j, -(H : Int) ≤ B i j ∧ B i j ≤ (H : Int)

def PrefixHeightLe (B : Matrix 4) (w : List (Fin 4)) (H : Nat) : Prop :=
  ∀ u v, w = u ++ v → HeightLe (applyWord B u) H

theorem height_mem_box (B : Matrix 4) (skew : SkewSymmetric B)
    (H : Nat) (h : HeightLe B H) : B ∈ ForkPruning.matrixBox H := by
  have h01 := ForkPruning.coordinateBox_complete H (B 0 1) (h 0 1).1 (h 0 1).2
  have h02 := ForkPruning.coordinateBox_complete H (B 0 2) (h 0 2).1 (h 0 2).2
  have h03 := ForkPruning.coordinateBox_complete H (B 0 3) (h 0 3).1 (h 0 3).2
  have h12 := ForkPruning.coordinateBox_complete H (B 1 2) (h 1 2).1 (h 1 2).2
  have h13 := ForkPruning.coordinateBox_complete H (B 1 3) (h 1 3).1 (h 1 3).2
  have h23 := ForkPruning.coordinateBox_complete H (B 2 3) (h 2 3).1 (h 2 3).2
  simp only [ForkPruning.matrixBox, List.mem_flatMap, List.mem_map]
  exact ⟨B 0 1, h01, B 0 2, h02, B 0 3, h03, B 1 2, h12,
    B 1 3, h13, B 2 3, h23, ofSix_reconstruct B skew⟩

theorem matrixBox_length (H : Nat) :
    (ForkPruning.matrixBox H).length = (2 * H + 1)^6 := by
  simp [ForkPruning.matrixBox, ForkPruning.coordinateBox, List.length_flatMap,
    Function.comp_def, List.map_const', List.sum_replicate_nat, Nat.pow_succ,
    Nat.mul_assoc]

/-- An actual height-bounded path admits a short word with the same endpoint.
This does not provide a height bound for any new input. -/
theorem bounded_height_short_word (B : Matrix 4) (skew : SkewSymmetric B)
    (w : List (Fin 4)) (H : Nat) (bounded : PrefixHeightLe B w H) :
    ∃ v : List (Fin 4), applyWord B v = applyWord B w ∧
      v.length < (2 * H + 1)^6 ∧ PrefixHeightLe B v H := by
  classical
  obtain ⟨v, hv, hn, hs⟩ := erase_loops B w
  have mem_box : ∀ C ∈ trace B v, C ∈ ForkPruning.matrixBox H := by
    intro C hc
    obtain ⟨u, s, he, hu⟩ := (mem_trace_iff B C w).mp (hs hc)
    rw [← hu]
    exact height_mem_box _ (word_preserves_skew B u skew) H (bounded u s he)
  have sub : (trace B v).toFinset ⊆ (ForkPruning.matrixBox H).toFinset := by
    intro C hc
    exact List.mem_toFinset.mpr (mem_box C (List.mem_toFinset.mp hc))
  have count := Finset.card_le_card sub
  rw [List.toFinset_card_of_nodup hn, trace_length] at count
  have box_count := List.toFinset_card_le (l := ForkPruning.matrixBox H)
  rw [matrixBox_length] at box_count
  refine ⟨v, hv, by omega, ?_⟩
  intro u s he
  have hc : applyWord B u ∈ trace B v := (mem_trace_iff B _ v).mpr ⟨u, s, he, rfl⟩
  obtain ⟨p, t, hpt, hp⟩ := (mem_trace_iff B _ w).mp (hs hc)
  rw [← hp]
  exact bounded p t hpt

abbrev Rank4Input := {B : Matrix 4 // SkewSymmetric B}

/-- Exact open mathematical obligation. It has no asserted inhabitant. -/
def HeightCoverage (H : Rank4Input → Nat) : Prop :=
  ∀ Q, MutationAcyclic Q.val → ∃ w : List (Fin 4),
    Acyclic (applyWord Q.val w) ∧ PrefixHeightLe Q.val w (H Q)

def lengthBound (H : Rank4Input → Nat) (Q : Rank4Input) : Nat :=
  (2 * H Q + 1)^6 - 1

/-- Conditional reduction for the live search-bound route. The universally
valid, computable H and its coverage proof remain the central open task. -/
theorem word_bound_of_height_coverage (H : Rank4Input → Nat)
    (coverage : HeightCoverage H) (Q : Rank4Input) (ma : MutationAcyclic Q.val) :
    ∃ v : List (Fin 4), v.length ≤ lengthBound H Q ∧ Acyclic (applyWord Q.val v) := by
  obtain ⟨w, ha, hh⟩ := coverage Q ma
  obtain ⟨v, he, hl, _⟩ := bounded_height_short_word Q.val Q.property w (H Q) hh
  refine ⟨v, ?_, he.symm ▸ ha⟩
  unfold lengthBound
  omega

#print axioms erase_loops
#print axioms height_mem_box
#print axioms matrixBox_length
#print axioms bounded_height_short_word
#print axioms word_bound_of_height_coverage
end Rank4Coordinator
