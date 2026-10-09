import QuiverProofs.BoundedClassificationAssembly
import QuiverProofs.BoundedClassificationNegative

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace QuiverProofs.BoundedClassification
open Census BoundedClassificationData BoundedClassificationNegative

/-- The table's classification flag is equivalent to semantic mutation
acyclicity, using all134 independent all-word negative proofs. -/
theorem representative_MA_iff_tag (r : Fin 695) :
    MutationAcyclic (representative r) ↔ tag r < 561 := by
  constructor
  · intro hMA
    by_cases hn : tag r < 561
    · exact hn
    apply False.elim
    have he : representative r = negativeRepresentative (negativeIndex r hn) :=
      funext (fun u => funext (negative_lookup r hn u))
    rw [he] at hMA
    exact all_negative _ hMA
  · intro hp
    have he : representative r = maRepresentative (positiveIndex r hp) :=
      funext (fun u => funext (positive_lookup r hp u))
    rw [he]
    obtain ⟨w,_,_,ha⟩ := all_ma_short_bounded (positiveIndex r hp)
    exact ⟨w,ha⟩

theorem complete_positive_table (r : Fin 695) (h : MutationAcyclic (representative r)) :
    ∃ i : Fin 561, representative r = maRepresentative i := by
  have hp := (representative_MA_iff_tag r).mp h
  exact ⟨positiveIndex r hp,funext (fun u => funext (positive_lookup r hp u))⟩

/-- Every initially bounded matrix that is MA has a word of length at most
three, with the initial, every intermediate, and terminal matrix bounded by2. -/
theorem bounded_MA_iff_short_bounded (B : Matrix 4) (hs : SkewSymmetric B)
    (hb : BoundedTwo B) : MutationAcyclic B ↔ ShortBounded B :=
  bounded_classification_of_table complete_positive_table B hs hb

theorem bounded_MA_iff_three_mutations (B : Matrix 4) (hs : SkewSymmetric B)
    (hb : BoundedTwo B) :
    MutationAcyclic B ↔ ∃ w : List (Fin 4), w.length ≤ 3 ∧ Acyclic (applyWord B w) := by
  constructor
  · intro hm
    obtain ⟨w,hl,_,ha⟩ := (bounded_MA_iff_short_bounded B hs hb).mp hm
    exact ⟨w,hl,ha⟩
  · rintro ⟨w,_,ha⟩
    exact ⟨w,ha⟩

/-- A constructive decision for each actual census representative, justified
by the full semantic classification rather than imported source labels. -/
instance representativeMADecidable (r : Fin 695) : Decidable (MutationAcyclic (representative r)) :=
  if h : tag r < 561 then .isTrue ((representative_MA_iff_tag r).mpr h)
  else .isFalse (fun hm => h ((representative_MA_iff_tag r).mp hm))

theorem semantic_MA_count :
    ((List.finRange 695).filter (fun r => decide (MutationAcyclic (representative r)))).length = 561 := by
  simp only [representative_MA_iff_tag]
  exact positive_count

theorem semantic_NMA_count :
    ((List.finRange 695).filter (fun r => decide (¬ MutationAcyclic (representative r)))).length = 134 := by
  simp only [representative_MA_iff_tag,decide_not]
  exact negative_count

theorem semantic_connected_MA_count :
    ((List.finRange 695).filter (fun r => decide (ConnectedSupport (representative r)) &&
      decide (MutationAcyclic (representative r)))).length = 534 := by
  simp only [representative_MA_iff_tag,representative_connectivity_index]
  exact connected_positive_count

theorem semantic_connected_NMA_count :
    ((List.finRange 695).filter (fun r => decide (ConnectedSupport (representative r)) &&
      decide (¬ MutationAcyclic (representative r)))).length = 133 := by
  simp only [representative_MA_iff_tag,representative_connectivity_index,decide_not]
  exact connected_negative_count

theorem semantic_disconnected_MA_count :
    ((List.finRange 695).filter (fun r => decide (¬ ConnectedSupport (representative r)) &&
      decide (MutationAcyclic (representative r)))).length = 27 := by
  simp only [representative_MA_iff_tag,representative_connectivity_index,decide_not]
  exact disconnected_positive_count

theorem semantic_disconnected_NMA_count :
    ((List.finRange 695).filter (fun r => decide (¬ ConnectedSupport (representative r)) &&
      decide (¬ MutationAcyclic (representative r)))).length = 1 := by
  simp only [representative_MA_iff_tag,representative_connectivity_index,decide_not]
  exact disconnected_negative_count

/-- Exact numbers of semantic MA/NMA classes among the unique census
representatives. Connectedness and MA are the actual mathematical predicates. -/
structure ExactClassCounts : Prop where
  total : (List.finRange 695).length = 695
  connected : ((List.finRange 695).filter (fun r => decide (ConnectedSupport (representative r)))).length = 667
  disconnected : ((List.finRange 695).filter (fun r => !decide (ConnectedSupport (representative r)))).length = 28
  MA : ((List.finRange 695).filter (fun r => decide (MutationAcyclic (representative r)))).length = 561
  NMA : ((List.finRange 695).filter (fun r => decide (¬ MutationAcyclic (representative r)))).length = 134
  connectedMA : ((List.finRange 695).filter (fun r => decide (ConnectedSupport (representative r)) && decide (MutationAcyclic (representative r)))).length = 534
  connectedNMA : ((List.finRange 695).filter (fun r => decide (ConnectedSupport (representative r)) && decide (¬ MutationAcyclic (representative r)))).length = 133
  disconnectedMA : ((List.finRange 695).filter (fun r => decide (¬ ConnectedSupport (representative r)) && decide (MutationAcyclic (representative r)))).length = 27
  disconnectedNMA : ((List.finRange 695).filter (fun r => decide (¬ ConnectedSupport (representative r)) && decide (¬ MutationAcyclic (representative r)))).length = 1

theorem exact_class_counts : ExactClassCounts :=
  ⟨by decide,connected_representative_count,disconnected_representative_count,
    semantic_MA_count,semantic_NMA_count,semantic_connected_MA_count,
    semantic_connected_NMA_count,semantic_disconnected_MA_count,semantic_disconnected_NMA_count⟩

/-- Full source Theorem1.1 (`thm:bounded`): the three-mutation equivalence,
bounded witnessing words, unique exhaustive isomorphism census, and all counts.
No proper-order, hereditary-MA, or finite-search-completeness assumption occurs. -/
theorem corrected_bounded_classification :
    (∀ (B : Matrix 4), SkewSymmetric B → BoundedTwo B →
      (MutationAcyclic B ↔ ∃ w : List (Fin 4), w.length ≤ 3 ∧ Acyclic (applyWord B w)) ∧
      (MutationAcyclic B ↔ ShortBounded B)) ∧
    (∀ (B : Matrix 4), SkewSymmetric B → BoundedTwo B →
      ∃ i : Fin 695, (∃ p : Relabeling 4, relabel (representative i) p = B) ∧
        ∀ (j : Fin 695) (q : Relabeling 4), relabel (representative j) q = B → j=i) ∧
    (∀ (i j : Fin 695) (p : Relabeling 4), relabel (representative i) p = representative j → i=j) ∧
    ExactClassCounts :=
  ⟨fun B hs hb => ⟨bounded_MA_iff_three_mutations B hs hb,bounded_MA_iff_short_bounded B hs hb⟩,
   bounded_quiver_unique_representative,representatives_pairwise_nonisomorphic,exact_class_counts⟩

end QuiverProofs.BoundedClassification
