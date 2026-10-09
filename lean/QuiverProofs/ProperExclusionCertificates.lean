import QuiverProofs.ProperScalarTargets

/- Exact-source scalar exclusions. Parent NMA retains BOTH named structural hypotheses. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace QuiverProofs.ProperExclusionCertificates
open ProperOrder ProperWiggle ProperObstructionSoundness ProperScalarTargets

namespace q013
def initial : Matrix 4 := (ofSix (-2) (-2) (-2) (-2) (1) (-2))
def terminal : Matrix 4 := (ofSix (-2) (-2) (-2) (-2) (1) (-2))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q013

namespace q014
def initial : Matrix 4 := (ofSix (-2) (-2) (-2) (-2) (1) (-1))
def terminal : Matrix 4 := (ofSix (-2) (-2) (-2) (-2) (1) (-1))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q014

namespace q040
def initial : Matrix 4 := (ofSix (-2) (-2) (-1) (-2) (1) (-2))
def terminal : Matrix 4 := (ofSix (-2) (-2) (-1) (-2) (1) (-2))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q040

namespace q041
def initial : Matrix 4 := (ofSix (-2) (-2) (-1) (-2) (1) (-1))
def terminal : Matrix 4 := (ofSix (-2) (-2) (-1) (-2) (1) (-1))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q041

namespace q046
def initial : Matrix 4 := (ofSix (-2) (-2) (-1) (-2) (2) (-1))
def terminal : Matrix 4 := (ofSix (-2) (-2) (-1) (-2) (2) (-1))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q046

namespace q065
def initial : Matrix 4 := (ofSix (-2) (-2) (-1) (-1) (1) (-2))
def terminal : Matrix 4 := (ofSix (-2) (-2) (-1) (-1) (1) (-2))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q065

namespace q066
def initial : Matrix 4 := (ofSix (-2) (-2) (-1) (-1) (1) (-1))
def terminal : Matrix 4 := (ofSix (-2) (-2) (-1) (-1) (1) (-1))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q066

namespace q070
def initial : Matrix 4 := (ofSix (-2) (-2) (-1) (-1) (2) (-2))
def terminal : Matrix 4 := (ofSix (-2) (-2) (-1) (-1) (2) (-2))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q070

namespace q071
def initial : Matrix 4 := (ofSix (-2) (-2) (-1) (-1) (2) (-1))
def terminal : Matrix 4 := (ofSix (-2) (-2) (-1) (-1) (2) (-1))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q071

namespace q128
def initial : Matrix 4 := (ofSix (-2) (-2) (0) (-1) (1) (-2))
def terminal : Matrix 4 := (ofSix (-2) (-2) (0) (-1) (1) (-2))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q128

namespace q133
def initial : Matrix 4 := (ofSix (-2) (-2) (0) (-1) (2) (-2))
def terminal : Matrix 4 := (ofSix (-2) (-2) (0) (-1) (2) (-2))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q133

namespace q134
def initial : Matrix 4 := (ofSix (-2) (-2) (0) (-1) (2) (-1))
def terminal : Matrix 4 := (ofSix (-2) (-2) (0) (-1) (2) (-1))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q134

namespace q155
def initial : Matrix 4 := (ofSix (-2) (-2) (1) (-2) (-2) (1))
def terminal : Matrix 4 := (ofSix (-2) (-2) (1) (-2) (-2) (1))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q155

namespace q156
def initial : Matrix 4 := (ofSix (-2) (-2) (1) (-2) (-2) (2))
def terminal : Matrix 4 := (ofSix (-2) (-2) (1) (-2) (-2) (2))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q156

namespace q160
def initial : Matrix 4 := (ofSix (-2) (-2) (1) (-2) (-1) (1))
def terminal : Matrix 4 := (ofSix (-2) (-2) (1) (-2) (-1) (1))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q160

namespace q161
def initial : Matrix 4 := (ofSix (-2) (-2) (1) (-2) (-1) (2))
def terminal : Matrix 4 := (ofSix (-2) (-2) (1) (-2) (-1) (2))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q161

namespace q179
def initial : Matrix 4 := (ofSix (-2) (-2) (1) (-1) (-2) (1))
def terminal : Matrix 4 := (ofSix (-2) (-2) (1) (-1) (-2) (1))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q179

namespace q180
def initial : Matrix 4 := (ofSix (-2) (-2) (1) (-1) (-2) (2))
def terminal : Matrix 4 := (ofSix (-2) (-2) (1) (-1) (-2) (2))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q180

namespace q184
def initial : Matrix 4 := (ofSix (-2) (-2) (1) (-1) (-1) (1))
def terminal : Matrix 4 := (ofSix (-2) (-2) (1) (-1) (-1) (1))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q184

namespace q185
def initial : Matrix 4 := (ofSix (-2) (-2) (1) (-1) (-1) (2))
def terminal : Matrix 4 := (ofSix (-2) (-2) (1) (-1) (-1) (2))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q185

namespace q191
def initial : Matrix 4 := (ofSix (-2) (-2) (1) (-1) (1) (-2))
def terminal : Matrix 4 := (ofSix (-2) (-2) (1) (-1) (1) (-2))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q191

namespace q196
def initial : Matrix 4 := (ofSix (-2) (-2) (1) (-1) (2) (-2))
def terminal : Matrix 4 := (ofSix (-2) (-2) (1) (-1) (2) (-2))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q196

namespace q197
def initial : Matrix 4 := (ofSix (-2) (-2) (1) (-1) (2) (-1))
def terminal : Matrix 4 := (ofSix (-2) (-2) (1) (-1) (2) (-1))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q197

namespace q203
def initial : Matrix 4 := (ofSix (-2) (-2) (1) (0) (-2) (1))
def terminal : Matrix 4 := (ofSix (-2) (-2) (1) (0) (-2) (1))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q203

namespace q204
def initial : Matrix 4 := (ofSix (-2) (-2) (1) (0) (-2) (2))
def terminal : Matrix 4 := (ofSix (-2) (-2) (1) (0) (-2) (2))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q204

namespace q207
def initial : Matrix 4 := (ofSix (-2) (-2) (1) (0) (-1) (1))
def terminal : Matrix 4 := (ofSix (-2) (-2) (1) (0) (-1) (1))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q207

namespace q208
def initial : Matrix 4 := (ofSix (-2) (-2) (1) (0) (-1) (2))
def terminal : Matrix 4 := (ofSix (-2) (-2) (1) (0) (-1) (2))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q208

namespace q222
def initial : Matrix 4 := (ofSix (-2) (-2) (2) (-2) (-1) (1))
def terminal : Matrix 4 := (ofSix (-2) (-2) (2) (-2) (-1) (1))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q222

namespace q238
def initial : Matrix 4 := (ofSix (-2) (-2) (2) (-1) (-1) (1))
def terminal : Matrix 4 := (ofSix (-2) (-2) (2) (-1) (-1) (1))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q238

namespace q267
def initial : Matrix 4 := (ofSix (-2) (-1) (-1) (-2) (1) (-2))
def terminal : Matrix 4 := (ofSix (-2) (-1) (-1) (-2) (1) (-2))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q267

namespace q268
def initial : Matrix 4 := (ofSix (-2) (-1) (-1) (-2) (1) (-1))
def terminal : Matrix 4 := (ofSix (-2) (-1) (-1) (-2) (1) (-1))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q268

namespace q273
def initial : Matrix 4 := (ofSix (-2) (-1) (-1) (-2) (2) (-1))
def terminal : Matrix 4 := (ofSix (-2) (-1) (-1) (-2) (2) (-1))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q273

namespace q284
def initial : Matrix 4 := (ofSix (-2) (-1) (-1) (-1) (1) (-2))
def terminal : Matrix 4 := (ofSix (-2) (-1) (-1) (-1) (1) (-2))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q284

namespace q285
def initial : Matrix 4 := (ofSix (-2) (-1) (-1) (-1) (1) (-1))
def terminal : Matrix 4 := (ofSix (-2) (-1) (-1) (-1) (1) (-1))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q285

namespace q289
def initial : Matrix 4 := (ofSix (-2) (-1) (-1) (-1) (2) (-2))
def terminal : Matrix 4 := (ofSix (-2) (-1) (-1) (-1) (2) (-2))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q289

namespace q290
def initial : Matrix 4 := (ofSix (-2) (-1) (-1) (-1) (2) (-1))
def terminal : Matrix 4 := (ofSix (-2) (-1) (-1) (-1) (2) (-1))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q290

namespace q346
def initial : Matrix 4 := (ofSix (-2) (-1) (0) (-1) (1) (-2))
def terminal : Matrix 4 := (ofSix (-2) (-1) (0) (-1) (1) (-2))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q346

namespace q351
def initial : Matrix 4 := (ofSix (-2) (-1) (0) (-1) (2) (-2))
def terminal : Matrix 4 := (ofSix (-2) (-1) (0) (-1) (2) (-2))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q351

namespace q352
def initial : Matrix 4 := (ofSix (-2) (-1) (0) (-1) (2) (-1))
def terminal : Matrix 4 := (ofSix (-2) (-1) (0) (-1) (2) (-1))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q352

namespace q381
def initial : Matrix 4 := (ofSix (-2) (-1) (0) (1) (-2) (1))
def terminal : Matrix 4 := (ofSix (-2) (-1) (0) (1) (-2) (1))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q381

namespace q382
def initial : Matrix 4 := (ofSix (-2) (-1) (0) (1) (-2) (2))
def terminal : Matrix 4 := (ofSix (-2) (-1) (0) (1) (-2) (2))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q382

namespace q387
def initial : Matrix 4 := (ofSix (-2) (-1) (0) (1) (-1) (2))
def terminal : Matrix 4 := (ofSix (-2) (-1) (0) (1) (-1) (2))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q387

namespace q420
def initial : Matrix 4 := (ofSix (-2) (-1) (1) (-2) (-1) (1))
def terminal : Matrix 4 := (ofSix (-2) (-1) (1) (-2) (-1) (1))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q420

namespace q421
def initial : Matrix 4 := (ofSix (-2) (-1) (1) (-2) (-1) (2))
def terminal : Matrix 4 := (ofSix (-2) (-1) (1) (-2) (-1) (2))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q421

namespace q426
def initial : Matrix 4 := (ofSix (-2) (-1) (1) (-2) (1) (-2))
def terminal : Matrix 4 := (ofSix (-2) (-1) (1) (-2) (1) (-2))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q426

namespace q435
def initial : Matrix 4 := (ofSix (-2) (-1) (1) (-1) (-2) (1))
def terminal : Matrix 4 := (ofSix (-2) (-1) (1) (-1) (-2) (1))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q435

namespace q436
def initial : Matrix 4 := (ofSix (-2) (-1) (1) (-1) (-2) (2))
def terminal : Matrix 4 := (ofSix (-2) (-1) (1) (-1) (-2) (2))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q436

namespace q440
def initial : Matrix 4 := (ofSix (-2) (-1) (1) (-1) (-1) (1))
def terminal : Matrix 4 := (ofSix (-2) (-1) (1) (-1) (-1) (1))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q440

namespace q441
def initial : Matrix 4 := (ofSix (-2) (-1) (1) (-1) (-1) (2))
def terminal : Matrix 4 := (ofSix (-2) (-1) (1) (-1) (-1) (2))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q441

namespace q442
def initial : Matrix 4 := (ofSix (-2) (-1) (1) (-1) (0) (-2))
def terminal : Matrix 4 := (ofSix (-2) (-1) (1) (-1) (0) (-2))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q442

namespace q446
def initial : Matrix 4 := (ofSix (-2) (-1) (1) (-1) (1) (-2))
def terminal : Matrix 4 := (ofSix (-2) (-1) (1) (-1) (1) (-2))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q446

namespace q450
def initial : Matrix 4 := (ofSix (-2) (-1) (1) (-1) (2) (-2))
def terminal : Matrix 4 := (ofSix (-2) (-1) (1) (-1) (2) (-2))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q450

namespace q455
def initial : Matrix 4 := (ofSix (-2) (-1) (1) (0) (-2) (1))
def terminal : Matrix 4 := (ofSix (-2) (-1) (1) (0) (-2) (1))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q455

namespace q456
def initial : Matrix 4 := (ofSix (-2) (-1) (1) (0) (-2) (2))
def terminal : Matrix 4 := (ofSix (-2) (-1) (1) (0) (-2) (2))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q456

namespace q457
def initial : Matrix 4 := (ofSix (-2) (-1) (1) (0) (-1) (-2))
def terminal : Matrix 4 := (ofSix (-2) (-1) (1) (0) (-1) (-2))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q457

namespace q460
def initial : Matrix 4 := (ofSix (-2) (-1) (1) (0) (-1) (1))
def terminal : Matrix 4 := (ofSix (-2) (-1) (1) (0) (-1) (1))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q460

namespace q461
def initial : Matrix 4 := (ofSix (-2) (-1) (1) (0) (-1) (2))
def terminal : Matrix 4 := (ofSix (-2) (-1) (1) (0) (-1) (2))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q461

namespace q462
def initial : Matrix 4 := (ofSix (-2) (-1) (1) (0) (0) (-2))
def terminal : Matrix 4 := (ofSix (-2) (-1) (1) (0) (0) (-2))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q462

namespace q466
def initial : Matrix 4 := (ofSix (-2) (-1) (1) (0) (1) (-2))
def terminal : Matrix 4 := (ofSix (-2) (-1) (1) (0) (1) (-2))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q466

namespace q470
def initial : Matrix 4 := (ofSix (-2) (-1) (1) (0) (2) (-2))
def terminal : Matrix 4 := (ofSix (-2) (-1) (1) (0) (2) (-2))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q470

namespace q475
def initial : Matrix 4 := (ofSix (-2) (-1) (1) (1) (-2) (1))
def terminal : Matrix 4 := (ofSix (-2) (-1) (1) (1) (-2) (1))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q475

namespace q476
def initial : Matrix 4 := (ofSix (-2) (-1) (1) (1) (-2) (2))
def terminal : Matrix 4 := (ofSix (-2) (-1) (1) (1) (-2) (2))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q476

namespace q477
def initial : Matrix 4 := (ofSix (-2) (-1) (1) (1) (-1) (-2))
def terminal : Matrix 4 := (ofSix (-2) (-1) (1) (1) (-1) (-2))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q477

namespace q484
def initial : Matrix 4 := (ofSix (-2) (-1) (1) (1) (1) (-1))
def terminal : Matrix 4 := (ofSix (-2) (-1) (1) (1) (1) (-1))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q484

namespace q487
def initial : Matrix 4 := (ofSix (-2) (-1) (1) (1) (2) (-1))
def terminal : Matrix 4 := (ofSix (-2) (-1) (1) (1) (2) (-1))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q487

namespace q498
def initial : Matrix 4 := (ofSix (-2) (-1) (2) (-2) (-1) (-2))
def terminal : Matrix 4 := (ofSix (-2) (-1) (2) (-2) (-1) (-2))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q498

namespace q499
def initial : Matrix 4 := (ofSix (-2) (-1) (2) (-2) (-1) (-1))
def terminal : Matrix 4 := (ofSix (-2) (-1) (2) (-2) (-1) (-1))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q499

namespace q511
def initial : Matrix 4 := (ofSix (-2) (-1) (2) (-1) (0) (-2))
def terminal : Matrix 4 := (ofSix (-2) (-1) (2) (-1) (0) (-2))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q511

namespace q517
def initial : Matrix 4 := (ofSix (-2) (-1) (2) (0) (-1) (-2))
def terminal : Matrix 4 := (ofSix (-2) (-1) (2) (0) (-1) (-2))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q517

namespace q525
def initial : Matrix 4 := (ofSix (-2) (-1) (2) (1) (-1) (-1))
def terminal : Matrix 4 := (ofSix (-2) (-1) (2) (1) (-1) (-1))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q525

namespace q527
def initial : Matrix 4 := (ofSix (-2) (-1) (2) (1) (0) (-1))
def terminal : Matrix 4 := (ofSix (-2) (-1) (2) (1) (0) (-1))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q527

namespace q550
def initial : Matrix 4 := (ofSix (-2) (0) (0) (-1) (1) (-2))
def terminal : Matrix 4 := (ofSix (-2) (0) (0) (-1) (1) (-2))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q550

namespace q569
def initial : Matrix 4 := (ofSix (-2) (0) (1) (-2) (1) (-2))
def terminal : Matrix 4 := (ofSix (-2) (0) (1) (-2) (1) (-2))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q569

namespace q573
def initial : Matrix 4 := (ofSix (-2) (0) (1) (-1) (-1) (-2))
def terminal : Matrix 4 := (ofSix (-2) (0) (1) (-1) (-1) (-2))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q573

namespace q576
def initial : Matrix 4 := (ofSix (-2) (0) (1) (-1) (-1) (1))
def terminal : Matrix 4 := (ofSix (-2) (0) (1) (-1) (-1) (1))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q576

namespace q577
def initial : Matrix 4 := (ofSix (-2) (0) (1) (-1) (0) (-2))
def terminal : Matrix 4 := (ofSix (2) (0) (-1) (-1) (2) (-2))
def word : List (Fin 4) := [0]

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q577

namespace q595
def initial : Matrix 4 := (ofSix (-2) (0) (1) (1) (-1) (-1))
def terminal : Matrix 4 := (ofSix (-2) (0) (1) (1) (-1) (-1))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q595

namespace q613
def initial : Matrix 4 := (ofSix (-2) (0) (2) (1) (-1) (-1))
def terminal : Matrix 4 := (ofSix (-2) (0) (2) (1) (-1) (-1))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q613

namespace q616
def initial : Matrix 4 := (ofSix (-2) (1) (1) (-2) (1) (1))
def terminal : Matrix 4 := (ofSix (-2) (1) (1) (-2) (1) (1))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q616

namespace q621
def initial : Matrix 4 := (ofSix (-2) (1) (1) (-1) (0) (1))
def terminal : Matrix 4 := (ofSix (-2) (1) (1) (-1) (0) (1))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q621

namespace q624
def initial : Matrix 4 := (ofSix (-2) (1) (1) (-1) (1) (1))
def terminal : Matrix 4 := (ofSix (-2) (1) (1) (-1) (1) (1))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q624

namespace q638
def initial : Matrix 4 := (ofSix (-1) (-1) (-1) (-1) (1) (-1))
def terminal : Matrix 4 := (ofSix (-1) (-1) (-1) (-1) (1) (-1))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q638

namespace q655
def initial : Matrix 4 := (ofSix (-1) (-1) (1) (-1) (-1) (1))
def terminal : Matrix 4 := (ofSix (-1) (-1) (1) (-1) (-1) (1))
def word : List (Fin 4) := []

theorem source_word : applyWord initial word = terminal := by
  funext i j
  exact (show ∀ i j : Fin 4, applyWord initial word i j = terminal i j from by decide) i j

theorem proper_classes_excluded : ∀ i : Fin 6, ProperClassTable terminal i →
    ExcludedPair (orderMarkov terminal (order i)) (matrixPfaffian terminal ^ 2) := by decide

theorem NMA_of_structural_bridges (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) : ¬ MutationAcyclic initial := by
  have hn : ¬ MutationAcyclic terminal :=
    NMA_of_scalar_exclusion hExist hEndpoint terminal (ofSix_skew _ _ _ _ _ _)
      (by decide) (scalar_exclusion_of_table terminal (ofSix_skew _ _ _ _ _ _) proper_classes_excluded)
  intro hm
  apply hn
  rw [← source_word]
  exact (mutationAcyclic_word_iff initial word).mpr hm
end q655

end QuiverProofs.ProperExclusionCertificates
