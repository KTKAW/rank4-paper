import QuiverProofs.ProperMutationSupportVerification
import QuiverProofs.ProperMutationChoiceBatches.Batch00
import QuiverProofs.ProperMutationChoiceBatches.Batch01
import QuiverProofs.ProperMutationChoiceBatches.Batch02
import QuiverProofs.ProperMutationChoiceBatches.Batch03
import QuiverProofs.ProperMutationChoiceBatches.Batch04
import QuiverProofs.ProperMutationChoiceBatches.Batch05
import QuiverProofs.ProperMutationChoiceBatches.Batch06
import QuiverProofs.ProperMutationChoiceBatches.Batch07
import QuiverProofs.ProperMutationChoiceBatches.Batch08
import QuiverProofs.ProperMutationChoiceBatches.Batch09
import QuiverProofs.ProperMutationChoiceBatches.Batch10
import QuiverProofs.ProperMutationChoiceBatches.Batch11
import QuiverProofs.ProperMutationChoiceBatches.Batch12
import QuiverProofs.ProperMutationChoiceBatches.Batch13
import QuiverProofs.ProperMutationChoiceBatches.Batch14
import QuiverProofs.ProperMutationChoiceBatches.Batch15
import QuiverProofs.ProperMutationChoiceBatches.Batch16
import QuiverProofs.ProperMutationChoiceBatches.Batch17
import QuiverProofs.ProperMutationChoiceBatches.Batch18
import QuiverProofs.ProperMutationChoiceBatches.Batch19
import QuiverProofs.ProperMutationChoiceBatches.Batch20
import QuiverProofs.ProperMutationChoiceBatches.Batch21
import QuiverProofs.ProperMutationChoiceBatches.Batch22
import QuiverProofs.ProperMutationChoiceBatches.Batch23
import QuiverProofs.ProperMutationChoiceBatches.Batch24
import QuiverProofs.ProperMutationChoiceBatches.Batch25
import QuiverProofs.ProperMutationChoiceBatches.Batch26
namespace QuiverProofs.ProperMutationRepresentativeChoice
open ProperOrder ProperWiggle ProperMutation ProperWiggleInvariants Census
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem finite_choices_all_chunks : ∀ (block offset : Fin 27) (k : Fin 4) (i : Fin 6) (c : Fin 4),
    Cut (pattern (choiceChunkCode block offset)) (firstOrder k i) c →
    component (ProperMutationChoiceTables.targetMask (choiceChunkCode block offset) k) (resultIndex k i c) =
      ProperMutationChoiceTables.chosenClass (choiceChunkCode block offset) k
        (component (ProperMutationChoiceTables.sourceMask (choiceChunkCode block offset)) (canonicalIndex (firstIndex k i))) := by
  intro block
  have hb : block=0 ∨ block=1 ∨ block=2 ∨ block=3 ∨ block=4 ∨ block=5 ∨ block=6 ∨ block=7 ∨ block=8 ∨ block=9 ∨ block=10 ∨ block=11 ∨ block=12 ∨ block=13 ∨ block=14 ∨ block=15 ∨ block=16 ∨ block=17 ∨ block=18 ∨ block=19 ∨ block=20 ∨ block=21 ∨ block=22 ∨ block=23 ∨ block=24 ∨ block=25 ∨ block=26 := by omega
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact finite_choice_chunk00
  · exact finite_choice_chunk01
  · exact finite_choice_chunk02
  · exact finite_choice_chunk03
  · exact finite_choice_chunk04
  · exact finite_choice_chunk05
  · exact finite_choice_chunk06
  · exact finite_choice_chunk07
  · exact finite_choice_chunk08
  · exact finite_choice_chunk09
  · exact finite_choice_chunk10
  · exact finite_choice_chunk11
  · exact finite_choice_chunk12
  · exact finite_choice_chunk13
  · exact finite_choice_chunk14
  · exact finite_choice_chunk15
  · exact finite_choice_chunk16
  · exact finite_choice_chunk17
  · exact finite_choice_chunk18
  · exact finite_choice_chunk19
  · exact finite_choice_chunk20
  · exact finite_choice_chunk21
  · exact finite_choice_chunk22
  · exact finite_choice_chunk23
  · exact finite_choice_chunk24
  · exact finite_choice_chunk25
  · exact finite_choice_chunk26

/-- The complete 729-pattern choice classification, assembled from kernel-checked chunks. -/
theorem finite_choice_class : ∀ (code : Fin 729) (k : Fin 4) (i : Fin 6) (c : Fin 4),
    Cut (pattern code) (firstOrder k i) c →
    component (ProperMutationChoiceTables.targetMask code k) (resultIndex k i c) =
      ProperMutationChoiceTables.chosenClass code k
        (component (ProperMutationChoiceTables.sourceMask code) (canonicalIndex (firstIndex k i))) := by
  intro code k i c
  have h := finite_choices_all_chunks (choiceBlock code) (choiceOffset code) k i c
  simpa only [choiceChunkCode_correct] using h

theorem finite_choice_independence (code : Fin 729) (k : Fin 4)
    (i j : Fin 6) (c d : Fin 4)
    (hi : Cut (pattern code) (firstOrder k i) c)
    (hj : Cut (pattern code) (firstOrder k j) d)
    (hc : component (supportMask (pattern code)) (canonicalIndex (firstIndex k i)) =
      component (supportMask (pattern code)) (canonicalIndex (firstIndex k j))) :
    component (supportMask (mutate (pattern code) k)) (resultIndex k i c) =
      component (supportMask (mutate (pattern code) k)) (resultIndex k j d) := by
  have hci := finite_choice_class code k i c hi
  have hcj := finite_choice_class code k j d hj
  rw [source_mask_correct code] at hc
  rw [target_mask_correct code k,hci,hcj,hc]

end QuiverProofs.ProperMutationRepresentativeChoice
