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
theorem source_masks_all_chunks : ∀ (block offset : Fin 27),
    supportMask (pattern (choiceChunkCode block offset)) =
      ProperMutationChoiceTables.sourceMask (choiceChunkCode block offset) := by
  intro block
  have hb : block=0 ∨ block=1 ∨ block=2 ∨ block=3 ∨ block=4 ∨ block=5 ∨ block=6 ∨ block=7 ∨ block=8 ∨ block=9 ∨ block=10 ∨ block=11 ∨ block=12 ∨ block=13 ∨ block=14 ∨ block=15 ∨ block=16 ∨ block=17 ∨ block=18 ∨ block=19 ∨ block=20 ∨ block=21 ∨ block=22 ∨ block=23 ∨ block=24 ∨ block=25 ∨ block=26 := by omega
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact source_mask_chunk00
  · exact source_mask_chunk01
  · exact source_mask_chunk02
  · exact source_mask_chunk03
  · exact source_mask_chunk04
  · exact source_mask_chunk05
  · exact source_mask_chunk06
  · exact source_mask_chunk07
  · exact source_mask_chunk08
  · exact source_mask_chunk09
  · exact source_mask_chunk10
  · exact source_mask_chunk11
  · exact source_mask_chunk12
  · exact source_mask_chunk13
  · exact source_mask_chunk14
  · exact source_mask_chunk15
  · exact source_mask_chunk16
  · exact source_mask_chunk17
  · exact source_mask_chunk18
  · exact source_mask_chunk19
  · exact source_mask_chunk20
  · exact source_mask_chunk21
  · exact source_mask_chunk22
  · exact source_mask_chunk23
  · exact source_mask_chunk24
  · exact source_mask_chunk25
  · exact source_mask_chunk26

theorem target_masks_all_chunks : ∀ (block offset : Fin 27) (k : Fin 4),
    supportMask (mutate (pattern (choiceChunkCode block offset)) k) =
      ProperMutationChoiceTables.targetMask (choiceChunkCode block offset) k := by
  intro block
  have hb : block=0 ∨ block=1 ∨ block=2 ∨ block=3 ∨ block=4 ∨ block=5 ∨ block=6 ∨ block=7 ∨ block=8 ∨ block=9 ∨ block=10 ∨ block=11 ∨ block=12 ∨ block=13 ∨ block=14 ∨ block=15 ∨ block=16 ∨ block=17 ∨ block=18 ∨ block=19 ∨ block=20 ∨ block=21 ∨ block=22 ∨ block=23 ∨ block=24 ∨ block=25 ∨ block=26 := by omega
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact target_mask_chunk00
  · exact target_mask_chunk01
  · exact target_mask_chunk02
  · exact target_mask_chunk03
  · exact target_mask_chunk04
  · exact target_mask_chunk05
  · exact target_mask_chunk06
  · exact target_mask_chunk07
  · exact target_mask_chunk08
  · exact target_mask_chunk09
  · exact target_mask_chunk10
  · exact target_mask_chunk11
  · exact target_mask_chunk12
  · exact target_mask_chunk13
  · exact target_mask_chunk14
  · exact target_mask_chunk15
  · exact target_mask_chunk16
  · exact target_mask_chunk17
  · exact target_mask_chunk18
  · exact target_mask_chunk19
  · exact target_mask_chunk20
  · exact target_mask_chunk21
  · exact target_mask_chunk22
  · exact target_mask_chunk23
  · exact target_mask_chunk24
  · exact target_mask_chunk25
  · exact target_mask_chunk26

theorem source_mask_correct (code : Fin 729) :
    supportMask (pattern code)=ProperMutationChoiceTables.sourceMask code := by
  simpa only [choiceChunkCode_correct] using
    source_masks_all_chunks (choiceBlock code) (choiceOffset code)

theorem target_mask_correct (code : Fin 729) (k : Fin 4) :
    supportMask (mutate (pattern code) k)=ProperMutationChoiceTables.targetMask code k := by
  simpa only [choiceChunkCode_correct] using
    target_masks_all_chunks (choiceBlock code) (choiceOffset code) k
end QuiverProofs.ProperMutationRepresentativeChoice
