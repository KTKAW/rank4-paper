import QuiverProofs.ProperMutationChoiceChunkCode
namespace QuiverProofs.ProperMutationRepresentativeChoice
open ProperOrder ProperWiggle ProperMutation ProperWiggleInvariants Census
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem source_mask_chunk15 : ∀ offset : Fin 27,
    supportMask (pattern (choiceChunkCode 15 offset)) =
      ProperMutationChoiceTables.sourceMask (choiceChunkCode 15 offset) := by decide

theorem target_mask_chunk15 : ∀ (offset : Fin 27) (k : Fin 4),
    supportMask (mutate (pattern (choiceChunkCode 15 offset)) k) =
      ProperMutationChoiceTables.targetMask (choiceChunkCode 15 offset) k := by decide

theorem finite_choice_chunk15 : ∀ (offset : Fin 27) (k : Fin 4) (i : Fin 6) (c : Fin 4),
    Cut (pattern (choiceChunkCode 15 offset)) (firstOrder k i) c →
    component (ProperMutationChoiceTables.targetMask (choiceChunkCode 15 offset) k) (resultIndex k i c) =
      ProperMutationChoiceTables.chosenClass (choiceChunkCode 15 offset) k
        (component (ProperMutationChoiceTables.sourceMask (choiceChunkCode 15 offset)) (canonicalIndex (firstIndex k i))) := by decide
end QuiverProofs.ProperMutationRepresentativeChoice
