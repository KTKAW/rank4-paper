import QuiverProofs.ProperMutationChoiceChunkCode
namespace QuiverProofs.ProperMutationRepresentativeChoice
open ProperOrder ProperWiggle ProperMutation ProperWiggleInvariants Census
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem source_mask_chunk11 : ∀ offset : Fin 27,
    supportMask (pattern (choiceChunkCode 11 offset)) =
      ProperMutationChoiceTables.sourceMask (choiceChunkCode 11 offset) := by decide

theorem target_mask_chunk11 : ∀ (offset : Fin 27) (k : Fin 4),
    supportMask (mutate (pattern (choiceChunkCode 11 offset)) k) =
      ProperMutationChoiceTables.targetMask (choiceChunkCode 11 offset) k := by decide

theorem finite_choice_chunk11 : ∀ (offset : Fin 27) (k : Fin 4) (i : Fin 6) (c : Fin 4),
    Cut (pattern (choiceChunkCode 11 offset)) (firstOrder k i) c →
    component (ProperMutationChoiceTables.targetMask (choiceChunkCode 11 offset) k) (resultIndex k i c) =
      ProperMutationChoiceTables.chosenClass (choiceChunkCode 11 offset) k
        (component (ProperMutationChoiceTables.sourceMask (choiceChunkCode 11 offset)) (canonicalIndex (firstIndex k i))) := by decide
end QuiverProofs.ProperMutationRepresentativeChoice
