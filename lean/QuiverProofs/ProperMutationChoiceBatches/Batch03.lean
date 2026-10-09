import QuiverProofs.ProperMutationChoiceChunkCode
namespace QuiverProofs.ProperMutationRepresentativeChoice
open ProperOrder ProperWiggle ProperMutation ProperWiggleInvariants Census
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem source_mask_chunk03 : ∀ offset : Fin 27,
    supportMask (pattern (choiceChunkCode 3 offset)) =
      ProperMutationChoiceTables.sourceMask (choiceChunkCode 3 offset) := by decide

theorem target_mask_chunk03 : ∀ (offset : Fin 27) (k : Fin 4),
    supportMask (mutate (pattern (choiceChunkCode 3 offset)) k) =
      ProperMutationChoiceTables.targetMask (choiceChunkCode 3 offset) k := by decide

theorem finite_choice_chunk03 : ∀ (offset : Fin 27) (k : Fin 4) (i : Fin 6) (c : Fin 4),
    Cut (pattern (choiceChunkCode 3 offset)) (firstOrder k i) c →
    component (ProperMutationChoiceTables.targetMask (choiceChunkCode 3 offset) k) (resultIndex k i c) =
      ProperMutationChoiceTables.chosenClass (choiceChunkCode 3 offset) k
        (component (ProperMutationChoiceTables.sourceMask (choiceChunkCode 3 offset)) (canonicalIndex (firstIndex k i))) := by decide
end QuiverProofs.ProperMutationRepresentativeChoice
