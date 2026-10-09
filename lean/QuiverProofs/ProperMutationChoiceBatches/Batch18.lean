import QuiverProofs.ProperMutationChoiceChunkCode
namespace QuiverProofs.ProperMutationRepresentativeChoice
open ProperOrder ProperWiggle ProperMutation ProperWiggleInvariants Census
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem source_mask_chunk18 : ∀ offset : Fin 27,
    supportMask (pattern (choiceChunkCode 18 offset)) =
      ProperMutationChoiceTables.sourceMask (choiceChunkCode 18 offset) := by decide

theorem target_mask_chunk18 : ∀ (offset : Fin 27) (k : Fin 4),
    supportMask (mutate (pattern (choiceChunkCode 18 offset)) k) =
      ProperMutationChoiceTables.targetMask (choiceChunkCode 18 offset) k := by decide

theorem finite_choice_chunk18 : ∀ (offset : Fin 27) (k : Fin 4) (i : Fin 6) (c : Fin 4),
    Cut (pattern (choiceChunkCode 18 offset)) (firstOrder k i) c →
    component (ProperMutationChoiceTables.targetMask (choiceChunkCode 18 offset) k) (resultIndex k i c) =
      ProperMutationChoiceTables.chosenClass (choiceChunkCode 18 offset) k
        (component (ProperMutationChoiceTables.sourceMask (choiceChunkCode 18 offset)) (canonicalIndex (firstIndex k i))) := by decide
end QuiverProofs.ProperMutationRepresentativeChoice
