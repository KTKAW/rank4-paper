import QuiverProofs.ProperMutationSignModel
import QuiverProofs.ProperMutationChoiceTables
namespace QuiverProofs.ProperMutationRepresentativeChoice
open ProperOrder ProperWiggle ProperMutation ProperWiggleInvariants Census
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def choiceChunkCode (block offset : Fin 27) : Fin 729 :=
  ⟨block.val*27+offset.val, by omega⟩
def choiceBlock (code : Fin 729) : Fin 27 := ⟨code.val/27, by omega⟩
def choiceOffset (code : Fin 729) : Fin 27 := ⟨code.val%27, Nat.mod_lt _ (by decide)⟩
theorem choiceChunkCode_correct (code : Fin 729) :
    choiceChunkCode (choiceBlock code) (choiceOffset code)=code := by
  apply Fin.ext
  simp only [choiceChunkCode,choiceBlock,choiceOffset]
  omega
end QuiverProofs.ProperMutationRepresentativeChoice
