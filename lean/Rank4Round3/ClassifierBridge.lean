import Rank4CoordinatorR2.ClassificationCompletion
import Rank4Formula.FormulaLanguage

/-!
The supplied archive's unrestricted bounded-word decision theorem, stated
directly for every six-coordinate integer input. This is a computable
classification criterion, not a fixed polynomial-sign formula.
-/

namespace Rank4Round3
open Rank4Formula QuiverProofs

def certifiedInput (q : SixTuple) : Rank4Classification.Input :=
  ⟨ofTuple q, ofSix_skew (q 0) (q 1) (q 2) (q 3) (q 4) (q 5)⟩

def classifySix (q : SixTuple) : Bool :=
  Rank4Classification.classify4 (certifiedInput q)

theorem classifySix_MA_iff (q : SixTuple) :
    classifySix q = true ↔ MutationAcyclic (ofTuple q) := by
  simpa [classifySix, certifiedInput] using
    Rank4Classification.classify4_ma_iff (certifiedInput q)

theorem classifySix_NMA_iff (q : SixTuple) :
    classifySix q = false ↔ ¬ MutationAcyclic (ofTuple q) := by
  simpa [classifySix, certifiedInput] using
    Rank4Classification.classify4_nma_iff (certifiedInput q)

#print axioms classifySix_MA_iff
#print axioms classifySix_NMA_iff

end Rank4Round3
