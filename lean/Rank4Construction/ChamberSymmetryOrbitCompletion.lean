import Rank4Construction.ChamberSymmetryOrbit
import QuiverProofs.MAHasTotalProper4Completion

/-! Unconditional 48-chamber formula using the checked total-properness bridge. -/

namespace Rank4Construction
open Rank4Formula QuiverProofs

theorem fortyEightChamberMASetSyntax_correct_unconditional
    (q : SixTuple) :
    fortyEightChamberMASetSyntax.eval q = true ↔
      FullSymmetryChamber q ∧ MutationAcyclic (ofTuple q) :=
  fortyEightChamberMASetSyntax_correct_allSymmetries
    MAHasTotalProper4Completion.maHasTotalProper4 q

theorem fortyEightChamberMASetSyntax_on_chamber
    (q : SixTuple) (hch : FullSymmetryChamber q) :
    fortyEightChamberMASetSyntax.eval q = true ↔
      MutationAcyclic (ofTuple q) := by
  rw [fortyEightChamberMASetSyntax_correct_unconditional, and_iff_right hch]

#print axioms fortyEightChamberMASetSyntax_correct_unconditional
#print axioms fortyEightChamberMASetSyntax_on_chamber

end Rank4Construction
