import MA4RestartCoordinator20261003.StableColoredFrameSort
import MA4RestartCoordinator20261003.ActualColoredArrowProjection

/-! Stable sorting removes the supplied next-color-block premise. The
remaining terminal same-color Hom and inversion orthogonality gates are
exactly the categorical sweep preservation obligations. -/
namespace QuiverProofs.MA4RestartSortedNextArrowProjection
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open ProperOrder MAExistenceLiterature MAExistenceCompanions
open MAExistenceCoefficients MAExistenceTeamDJointSeed MAExistenceTeamCTriangleOutside
open MA4RestartWeightedQuiverModel MA4RestartModelExt
open MA4RestartArrow20261003.AdjacentExceptionalFrame
open MA4RestartStableColoredFrameSort MA4RestartActualColoredArrowProjection
set_option maxHeartbeats 0

local instance actualHasExt (B : Matrix 4) (K : Type) [Field K] :
    HasExt.{0} (Representation B K) := representation_hasExt B K

theorem chronological_next_arrows_of_terminal_color_gates
    (B₀ U : Matrix 4) (K : Type) [Field K] (hB₀ : SkewSymmetric B₀)
    (hs : Cosquare.add U (Cosquare.transpose U) = initialCompanion B₀)
    (ha : Cosquare.add U (Cosquare.scale (-1) (Cosquare.transpose U)) = reverse B₀)
    (w : List (Fin 4)) (hOld : SeedInv B₀ w) (k : Fin 4)
    (p : CyclicOrder) (M : Fin 4 → Representation B₀ K)
    (hFrame : ExceptionalFrame (vertexFunctor B₀ K) M)
    (hDims : ∀ a b, (Module.finrank K ((vertexFunctor B₀ K b).obj (M a)) : Int) =
      colorSign (columnColor (principalSeed B₀ (w ++ [k])).2) (p.toFun a) *
        (principalSeed B₀ (w ++ [k])).2 b (p.toFun a))
    (hSame : ∀ a b, a < b →
      columnColor (principalSeed B₀ (w ++ [k])).2 (p.toFun a) =
        columnColor (principalSeed B₀ (w ++ [k])).2 (p.toFun b) →
      ∀ f : M a ⟶ M b, f = 0)
    (hInversions : ∀ a b, a < b →
      columnColor (principalSeed B₀ (w ++ [k])).2 (p.toFun a) = false →
      columnColor (principalSeed B₀ (w ++ [k])).2 (p.toFun b) = true →
      (∀ f : M a ⟶ M b, f = 0) ∧ (∀ e : Ext (M a) (M b) 1, e = 0)) :
    ArrowSigns (principalSeed B₀ (w ++ [k])).1
      (coefficientCompanion B₀ (principalSeed B₀ (w ++ [k])).2)
      (columnColor (principalSeed B₀ (w ++ [k])).2) := by
  let g := columnColor (principalSeed B₀ (w ++ [k])).2
  obtain ⟨q,hBlock,hSorted,hSortedSame⟩ := stable_sort_actual_colored_frame
    (vertexFunctor B₀ K) M hFrame (fun a => g (p.toFun a)) hSame hInversions
  have hBlockLabels : GreenBeforeRed g (p.trans q) := by
    intro i j hi hj
    have h := hBlock (p.invFun i) (p.invFun j)
      (by simpa only [p.right_inv] using hi) (by simpa only [p.right_inv] using hj)
    exact h
  exact chronological_next_arrowSigns_of_actual_colored_frame B₀ U K hB₀ hs ha w hOld k
    (p.trans q) (fun a => M (q.toFun a)) hSorted
    (fun a b => hDims (q.toFun a) b) hSortedSame hBlockLabels

#check chronological_next_arrows_of_terminal_color_gates
#print axioms chronological_next_arrows_of_terminal_color_gates
end QuiverProofs.MA4RestartSortedNextArrowProjection
