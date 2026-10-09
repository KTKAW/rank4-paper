import MA4RestartCoordinator20261003.InitialOrderedFrame
import MA4RestartEuler20261003.ActualGreenChronologicalNoThreeCycle
import QuiverProofs.MAExistenceTeamCTriangleRefinedClosure
import QuiverProofs.MAExistenceTeamDProperCertificate

/-! The concrete alternative all-word consumer. The original six-field
SeedInv is unchanged; actual realization is a separate initialized field.
The ONLY remaining supplier is next ArrowSigns from this old joint state.
That supplier is an explicit unproved argument, not an axiom or conclusion. -/
namespace QuiverProofs.MA4RestartJointHistoryIntegration
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open ProperOrder ProperObstructionSoundness
open MAExistenceLiterature MAExistenceCompanions MAExistenceCoefficients
open MAExistenceTeamDJointSeed MAExistenceTeamCTriangleOutside
open MAExistenceTeamCTriangleRefinedClosure MAExistenceTeamDProperCertificate
open MA4RestartWeightedQuiverModel MA4RestartModelExt MA4RestartMatrixEuler
open MA4RestartInitialOrderedFrame MA4RestartActualGreenChronologicalNoThreeCycle
open MA4RestartArrow20261003.AdjacentExceptionalFrame
open MA4RestartArrow20261003.ActualLeftSweep
open MA4RestartArrow20261003.ActualFrameChronology
set_option maxHeartbeats 0

local instance actualHasExt (B : Matrix 4) :
    HasExt.{0} (Representation B ℚ) := representation_hasExt B ℚ

/-- The original numeric invariant and separate actual objects. -/
def JointState (B₀ : Matrix 4) (w : List (Fin 4)) : Prop :=
  SeedInv B₀ w ∧
    UnorderedActualRealization (vertexFunctor B₀ ℚ) (principalSeed B₀ w).2

/-- Exact local consumer contract for the unfinished colored-sweep proof.
No next invariant, actual tuple, admissibility, or No3 is an input. -/
def RealizedArrowStep (B₀ : Matrix 4) : Prop :=
  ∀ (w : List (Fin 4)), SeedInv B₀ w →
    UnorderedActualRealization (vertexFunctor B₀ ℚ) (principalSeed B₀ w).2 →
    ∀ k : Fin 4,
      ArrowSigns (principalSeed B₀ (w ++ [k])).1
        (coefficientCompanion B₀ (principalSeed B₀ (w ++ [k])).2)
        (columnColor (principalSeed B₀ (w ++ [k])).2)

def RealizedArrowLaw : Prop :=
  ∀ B₀ : Matrix 4, SkewSymmetric B₀ → Acyclic B₀ → RealizedArrowStep B₀

/-- The literal empty chronology starts with the actual four simples. -/
theorem jointState_nil (B₀ : Matrix 4) (hB₀ : SkewSymmetric B₀) (hAc : Acyclic B₀) :
    JointState B₀ [] := by
  refine ⟨seedInv_nil B₀ hB₀ hAc, ?_⟩
  change UnorderedActualRealization (vertexFunctor B₀ ℚ) (Cosquare.one : Matrix 4)
  obtain ⟨p,hp⟩ := acyclic_topological_order B₀ hB₀ hAc
  refine ⟨p,initialObjects B₀ ℚ p,(fun _ => 1),
    initial_exceptional_frame B₀ ℚ hB₀ p hp, ?_⟩
  intro a
  refine ⟨Or.inl rfl, ?_⟩
  intro b
  have h := congrFun (initial_dimension_columns B₀ ℚ p a) b
  simpa only [one_mul] using h

/-- Both-color actual realization and No3 are constructed before next
SeedInv. Only the unfinished arrow supplier is supplied. -/
theorem jointState_append (B₀ : Matrix 4) (hB₀ : SkewSymmetric B₀)
    (hArrows : RealizedArrowStep B₀) (w : List (Fin 4)) (k : Fin 4)
    (hOld : JointState B₀ w) : JointState B₀ (w ++ [k]) := by
  have hParts := original_euler_matrix_parts B₀ hB₀
  obtain ⟨hActual,hNo3⟩ := principal_seed_next_actual_and_no_three_cycle B₀ ℚ
    (originalEulerMatrix B₀) hB₀ hParts.1 hParts.2 w hOld.1 hOld.2 k
  have hSigns := hArrows w hOld.1 hOld.2 k
  have hTriangles := principalSeed_triangles_of_supported_mixed_nonoriented_noEulerThreeCycle
    B₀ (originalEulerMatrix B₀) hB₀ hParts.1 hParts.2 w k hOld.1 hSigns
    (fun i j l hij hjl hli _ _ _ _ _ _ _ _ => hNo3 i j l hij hjl hli)
  exact ⟨seedInv_append_of_updatedArrowSigns_triangles B₀ hB₀ w k hOld.1 hSigns hTriangles,
    hActual⟩

/-- Induction runs from actual initialization and uses only the old joint
state at each unrestricted append. This remains conditional on hArrows. -/
theorem jointState_all_words (B₀ : Matrix 4) (hB₀ : SkewSymmetric B₀)
    (hAc : Acyclic B₀) (hArrows : RealizedArrowStep B₀) (w : List (Fin 4)) :
    JointState B₀ w := by
  induction w using List.reverseRecOn with
  | nil => exact jointState_nil B₀ hB₀ hAc
  | append_singleton w k ih => exact jointState_append B₀ hB₀ hArrows w k ih

/-- Actual application to the original total-properness target. The single
remaining global realized-arrow law is explicit and is not proved here. -/
theorem maHasTotalProper4_of_realizedArrowLaw (hArrows : RealizedArrowLaw) :
    MAHasTotalProper4 := by
  apply maHasTotalProper4_of_companionClosure
  intro B₀ hB₀ hAc w _hInv k
  have hNext := (jointState_all_words B₀ hB₀ hAc (hArrows B₀ hB₀ hAc) (w ++ [k])).1
  exact ⟨hNext.arrowSigns,hNext.admissible⟩

#print RealizedArrowStep
#print RealizedArrowLaw
#check jointState_nil
#check jointState_append
#check jointState_all_words
#print maHasTotalProper4_of_realizedArrowLaw
#print axioms maHasTotalProper4_of_realizedArrowLaw
end QuiverProofs.MA4RestartJointHistoryIntegration
