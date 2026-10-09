import MA4RestartCoordinator20261003.JointHistoryIntegration
import MA4RestartArrow20261003.ChronologicalColoredArrowStep

/-! The exact MA existence conclusion from the initialized actual principal
chronology. `SeedInv` keeps its original six fields; actual representations
are a separate initialized and preserved witness. -/
namespace QuiverProofs.MAHasTotalProper4Completion
open ProperOrder ProperObstructionSoundness
open MAExistenceLiterature MAExistenceCoefficients MAExistenceCompanions
open MAExistenceTeamDJointSeed MAExistenceTeamBRootPositivity
open MAExistenceTeamCTriangleOutside
open MAExistenceTeamCCertificateTransport
open MA4RestartMatrixEuler MA4RestartJointHistoryIntegration
open MA4RestartActualGreenChronologicalNoThreeCycle
open MA4RestartArrow20261003.ChronologicalColoredArrowStep
set_option maxHeartbeats 0

/-- Both colors of the actual unrestricted mutation step supply the exact
arrow law consumed by the separate joint induction. -/
theorem realizedArrowLaw : RealizedArrowLaw := by
  intro B₀ hB₀ _hAc w hInv hActual k
  have hParts := original_euler_matrix_parts B₀ hB₀
  exact principalSeed_next_arrowSigns B₀ (originalEulerMatrix B₀) ℚ hB₀
    hParts.1 hParts.2 w hInv hActual k

/-- The original invariant and actual objects are established for every
finite word, with no current or future invariant supplied. -/
theorem principalSeed_jointState_all_words (B₀ : Matrix 4)
    (hB₀ : SkewSymmetric B₀) (hAc : Acyclic B₀) (w : List (Fin 4)) :
    JointState B₀ w :=
  jointState_all_words B₀ hB₀ hAc (realizedArrowLaw B₀ hB₀ hAc) w

theorem principalSeed_seedInv_all_words (B₀ : Matrix 4)
    (hB₀ : SkewSymmetric B₀) (hAc : Acyclic B₀) (w : List (Fin 4)) :
    SeedInv B₀ w :=
  (principalSeed_jointState_all_words B₀ hB₀ hAc w).1

/-- Global next Euler No3, including pivot triples and every initial Euler
matrix with both required parts. No connected-support restriction is used. -/
theorem principalSeed_next_noEulerThreeCycle (B₀ U₀ : Matrix 4)
    (hB₀ : SkewSymmetric B₀) (hAc : Acyclic B₀)
    (hs : Cosquare.add U₀ (Cosquare.transpose U₀) = initialCompanion B₀)
    (ha : Cosquare.add U₀ (Cosquare.scale (-1) (Cosquare.transpose U₀)) = reverse B₀)
    (w : List (Fin 4)) (k i j l : Fin 4)
    (hij : i ≠ j) (hjl : j ≠ l) (hli : l ≠ i) :
    noEulerThreeCycle
      (normalizedEuler (coefficientBilinear U₀ (principalSeed B₀ (w ++ [k])).2)
        (columnColor (principalSeed B₀ (w ++ [k])).2)) i j l := by
  have hOld := principalSeed_jointState_all_words B₀ hB₀ hAc w
  exact (principal_seed_next_actual_and_no_three_cycle B₀ ℚ U₀ hB₀ hs ha
    w hOld.1 hOld.2 k).2 i j l hij hjl hli

/-- The original local mutation arrow equivalence holds for every positive
next arrow. The residual-case callback is a restriction of this theorem. -/
theorem principalSeed_next_localMutation_arrowSigns (B₀ : Matrix 4)
    (hB₀ : SkewSymmetric B₀) (hAc : Acyclic B₀)
    (w : List (Fin 4)) (k i j : Fin 4)
    (hb : 0 < mutate (principalSeed B₀ w).1 k i j) :
    (0 < localMutation (principalSeed B₀ w).1
      (coefficientCompanion B₀ (principalSeed B₀ w).2)
      (columnColor (principalSeed B₀ w).2) k i j ↔
      columnColor (mutateCoefficients (principalSeed B₀ w).1
        (principalSeed B₀ w).2 k) i = false ∧
      columnColor (mutateCoefficients (principalSeed B₀ w).1
        (principalSeed B₀ w).2 k) j = true) := by
  have hInv := principalSeed_seedInv_all_words B₀ hB₀ hAc w
  have hC := seedInv_signCoherent B₀ hB₀ w hInv
  have hg : columnColor (principalSeed B₀ w).2 k = true →
      ∀ a, 0 ≤ (principalSeed B₀ w).2 a k :=
    fun hk => ((color_iff_green hC k).mp hk).1
  have hr : columnColor (principalSeed B₀ w).2 k = false →
      ∀ a, (principalSeed B₀ w).2 a k ≤ 0 :=
    fun hk => ((color_iff_red hC k).mp hk).1
  have he : principalSeed B₀ (w ++ [k]) = mutateSeed (principalSeed B₀ w) k :=
    evolve_append_singleton B₀ identityCoefficients w k
  have hSigns := (principalSeed_seedInv_all_words B₀ hB₀ hAc (w ++ [k])).arrowSigns
  have hLocal : ArrowSigns (mutate (principalSeed B₀ w).1 k)
      (localMutation (principalSeed B₀ w).1
        (coefficientCompanion B₀ (principalSeed B₀ w).2)
        (columnColor (principalSeed B₀ w).2) k)
      (columnColor (mutateCoefficients (principalSeed B₀ w).1
        (principalSeed B₀ w).2 k)) := by
    simpa only [he, mutateSeed, coefficientCompanion_mutation_local B₀
      (principalSeed B₀ w).1 (principalSeed B₀ w).2
      (columnColor (principalSeed B₀ w).2) k hg hr] using hSigns
  exact hLocal i j hb

/-- Unconditional inhabitant of the original project proposition. -/
theorem maHasTotalProper4 : MAHasTotalProper4 :=
  maHasTotalProper4_of_realizedArrowLaw realizedArrowLaw

#print maHasTotalProper4
#print axioms maHasTotalProper4
end QuiverProofs.MAHasTotalProper4Completion
