import QuiverProofs.MAExistenceTeamCRootSigns
import QuiverProofs.MAExistenceTeamBCompanionClosure
/-! Actual principal-coefficient root and sign interfaces.

The local step proves only the updated actual root columns, their strict sign
coherence and (under current admissibility) the updated actual Gram companion.
Updated arrow signs and updated admissibility are separate open obligations.

The all-word wrappers expose current actual Gram quasi-Cartan and arrow-sign
data at every prefix as hypotheses. They do not establish that supply, and do
not assert an unconditional principal-coefficient or TotalProper theorem.
-/
namespace QuiverProofs.MAExistenceTeamCSeedStep
open MAExistenceLiterature MAExistenceCompanions MAExistenceCoefficients
open MAExistenceTeamBRootPositivity MAExistenceTeamCRootSigns
open MAExistenceAuxiliaryOrders
set_option maxHeartbeats 0

theorem coefficientMutation_rooted_and_signCoherent (B₀ B C : Matrix 4)
    (hB₀ : SkewSymmetric B₀) (hB : SkewSymmetric B) (k : Fin 4)
    (hA : QuasiCartanCompanion B (coefficientCompanion B₀ C))
    (hs : ArrowSigns B (coefficientCompanion B₀ C) (columnColor C))
    (hroots : ∀ j, RealRoot (initialCompanion B₀) (column C j)) :
    (∀ j, RealRoot (initialCompanion B₀) (column (mutateCoefficients B C k) j)) ∧
      SignCoherent (mutateCoefficients B C k) := by
  have hcoh := realRootColumns_signCoherent B₀ C hB₀ hroots
  have hg : columnColor C k = true → ∀ i, 0 ≤ C i k :=
    fun hk => ((color_iff_green hcoh k).mp hk).1
  have hr : columnColor C k = false → ∀ i, C i k ≤ 0 :=
    fun hk => ((color_iff_red hcoh k).mp hk).1
  have hnew := coefficientMutation_realRoots B₀ B C hB₀ hB (columnColor C) k hA hs hg hr hroots
  exact ⟨hnew, realRootColumns_signCoherent B₀ _ hB₀ hnew⟩

/-- Root identification along the actual chronological evolution, conditional
on independently supplied current companion data at every prefix. -/
theorem evolve_realRoots_of_companionData (B₀ B C : Matrix 4)
    (hB₀ : SkewSymmetric B₀) (hB : SkewSymmetric B)
    (hroots : ∀ j, RealRoot (initialCompanion B₀) (column C j))
    (hdata : ∀ w : List (Fin 4),
      QuasiCartanCompanion (evolve B C w).1 (coefficientCompanion B₀ (evolve B C w).2) ∧
      ArrowSigns (evolve B C w).1 (coefficientCompanion B₀ (evolve B C w).2)
        (columnColor (evolve B C w).2)) (w : List (Fin 4)) :
    ∀ j, RealRoot (initialCompanion B₀) (column (evolve B C w).2 j) := by
  induction w generalizing B C with
  | nil => exact hroots
  | cons k w ih =>
      have hcurrent := hdata []
      have hnew := coefficientMutation_rooted_and_signCoherent B₀ B C hB₀ hB k
        hcurrent.1 hcurrent.2 hroots
      exact ih (mutate B k) (mutateCoefficients B C k)
        (mutation_preserves_skew B k hB) hnew.1 (fun v => hdata (k :: v))

/-- The actual identity-initialized columns lie in the real-root orbit when
the explicit all-prefix companion supply has independently been established. -/
theorem principalSeed_realRoots_of_companionData (B₀ : Matrix 4)
    (hB₀ : SkewSymmetric B₀)
    (hdata : ∀ w : List (Fin 4),
      QuasiCartanCompanion (principalSeed B₀ w).1 (coefficientCompanion B₀ (principalSeed B₀ w).2) ∧
      ArrowSigns (principalSeed B₀ w).1 (coefficientCompanion B₀ (principalSeed B₀ w).2)
        (columnColor (principalSeed B₀ w).2)) (w : List (Fin 4)) :
    ∀ j, RealRoot (initialCompanion B₀) (column (principalSeed B₀ w).2 j) :=
  evolve_realRoots_of_companionData B₀ B₀ identityCoefficients hB₀ hB₀
    (identity_realRoots B₀) hdata w

theorem principalSeed_signCoherent_of_companionData (B₀ : Matrix 4)
    (hB₀ : SkewSymmetric B₀)
    (hdata : ∀ w : List (Fin 4),
      QuasiCartanCompanion (principalSeed B₀ w).1 (coefficientCompanion B₀ (principalSeed B₀ w).2) ∧
      ArrowSigns (principalSeed B₀ w).1 (coefficientCompanion B₀ (principalSeed B₀ w).2)
        (columnColor (principalSeed B₀ w).2)) (w : List (Fin 4)) :
    SignCoherent (principalSeed B₀ w).2 :=
  realRootColumns_signCoherent B₀ _ hB₀ (principalSeed_realRoots_of_companionData B₀ hB₀ hdata w)


/-- Current roots supply pivot coherence; current admissibility supplies the
next Gram magnitudes. Future arrow signs and admissibility are not conclusions. -/
theorem coefficientMutation_rooted_signCoherent_quasiCartan (B₀ B C : Matrix 4)
    (hB₀ : SkewSymmetric B₀) (hB : SkewSymmetric B) (k : Fin 4)
    (hA : QuasiCartanCompanion B (coefficientCompanion B₀ C))
    (hs : ArrowSigns B (coefficientCompanion B₀ C) (columnColor C))
    (ha : CompanionAdmissible4 B (coefficientCompanion B₀ C))
    (hroots : ∀ j, RealRoot (initialCompanion B₀) (column C j)) :
    (∀ j, RealRoot (initialCompanion B₀) (column (mutateCoefficients B C k) j)) ∧
      SignCoherent (mutateCoefficients B C k) ∧
      QuasiCartanCompanion (mutate B k) (coefficientCompanion B₀ (mutateCoefficients B C k)) := by
  have hcoh := realRootColumns_signCoherent B₀ C hB₀ hroots
  have hg : columnColor C k = true → ∀ i, 0 ≤ C i k :=
    fun hk => ((color_iff_green hcoh k).mp hk).1
  have hr : columnColor C k = false → ∀ i, C i k ≤ 0 :=
    fun hk => ((color_iff_red hcoh k).mp hk).1
  have hnew := coefficientMutation_rooted_and_signCoherent B₀ B C hB₀ hB k hA hs hroots
  refine ⟨hnew.1, hnew.2, ?_⟩
  rw [coefficientCompanion_mutation_local B₀ B C (columnColor C) k hg hr]
  exact MAExistenceTeamBCompanionClosure.localMutation_quasiCartan B _ (columnColor C) k hB hA hs ha

/-- Actual principal data initializes with roots, signs, Gram magnitudes and
arrow signs. Companion admissibility is deliberately not asserted here. -/
theorem identity_rooted_signCoherent_quasiCartan_arrowSigns (B₀ : Matrix 4)
    (hB₀ : SkewSymmetric B₀) :
    (∀ j, RealRoot (initialCompanion B₀) (column identityCoefficients j)) ∧
      SignCoherent (identityCoefficients : Matrix 4) ∧
      QuasiCartanCompanion B₀ (coefficientCompanion B₀ identityCoefficients) ∧
      ArrowSigns B₀ (coefficientCompanion B₀ identityCoefficients) (columnColor identityCoefficients) := by
  have hgram : coefficientCompanion B₀ identityCoefficients = initialCompanion B₀ :=
    coefficientCompanion_initial B₀
  have hcolor : columnColor (identityCoefficients : Matrix 4) = fun _ => true := by
    funext j
    exact color_green (identity_green j)
  refine ⟨identity_realRoots B₀, identity_signCoherent, ?_, ?_⟩
  · rw [hgram]
    exact initialCompanion_quasiCartan B₀ hB₀
  · rw [hgram, hcolor]
    exact initialCompanion_arrowSigns B₀ hB₀

end QuiverProofs.MAExistenceTeamCSeedStep
