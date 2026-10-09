import QuiverProofs.MAExistenceTeamDAdmissibility
import QuiverProofs.MAExistenceTeamCSeedStep
import QuiverProofs.MAExistenceTeamCCertificateTransport
import Mathlib.Data.List.Induction

/-! Actual chronological seed data for Team D. Next arrow signs and cycle
admissibility remain explicit obligations; no preservation law is a field. -/
namespace QuiverProofs.MAExistenceTeamDJointSeed
open MAExistenceLiterature MAExistenceCoefficients MAExistenceCompanions
open MAExistenceAuxiliaryOrders MAExistenceTeamBRootPositivity
open MAExistenceTeamCRootSigns MAExistenceTeamCSeedStep
open MAExistenceTeamCCertificateTransport Cosquare

/-- The current state is the actual identity-initialized chronological seed. -/
structure SeedInv (B₀ : Matrix 4) (w : List (Fin 4)) : Prop where
  roots : ∀ j, RealRoot (initialCompanion B₀) (column (principalSeed B₀ w).2 j)
  companion : QuasiCartanCompanion (principalSeed B₀ w).1
    (coefficientCompanion B₀ (principalSeed B₀ w).2)
  arrowSigns : ArrowSigns (principalSeed B₀ w).1
    (coefficientCompanion B₀ (principalSeed B₀ w).2) (columnColor (principalSeed B₀ w).2)
  admissible : CompanionAdmissible4 (principalSeed B₀ w).1
    (coefficientCompanion B₀ (principalSeed B₀ w).2)
  basis : IntegralBasis (principalSeed B₀ w).2
  exchangeOrigin : (principalSeed B₀ w).1 =
    mul (mul (transpose (principalSeed B₀ w).2) B₀) (principalSeed B₀ w).2

/-- Acyclicity gives every initial chordless-cycle parity, including missing
edges and disconnected supports. -/
theorem initialCompanion_admissible (B₀ : Matrix 4)
    (hB₀ : SkewSymmetric B₀) (hAc : Acyclic B₀) :
    CompanionAdmissible4 B₀ (initialCompanion B₀) := by
  have hc := acyclic_allGreen_colorAdmissible B₀ hB₀ hAc
  have hA := initialCompanion_quasiCartan B₀ hB₀
  have hs := initialCompanion_arrowSigns B₀ hB₀
  have tri : ∀ i j k, triangleColorAdmissible B₀ (fun _ => true) i j k →
      triangleCompanionAdmissible B₀ (initialCompanion B₀) i j k := by
    intro i j k h hij hjk hki
    rw [← positiveColorEdge_companion B₀ _ hB₀ hA.1 _ hs i j hij,
      ← positiveColorEdge_companion B₀ _ hB₀ hA.1 _ hs j k hjk,
      ← positiveColorEdge_companion B₀ _ hB₀ hA.1 _ hs k i hki]
    exact h hij hjk hki
  have square : ∀ i j k l, squareColorAdmissible B₀ (fun _ => true) i j k l →
      squareCompanionAdmissible B₀ (initialCompanion B₀) i j k l := by
    intro i j k l h hij hjk hkl hli hik hjl
    rw [← positiveColorEdge_companion B₀ _ hB₀ hA.1 _ hs i j hij,
      ← positiveColorEdge_companion B₀ _ hB₀ hA.1 _ hs j k hjk,
      ← positiveColorEdge_companion B₀ _ hB₀ hA.1 _ hs k l hkl,
      ← positiveColorEdge_companion B₀ _ hB₀ hA.1 _ hs l i hli]
    exact h hij hjk hkl hli hik hjl
  exact ⟨tri 0 1 2 hc.1, tri 0 1 3 hc.2.1, tri 0 2 3 hc.2.2.1,
    tri 1 2 3 hc.2.2.2.1, square 0 1 2 3 hc.2.2.2.2.1,
    square 0 1 3 2 hc.2.2.2.2.2.1, square 0 2 1 3 hc.2.2.2.2.2.2⟩

theorem seedInv_nil (B₀ : Matrix 4) (hB₀ : SkewSymmetric B₀)
    (hAc : Acyclic B₀) : SeedInv B₀ [] := by
  obtain ⟨hroots, _, hA, hs⟩ := identity_rooted_signCoherent_quasiCartan_arrowSigns B₀ hB₀
  refine ⟨hroots, hA, hs, ?_, identity_integralBasis, ?_⟩
  · change CompanionAdmissible4 B₀ (coefficientCompanion B₀ identityCoefficients)
    rw [show coefficientCompanion B₀ identityCoefficients = initialCompanion B₀ from
      coefficientCompanion_initial B₀]
    exact initialCompanion_admissible B₀ hB₀ hAc
  · change B₀ = mul (mul (transpose one) B₀) one
    have ht : transpose one = one := by funext i j; simp [transpose, one, eq_comm]
    rw [ht, one_mul, mul_one]

theorem seedInv_signCoherent (B₀ : Matrix 4) (hB₀ : SkewSymmetric B₀)
    (w : List (Fin 4)) (h : SeedInv B₀ w) : SignCoherent (principalSeed B₀ w).2 :=
  realRootColumns_signCoherent B₀ _ hB₀ h.roots

theorem principalSeed_skew (B₀ : Matrix 4) (hB₀ : SkewSymmetric B₀)
    (w : List (Fin 4)) : SkewSymmetric (principalSeed B₀ w).1 := by
  rw [principalSeed, evolve_exchange]
  exact word_preserves_skew B₀ w hB₀

/-- STEP assembly. The only supplied next-state data are arrow signs and cycle
admissibility. Roots, coherence, Gram magnitudes, basis and origin are proved
from the previous state before those supplied facts are used. -/
theorem seedInv_append_of_updatedCompanionData (B₀ : Matrix 4)
    (hB₀ : SkewSymmetric B₀) (w : List (Fin 4)) (k : Fin 4) (h : SeedInv B₀ w)
    (hs : ArrowSigns (principalSeed B₀ (w ++ [k])).1
      (coefficientCompanion B₀ (principalSeed B₀ (w ++ [k])).2)
      (columnColor (principalSeed B₀ (w ++ [k])).2))
    (ha : CompanionAdmissible4 (principalSeed B₀ (w ++ [k])).1
      (coefficientCompanion B₀ (principalSeed B₀ (w ++ [k])).2)) :
    SeedInv B₀ (w ++ [k]) := by
  have hB := principalSeed_skew B₀ hB₀ w
  have hc := seedInv_signCoherent B₀ hB₀ w h
  have hg : columnColor (principalSeed B₀ w).2 k = true →
      ∀ i, 0 ≤ (principalSeed B₀ w).2 i k :=
    fun hk => ((color_iff_green hc k).mp hk).1
  have hr : columnColor (principalSeed B₀ w).2 k = false →
      ∀ i, (principalSeed B₀ w).2 i k ≤ 0 :=
    fun hk => ((color_iff_red hc k).mp hk).1
  have hn := coefficientMutation_rooted_signCoherent_quasiCartan B₀
    (principalSeed B₀ w).1 (principalSeed B₀ w).2 hB₀ hB k
    h.companion h.arrowSigns h.admissible h.roots
  have he : principalSeed B₀ (w ++ [k]) = mutateSeed (principalSeed B₀ w) k :=
    evolve_append_singleton B₀ identityCoefficients w k
  refine ⟨?_, ?_, hs, ha, ?_, ?_⟩
  · simpa only [he, mutateSeed] using hn.1
  · simpa only [he, mutateSeed] using hn.2.2
  · simpa only [he, mutateSeed] using integralBasis_mutation
      (principalSeed B₀ w).1 (principalSeed B₀ w).2 k h.basis (hc k)
  · simpa only [he, mutateSeed] using exchange_coefficientBasis_update B₀
      (principalSeed B₀ w).1 (principalSeed B₀ w).2 hB
      (columnColor (principalSeed B₀ w).2) k hg hr h.exchangeOrigin

/-- The first actual mutation preserves every seed field for every acyclic
skew input. This is an unconditional singleton result, not an all-word law. -/
theorem seedInv_singleton (B₀ : Matrix 4) (hB₀ : SkewSymmetric B₀)
    (hAc : Acyclic B₀) (k : Fin 4) : SeedInv B₀ [k] := by
  apply seedInv_append_of_updatedCompanionData B₀ hB₀ [] k (seedInv_nil B₀ hB₀ hAc)
  · simpa only [principalSeed, evolve] using
      MAExistenceTeamDArrowSigns.firstMutation_arrowSigns B₀ hB₀ k
  · simpa only [principalSeed, evolve] using
      MAExistenceTeamDAdmissibility.firstMutation_companionAdmissible B₀ hB₀ hAc k

/-- Chronological all-word induction with the still-open preservation premise
visible as an argument, never embedded in the current-state invariant. -/
theorem seedInv_all_words_of_companionClosure (B₀ : Matrix 4)
    (hB₀ : SkewSymmetric B₀) (hAc : Acyclic B₀)
    (hclosure : ∀ w, SeedInv B₀ w → ∀ k,
      ArrowSigns (principalSeed B₀ (w ++ [k])).1
        (coefficientCompanion B₀ (principalSeed B₀ (w ++ [k])).2)
        (columnColor (principalSeed B₀ (w ++ [k])).2) ∧
      CompanionAdmissible4 (principalSeed B₀ (w ++ [k])).1
        (coefficientCompanion B₀ (principalSeed B₀ (w ++ [k])).2))
    (w : List (Fin 4)) : SeedInv B₀ w := by
  induction w using List.reverseRecOn with
  | nil => exact seedInv_nil B₀ hB₀ hAc
  | append_singleton w k ih =>
      obtain ⟨hs, ha⟩ := hclosure w ih k
      exact seedInv_append_of_updatedCompanionData B₀ hB₀ w k ih hs ha

/-- Genuine roots at every finite word, conditional on the stated local
companion closure obligation. -/
theorem principalSeed_realRoots_of_companionClosure (B₀ : Matrix 4)
    (hB₀ : SkewSymmetric B₀) (hAc : Acyclic B₀)
    (hclosure : ∀ w, SeedInv B₀ w → ∀ k,
      ArrowSigns (principalSeed B₀ (w ++ [k])).1
        (coefficientCompanion B₀ (principalSeed B₀ (w ++ [k])).2)
        (columnColor (principalSeed B₀ (w ++ [k])).2) ∧
      CompanionAdmissible4 (principalSeed B₀ (w ++ [k])).1
        (coefficientCompanion B₀ (principalSeed B₀ (w ++ [k])).2))
    (w : List (Fin 4)) :
    ∀ j, RealRoot (initialCompanion B₀) (column (principalSeed B₀ w).2 j) :=
  (seedInv_all_words_of_companionClosure B₀ hB₀ hAc hclosure w).roots

theorem principalSeed_signCoherent_of_companionClosure (B₀ : Matrix 4)
    (hB₀ : SkewSymmetric B₀) (hAc : Acyclic B₀)
    (hclosure : ∀ w, SeedInv B₀ w → ∀ k,
      ArrowSigns (principalSeed B₀ (w ++ [k])).1
        (coefficientCompanion B₀ (principalSeed B₀ (w ++ [k])).2)
        (columnColor (principalSeed B₀ (w ++ [k])).2) ∧
      CompanionAdmissible4 (principalSeed B₀ (w ++ [k])).1
        (coefficientCompanion B₀ (principalSeed B₀ (w ++ [k])).2))
    (w : List (Fin 4)) : SignCoherent (principalSeed B₀ w).2 :=
  seedInv_signCoherent B₀ hB₀ w
    (seedInv_all_words_of_companionClosure B₀ hB₀ hAc hclosure w)

/-- Only actual current prefix data supplies the finite pivot-sign contract.
No signs of a future endpoint are used to justify an earlier mutation. -/
theorem coherentPivots_of_seedInv_prefixes (B₀ : Matrix 4)
    (hB₀ : SkewSymmetric B₀) (w : List (Fin 4))
    (hprefix : ∀ u k v, w = u ++ k :: v → SeedInv B₀ u) :
    CoherentPivots B₀ identityCoefficients w := by
  intro u k v huv
  have hc := seedInv_signCoherent B₀ hB₀ u (hprefix u k v huv)
  rcases hc k with hg | hr
  · exact Or.inl hg.1
  · exact Or.inr hr.1


/-- With square preservation independently proved, only actual next arrow
signs and triangle parity remain to assemble the complete next seed. -/
theorem seedInv_append_of_updatedArrowSigns_triangles (B₀ : Matrix 4)
    (hB₀ : SkewSymmetric B₀) (w : List (Fin 4)) (k : Fin 4) (h : SeedInv B₀ w)
    (hs : ArrowSigns (principalSeed B₀ (w ++ [k])).1
      (coefficientCompanion B₀ (principalSeed B₀ (w ++ [k])).2)
      (columnColor (principalSeed B₀ (w ++ [k])).2))
    (ht : ∀ i j l, triangleCompanionAdmissible (principalSeed B₀ (w ++ [k])).1
      (coefficientCompanion B₀ (principalSeed B₀ (w ++ [k])).2) i j l) :
    SeedInv B₀ (w ++ [k]) := by
  have hsq := MAExistenceTeamDAdmissibility.coefficientMutation_admissible_squares
    B₀ (principalSeed B₀ w).1 (principalSeed B₀ w).2 k
    (principalSeed_skew B₀ hB₀ w) h.companion h.arrowSigns h.admissible
    (seedInv_signCoherent B₀ hB₀ w h)
  have he : principalSeed B₀ (w ++ [k]) = mutateSeed (principalSeed B₀ w) k :=
    evolve_append_singleton B₀ identityCoefficients w k
  have hsq' :
      squareCompanionAdmissible (principalSeed B₀ (w ++ [k])).1
        (coefficientCompanion B₀ (principalSeed B₀ (w ++ [k])).2) 0 1 2 3 ∧
      squareCompanionAdmissible (principalSeed B₀ (w ++ [k])).1
        (coefficientCompanion B₀ (principalSeed B₀ (w ++ [k])).2) 0 1 3 2 ∧
      squareCompanionAdmissible (principalSeed B₀ (w ++ [k])).1
        (coefficientCompanion B₀ (principalSeed B₀ (w ++ [k])).2) 0 2 1 3 := by
    simpa only [he, mutateSeed] using hsq
  exact seedInv_append_of_updatedCompanionData B₀ hB₀ w k h hs
    ⟨ht 0 1 2, ht 0 1 3, ht 0 2 3, ht 1 2 3, hsq'.1, hsq'.2.1, hsq'.2.2⟩

end QuiverProofs.MAExistenceTeamDJointSeed
