import QuiverProofs.MAExistenceAuxiliaryOrders
import QuiverProofs.MAExistenceTeamBOrderMutation
import QuiverProofs.MAExistenceCoefficients
import QuiverProofs.MAExistenceTeamCSelectedShear
import QuiverProofs.MAExistenceTeamDJointSeed

/-! Conditional assembly of an updated actual proper-order certificate.

All source and target bilinear matrices use the original vertex labels.
The chosen elementary matrix is precisely `coefficientBasis`, and companion
and coefficient updates are the actual project recurrences.  The updated
arrow-sign and cycle-admissibility obligations remain explicit hypotheses.
No preservation or future-properness proof is stored inside a certificate.
-/
namespace QuiverProofs.MAExistenceTeamDProperCertificate
open ProperOrder ProperWiggle ProperMutation ProperObstructionSoundness
open ProperMutationIndependence MAExistenceLiterature MAExistenceCoefficients
open MAExistenceCompanions MAExistenceInitialization MAExistenceAuxiliaryOrders
open MAExistenceTeamBOrderMutation Cosquare
open MAExistenceTeamCSelectedShear
open MAExistenceTeamDJointSeed MAExistenceCoordinator

/-- Supplied selected shear plus actual current/next companion data yields
an actual next auxiliary certificate.  Every next pivot gets its own compatible
linear representative; their labels are compared exactly before taking wiggles.
-/
theorem auxiliaryCertificate_selected_update
    (B A : Matrix 4) (hB : SkewSymmetric B) (green green' : Colors)
    (p : CyclicOrder) (k : Fin 4)
    (hA : QuasiCartanCompanion B A) (hs : ArrowSigns B A green)
    (hp : AuxiliaryCertificate B green p)
    (hA' : QuasiCartanCompanion (mutate B k) (localMutation B A green k))
    (hs' : ArrowSigns (mutate B k) (localMutation B A green k) green')
    (ha' : CompanionAdmissible4 (mutate B k) (localMutation B A green k))
    (hselected : ∀ r : CyclicOrder, Compatible B green k r →
      GreenBeforeRed green r →
      ∃ q : CyclicOrder, ProperMutation B r k q ∧
        labeledUnipotent (mutate B k) q =
          mul (mul (transpose (coefficientBasis B green k))
            (labeledUnipotent B r)) (coefficientBasis B green k)) :
    ∃ q : CyclicOrder, ProperMutation B p k q ∧
      AuxiliaryCertificate (mutate B k) green' q := by
  obtain ⟨r, hpr, hr, hcr⟩ := hp k
  obtain ⟨q, hrq, hq⟩ := hselected r hr hcr
  refine ⟨q, (properMutation_input_wiggle B hB hpr).mpr hrq, ?_⟩
  have hB' := mutation_preserves_skew B k hB
  have hc' := companion_colorAdmissible (mutate B k)
    (localMutation B A green k) hB' hA'.1 green' hs' ha'
  intro l
  obtain ⟨s, hcs, hgs⟩ :=
    colorAdmissible_has_extensions (mutate B k) hB' green' hc' l
  have he := compatible_labeledUnipotent_mutation B A hB green green'
    k l r s hA hs hA' hs' hr hcs
  have hqs := labeledUnipotent_eq_wiggle (mutate B k) hB' q s (hq.trans he.symm)
  exact ⟨s, hqs, hcs, hgs⟩

/-- The preceding assembly for one actual coefficient step.  Only the current
pivot needs coherent signs.  The next companion and colors are not arbitrary
witnesses: they are the updated Gram matrix and actual column-color function.
-/
theorem actualCoefficient_selected_update
    (B₀ B C : Matrix 4) (hB : SkewSymmetric B) (p : CyclicOrder) (k : Fin 4)
    (hC : SignCoherent C)
    (hA : QuasiCartanCompanion B (coefficientCompanion B₀ C))
    (hs : ArrowSigns B (coefficientCompanion B₀ C) (columnColor C))
    (hp : AuxiliaryCertificate B (columnColor C) p)
    (hA' : QuasiCartanCompanion (mutate B k)
      (coefficientCompanion B₀ (mutateCoefficients B C k)))
    (hs' : ArrowSigns (mutate B k)
      (coefficientCompanion B₀ (mutateCoefficients B C k))
      (columnColor (mutateCoefficients B C k)))
    (ha' : CompanionAdmissible4 (mutate B k)
      (coefficientCompanion B₀ (mutateCoefficients B C k)))
    (hselected : ∀ r : CyclicOrder, Compatible B (columnColor C) k r →
      GreenBeforeRed (columnColor C) r →
      ∃ q : CyclicOrder, ProperMutation B r k q ∧
        labeledUnipotent (mutate B k) q =
          mul (mul (transpose (coefficientBasis B (columnColor C) k))
            (labeledUnipotent B r)) (coefficientBasis B (columnColor C) k)) :
    ∃ q : CyclicOrder, ProperMutation B p k q ∧
      AuxiliaryCertificate (mutate B k) (columnColor (mutateCoefficients B C k)) q := by
  have hg : columnColor C k = true → ∀ i, 0 ≤ C i k := by
    intro hk
    exact ((color_iff_green hC k).mp hk).1
  have hr : columnColor C k = false → ∀ i, C i k ≤ 0 := by
    intro hk
    exact ((color_iff_red hC k).mp hk).1
  have he := coefficientCompanion_mutation_local B₀ B C (columnColor C) k hg hr
  rw [he] at hA' hs' ha'
  exact auxiliaryCertificate_selected_update B (coefficientCompanion B₀ C)
    hB (columnColor C) (columnColor (mutateCoefficients B C k)) p k
    hA hs hp hA' hs' ha' hselected

/-- Team C's checked selected shear discharges the construction premise.
The next sign and admissibility inputs remain visible.
-/
theorem auxiliaryCertificate_update
    (B A : Matrix 4) (hB : SkewSymmetric B) (green green' : Colors)
    (p : CyclicOrder) (k : Fin 4)
    (hA : QuasiCartanCompanion B A) (hs : ArrowSigns B A green)
    (hp : AuxiliaryCertificate B green p)
    (hA' : QuasiCartanCompanion (mutate B k) (localMutation B A green k))
    (hs' : ArrowSigns (mutate B k) (localMutation B A green k) green')
    (ha' : CompanionAdmissible4 (mutate B k) (localMutation B A green k)) :
    ∃ q : CyclicOrder, ProperMutation B p k q ∧
      AuxiliaryCertificate (mutate B k) green' q :=
  auxiliaryCertificate_selected_update B A hB green green' p k hA hs hp hA' hs' ha'
    (fun r hr hc => compatible_selected_shear B hB green r k hr hc)

/-- One actual coefficient step carries the updated auxiliary certificate,
under independently supplied next actual companion data.
-/
theorem actualCoefficient_update
    (B₀ B C : Matrix 4) (hB : SkewSymmetric B) (p : CyclicOrder) (k : Fin 4)
    (hC : SignCoherent C)
    (hA : QuasiCartanCompanion B (coefficientCompanion B₀ C))
    (hs : ArrowSigns B (coefficientCompanion B₀ C) (columnColor C))
    (hp : AuxiliaryCertificate B (columnColor C) p)
    (hA' : QuasiCartanCompanion (mutate B k)
      (coefficientCompanion B₀ (mutateCoefficients B C k)))
    (hs' : ArrowSigns (mutate B k)
      (coefficientCompanion B₀ (mutateCoefficients B C k))
      (columnColor (mutateCoefficients B C k)))
    (ha' : CompanionAdmissible4 (mutate B k)
      (coefficientCompanion B₀ (mutateCoefficients B C k))) :
    ∃ q : CyclicOrder, ProperMutation B p k q ∧
      AuxiliaryCertificate (mutate B k) (columnColor (mutateCoefficients B C k)) q :=
  actualCoefficient_selected_update B₀ B C hB p k hC hA hs hp hA' hs' ha'
    (fun r hr hc => compatible_selected_shear B hB (columnColor C) r k hr hc)

/-- Chronological append uses the actual updated principal seed, retaining
the initial matrix and word.  There is no all-word companion premise here.
-/
theorem principalSeed_certificate_step
    (B₀ : Matrix 4) (hB₀ : SkewSymmetric B₀) (w : List (Fin 4))
    (p : CyclicOrder) (k : Fin 4)
    (hC : SignCoherent (principalSeed B₀ w).2)
    (hA : QuasiCartanCompanion (principalSeed B₀ w).1
      (coefficientCompanion B₀ (principalSeed B₀ w).2))
    (hs : ArrowSigns (principalSeed B₀ w).1
      (coefficientCompanion B₀ (principalSeed B₀ w).2)
      (columnColor (principalSeed B₀ w).2))
    (hp : AuxiliaryCertificate (principalSeed B₀ w).1
      (columnColor (principalSeed B₀ w).2) p)
    (hA' : QuasiCartanCompanion (principalSeed B₀ (w ++ [k])).1
      (coefficientCompanion B₀ (principalSeed B₀ (w ++ [k])).2))
    (hs' : ArrowSigns (principalSeed B₀ (w ++ [k])).1
      (coefficientCompanion B₀ (principalSeed B₀ (w ++ [k])).2)
      (columnColor (principalSeed B₀ (w ++ [k])).2))
    (ha' : CompanionAdmissible4 (principalSeed B₀ (w ++ [k])).1
      (coefficientCompanion B₀ (principalSeed B₀ (w ++ [k])).2)) :
    ∃ q : CyclicOrder, ProperMutation (principalSeed B₀ w).1 p k q ∧
      AuxiliaryCertificate (principalSeed B₀ (w ++ [k])).1
        (columnColor (principalSeed B₀ (w ++ [k])).2) q := by
  have hB : SkewSymmetric (principalSeed B₀ w).1 := by
    rw [principalSeed, evolve_exchange]
    exact word_preserves_skew B₀ w hB₀
  have he : principalSeed B₀ (w ++ [k]) = mutateSeed (principalSeed B₀ w) k :=
    evolve_append_singleton B₀ identityCoefficients w k
  rw [he] at hA' hs' ha' ⊢
  exact actualCoefficient_update B₀ (principalSeed B₀ w).1
    (principalSeed B₀ w).2 hB p k hC hA hs hp hA' hs' ha'

/-- Every allowed target representative inherits the actual updated
certificate from the constructed target.  Arbitrary representative and cut
choices are handled by the project's independent target-uniqueness theorem.
-/
theorem principalSeed_certificate_all_outputs
    (B₀ : Matrix 4) (hB₀ : SkewSymmetric B₀) (w : List (Fin 4))
    (p q : CyclicOrder) (k : Fin 4)
    (hC : SignCoherent (principalSeed B₀ w).2)
    (hA : QuasiCartanCompanion (principalSeed B₀ w).1
      (coefficientCompanion B₀ (principalSeed B₀ w).2))
    (hs : ArrowSigns (principalSeed B₀ w).1
      (coefficientCompanion B₀ (principalSeed B₀ w).2)
      (columnColor (principalSeed B₀ w).2))
    (hp : AuxiliaryCertificate (principalSeed B₀ w).1
      (columnColor (principalSeed B₀ w).2) p)
    (hA' : QuasiCartanCompanion (principalSeed B₀ (w ++ [k])).1
      (coefficientCompanion B₀ (principalSeed B₀ (w ++ [k])).2))
    (hs' : ArrowSigns (principalSeed B₀ (w ++ [k])).1
      (coefficientCompanion B₀ (principalSeed B₀ (w ++ [k])).2)
      (columnColor (principalSeed B₀ (w ++ [k])).2))
    (ha' : CompanionAdmissible4 (principalSeed B₀ (w ++ [k])).1
      (coefficientCompanion B₀ (principalSeed B₀ (w ++ [k])).2))
    (hm : ProperMutation (principalSeed B₀ w).1 p k q) :
    AuxiliaryCertificate (principalSeed B₀ (w ++ [k])).1
      (columnColor (principalSeed B₀ (w ++ [k])).2) q := by
  obtain ⟨r, hmr, hr⟩ := principalSeed_certificate_step B₀ hB₀ w p k
    hC hA hs hp hA' hs' ha'
  have hB : SkewSymmetric (principalSeed B₀ w).1 := by
    rw [principalSeed, evolve_exchange]
    exact word_preserves_skew B₀ w hB₀
  have hw := ProperMutationRepresentativeChoice.properMutation_target_unique
    (principalSeed B₀ w).1 hB hmr hm
  have he : (principalSeed B₀ (w ++ [k])).1 = mutate (principalSeed B₀ w).1 k := by
    rw [principalSeed, evolve_append_singleton]
    rfl
  rw [←he] at hw
  apply auxiliaryCertificate_wiggle (B := (principalSeed B₀ (w ++ [k])).1) _ hw hr
  rw [he]
  exact mutation_preserves_skew (principalSeed B₀ w).1 k hB

/-- A full present-state certificate with actual acyclic origin and actual
chronological coefficient/root/companion data.  The order certificate uses
the actual current column colors.  This contains no future-state assertion.
-/
def actualSeedCertificate (B : Matrix 4) (p : CyclicOrder) : Prop :=
  ∃ (B₀ : Matrix 4) (w : List (Fin 4)),
    SkewSymmetric B₀ ∧ Acyclic B₀ ∧ B = (principalSeed B₀ w).1 ∧
      SeedInv B₀ w ∧ AuxiliaryCertificate B (columnColor (principalSeed B₀ w).2) p

/-- Unrestricted acyclic initialization of every present-state field. -/
theorem actualSeedCertificate_init (B : Matrix 4) (hB : SkewSymmetric B)
    (hAc : Acyclic B) : ∃ p : CyclicOrder, actualSeedCertificate B p := by
  obtain ⟨p, _, hp⟩ := acyclic_auxiliaryCertificate B hB hAc
  refine ⟨p, B, [], hB, hAc, rfl, seedInv_nil B hB hAc, ?_⟩
  have hg : columnColor (identityCoefficients : Matrix 4) = (fun _ => true) := by
    funext j
    exact color_green (identity_green j)
  change AuxiliaryCertificate B (columnColor (identityCoefficients : Matrix 4)) p
  rw [hg]
  exact hp

/-- Wiggles change only the supplied order representative.  All actual seed,
coefficient, origin and companion witnesses are retained verbatim.
-/
theorem actualSeedCertificate_wiggle (B : Matrix 4) (hB : SkewSymmetric B)
    (p q : CyclicOrder) (hw : WiggleEquivalent B p q)
    (hp : actualSeedCertificate B p) : actualSeedCertificate B q := by
  obtain ⟨B₀, w, hB₀, hAc, he, hInv, haux⟩ := hp
  exact ⟨B₀, w, hB₀, hAc, he, hInv, auxiliaryCertificate_wiggle hB hw haux⟩

/-- The complete actual certificate implies membership in a proper class. -/
theorem actualSeedCertificate_proper (B : Matrix 4) (_hB : SkewSymmetric B)
    (p : CyclicOrder) (hp : actualSeedCertificate B p) : ProperClass B p := by
  obtain ⟨_, _, _, _, _, _, haux⟩ := hp
  exact auxiliaryCertificate_proper haux

/-- One actual certified output per vertex, conditional only on the displayed
local arrow-sign/admissibility preservation input.  That input is a theorem
argument and is not a field of `actualSeedCertificate` or `SeedInv`.
-/
theorem actualSeedCertificate_step_of_companionClosure
    (hclosure : ∀ (B₀ : Matrix 4), SkewSymmetric B₀ → Acyclic B₀ →
      ∀ w, SeedInv B₀ w → ∀ k,
        ArrowSigns (principalSeed B₀ (w ++ [k])).1
          (coefficientCompanion B₀ (principalSeed B₀ (w ++ [k])).2)
          (columnColor (principalSeed B₀ (w ++ [k])).2) ∧
        CompanionAdmissible4 (principalSeed B₀ (w ++ [k])).1
          (coefficientCompanion B₀ (principalSeed B₀ (w ++ [k])).2))
    (B : Matrix 4) (_hB : SkewSymmetric B) (p : CyclicOrder)
    (hp : actualSeedCertificate B p) (k : Fin 4) :
    ∃ q : CyclicOrder, ProperMutation B p k q ∧ actualSeedCertificate (mutate B k) q := by
  obtain ⟨B₀, w, hB₀, hAc, he, hInv, haux⟩ := hp
  subst B
  obtain ⟨hs', ha'⟩ := hclosure B₀ hB₀ hAc w hInv k
  have hInv' := seedInv_append_of_updatedCompanionData B₀ hB₀ w k hInv hs' ha'
  obtain ⟨q, hmq, haux'⟩ := principalSeed_certificate_step B₀ hB₀ w p k
    (seedInv_signCoherent B₀ hB₀ w hInv) hInv.companion hInv.arrowSigns haux
    hInv'.companion hInv'.arrowSigns hInv'.admissible
  have he' : mutate (principalSeed B₀ w).1 k = (principalSeed B₀ (w ++ [k])).1 := by
    exact (congrArg Prod.fst (evolve_append_singleton B₀ identityCoefficients w k)).symm
  refine ⟨q, hmq, B₀, w ++ [k], hB₀, hAc, he', hInv', ?_⟩
  rw [he']
  exact haux'

/-- Representative independence covers every allowed proper-mutation output
with the full updated actual seed certificate, including all cut choices.
-/
theorem actualSeedCertificate_all_outputs_of_companionClosure
    (hclosure : ∀ (B₀ : Matrix 4), SkewSymmetric B₀ → Acyclic B₀ →
      ∀ w, SeedInv B₀ w → ∀ k,
        ArrowSigns (principalSeed B₀ (w ++ [k])).1
          (coefficientCompanion B₀ (principalSeed B₀ (w ++ [k])).2)
          (columnColor (principalSeed B₀ (w ++ [k])).2) ∧
        CompanionAdmissible4 (principalSeed B₀ (w ++ [k])).1
          (coefficientCompanion B₀ (principalSeed B₀ (w ++ [k])).2))
    {B : Matrix 4} (hB : SkewSymmetric B) {p q : CyclicOrder} {k : Fin 4}
    (hp : actualSeedCertificate B p) (hm : ProperMutation B p k q) :
    actualSeedCertificate (mutate B k) q :=
  invariant_preserved_all_choices actualSeedCertificate actualSeedCertificate_wiggle
    (actualSeedCertificate_step_of_companionClosure hclosure) hB hp hm

/-- Arbitrary finite transport preserves every actual certificate field once
the explicit local companion-preservation obligation is proved.
-/
theorem actualSeedCertificate_transport_of_companionClosure
    (hclosure : ∀ (B₀ : Matrix 4), SkewSymmetric B₀ → Acyclic B₀ →
      ∀ w, SeedInv B₀ w → ∀ k,
        ArrowSigns (principalSeed B₀ (w ++ [k])).1
          (coefficientCompanion B₀ (principalSeed B₀ (w ++ [k])).2)
          (columnColor (principalSeed B₀ (w ++ [k])).2) ∧
        CompanionAdmissible4 (principalSeed B₀ (w ++ [k])).1
          (coefficientCompanion B₀ (principalSeed B₀ (w ++ [k])).2))
    {B C : Matrix 4} (hB : SkewSymmetric B) {p q : CyclicOrder}
    (hp : actualSeedCertificate B p) (ht : Transport B p C q) :
    actualSeedCertificate C q :=
  invariant_transport actualSeedCertificate actualSeedCertificate_wiggle
    (actualSeedCertificate_step_of_companionClosure hclosure) hB hp ht

/-- Exact requested MA conclusion reduced to the two still-explicit local
companion obligations.  This theorem does not discharge `hclosure`.
-/
theorem maHasTotalProper4_of_companionClosure
    (hclosure : ∀ (B₀ : Matrix 4), SkewSymmetric B₀ → Acyclic B₀ →
      ∀ w, SeedInv B₀ w → ∀ k,
        ArrowSigns (principalSeed B₀ (w ++ [k])).1
          (coefficientCompanion B₀ (principalSeed B₀ (w ++ [k])).2)
          (columnColor (principalSeed B₀ (w ++ [k])).2) ∧
        CompanionAdmissible4 (principalSeed B₀ (w ++ [k])).1
          (coefficientCompanion B₀ (principalSeed B₀ (w ++ [k])).2)) :
    MAHasTotalProper4 := by
  apply existence_of_acyclic_total
  intro B hB hAc
  obtain ⟨p, hp⟩ := actualSeedCertificate_init B hB hAc
  exact ⟨p, totalProper_of_invariant actualSeedCertificate actualSeedCertificate_wiggle
    (actualSeedCertificate_step_of_companionClosure hclosure)
    actualSeedCertificate_proper hB hp⟩

/-- Every first proper mutation from an actual acyclic all-green certificate
carries the full actual singleton seed certificate.  This is a genuine local
result with no all-word companion-preservation premise.
-/
theorem actualSeedCertificate_firstStep (B : Matrix 4) (hB : SkewSymmetric B)
    (hAc : Acyclic B) (p : CyclicOrder)
    (hp : AuxiliaryCertificate B (fun _ => true) p) (k : Fin 4) :
    ∃ q : CyclicOrder, ProperMutation B p k q ∧ actualSeedCertificate (mutate B k) q := by
  have hInv := seedInv_nil B hB hAc
  have hInv' := seedInv_singleton B hB hAc k
  have hcolor : columnColor (identityCoefficients : Matrix 4) = (fun _ => true) := by
    funext j
    exact color_green (identity_green j)
  have haux : AuxiliaryCertificate (principalSeed B []).1
      (columnColor (principalSeed B []).2) p := by
    change AuxiliaryCertificate B (columnColor (identityCoefficients : Matrix 4)) p
    rw [hcolor]
    exact hp
  obtain ⟨q, hmq, haux'⟩ := principalSeed_certificate_step B hB [] p k
    (seedInv_signCoherent B hB [] hInv) hInv.companion hInv.arrowSigns haux
    hInv'.companion hInv'.arrowSigns hInv'.admissible
  exact ⟨q, hmq, B, [k], hB, hAc, rfl, hInv', haux'⟩

/-- Every permitted first-step output and cut carries the same full actual
updated certificate, using representative independence directly.
-/
theorem actualSeedCertificate_firstStep_all_outputs
    (B : Matrix 4) (hB : SkewSymmetric B) (hAc : Acyclic B)
    (p q : CyclicOrder) (hp : AuxiliaryCertificate B (fun _ => true) p)
    (k : Fin 4) (hm : ProperMutation B p k q) :
    actualSeedCertificate (mutate B k) q := by
  obtain ⟨r, hmr, hr⟩ := actualSeedCertificate_firstStep B hB hAc p hp k
  have hw := ProperMutationRepresentativeChoice.properMutation_target_unique B hB hmr hm
  exact actualSeedCertificate_wiggle (mutate B k) (mutation_preserves_skew B k hB)
    r q hw hr

end QuiverProofs.MAExistenceTeamDProperCertificate

namespace QuiverProofs.MAExistenceTeamDProperCertificate
open ProperOrder ProperWiggle ProperMutation ProperObstructionSoundness
open MAExistenceLiterature MAExistenceCoefficients MAExistenceCompanions
open MAExistenceAuxiliaryOrders MAExistenceTeamDJointSeed

/-- The reviewed square-preservation package removes square parity from the
remaining general closure premise. Actual next arrow signs and next triangles
are still supplied explicitly; no general preservation assertion is proved here.
-/
theorem maHasTotalProper4_of_arrowSigns_triangleClosure
    (hclosure : ∀ (B₀ : Matrix 4), SkewSymmetric B₀ → Acyclic B₀ →
      ∀ w, SeedInv B₀ w → ∀ k,
        ArrowSigns (principalSeed B₀ (w ++ [k])).1
          (coefficientCompanion B₀ (principalSeed B₀ (w ++ [k])).2)
          (columnColor (principalSeed B₀ (w ++ [k])).2) ∧
        (∀ i j l, triangleCompanionAdmissible (principalSeed B₀ (w ++ [k])).1
          (coefficientCompanion B₀ (principalSeed B₀ (w ++ [k])).2) i j l)) :
    MAHasTotalProper4 := by
  apply maHasTotalProper4_of_companionClosure
  intro B₀ hB₀ hAc w hInv k
  obtain ⟨hs, ht⟩ := hclosure B₀ hB₀ hAc w hInv k
  have hsq := MAExistenceTeamDAdmissibility.coefficientMutation_admissible_squares B₀
    (principalSeed B₀ w).1 (principalSeed B₀ w).2 k (principalSeed_skew B₀ hB₀ w)
    hInv.companion hInv.arrowSigns hInv.admissible (seedInv_signCoherent B₀ hB₀ w hInv)
  have he : principalSeed B₀ (w ++ [k]) = mutateSeed (principalSeed B₀ w) k :=
    evolve_append_singleton B₀ identityCoefficients w k
  have ha : CompanionAdmissible4 (principalSeed B₀ (w ++ [k])).1
      (coefficientCompanion B₀ (principalSeed B₀ (w ++ [k])).2) := by
    refine ⟨ht 0 1 2, ht 0 1 3, ht 0 2 3, ht 1 2 3, ?_⟩
    simpa only [he, mutateSeed] using hsq
  exact ⟨hs, ha⟩

end QuiverProofs.MAExistenceTeamDProperCertificate
