import QuiverProofs.MAExistenceTeamDJointSeed

/-! Present-state sign-reversal bridges for the actual mutation project.

The exchange matrix and coefficient matrix are simultaneously negated, while
the Gram companion is unchanged.  Chronological negation starts from `-I`.
Both signs of the initial coefficient matrix are kept explicit below; no
future arrow-sign or triangle assertion is part of the state predicate.
-/
namespace QuiverProofs.MAExistenceTeamDMutationSymmetry
open MAExistenceLiterature MAExistenceCoefficients MAExistenceCompanions
open MAExistenceAuxiliaryOrders MAExistenceTeamBRootPositivity
open MAExistenceTeamCRootSigns MAExistenceTeamDJointSeed
open Cosquare
set_option maxHeartbeats 0

/- The following five reversal APIs and `negMatrix` are adopted verbatim from
the coordinator-owned, independently reviewed DependencyAudit checkpoint
SHA256 2fd6783b8b7b7e6d2e0203181e3915f073151019a73437807ae666c3a3f93aee.
Team D coordinator authorized this exclusive publication handoff. -/
def negMatrix {n : Nat} (M : Matrix n) : Matrix n := fun i j => -M i j

theorem mutate_negMatrix {n : Nat} (B : Matrix n) (k : Fin n) :
    mutate (negMatrix B) k = negMatrix (mutate B k) := by
  funext i j
  by_cases h : i = k ∨ j = k
  · simp [mutate, negMatrix, h]
  · simp only [mutate, negMatrix, h, if_false, correction_neg]
    omega

theorem mutateCoefficients_negMatrix {n : Nat} (B C : Matrix n) (k : Fin n) :
    mutateCoefficients (negMatrix B) (negMatrix C) k =
      negMatrix (mutateCoefficients B C k) := by
  funext i j
  by_cases h : j = k
  · simp [mutateCoefficients, negMatrix, h]
  · simp only [mutateCoefficients, negMatrix, h, if_false, correction_neg]
    omega

/-- Simultaneous reversal changes both the exchange and coefficient start. -/
theorem evolve_negMatrix {n : Nat} (B C : Matrix n) (w : List (Fin n)) :
    evolve (negMatrix B) (negMatrix C) w =
      (negMatrix (evolve B C w).1, negMatrix (evolve B C w).2) := by
  induction w generalizing B C with
  | nil => rfl
  | cons k w ih =>
      simp only [evolve, mutate_negMatrix, mutateCoefficients_negMatrix]
      exact ih (mutate B k) (mutateCoefficients B C k)

/-- Reversing an actual principal seed produces a seed initialized at -I.
This is deliberately not `principalSeed (negMatrix B₀) w`. -/
theorem signed_initial_evolve_principalSeed {n : Nat} (B₀ : Matrix n)
    (w : List (Fin n)) :
    evolve (negMatrix B₀) (negMatrix identityCoefficients) w =
      (negMatrix (principalSeed B₀ w).1, negMatrix (principalSeed B₀ w).2) :=
  evolve_negMatrix B₀ identityCoefficients w

theorem columnColor_negMatrix {n : Nat} (C : Matrix n) (hC : SignCoherent C)
    (j : Fin n) : columnColor (negMatrix C) j = !(columnColor C j) := by
  rcases hC j with hg | hr
  · have hn : ColumnRed (negMatrix C) j := by
      refine ⟨fun i => ?_, ?_⟩
      · change -C i j ≤ 0
        have := hg.1 i
        omega
      · obtain ⟨i, hi⟩ := hg.2
        exact ⟨i, by change -C i j < 0; omega⟩
    rw [color_red hn, color_green hg]
    rfl
  · have hn : ColumnGreen (negMatrix C) j := by
      refine ⟨fun i => ?_, ?_⟩
      · change 0 ≤ -C i j
        have := hr.1 i
        omega
      · obtain ⟨i, hi⟩ := hr.2
        exact ⟨i, by change 0 < -C i j; omega⟩
    rw [color_green hn, color_red hr]
    rfl


theorem negMatrix_involutive {n : Nat} (M : Matrix n) : negMatrix (negMatrix M) = M := by
  funext i j
  simp [negMatrix]

theorem negMatrix_skew {n : Nat} (B : Matrix n) (hB : SkewSymmetric B) :
    SkewSymmetric (negMatrix B) := by
  intro i j
  have := hB i j
  simp only [negMatrix]
  omega

theorem negMatrix_acyclic {n : Nat} (B : Matrix n) (hB : SkewSymmetric B)
    (hAc : Acyclic B) : Acyclic (negMatrix B) :=
  (acyclic_reverse_iff B hB).mpr hAc

theorem initialCompanion_negMatrix {n : Nat} (B : Matrix n) :
    initialCompanion (negMatrix B) = initialCompanion B := by
  funext i j
  simp [initialCompanion, negMatrix]

theorem signCoherent_negMatrix {n : Nat} (C : Matrix n) (hC : SignCoherent C) :
    SignCoherent (negMatrix C) := by
  intro j
  rcases hC j with hg | hr
  · right
    refine ⟨?_, ?_⟩
    · intro i
      change -C i j ≤ 0
      have := hg.1 i
      omega
    · obtain ⟨i, hi⟩ := hg.2
      exact ⟨i, by change -C i j < 0; omega⟩
  · left
    refine ⟨?_, ?_⟩
    · intro i
      change 0 ≤ -C i j
      have := hr.1 i
      omega
    · obtain ⟨i, hi⟩ := hr.2
      exact ⟨i, by change 0 < -C i j; omega⟩

theorem coefficientCompanion_negMatrix (B₀ C : Matrix 4) :
    coefficientCompanion (negMatrix B₀) (negMatrix C) = coefficientCompanion B₀ C := by
  rw [coefficientCompanion, initialCompanion_negMatrix]
  funext i j
  simp only [coefficientCompanion, mul, transpose, negMatrix]
  grind

theorem quasiCartan_negMatrix {n : Nat} (B A : Matrix n)
    (hA : QuasiCartanCompanion B A) : QuasiCartanCompanion (negMatrix B) A := by
  refine ⟨hA.1, hA.2.1, ?_⟩
  intro i j hij
  simpa only [negMatrix, Int.natAbs_neg] using hA.2.2 i j hij

/-- Arrow reversal and color complementation preserve the exact arrow law. -/
theorem arrowSigns_negMatrix {n : Nat} (B A : Matrix n) (green : Fin n → Bool)
    (hB : SkewSymmetric B) (hA : ∀ i j, A i j = A j i)
    (hs : ArrowSigns B A green) :
    ArrowSigns (negMatrix B) A (fun i => !(green i)) := by
  intro i j hij
  have hji : 0 < B j i := by
    change 0 < -B i j at hij
    have := hB i j
    omega
  have hh := hs j i hji
  rw [hA j i] at hh
  cases hi : green i <;> cases hj : green j <;> simpa [hi, hj] using hh

theorem actualArrowSigns_negMatrix (B₀ B C : Matrix 4)
    (hB₀ : SkewSymmetric B₀) (hB : SkewSymmetric B) (hC : SignCoherent C)
    (hs : ArrowSigns B (coefficientCompanion B₀ C) (columnColor C)) :
    ArrowSigns (negMatrix B) (coefficientCompanion (negMatrix B₀) (negMatrix C))
      (columnColor (negMatrix C)) := by
  rw [coefficientCompanion_negMatrix]
  have he : columnColor (negMatrix C) = (fun i => !(columnColor C i)) :=
    funext (columnColor_negMatrix C hC)
  rw [he]
  exact arrowSigns_negMatrix B _ _ hB (coefficientCompanion_symmetric B₀ C hB₀) hs

theorem triangleCompanionAdmissible_negMatrix (B A : Matrix 4) (i j l : Fin 4)
    (h : triangleCompanionAdmissible B A i j l) :
    triangleCompanionAdmissible (negMatrix B) A i j l := by
  simpa [triangleCompanionAdmissible, negMatrix, or_comm] using h

theorem squareCompanionAdmissible_negMatrix (B A : Matrix 4) (i j l m : Fin 4)
    (h : squareCompanionAdmissible B A i j l m) :
    squareCompanionAdmissible (negMatrix B) A i j l m := by
  simpa [squareCompanionAdmissible, negMatrix, or_comm] using h

theorem companionAdmissible4_negMatrix (B A : Matrix 4)
    (ha : CompanionAdmissible4 B A) : CompanionAdmissible4 (negMatrix B) A := by
  exact ⟨triangleCompanionAdmissible_negMatrix B A 0 1 2 ha.1,
    triangleCompanionAdmissible_negMatrix B A 0 1 3 ha.2.1,
    triangleCompanionAdmissible_negMatrix B A 0 2 3 ha.2.2.1,
    triangleCompanionAdmissible_negMatrix B A 1 2 3 ha.2.2.2.1,
    squareCompanionAdmissible_negMatrix B A 0 1 2 3 ha.2.2.2.2.1,
    squareCompanionAdmissible_negMatrix B A 0 1 3 2 ha.2.2.2.2.2.1,
    squareCompanionAdmissible_negMatrix B A 0 2 1 3 ha.2.2.2.2.2.2⟩

theorem integralBasis_negMatrix (C : Matrix 4) (hC : IntegralBasis C) :
    IntegralBasis (negMatrix C) := by
  obtain ⟨D, hDC, hCD⟩ := hC
  refine ⟨negMatrix D, ?_, ?_⟩
  · have he : mul (negMatrix D) (negMatrix C) = mul D C := by
      funext i j
      simp [mul, negMatrix]
    rwa [he]
  · have he : mul (negMatrix C) (negMatrix D) = mul C D := by
      funext i j
      simp [mul, negMatrix]
    rwa [he]

theorem exchangeOrigin_negMatrix (B₀ B C : Matrix 4)
    (he : B = mul (mul (transpose C) B₀) C) :
    negMatrix B = mul (mul (transpose (negMatrix C)) (negMatrix B₀)) (negMatrix C) := by
  rw [he]
  funext i j
  simp only [mul, transpose, negMatrix]
  grind

theorem realRootColumns_negMatrix (B₀ C : Matrix 4) (hB₀ : SkewSymmetric B₀)
    (hroots : ∀ j, RealRoot (initialCompanion B₀) (column C j)) :
    ∀ j, RealRoot (initialCompanion (negMatrix B₀)) (column (negMatrix C) j) := by
  rw [initialCompanion_negMatrix]
  have hA := initialCompanion_quasiCartan B₀ hB₀
  intro j
  exact realRoot_neg _ hA.1 hA.2.1 (hroots j)

theorem pivotWeight_negMatrix (B : Matrix 4) (green : Fin 4 → Bool) (k j : Fin 4) :
    pivotWeight (negMatrix B) (fun i => !(green i)) k j = pivotWeight B green k j := by
  cases hk : green k <;> simp [pivotWeight, negMatrix, hk]

theorem localMutation_negMatrix (B A : Matrix 4) (green : Fin 4 → Bool) (k : Fin 4) :
    localMutation (negMatrix B) A (fun i => !(green i)) k = localMutation B A green k := by
  funext i j
  simp only [localMutation, pivotWeight_negMatrix]

theorem coefficientBasis_negMatrix (B : Matrix 4) (green : Fin 4 → Bool) (k : Fin 4) :
    coefficientBasis (negMatrix B) (fun i => !(green i)) k = coefficientBasis B green k := by
  funext i j
  simp only [coefficientBasis, pivotWeight_negMatrix]

/-- `true` denotes the actual principal initialization `+I`; `false` denotes
the explicit signed initialization `-I` needed after simultaneous reversal. -/
def signedInitialCoefficients (positive : Bool) : Matrix 4 :=
  if positive then identityCoefficients else negMatrix identityCoefficients

def signedPrincipalSeed (B₀ : Matrix 4) (positive : Bool) (w : List (Fin 4)) : Seed 4 :=
  evolve B₀ (signedInitialCoefficients positive) w

theorem signedPrincipalSeed_positive (B₀ : Matrix 4) (w : List (Fin 4)) :
    signedPrincipalSeed B₀ true w = principalSeed B₀ w := rfl

theorem signedPrincipalSeed_negMatrix (B₀ : Matrix 4) (positive : Bool) (w : List (Fin 4)) :
    signedPrincipalSeed (negMatrix B₀) (!positive) w =
      (negMatrix (signedPrincipalSeed B₀ positive w).1,
        negMatrix (signedPrincipalSeed B₀ positive w).2) := by
  cases positive
  · have h := evolve_negMatrix B₀ (negMatrix identityCoefficients) w
    rw [negMatrix_involutive] at h
    exact h
  · exact signed_initial_evolve_principalSeed B₀ w

theorem signedPrincipalSeed_negative_origin (B₀ : Matrix 4) (w : List (Fin 4)) :
    signedPrincipalSeed B₀ false w =
      (negMatrix (principalSeed (negMatrix B₀) w).1,
        negMatrix (principalSeed (negMatrix B₀) w).2) := by
  have h := signed_initial_evolve_principalSeed (negMatrix B₀) w
  rw [negMatrix_involutive] at h
  exact h

/-- The six current actual-origin facts, with the sign of chronological
initialization explicit.  No mutation-preservation or future fact is a field. -/
structure SignedSeedInv (B₀ : Matrix 4) (positive : Bool) (w : List (Fin 4)) : Prop where
  roots : ∀ j, RealRoot (initialCompanion B₀) (column (signedPrincipalSeed B₀ positive w).2 j)
  companion : QuasiCartanCompanion (signedPrincipalSeed B₀ positive w).1
    (coefficientCompanion B₀ (signedPrincipalSeed B₀ positive w).2)
  arrowSigns : ArrowSigns (signedPrincipalSeed B₀ positive w).1
    (coefficientCompanion B₀ (signedPrincipalSeed B₀ positive w).2)
    (columnColor (signedPrincipalSeed B₀ positive w).2)
  admissible : CompanionAdmissible4 (signedPrincipalSeed B₀ positive w).1
    (coefficientCompanion B₀ (signedPrincipalSeed B₀ positive w).2)
  basis : IntegralBasis (signedPrincipalSeed B₀ positive w).2
  exchangeOrigin : (signedPrincipalSeed B₀ positive w).1 =
    mul (mul (transpose (signedPrincipalSeed B₀ positive w).2) B₀)
      (signedPrincipalSeed B₀ positive w).2

theorem signedSeedInv_positive_iff (B₀ : Matrix 4) (w : List (Fin 4)) :
    SignedSeedInv B₀ true w ↔ SeedInv B₀ w := by
  constructor
  · intro h
    exact ⟨h.roots, h.companion, h.arrowSigns, h.admissible, h.basis, h.exchangeOrigin⟩
  · intro h
    exact ⟨h.roots, h.companion, h.arrowSigns, h.admissible, h.basis, h.exchangeOrigin⟩

theorem signedPrincipalSeed_skew (B₀ : Matrix 4) (hB₀ : SkewSymmetric B₀)
    (positive : Bool) (w : List (Fin 4)) : SkewSymmetric (signedPrincipalSeed B₀ positive w).1 := by
  rw [signedPrincipalSeed, evolve_exchange]
  exact word_preserves_skew B₀ w hB₀

theorem signedSeedInv_signCoherent (B₀ : Matrix 4) (hB₀ : SkewSymmetric B₀)
    (positive : Bool) (w : List (Fin 4)) (h : SignedSeedInv B₀ positive w) :
    SignCoherent (signedPrincipalSeed B₀ positive w).2 :=
  realRootColumns_signCoherent B₀ _ hB₀ h.roots

/-- Current chronological state facts transfer across simultaneous reversal,
and the signed initialization flips from `+I` to `-I` or conversely. -/
theorem signedSeedInv_negMatrix (B₀ : Matrix 4) (hB₀ : SkewSymmetric B₀)
    (positive : Bool) (w : List (Fin 4)) (h : SignedSeedInv B₀ positive w) :
    SignedSeedInv (negMatrix B₀) (!positive) w := by
  have he := signedPrincipalSeed_negMatrix B₀ positive w
  have hB := signedPrincipalSeed_skew B₀ hB₀ positive w
  have hC := signedSeedInv_signCoherent B₀ hB₀ positive w h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [he] using realRootColumns_negMatrix B₀ _ hB₀ h.roots
  · simpa only [he, coefficientCompanion_negMatrix] using
      quasiCartan_negMatrix _ _ h.companion
  · simpa only [he] using actualArrowSigns_negMatrix B₀ _ _ hB₀ hB hC h.arrowSigns
  · simpa only [he, coefficientCompanion_negMatrix] using
      companionAdmissible4_negMatrix _ _ h.admissible
  · simpa only [he] using integralBasis_negMatrix _ h.basis
  · simpa only [he] using exchangeOrigin_negMatrix B₀ _ _ h.exchangeOrigin

/-- Both signed coefficient starts initialize all six present-state facts for
every acyclic skew input, including singular and disconnected matrices. -/
theorem signedSeedInv_nil (B₀ : Matrix 4) (hB₀ : SkewSymmetric B₀)
    (hAc : Acyclic B₀) (positive : Bool) : SignedSeedInv B₀ positive [] := by
  cases positive
  · have h0 := (signedSeedInv_positive_iff (negMatrix B₀) []).mpr
      (seedInv_nil (negMatrix B₀) (negMatrix_skew B₀ hB₀) (negMatrix_acyclic B₀ hB₀ hAc))
    have hn := signedSeedInv_negMatrix (negMatrix B₀) (negMatrix_skew B₀ hB₀) true [] h0
    simpa only [negMatrix_involutive, Bool.not_true] using hn
  · exact (signedSeedInv_positive_iff B₀ []).mpr (seedInv_nil B₀ hB₀ hAc)

/-- The existing actual principal invariant supplies its correctly signed
reversed-origin version, with no all-word closure premise. -/
theorem seedInv_signedReversal (B₀ : Matrix 4) (hB₀ : SkewSymmetric B₀)
    (w : List (Fin 4)) (h : SeedInv B₀ w) : SignedSeedInv (negMatrix B₀) false w :=
  signedSeedInv_negMatrix B₀ hB₀ true w ((signedSeedInv_positive_iff B₀ w).mpr h)

/-- A negative-start current invariant is exactly the negation of the actual
positive-start current invariant over the reversed initial exchange matrix. -/
theorem signedSeedInv_negative_iff_reversed (B₀ : Matrix 4) (hB₀ : SkewSymmetric B₀)
    (w : List (Fin 4)) : SignedSeedInv B₀ false w ↔ SeedInv (negMatrix B₀) w := by
  constructor
  · intro h
    exact (signedSeedInv_positive_iff (negMatrix B₀) w).mp
      (signedSeedInv_negMatrix B₀ hB₀ false w h)
  · intro h
    have hn := seedInv_signedReversal (negMatrix B₀) (negMatrix_skew B₀ hB₀) w h
    simpa only [negMatrix_involutive] using hn

/-- Ordinary principal initialization of the reversed matrix is `+I`, whereas
the reversed actual seed starts at `-I`. They already differ at the empty word. -/
theorem principalSeed_reversed_initial_coefficients_ne_signed (B₀ : Matrix 4) :
    (principalSeed (negMatrix B₀) []).2 ≠ (signedPrincipalSeed (negMatrix B₀) false []).2 := by
  intro he
  have hh := congrFun (congrFun he 0) 0
  change (1 : Int) = -1 at hh
  omega

theorem actualArrowSigns_negMatrix_iff (B₀ B C : Matrix 4)
    (hB₀ : SkewSymmetric B₀) (hB : SkewSymmetric B) (hC : SignCoherent C) :
    ArrowSigns (negMatrix B) (coefficientCompanion (negMatrix B₀) (negMatrix C))
      (columnColor (negMatrix C)) ↔
    ArrowSigns B (coefficientCompanion B₀ C) (columnColor C) := by
  constructor
  · intro hs
    have hn := actualArrowSigns_negMatrix (negMatrix B₀) (negMatrix B) (negMatrix C)
      (negMatrix_skew B₀ hB₀) (negMatrix_skew B hB) (signCoherent_negMatrix C hC) hs
    simpa only [negMatrix_involutive] using hn
  · exact actualArrowSigns_negMatrix B₀ B C hB₀ hB hC

/-- A completed one-step arrow law can be reflected back exactly. The only
next-column premise is sign coherence, independently available from current
genuine roots and current companion/arrow data before triangle preservation. -/
theorem mutation_actualArrowSigns_negMatrix_iff (B₀ B C : Matrix 4) (k : Fin 4)
    (hB₀ : SkewSymmetric B₀) (hB : SkewSymmetric B)
    (hC' : SignCoherent (mutateCoefficients B C k)) :
    ArrowSigns (mutate (negMatrix B) k)
      (coefficientCompanion (negMatrix B₀) (mutateCoefficients (negMatrix B) (negMatrix C) k))
      (columnColor (mutateCoefficients (negMatrix B) (negMatrix C) k)) ↔
    ArrowSigns (mutate B k) (coefficientCompanion B₀ (mutateCoefficients B C k))
      (columnColor (mutateCoefficients B C k)) := by
  rw [mutate_negMatrix, mutateCoefficients_negMatrix]
  exact actualArrowSigns_negMatrix_iff B₀ (mutate B k) (mutateCoefficients B C k)
    hB₀ (mutation_preserves_skew B k hB) hC'

/-- Current actual root membership, QCC and arrow signs supply next strict
coherence independently of next arrow signs and next triangle parity. -/
theorem signedSeedInv_mutation_signCoherent (B₀ : Matrix 4) (hB₀ : SkewSymmetric B₀)
    (positive : Bool) (w : List (Fin 4)) (h : SignedSeedInv B₀ positive w) (k : Fin 4) :
    SignCoherent (mutateCoefficients (signedPrincipalSeed B₀ positive w).1
      (signedPrincipalSeed B₀ positive w).2 k) :=
  (MAExistenceTeamCSeedStep.coefficientMutation_rooted_and_signCoherent B₀
    (signedPrincipalSeed B₀ positive w).1 (signedPrincipalSeed B₀ positive w).2 hB₀
    (signedPrincipalSeed_skew B₀ hB₀ positive w) k h.companion h.arrowSigns h.roots).2

/-- Red pivots reduce rigorously to a green-pivot law that covers both
chronological signs of initialization. A `+I`-only actual-origin theorem does
not match this hypothesis. The green law is an explicit theorem argument. -/
theorem signedSeedInv_arrowSigns_of_signedGreenLaw
    (hgreen : ∀ (B₀ : Matrix 4), SkewSymmetric B₀ → Acyclic B₀ →
      ∀ (positive : Bool) w, SignedSeedInv B₀ positive w → ∀ k,
        columnColor (signedPrincipalSeed B₀ positive w).2 k = true →
        ArrowSigns (mutate (signedPrincipalSeed B₀ positive w).1 k)
          (coefficientCompanion B₀ (mutateCoefficients (signedPrincipalSeed B₀ positive w).1
            (signedPrincipalSeed B₀ positive w).2 k))
          (columnColor (mutateCoefficients (signedPrincipalSeed B₀ positive w).1
            (signedPrincipalSeed B₀ positive w).2 k)))
    (B₀ : Matrix 4) (hB₀ : SkewSymmetric B₀) (hAc : Acyclic B₀)
    (positive : Bool) (w : List (Fin 4)) (h : SignedSeedInv B₀ positive w) (k : Fin 4) :
    ArrowSigns (mutate (signedPrincipalSeed B₀ positive w).1 k)
      (coefficientCompanion B₀ (mutateCoefficients (signedPrincipalSeed B₀ positive w).1
        (signedPrincipalSeed B₀ positive w).2 k))
      (columnColor (mutateCoefficients (signedPrincipalSeed B₀ positive w).1
        (signedPrincipalSeed B₀ positive w).2 k)) := by
  cases hk : columnColor (signedPrincipalSeed B₀ positive w).2 k
  · have hn := signedSeedInv_negMatrix B₀ hB₀ positive w h
    have he := signedPrincipalSeed_negMatrix B₀ positive w
    have hC := signedSeedInv_signCoherent B₀ hB₀ positive w h
    have hg : columnColor (signedPrincipalSeed (negMatrix B₀) (!positive) w).2 k = true := by
      rw [he]
      rw [columnColor_negMatrix _ hC, hk]
      rfl
    have hs := hgreen (negMatrix B₀) (negMatrix_skew B₀ hB₀)
      (negMatrix_acyclic B₀ hB₀ hAc) (!positive) w hn k hg
    rw [he] at hs
    exact (mutation_actualArrowSigns_negMatrix_iff B₀ (signedPrincipalSeed B₀ positive w).1
      (signedPrincipalSeed B₀ positive w).2 k hB₀ (signedPrincipalSeed_skew B₀ hB₀ positive w)
      (signedSeedInv_mutation_signCoherent B₀ hB₀ positive w h k)).mp hs
  · exact hgreen B₀ hB₀ hAc positive w h k hk

/-- Projection of the signed green-pivot contract to the original actual
principal seed. Its unresolved green law still occurs explicitly. -/
theorem seedInv_arrowSigns_of_signedGreenLaw
    (hgreen : ∀ (B₀ : Matrix 4), SkewSymmetric B₀ → Acyclic B₀ →
      ∀ (positive : Bool) w, SignedSeedInv B₀ positive w → ∀ k,
        columnColor (signedPrincipalSeed B₀ positive w).2 k = true →
        ArrowSigns (mutate (signedPrincipalSeed B₀ positive w).1 k)
          (coefficientCompanion B₀ (mutateCoefficients (signedPrincipalSeed B₀ positive w).1
            (signedPrincipalSeed B₀ positive w).2 k))
          (columnColor (mutateCoefficients (signedPrincipalSeed B₀ positive w).1
            (signedPrincipalSeed B₀ positive w).2 k)))
    (B₀ : Matrix 4) (hB₀ : SkewSymmetric B₀) (hAc : Acyclic B₀)
    (w : List (Fin 4)) (h : SeedInv B₀ w) (k : Fin 4) :
    ArrowSigns (mutate (principalSeed B₀ w).1 k)
      (coefficientCompanion B₀ (mutateCoefficients (principalSeed B₀ w).1 (principalSeed B₀ w).2 k))
      (columnColor (mutateCoefficients (principalSeed B₀ w).1 (principalSeed B₀ w).2 k)) :=
  signedSeedInv_arrowSigns_of_signedGreenLaw hgreen B₀ hB₀ hAc true w
    ((signedSeedInv_positive_iff B₀ w).mpr h) k

end QuiverProofs.MAExistenceTeamDMutationSymmetry
