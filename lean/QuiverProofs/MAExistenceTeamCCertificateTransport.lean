import QuiverProofs.MAExistenceTeamBOrderMutation
import QuiverProofs.MAExistenceCoefficients

/-! Actual-origin bilinear identities for the certificate project.

The coefficient matrix is the actual chronological coefficient evolution.
Uniform signs of its mutated pivot columns remain explicit hypotheses; this
module does not prove those signs, companion admissibility, or a selected
proper-mutation output.  The identities retain the original vertex labels and
hold for arbitrary integer weights, including singular and disconnected inputs.
-/
namespace QuiverProofs.MAExistenceTeamCCertificateTransport
open MAExistenceLiterature MAExistenceCoefficients MAExistenceCompanions
open MAExistenceTeamBOrderMutation Cosquare MutationCongruence

set_option maxHeartbeats 0

/-- The actual coefficient pullback of one fixed initial bilinear form. -/
def coefficientBilinear (U₀ C : Matrix 4) : Matrix 4 :=
  mul (mul (transpose C) U₀) C

theorem coefficientBilinear_initial (U₀ : Matrix 4) :
    coefficientBilinear U₀ identityCoefficients = U₀ := by
  have hid : (identityCoefficients : Matrix 4) = one := rfl
  have ht : transpose one = one := by
    funext i j
    simp [transpose, one, eq_comm]
  simp [coefficientBilinear, hid, ht, one_mul, mul_one]

/-- The actual coefficient update pulls back every bilinear form by the same
chosen shear. Only the sign of the current pivot column is used. -/
theorem coefficientBilinear_mutation (U₀ B C : Matrix 4)
    (green : Colors) (k : Fin 4)
    (hg : green k = true → ∀ i, 0 ≤ C i k)
    (hr : green k = false → ∀ i, C i k ≤ 0) :
    coefficientBilinear U₀ (mutateCoefficients B C k) =
      mul (mul (transpose (coefficientBasis B green k))
        (coefficientBilinear U₀ C)) (coefficientBasis B green k) := by
  rw [mutateCoefficients_matrix B C green k hg hr]
  simp only [coefficientBilinear, transpose_mul, mul_assoc]

/-- The exchange pullback uses the actual coefficient matrix, rather than
an unrelated integral congruence witness. -/
theorem exchange_coefficientBasis_update (B₀ B C : Matrix 4)
    (hB : SkewSymmetric B) (green : Colors) (k : Fin 4)
    (hg : green k = true → ∀ i, 0 ≤ C i k)
    (hr : green k = false → ∀ i, C i k ≤ 0)
    (he : B = mul (mul (transpose C) B₀) C) :
    mutate B k = mul (mul (transpose (mutateCoefficients B C k)) B₀)
      (mutateCoefficients B C k) := by
  calc
    mutate B k = mul (mul (transpose (coefficientBasis B green k)) B)
        (coefficientBasis B green k) :=
      mutation_coefficientBasis_congruence B hB green k
    _ = mul (mul (transpose (coefficientBasis B green k))
        (mul (mul (transpose C) B₀) C)) (coefficientBasis B green k) :=
      congrArg (fun D => mul (mul (transpose (coefficientBasis B green k)) D)
        (coefficientBasis B green k)) he
    _ = _ := by
      rw [mutateCoefficients_matrix B C green k hg hr]
      simp only [transpose_mul, mul_assoc]

/-- Signedness is required only at pivots that actually occur, and only
before their mutation. There is no sign assumption on the endpoint columns. -/
def CoherentPivots (B C : Matrix 4) (w : List (Fin 4)) : Prop :=
  ∀ u k v, w = u ++ k :: v →
    (∀ i, 0 ≤ (evolve B C u).2 i k) ∨
      (∀ i, (evolve B C u).2 i k ≤ 0)

theorem coherentPivots_of_all_word_signCoherent (B C : Matrix 4)
    (hc : ∀ u, SignCoherent (evolve B C u).2) (w : List (Fin 4)) :
    CoherentPivots B C w := by
  intro u k v _
  rcases hc u k with hg | hr
  · exact Or.inl hg.1
  · exact Or.inr hr.1

/-- Exact exchange origin along the actual chronological coefficient
evolution. The initial coefficient matrix may be arbitrary, provided it
already realizes the displayed exchange pullback. -/
theorem evolve_exchange_pullback (B₀ B C : Matrix 4)
    (hB : SkewSymmetric B) (w : List (Fin 4))
    (he : B = mul (mul (transpose C) B₀) C)
    (hc : CoherentPivots B C w) :
    (evolve B C w).1 =
      mul (mul (transpose (evolve B C w).2) B₀) (evolve B C w).2 := by
  induction w generalizing B C with
  | nil => exact he
  | cons k ks ih =>
    have hk := hc [] k ks rfl
    have hnext : mutate B k =
        mul (mul (transpose (mutateCoefficients B C k)) B₀)
          (mutateCoefficients B C k) := by
      rcases hk with hg | hr
      · exact exchange_coefficientBasis_update B₀ B C hB (fun _ => true) k
          (fun _ => hg) (by simp) he
      · exact exchange_coefficientBasis_update B₀ B C hB (fun _ => false) k
          (by simp) (fun _ => hr) he
    apply ih (mutate B k) (mutateCoefficients B C k)
      (mutation_preserves_skew B k hB) hnext
    intro u j v hw
    exact hc (k :: u) j v (congrArg (List.cons k) hw)

theorem principalSeed_exchange_pullback (B₀ : Matrix 4)
    (hB₀ : SkewSymmetric B₀) (w : List (Fin 4))
    (hc : CoherentPivots B₀ identityCoefficients w) :
    (principalSeed B₀ w).1 =
      mul (mul (transpose (principalSeed B₀ w).2) B₀) (principalSeed B₀ w).2 := by
  apply evolve_exchange_pullback B₀ B₀ identityCoefficients hB₀ w _ hc
  have hid : (identityCoefficients : Matrix 4) = one := rfl
  have ht : transpose one = one := by
    funext i j
    simp [transpose, one, eq_comm]
  simp [hid, ht, one_mul, mul_one]

/-- Symmetric and skew parts commute with the actual coefficient pullback. -/
theorem coefficientBilinear_symmetric_part (U₀ C : Matrix 4) :
    add (coefficientBilinear U₀ C) (transpose (coefficientBilinear U₀ C)) =
      mul (mul (transpose C) (add U₀ (transpose U₀))) C := by
  simp only [coefficientBilinear, transpose_mul]
  change add (mul (mul (transpose C) U₀) C)
      (mul (transpose C) (mul (transpose U₀) C)) = _
  rw [←mul_assoc, mul_add, add_mul]

theorem coefficientBilinear_skew_part (U₀ C : Matrix 4) :
    add (coefficientBilinear U₀ C)
        (scale (-1) (transpose (coefficientBilinear U₀ C))) =
      mul (mul (transpose C) (add U₀ (scale (-1) (transpose U₀)))) C := by
  simp only [coefficientBilinear, transpose_mul]
  change add (mul (mul (transpose C) U₀) C)
      (scale (-1) (mul (transpose C) (mul (transpose U₀) C))) = _
  rw [←mul_assoc, mul_add, mul_scale, add_mul, scale_mul]

/-- Origin data pins both parts of the pulled-back form to the actual
coefficient companion and exchange matrix. No order existence is assumed. -/
theorem coefficientBilinear_parts (B₀ U₀ B C : Matrix 4)
    (hs : add U₀ (transpose U₀) = initialCompanion B₀)
    (ha : add U₀ (scale (-1) (transpose U₀)) = reverse B₀)
    (he : B = mul (mul (transpose C) B₀) C) :
    add (coefficientBilinear U₀ C) (transpose (coefficientBilinear U₀ C)) =
        coefficientCompanion B₀ C ∧
      add (coefficientBilinear U₀ C)
        (scale (-1) (transpose (coefficientBilinear U₀ C))) = reverse B := by
  constructor
  · rw [coefficientBilinear_symmetric_part, hs]
    rfl
  · rw [coefficientBilinear_skew_part, ha]
    have hrev : reverse B₀ = scale (-1) B₀ := by
      funext i j
      simp [reverse, scale]
    rw [hrev, mul_scale, scale_mul, ←he]
    funext i j
    simp [reverse, scale]

/-- The two origin identities at the actual principal seed. The only
chronological premise is signedness of the pivots that were mutated. -/
theorem principalSeed_bilinear_parts (B₀ U₀ : Matrix 4)
    (hB₀ : SkewSymmetric B₀) (w : List (Fin 4))
    (hs : add U₀ (transpose U₀) = initialCompanion B₀)
    (ha : add U₀ (scale (-1) (transpose U₀)) = reverse B₀)
    (hc : CoherentPivots B₀ identityCoefficients w) :
    add (coefficientBilinear U₀ (principalSeed B₀ w).2)
        (transpose (coefficientBilinear U₀ (principalSeed B₀ w).2)) =
        coefficientCompanion B₀ (principalSeed B₀ w).2 ∧
      add (coefficientBilinear U₀ (principalSeed B₀ w).2)
        (scale (-1) (transpose (coefficientBilinear U₀ (principalSeed B₀ w).2))) =
        reverse (principalSeed B₀ w).1 :=
  coefficientBilinear_parts B₀ U₀ (principalSeed B₀ w).1
    (principalSeed B₀ w).2 hs ha (principalSeed_exchange_pullback B₀ hB₀ w hc)

/-- Over the integers, equal symmetric and skew parts determine the entire
bilinear form. This provides exact equality, rather than just congruence. -/
theorem bilinear_eq_of_parts (U V : Matrix 4)
    (hs : add U (transpose U) = add V (transpose V))
    (ha : add U (scale (-1) (transpose U)) =
      add V (scale (-1) (transpose V))) : U = V := by
  funext i j
  have hsij := congrFun (congrFun hs i) j
  have haij := congrFun (congrFun ha i) j
  simp only [add, transpose, scale] at hsij haij
  omega

/-- A supplied current compatible order realizes the fixed initial
bilinear form pulled back by the actual coefficient matrix. The origin
identities and the current companion/sign hypotheses are all explicit. -/
theorem coefficientBilinear_eq_compatible (B₀ U₀ B C : Matrix 4)
    (hB : SkewSymmetric B)
    (hs₀ : add U₀ (transpose U₀) = initialCompanion B₀)
    (ha₀ : add U₀ (scale (-1) (transpose U₀)) = reverse B₀)
    (he : B = mul (mul (transpose C) B₀) C)
    (hA : QuasiCartanCompanion B (coefficientCompanion B₀ C))
    (green : Colors) (hs : ArrowSigns B (coefficientCompanion B₀ C) green)
    (k : Fin 4) (p : ProperOrder.CyclicOrder) (hp : Compatible B green k p) :
    coefficientBilinear U₀ C = labeledUnipotent B p := by
  obtain ⟨hss, haa⟩ := coefficientBilinear_parts B₀ U₀ B C hs₀ ha₀ he
  funext i j
  have hsij := congrFun (congrFun hss i) j
  have haij := congrFun (congrFun haa i) j
  have hu := compatible_labeledUnipotent B (coefficientCompanion B₀ C)
    hB hA green hs k p hp i j
  simp only [add, transpose, scale, reverse] at hsij haij
  omega

/-- Every initial topological order supplies both required parts of the
fixed origin form. This uses Team B's compatible-order identity. -/
theorem topological_labeledUnipotent_parts (B₀ : Matrix 4)
    (hB₀ : SkewSymmetric B₀) (p₀ : ProperOrder.CyclicOrder)
    (hp₀ : ProperObstructionSoundness.Topological B₀ p₀) :
    add (labeledUnipotent B₀ p₀) (transpose (labeledUnipotent B₀ p₀)) =
        initialCompanion B₀ ∧
      add (labeledUnipotent B₀ p₀)
        (scale (-1) (transpose (labeledUnipotent B₀ p₀))) = reverse B₀ := by
  have hp : Compatible B₀ (fun _ => true) 0 p₀ := by
    intro i j hij
    exact MAExistenceCoordinator.topological_arrows_increase B₀ hB₀ p₀ hp₀ i j
      ((MAExistenceInitialization.allGreen_auxiliaryArrow B₀ 0 i j).mp hij)
  have hA := initialCompanion_quasiCartan B₀ hB₀
  have hu := compatible_labeledUnipotent B₀ (initialCompanion B₀) hB₀
    hA (fun _ => true) (initialCompanion_arrowSigns B₀ hB₀) 0 p₀ hp
  constructor <;> funext i j
  all_goals
    have hij := hu i j
    have hji := hu j i
    have hsym := hA.1 i j
    have hskew := hB₀ i j
    simp only [add, transpose, scale, reverse]
    omega

/-- Fully supplied initial origin form and its exact principal-seed parts.
The remaining chronological pivot-sign premise is not hidden. -/
theorem principalSeed_topological_bilinear_parts (B₀ : Matrix 4)
    (hB₀ : SkewSymmetric B₀) (p₀ : ProperOrder.CyclicOrder)
    (hp₀ : ProperObstructionSoundness.Topological B₀ p₀) (w : List (Fin 4))
    (hc : CoherentPivots B₀ identityCoefficients w) :
    add (coefficientBilinear (labeledUnipotent B₀ p₀) (principalSeed B₀ w).2)
        (transpose (coefficientBilinear (labeledUnipotent B₀ p₀)
          (principalSeed B₀ w).2)) = coefficientCompanion B₀ (principalSeed B₀ w).2 ∧
      add (coefficientBilinear (labeledUnipotent B₀ p₀) (principalSeed B₀ w).2)
        (scale (-1) (transpose (coefficientBilinear (labeledUnipotent B₀ p₀)
          (principalSeed B₀ w).2))) = reverse (principalSeed B₀ w).1 := by
  obtain ⟨hs, ha⟩ := topological_labeledUnipotent_parts B₀ hB₀ p₀ hp₀
  exact principalSeed_bilinear_parts B₀ (labeledUnipotent B₀ p₀) hB₀ w hs ha hc

end QuiverProofs.MAExistenceTeamCCertificateTransport
