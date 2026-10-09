import QuiverProofs.MAExistenceCompanions
import QuiverProofs.MAExistenceCoefficients

/-! Elementary integral reflection-orbit foundations for the rank-four
principal-coefficient route. Real roots are defined by their actual orbit,
without putting coordinate positivity or a norm condition into the definition.
The coordinate sign dichotomy and mutation preservation of companion arrow
signs/admissibility remain separate mathematical obligations.
-/
namespace QuiverProofs.MAExistenceTeamBRootPositivity
open MAExistenceLiterature MAExistenceCompanions MAExistenceCoefficients

set_option maxHeartbeats 0

abbrev Vector4 := Fin 4 → Int

/-- The integer bilinear pairing with matrix `A`, with all summands explicit. -/
def pairing (A : Matrix 4) (x y : Vector4) : Int :=
  x 0 * (A 0 0 * y 0 + A 0 1 * y 1 + A 0 2 * y 2 + A 0 3 * y 3) +
  x 1 * (A 1 0 * y 0 + A 1 1 * y 1 + A 1 2 * y 2 + A 1 3 * y 3) +
  x 2 * (A 2 0 * y 0 + A 2 1 * y 1 + A 2 2 * y 2 + A 2 3 * y 3) +
  x 3 * (A 3 0 * y 0 + A 3 1 * y 1 + A 3 2 * y 2 + A 3 3 * y 3)

def simple (k : Fin 4) : Vector4 := fun i => if i = k then 1 else 0

/-- This is the reflection formula for roots of squared length two. -/
def reflection (A : Matrix 4) (r x : Vector4) : Vector4 :=
  fun i => x i - pairing A r x * r i

def simpleReflection (A : Matrix 4) (k : Fin 4) (x : Vector4) : Vector4 :=
  reflection A (simple k) x

/-- The orbit of the standard basis under simple reflections. In particular,
arbitrary integer norm-two vectors are not declared to be real roots. -/
inductive RealRoot (A : Matrix 4) : Vector4 → Prop
  | simple (k : Fin 4) : RealRoot A (simple k)
  | reflect {x : Vector4} (k : Fin 4) :
      RealRoot A x → RealRoot A (simpleReflection A k x)

private theorem fin4 (i : Fin 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega

theorem pairing_sub_smul_left (A : Matrix 4) (x y z : Vector4) (a : Int) :
    pairing A (fun i => x i - a * y i) z = pairing A x z - a * pairing A y z := by
  simp only [pairing]
  grind

theorem pairing_sub_smul_right (A : Matrix 4) (x y z : Vector4) (a : Int) :
    pairing A x (fun i => y i - a * z i) = pairing A x y - a * pairing A x z := by
  simp only [pairing]
  grind

theorem pairing_symmetric (A : Matrix 4) (hA : ∀ i j, A i j = A j i)
    (x y : Vector4) : pairing A x y = pairing A y x := by
  have h01 := hA 0 1; have h02 := hA 0 2; have h03 := hA 0 3
  have h12 := hA 1 2; have h13 := hA 1 3; have h23 := hA 2 3
  simp only [pairing]
  grind

theorem pairing_simple_self (A : Matrix 4) (k : Fin 4) :
    pairing A (simple k) (simple k) = A k k := by
  rcases fin4 k with rfl | rfl | rfl | rfl <;> simp [pairing, simple]

theorem reflection_pairing (A : Matrix 4) (r x : Vector4)
    (hr : pairing A r r = 2) :
    pairing A r (reflection A r x) = -pairing A r x := by
  unfold reflection
  rw [pairing_sub_smul_right, hr]
  omega

theorem reflection_involutive (A : Matrix 4) (r x : Vector4)
    (hr : pairing A r r = 2) :
    reflection A r (reflection A r x) = x := by
  funext i
  simp only [reflection, reflection_pairing A r x hr]
  grind

theorem reflection_isometry (A : Matrix 4)
    (hA : ∀ i j, A i j = A j i) (r x y : Vector4)
    (hr : pairing A r r = 2) :
    pairing A (reflection A r x) (reflection A r y) = pairing A x y := by
  unfold reflection
  rw [pairing_sub_smul_left, pairing_sub_smul_right,
    pairing_sub_smul_right, hr, pairing_symmetric A hA x r]
  grind

theorem realRoot_norm_two (A : Matrix 4)
    (hA : ∀ i j, A i j = A j i) (hd : ∀ i, A i i = 2)
    {r : Vector4} (hr : RealRoot A r) : pairing A r r = 2 := by
  induction hr with
  | simple k => rw [pairing_simple_self, hd]
  | reflect k hr ih =>
      unfold simpleReflection
      rw [reflection_isometry A hA _ _ _ (by rw [pairing_simple_self, hd])]
      exact ih

/-- Reflection in a norm-two vector intertwines the reflections in `u`
and in its image. This is the elementary conjugation identity. -/
theorem reflection_covariant (A : Matrix 4)
    (hA : ∀ i j, A i j = A j i) (r u x : Vector4)
    (hr : pairing A r r = 2) :
    reflection A (reflection A r u) (reflection A r x) =
      reflection A r (reflection A u x) := by
  have hp := reflection_isometry A hA r u x hr
  funext i
  unfold reflection at hp ⊢
  rw [hp, pairing_sub_smul_right]
  grind

/-- Reflection in any actual orbit root preserves the same simple-reflection
orbit. No coordinate-sign or finite-type premise occurs here. -/
theorem realRoot_reflection (A : Matrix 4)
    (hA : ∀ i j, A i j = A j i) (hd : ∀ i, A i i = 2)
    {r x : Vector4} (hr : RealRoot A r) (hx : RealRoot A x) :
    RealRoot A (reflection A r x) := by
  induction hr generalizing x with
  | simple k => exact RealRoot.reflect k hx
  | @reflect u k hu ih =>
      have hs : pairing A (simple k) (simple k) = 2 := by
        rw [pairing_simple_self, hd]
      have hv := ih (RealRoot.reflect k hx)
      have hout := RealRoot.reflect k hv
      have hc := reflection_covariant A hA (simple k) u
        (simpleReflection A k x) hs
      rw [show reflection A (simple k) (simpleReflection A k x) = x from
        reflection_involutive A (simple k) x hs] at hc
      unfold simpleReflection at hout
      unfold simpleReflection at hc
      rw [←hc] at hout
      exact hout

theorem realRoot_neg (A : Matrix 4)
    (hA : ∀ i j, A i j = A j i) (hd : ∀ i, A i i = 2)
    {r : Vector4} (hr : RealRoot A r) : RealRoot A (fun i => -r i) := by
  have hn := realRoot_norm_two A hA hd hr
  have hh := realRoot_reflection A hA hd hr hr
  have he : reflection A r r = fun i => -r i := by
    funext i
    simp only [reflection, hn]
    omega
  rw [he] at hh
  exact hh

theorem realRoot_nonzero (A : Matrix 4)
    (hA : ∀ i j, A i j = A j i) (hd : ∀ i, A i i = 2)
    {r : Vector4} (hr : RealRoot A r) : ∃ i, r i ≠ 0 := by
  have hn := realRoot_norm_two A hA hd hr
  by_cases h0 : r 0 = 0
  · by_cases h1 : r 1 = 0
    · by_cases h2 : r 2 = 0
      · by_cases h3 : r 3 = 0
        · simp [pairing, h0, h1, h2, h3] at hn
        · exact ⟨3, h3⟩
      · exact ⟨2, h2⟩
    · exact ⟨1, h1⟩
  · exact ⟨0, h0⟩

def column (C : Matrix 4) (j : Fin 4) : Vector4 := fun i => C i j

theorem coefficientCompanion_pairing (B₀ C : Matrix 4) (i j : Fin 4) :
    pairing (initialCompanion B₀) (column C i) (column C j) =
      coefficientCompanion B₀ C i j := by
  simp only [pairing, column, coefficientCompanion, Cosquare.mul, Cosquare.transpose]
  grind

/-- The actual nonlinear coefficient update is reflection in the current
pivot root when its shear weight is nonzero. Coherence is needed only for
the pivot here; quasi-Cartan magnitudes and arrow signs supply the exact Gram
pairing. No all-word coefficient premise is assumed. -/
theorem coefficientMutation_as_reflection (B₀ B C : Matrix 4)
    (green : Fin 4 → Bool) (k j : Fin 4) (hjk : j ≠ k)
    (hB : SkewSymmetric B)
    (hA : QuasiCartanCompanion B (coefficientCompanion B₀ C))
    (hs : ArrowSigns B (coefficientCompanion B₀ C) green)
    (hg : green k = true → ∀ i, 0 ≤ C i k)
    (hr : green k = false → ∀ i, C i k ≤ 0)
    (ht : pivotWeight B green k j ≠ 0) :
    column (mutateCoefficients B C k) j =
      reflection (initialCompanion B₀) (column C k) (column C j) := by
  have hp := pivotWeight_companion B (coefficientCompanion B₀ C) green k j
    hjk hB hA hs
  have he : coefficientCompanion B₀ C k j = -pivotWeight B green k j := by
    rcases hp with hp | hp
    · exact False.elim (ht hp)
    · rw [hA.1 k j]
      exact hp
  funext i
  rw [mutateCoefficients_matrix B C green k hg hr]
  simp only [column, mul_coefficientBasis_entry, hjk, if_false, reflection]
  rw [coefficientCompanion_pairing, he]
  grind

theorem coefficientMutation_zero_weight (B C : Matrix 4)
    (green : Fin 4 → Bool) (k j : Fin 4) (hjk : j ≠ k)
    (hg : green k = true → ∀ i, 0 ≤ C i k)
    (hr : green k = false → ∀ i, C i k ≤ 0)
    (ht : pivotWeight B green k j = 0) :
    column (mutateCoefficients B C k) j = column C j := by
  funext i
  rw [mutateCoefficients_matrix B C green k hg hr]
  simp [column, mul_coefficientBasis_entry, hjk, ht]

/-- Current actual orbit roots are preserved by one coefficient mutation,
provided the current companion and arrow signs are supplied. This is a local
closure theorem for root membership, not for the full seed certificate. -/
theorem coefficientMutation_realRoots (B₀ B C : Matrix 4)
    (hB₀ : SkewSymmetric B₀) (hB : SkewSymmetric B)
    (green : Fin 4 → Bool) (k : Fin 4)
    (hA : QuasiCartanCompanion B (coefficientCompanion B₀ C))
    (hs : ArrowSigns B (coefficientCompanion B₀ C) green)
    (hg : green k = true → ∀ i, 0 ≤ C i k)
    (hr : green k = false → ∀ i, C i k ≤ 0)
    (hroots : ∀ j, RealRoot (initialCompanion B₀) (column C j)) :
    ∀ j, RealRoot (initialCompanion B₀) (column (mutateCoefficients B C k) j) := by
  have h0 := initialCompanion_quasiCartan B₀ hB₀
  intro j
  by_cases hj : j = k
  · subst j
    have he : column (mutateCoefficients B C k) k = fun i => -(column C k) i := by
      funext i
      simp [column, mutateCoefficients]
    rw [he]
    exact realRoot_neg _ h0.1 h0.2.1 (hroots k)
  · by_cases ht : pivotWeight B green k j = 0
    · rw [coefficientMutation_zero_weight B C green k j hj hg hr ht]
      exact hroots j
    · rw [coefficientMutation_as_reflection B₀ B C green k j hj hB hA hs hg hr ht]
      exact realRoot_reflection _ h0.1 h0.2.1 (hroots k) (hroots j)

/-- Root membership initializes at the actual identity coefficient matrix. -/
theorem identity_realRoots (B₀ : Matrix 4) :
    ∀ j, RealRoot (initialCompanion B₀) (column identityCoefficients j) := by
  intro j
  exact RealRoot.simple j

/- The missing coordinate theorem has the exact intended mathematical content:

  ∀ B₀ : Matrix 4, SkewSymmetric B₀ →
    ∀ r : Vector4, RealRoot (initialCompanion B₀) r →
      (∀ i, 0 ≤ r i) ∨ (∀ i, r i ≤ 0).

It is not established by this module. Together with realRoot_nonzero this would
give the strict green/red dichotomy. Updated ArrowSigns and admissibility also
remain independent obligations for a simultaneous mutation-closed certificate.
-/

end QuiverProofs.MAExistenceTeamBRootPositivity
