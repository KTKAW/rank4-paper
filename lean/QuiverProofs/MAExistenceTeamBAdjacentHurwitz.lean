import QuiverProofs.MAExistenceTeamBRootWordExchange

/-! Adjacent Hurwitz transport for genuine initial root frames. The current
Euler order and integral basis are preserved by the reflection and swap.
Chronological selected-shear transport and global sign/order restrictions
remain separate obligations. -/

namespace QuiverProofs.MAExistenceTeamBAdjacentHurwitz
open QuiverProofs QuiverProofs.Cosquare
open QuiverProofs.MAExistenceLiterature QuiverProofs.MAExistenceCoefficients
open QuiverProofs.MAExistenceTeamBRootPositivity
open QuiverProofs.MAExistenceTeamBRootWordExchange
set_option maxHeartbeats 0

private theorem fin4 (i : Fin 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega

def change (a : Int) : Matrix 4 := mat4 (-a) 1 0 0 1 0 0 0 0 0 1 0 0 0 0 1
def changeInverse (a : Int) : Matrix 4 := mat4 0 1 0 0 1 a 0 0 0 0 1 0 0 0 0 1
def weight (U D : Matrix 4) : Int := pairing U (column D 0) (column D 1)
def frame (U D : Matrix 4) : Matrix 4 := mul D (change (weight U D))

def EulerUnitUpper (U D : Matrix 4) : Prop :=
  (∀ i, pairing U (column D i) (column D i) = 1) ∧
    ∀ i j, j < i → pairing U (column D i) (column D j) = 0

theorem pairing_symmetric_part (A U : Matrix 4)
    (hU : ∀ i j, U i j + U j i = A i j) (x y : Vector4) :
    pairing A x y = pairing U x y + pairing U y x := by
  simp only [pairing]
  simp_rw [← hU]
  ring

theorem initial_realRoot_euler_one (B U : Matrix 4) (hB : SkewSymmetric B)
    (hU : ∀ i j, U i j + U j i = initialCompanion B i j)
    (x : Vector4) (hx : RealRoot (initialCompanion B) x) : pairing U x x = 1 := by
  have hn := realRoot_norm_two _ (initialCompanion_quasiCartan B hB).1
    (initialCompanion_quasiCartan B hB).2.1 hx
  rw [pairing_symmetric_part _ U hU] at hn
  omega

theorem change_inverse (a : Int) :
    mul (changeInverse a) (change a) = one ∧ mul (change a) (changeInverse a) = one := by
  constructor
  all_goals
    funext i j
    rcases fin4 i with rfl | rfl | rfl | rfl <;>
      rcases fin4 j with rfl | rfl | rfl | rfl <;>
      simp [change, changeInverse, mul, mat4, one]

theorem frame_columns (U D : Matrix 4) :
    column (frame U D) 0 = (fun i => column D 1 i - weight U D * column D 0 i) ∧
      column (frame U D) 1 = column D 0 ∧
      column (frame U D) 2 = column D 2 ∧ column (frame U D) 3 = column D 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    funext i
    simp [frame, change, column, mul, mat4] <;> ring

theorem frame_integralBasis (U D : Matrix 4) (hD : IntegralBasis D) :
    IntegralBasis (frame U D) := by
  obtain ⟨Di, hl, hr⟩ := hD
  let a := weight U D
  have hi := change_inverse a
  refine ⟨mul (changeInverse a) Di, ?_, ?_⟩
  · change mul (mul (changeInverse a) Di) (mul D (change a)) = one
    rw [Cosquare.mul_assoc, ←Cosquare.mul_assoc Di, hl, Cosquare.one_mul, hi.1]
  · change mul (mul D (change a)) (mul (changeInverse a) Di) = one
    rw [Cosquare.mul_assoc, ←Cosquare.mul_assoc (change a), hi.2, Cosquare.one_mul, hr]

theorem frame_first_reflection (B U D : Matrix 4)
    (hU : ∀ i j, U i j + U j i = initialCompanion B i j)
    (hsr : pairing U (column D 1) (column D 0) = 0) :
    column (frame U D) 0 = reflection (initialCompanion B) (column D 0) (column D 1) := by
  rw [(frame_columns U D).1]
  have hp := pairing_symmetric_part (initialCompanion B) U hU (column D 0) (column D 1)
  rw [hsr, add_zero] at hp
  funext i
  simp only [reflection, hp, weight]

theorem frame_realRoot_columns (B U D : Matrix 4) (hB : SkewSymmetric B)
    (hU : ∀ i j, U i j + U j i = initialCompanion B i j)
    (hD : ∀ j, RealRoot (initialCompanion B) (column D j))
    (hsr : pairing U (column D 1) (column D 0) = 0) :
    ∀ j, RealRoot (initialCompanion B) (column (frame U D) j) := by
  intro j
  rcases fin4 j with rfl | rfl | rfl | rfl
  · rw [frame_first_reflection B U D hU hsr]
    exact realRoot_reflection _ (initialCompanion_quasiCartan B hB).1
      (initialCompanion_quasiCartan B hB).2.1 (hD 0) (hD 1)
  · rw [(frame_columns U D).2.1]
    exact hD 0
  · rw [(frame_columns U D).2.2.1]
    exact hD 2
  · rw [(frame_columns U D).2.2.2]
    exact hD 3

theorem frame_euler_unit_upper (U D : Matrix 4) (hD : EulerUnitUpper U D) :
    EulerUnitUpper U (frame U D) := by
  have h00 := hD.1 0
  have h11 := hD.1 1
  have h22 := hD.1 2
  have h33 := hD.1 3
  have h10 := hD.2 1 0 (by decide)
  have h20 := hD.2 2 0 (by decide)
  have h21 := hD.2 2 1 (by decide)
  have h30 := hD.2 3 0 (by decide)
  have h31 := hD.2 3 1 (by decide)
  have h32 := hD.2 3 2 (by decide)
  obtain ⟨hc0, hc1, hc2, hc3⟩ := frame_columns U D
  constructor
  · intro i
    rcases fin4 i with rfl | rfl | rfl | rfl
    · rw [hc0, pairing_sub_smul_left, pairing_sub_smul_right, pairing_sub_smul_right,
        h00, h11, h10]
      simp only [weight]
      ring
    · rw [hc1]; exact h00
    · rw [hc2]; exact h22
    · rw [hc3]; exact h33
  · intro i j hij
    rcases fin4 i with rfl | rfl | rfl | rfl <;>
      rcases fin4 j with rfl | rfl | rfl | rfl <;> try omega
    all_goals
      simp only [hc0, hc1, hc2, hc3, pairing_sub_smul_right,
        h00, h20, h21, h30, h31, h32, weight] <;> ring

theorem rootPerm_reflection_product (A : Matrix 4)
    (hA : ∀ i j, A i j = A j i) (r s : Vector4)
    (hr : pairing A r r = 2) (hs : pairing A s s = 2) :
    rootPerm A (reflection A r s)
      (by rw [reflection_isometry A hA r s s hr]; exact hs) * rootPerm A r hr =
      rootPerm A r hr * rootPerm A s hs := by
  apply Equiv.ext
  intro x
  simp only [Equiv.Perm.mul_apply, rootPerm_apply]
  exact reflection_covariant A hA r s x hr

theorem frame_rootPerm_product (B U D : Matrix 4) (hB : SkewSymmetric B)
    (hU : ∀ i j, U i j + U j i = initialCompanion B i j)
    (hr : ∀ j, RealRoot (initialCompanion B) (column D j))
    (hsr : pairing U (column D 1) (column D 0) = 0) :
    rootPerm (initialCompanion B) (column (frame U D) 0)
      (realRoot_norm_two _ (initialCompanion_quasiCartan B hB).1
        (initialCompanion_quasiCartan B hB).2.1
        (frame_realRoot_columns B U D hB hU hr hsr 0)) *
      rootPerm (initialCompanion B) (column (frame U D) 1)
        (realRoot_norm_two _ (initialCompanion_quasiCartan B hB).1
          (initialCompanion_quasiCartan B hB).2.1
          (frame_realRoot_columns B U D hB hU hr hsr 1)) =
      rootPerm (initialCompanion B) (column D 0)
        (realRoot_norm_two _ (initialCompanion_quasiCartan B hB).1
          (initialCompanion_quasiCartan B hB).2.1 (hr 0)) *
        rootPerm (initialCompanion B) (column D 1)
          (realRoot_norm_two _ (initialCompanion_quasiCartan B hB).1
            (initialCompanion_quasiCartan B hB).2.1 (hr 1)) := by
  apply Equiv.ext
  intro x
  simp only [Equiv.Perm.mul_apply, rootPerm_apply]
  rw [frame_first_reflection B U D hU hsr, (frame_columns U D).2.1]
  exact reflection_covariant _ (initialCompanion_quasiCartan B hB).1
    (column D 0) (column D 1) x
    (realRoot_norm_two _ (initialCompanion_quasiCartan B hB).1
      (initialCompanion_quasiCartan B hB).2.1 (hr 0))

/-- This primitive makes a valid adjacent Hurwitz move on a genuine integral
root frame with upper Euler Gram matrix. It has only current-state premises;
no graph, color, future, or global reduction property is asserted. -/
theorem adjacent_hurwitz_primitive (B U D : Matrix 4) (hB : SkewSymmetric B)
    (hU : ∀ i j, U i j + U j i = initialCompanion B i j)
    (hr : ∀ j, RealRoot (initialCompanion B) (column D j))
    (hD : IntegralBasis D)
    (hupper : ∀ i j, j < i → pairing U (column D i) (column D j) = 0) :
    (∀ j, RealRoot (initialCompanion B) (column (frame U D) j)) ∧
      IntegralBasis (frame U D) ∧ EulerUnitUpper U (frame U D) ∧
      column (frame U D) 0 = reflection (initialCompanion B) (column D 0) (column D 1) := by
  have hsr := hupper 1 0 (by decide)
  have he : EulerUnitUpper U D :=
    ⟨fun j => initial_realRoot_euler_one B U hB hU (column D j) (hr j), hupper⟩
  exact ⟨frame_realRoot_columns B U D hB hU hr hsr,
    frame_integralBasis U D hD, frame_euler_unit_upper U D he,
    frame_first_reflection B U D hU hsr⟩

end QuiverProofs.MAExistenceTeamBAdjacentHurwitz
