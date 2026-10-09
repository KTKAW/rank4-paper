import QuiverProofs.MAExistenceLiterature
import QuiverProofs.MutationCongruence

/-!
Local companion algebra with Neville's convention `B i j > 0` for `i → j`.
Current arrow signs are explicit hypotheses: this file does not assume that
they, admissibility, or sign coherence hold after every mutation word.

Source audit: https://arxiv.org/html/2409.17832v2, Definitions 2.7/2.10/2.24
match this project's arrow and coefficient conventions. Neville 2.25 invokes
Seven 1.3 for all-word admissible quasi-Cartan data; 2.26 invokes Seven 1.3/1.4
for arrow signs and the oriented-path constraint. These are separate missing
existence/preservation obligations, not consequences of symmetry. Lemma 5.5
also uses sign coherence and an admissible companion for the bundled frozen
extension via Theorem 4.4; a rank-four mutable companion alone does not provide
that extension. None of these external results is imported as an axiom here.

Remaining local magnitude case: for pairwise distinct `i,j,k`, with exactly
one of the two pivot weights nonzero, prove
`natAbs (A i j + t_i * A k j + t_j * A i k) =
 natAbs (B i j + correction (B i k) (B k j))`
from current companion data, arrow signs, and admissibility of this triangle.
The nonmixed and incident cases below are already proved. Even solving this
scalar case would not prove all-word admissibility or the path constraint.
-/
namespace QuiverProofs.MAExistenceCompanions
open MAExistenceLiterature Cosquare MutationCongruence

set_option maxHeartbeats 0

/-- Neville 2.26's first assertion, separated from ordinary companion data. -/
def ArrowSigns {n : Nat} (B A : Matrix n) (green : Fin n → Bool) : Prop :=
  ∀ i j, 0 < B i j → (0 < A i j ↔ green i = false ∧ green j = true)

/-- The coefficient-column shear chosen by the color of the pivot. -/
def pivotWeight {n : Nat} (B : Matrix n) (green : Fin n → Bool)
    (k i : Fin n) : Int :=
  max (if green k then B k i else -B k i) 0

/-- Entrywise `M A Mᵀ`, with `M` the simultaneous-mutation matrix.
The pivot weight on the diagonal is zero for a skew exchange matrix. -/
def localMutation {n : Nat} (B A : Matrix n) (green : Fin n → Bool)
    (k : Fin n) : Matrix n := fun i j =>
  if i = k then
    if j = k then A k k else -A k j - pivotWeight B green k j * A k k
  else if j = k then -A i k - pivotWeight B green k i * A k k
  else A i j + pivotWeight B green k i * A k j +
    pivotWeight B green k j * A i k +
    pivotWeight B green k i * pivotWeight B green k j * A k k

theorem localMutation_symmetric {n : Nat} (B A : Matrix n)
    (green : Fin n → Bool) (k : Fin n)
    (hA : ∀ i j, A i j = A j i) :
    ∀ i j, localMutation B A green k i j = localMutation B A green k j i := by
  intro i j
  by_cases hi : i = k <;> by_cases hj : j = k
  · subst i; subst j; rfl
  · subst i; simp only [localMutation, hj, if_false, if_true]; rw [hA k j]
  · subst j; simp only [localMutation, hi, if_false, if_true]; rw [hA i k]
  · simp only [localMutation, hi, hj, if_false]
    rw [hA i j, hA k j, hA i k]
    grind

private theorem companion_nonpos_eq {n : Nat} (B A : Matrix n)
    (hA : QuasiCartanCompanion B A) (i j : Fin n) (hij : i ≠ j)
    (hn : A i j ≤ 0) : A i j = -((B i j).natAbs : Int) := by
  have ha := hA.2.2 i j hij
  simpa only [ha] using Int.eq_neg_natAbs_of_nonpos hn

/-- The selected shear only uses negative companion entries. This is the
precise local input that keeps all diagonal entries equal to two. -/
theorem pivotWeight_companion {n : Nat} (B A : Matrix n)
    (green : Fin n → Bool) (k i : Fin n) (hik : i ≠ k)
    (hB : SkewSymmetric B) (hA : QuasiCartanCompanion B A)
    (hs : ArrowSigns B A green) :
    pivotWeight B green k i = 0 ∨ A i k = -pivotWeight B green k i := by
  cases hk : green k
  · by_cases hb : B k i < 0
    · have hbi : 0 < B i k := by have := hB i k; omega
      have hn : A i k ≤ 0 := by
        have hx := hs i k hbi
        simp [hk] at hx
        omega
      have he := companion_nonpos_eq B A hA i k hik hn
      have hm := Int.natAbs_of_nonneg (a := B i k) (by omega)
      right
      simp only [pivotWeight, hk, Bool.false_eq_true, ↓reduceIte]
      have hmax : max (-B k i) 0 = -B k i := by omega
      rw [hmax]
      have := hB i k
      omega
    · left; simp only [pivotWeight, hk, Bool.false_eq_true, ↓reduceIte]; omega
  · by_cases hb : 0 < B k i
    · have hn : A k i ≤ 0 := by
        have hx := hs k i hb
        simp [hk] at hx
        omega
      have he := companion_nonpos_eq B A hA k i (Ne.symm hik) hn
      have hm := Int.natAbs_of_nonneg (a := B k i) (by omega)
      right
      simp only [pivotWeight, hk, ↓reduceIte]
      have hmax : max (B k i) 0 = B k i := by omega
      rw [hmax, hA.1 i k]
      omega
    · left; simp only [pivotWeight, hk, ↓reduceIte]; omega

theorem localMutation_diagonal {n : Nat} (B A : Matrix n)
    (green : Fin n → Bool) (k : Fin n) (hB : SkewSymmetric B)
    (hA : QuasiCartanCompanion B A) (hs : ArrowSigns B A green) :
    ∀ i, localMutation B A green k i i = 2 := by
  intro i
  by_cases hik : i = k
  · subst i; simp [localMutation, hA.2.1 k]
  · simp only [localMutation, hik, if_false, hA.2.1 i, hA.2.1 k]
    rw [←hA.1 i k]
    rcases pivotWeight_companion B A green k i hik hB hA hs with hz | ha
    · simp [hz]
    · rw [ha]; grind

/-- Incident edge magnitudes are preserved under the simultaneous operation,
using just the current companion and arrow-sign rule. -/
theorem localMutation_incident_natAbs {n : Nat} (B A : Matrix n)
    (green : Fin n → Bool) (k i : Fin n) (hik : i ≠ k)
    (hB : SkewSymmetric B) (hA : QuasiCartanCompanion B A)
    (hs : ArrowSigns B A green) :
    (localMutation B A green k i k).natAbs = (mutate B k i k).natAbs := by
  simp only [localMutation, hik, if_false, if_true, hA.2.1 k,
    mutate, or_true, Int.natAbs_neg]
  rcases pivotWeight_companion B A green k i hik hB hA hs with hz | ha
  · simpa [hz] using hA.2.2 i k hik
  · have he : -A i k - pivotWeight B green k i * 2 = A i k := by rw [ha]; grind
    rw [he]
    exact hA.2.2 i k hik

/-- If the two shear weights are both nonzero or both zero, the companion
entry does not change. The mixed case is the triangle-sign obligation. -/
theorem localMutation_unmixed {n : Nat} (B A : Matrix n)
    (green : Fin n → Bool) (k i j : Fin n) (hik : i ≠ k) (hjk : j ≠ k)
    (hB : SkewSymmetric B) (hA : QuasiCartanCompanion B A)
    (hs : ArrowSigns B A green)
    (hm : (pivotWeight B green k i = 0 ↔ pivotWeight B green k j = 0)) :
    localMutation B A green k i j = A i j := by
  simp only [localMutation, hik, hjk, if_false, hA.2.1 k]
  rcases pivotWeight_companion B A green k i hik hB hA hs with hi | hi
  · have hj := hm.mp hi
    simp [hi, hj]
  · rcases pivotWeight_companion B A green k j hjk hB hA hs with hj | hj
    · have hz := hm.mpr hj
      simp [hz, hj]
    · rw [←hA.1 j k, hi, hj]
      grind

/-- The initial companion satisfies the required arrow-sign rule with every
vertex green, including absent arrows and disconnected supports. -/
theorem initialCompanion_arrowSigns {n : Nat} (B : Matrix n)
    (hB : SkewSymmetric B) : ArrowSigns B (initialCompanion B) (fun _ => true) := by
  intro i j hb
  have hij : i ≠ j := by
    intro he; subst i
    have := hB j j
    omega
  have hn := initialCompanion_offDiagonal_nonpos B i j hij
  simp only [Bool.true_eq_false, false_and, iff_false]
  omega

/-- Actual coefficient-derived companion; no quasi-Cartan property is built
into this definition. -/
def coefficientCompanion (B₀ C : Matrix 4) : Matrix 4 :=
  mul (mul (transpose C) (initialCompanion B₀)) C

theorem coefficientCompanion_initial (B₀ : Matrix 4) :
    coefficientCompanion B₀ one = initialCompanion B₀ := by
  have ht : transpose one = one := by funext i j; simp [transpose, one, eq_comm]
  simp [coefficientCompanion, ht, one_mul, mul_one]

theorem coefficientCompanion_symmetric (B₀ C : Matrix 4)
    (hB : SkewSymmetric B₀) :
    ∀ i j, coefficientCompanion B₀ C i j = coefficientCompanion B₀ C j i := by
  have hs := (initialCompanion_quasiCartan B₀ hB).1
  intro i j
  simp only [coefficientCompanion, mul, transpose]
  have h01 := hs 0 1; have h02 := hs 0 2; have h03 := hs 0 3
  have h12 := hs 1 2; have h13 := hs 1 3; have h23 := hs 2 3
  grind

/-- The transpose of Neville's `M`; coefficient columns change by `C E`. -/
def coefficientBasis (B : Matrix 4) (green : Fin 4 → Bool)
    (k : Fin 4) : Matrix 4 := fun i j =>
  if i = k then (if j = k then -1 else pivotWeight B green k j)
  else if i = j then 1 else 0

private theorem fin4 (i : Fin 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega

theorem mul_coefficientBasis_entry (B C : Matrix 4) (green : Fin 4 → Bool)
    (k i j : Fin 4) :
    mul C (coefficientBasis B green k) i j =
      if j = k then -C i k else C i j + C i k * pivotWeight B green k j := by
  rcases fin4 k with rfl | rfl | rfl | rfl <;>
    rcases fin4 j with rfl | rfl | rfl | rfl <;>
    simp [mul, coefficientBasis] <;> grind

theorem transpose_coefficientBasis_mul_entry (B A : Matrix 4)
    (green : Fin 4 → Bool) (k i j : Fin 4) :
    mul (transpose (coefficientBasis B green k)) A i j =
      if i = k then -A k j else A i j + pivotWeight B green k i * A k j := by
  rcases fin4 k with rfl | rfl | rfl | rfl <;>
    rcases fin4 i with rfl | rfl | rfl | rfl <;>
    simp [mul, coefficientBasis, transpose] <;> grind

/-- The entrywise and matrix forms of the simultaneous operation agree. -/
theorem localMutation_matrix (B A : Matrix 4) (green : Fin 4 → Bool)
    (k : Fin 4) :
    localMutation B A green k =
      mul (mul (transpose (coefficientBasis B green k)) A)
        (coefficientBasis B green k) := by
  funext i j
  rw [mul_coefficientBasis_entry]
  simp only [transpose_coefficientBasis_mul_entry]
  by_cases hi : i = k <;> by_cases hj : j = k <;>
    simp [localMutation, hi, hj] <;> grind

/-- The coefficient recurrence is the specified elementary matrix product.
Only the pivot column's sign is used; no all-word coherence is assumed. -/
theorem mutateCoefficients_matrix (B C : Matrix 4) (green : Fin 4 → Bool)
    (k : Fin 4)
    (hg : green k = true → ∀ i, 0 ≤ C i k)
    (hr : green k = false → ∀ i, C i k ≤ 0) :
    mutateCoefficients B C k = mul C (coefficientBasis B green k) := by
  funext i j
  rw [mul_coefficientBasis_entry]
  cases hk : green k
  · rw [mutateCoefficients_red B C k (hr hk)]
    simp [pivotWeight, hk]
    split <;> simp_all
  · rw [mutateCoefficients_green B C k (hg hk)]
    simp [pivotWeight, hk]
    split <;> simp_all

/-- Simultaneous companion recurrence follows algebraically from the actual
coefficient recurrence. It asserts no diagonal/absolute/admissibility facts. -/
theorem coefficientCompanion_mutation (B₀ B C : Matrix 4)
    (green : Fin 4 → Bool) (k : Fin 4)
    (hg : green k = true → ∀ i, 0 ≤ C i k)
    (hr : green k = false → ∀ i, C i k ≤ 0) :
    coefficientCompanion B₀ (mutateCoefficients B C k) =
      mul (mul (transpose (coefficientBasis B green k))
        (coefficientCompanion B₀ C)) (coefficientBasis B green k) := by
  rw [mutateCoefficients_matrix B C green k hg hr]
  simp only [coefficientCompanion, transpose_mul]
  simp only [mul_assoc]

theorem coefficientCompanion_mutation_local (B₀ B C : Matrix 4)
    (green : Fin 4 → Bool) (k : Fin 4)
    (hg : green k = true → ∀ i, 0 ≤ C i k)
    (hr : green k = false → ∀ i, C i k ≤ 0) :
    coefficientCompanion B₀ (mutateCoefficients B C k) =
      localMutation B (coefficientCompanion B₀ C) green k := by
  rw [localMutation_matrix]
  exact coefficientCompanion_mutation B₀ B C green k hg hr

/-- A simple oriented path has at most one positive companion entry.
This is Neville 2.26's second assertion, and is strictly additional data. -/
def OrientedPathConstraint {n : Nat} (B A : Matrix n) : Prop :=
  ∀ m : Nat, ∀ p : Fin (m + 1) → Fin n,
    (∀ a b, p a = p b → a = b) →
    (∀ a : Fin m, 0 < B (p a.castSucc) (p a.succ)) →
    ∀ a b : Fin m,
      0 < A (p a.castSucc) (p a.succ) →
      0 < A (p b.castSucc) (p b.succ) → a = b

theorem initialCompanion_orientedPathConstraint {n : Nat} (B : Matrix n)
    (hB : SkewSymmetric B) : OrientedPathConstraint B (initialCompanion B) := by
  intro m p _ he a b ha _
  have hb := he a
  have hne : p a.castSucc ≠ p a.succ := by
    intro hx
    rw [hx] at hb
    have := hB (p a.succ) (p a.succ)
    omega
  have hn := initialCompanion_offDiagonal_nonpos B (p a.castSucc) (p a.succ) hne
  omega

end QuiverProofs.MAExistenceCompanions
