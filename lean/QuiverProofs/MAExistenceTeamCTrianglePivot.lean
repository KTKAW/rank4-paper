import QuiverProofs.MAExistenceTeamBCompanionClosure
import QuiverProofs.MAExistenceCoefficients
import Mathlib.Tactic.LinearCombination

/-! Updated triangles containing the pivot. Current companion, arrow signs and
admissibility supply the next companion magnitudes. No next arrow signs or
triangle away from the pivot are assumed.
-/
namespace QuiverProofs.MAExistenceTeamCTrianglePivot
open MAExistenceLiterature MAExistenceCompanions MAExistenceAuxiliaryOrders
open MAExistenceTeamBCompanionClosure
open MAExistenceCoefficients
set_option maxHeartbeats 0

/-- For three nonzero entries, positive product is exactly odd positive parity. -/
private theorem positive_product_iff_odd (a b c : Int)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    0 < a * b * c ↔
      (decide (0 < a) ^^ decide (0 < b) ^^ decide (0 < c)) = true := by
  have hs : ∀ x : Int, x ≠ 0 → Int.sign x = if 0 < x then 1 else -1 := by
    intro x hx
    by_cases hp : 0 < x
    · simp only [hp, ↓reduceIte]
      exact Int.sign_eq_one_of_pos hp
    · simp only [hp, ↓reduceIte]
      exact Int.sign_eq_neg_one_of_neg (by omega)
  rw [← Int.sign_eq_one_iff_pos, Int.sign_mul, Int.sign_mul,
    hs a ha, hs b hb, hs c hc]
  by_cases hpa : 0 < a <;> by_cases hpb : 0 < b <;> by_cases hpc : 0 < c <;>
    simp [hpa, hpb, hpc]

/-- Triangle parity is invariant under cyclic relabelling, including zero edges. -/
private theorem triangleCompanionAdmissible_rotate (B A : Matrix 4) (i j l : Fin 4)
    (h : triangleCompanionAdmissible B A i j l) :
    triangleCompanionAdmissible B A j l i := by
  intro hjl hli hij
  have hc := h hij hjl hli
  have hxor : ∀ a b c : Bool, (a ^^ b ^^ c) = (b ^^ c ^^ a) := by decide
  rw [hxor] at hc
  constructor
  · intro hp
    rcases hc.mp hp with ⟨hij, hjl, hli⟩ | ⟨hij, hjl, hli⟩
    · exact Or.inl ⟨hjl, hli, hij⟩
    · exact Or.inr ⟨hjl, hli, hij⟩
  · intro hp
    apply hc.mpr
    rcases hp with ⟨hjl, hli, hij⟩ | ⟨hjl, hli, hij⟩
    · exact Or.inl ⟨hij, hjl, hli⟩
    · exact Or.inr ⟨hij, hjl, hli⟩

private theorem companion_nonzero (B A : Matrix 4)
    (hA : QuasiCartanCompanion B A) (i j : Fin 4) (hij : i ≠ j)
    (hb : B i j ≠ 0) : A i j ≠ 0 := by
  intro hz
  have hm := hA.2.2 i j hij
  rw [hz, Int.natAbs_zero] at hm
  exact hb (Int.natAbs_eq_zero.mp hm.symm)

private theorem correction_opposite_signs (x y : Int)
    (h : (0 < x ∧ y < 0) ∨ (x < 0 ∧ 0 < y)) : correction x y = 0 := by
  rcases h with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · have hx' : max x 0 = x := by omega
    have hy' : max y 0 = 0 := by omega
    have hnx : max (-x) 0 = 0 := by omega
    simp [correction, hx', hy', hnx]
  · have hx' : max x 0 = 0 := by omega
    have hy' : max y 0 = y := by omega
    have hny : max (-y) 0 = 0 := by omega
    simp [correction, hx', hy', hny]

private theorem localMutation_unmixed_triangle_product (B A : Matrix 4)
    (green : Colors) (k i j : Fin 4) (hik : i ≠ k) (hjk : j ≠ k)
    (hB : SkewSymmetric B) (hA : QuasiCartanCompanion B A)
    (hs : ArrowSigns B A green)
    (hm : pivotWeight B green k i = 0 ↔ pivotWeight B green k j = 0) :
    localMutation B A green k k i * localMutation B A green k i j *
        localMutation B A green k j k = A k i * A i j * A j k := by
  rw [localMutation_unmixed B A green k i j hik hjk hB hA hs hm]
  by_cases hi : pivotWeight B green k i = 0
  · have hj := hm.mp hi
    simp only [localMutation, hik, hjk, ↓reduceIte, hi, hj, Int.zero_mul,
      Int.sub_zero]
    ring
  · have hai : A i k = -pivotWeight B green k i :=
      (pivotWeight_companion B A green k i hik hB hA hs).resolve_left hi
    have hj : pivotWeight B green k j ≠ 0 := fun hz => hi (hm.mpr hz)
    have haj : A j k = -pivotWeight B green k j :=
      (pivotWeight_companion B A green k j hjk hB hA hs).resolve_left hj
    have hki : localMutation B A green k k i = A k i := by
      simp only [localMutation, hik, ↓reduceIte, hA.2.1 k]
      rw [hA.1 k i, hai]
      ring
    have hjk' : localMutation B A green k j k = A j k := by
      simp only [localMutation, hjk, ↓reduceIte, hA.2.1 k]
      rw [haj]
      ring
    rw [hki, hjk']

private theorem localMutation_same_side_triangle_product (B A : Matrix 4)
    (green : Colors) (k i j : Fin 4) (hik : i ≠ k) (hjk : j ≠ k)
    (hB : SkewSymmetric B) (hA : QuasiCartanCompanion B A)
    (hs : ArrowSigns B A green)
    (h : (0 < B i k ∧ B k j < 0) ∨ (B i k < 0 ∧ 0 < B k j)) :
    mutate B k i j = B i j ∧
    localMutation B A green k k i * localMutation B A green k i j *
        localMutation B A green k j k = A k i * A i j * A j k := by
  have hki := hB k i
  have hm : pivotWeight B green k i = 0 ↔ pivotWeight B green k j = 0 := by
    cases hk : green k <;>
      simp only [pivotWeight, hk, Bool.false_eq_true, ↓reduceIte] <;>
      rcases h with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> omega
  constructor
  · simp only [mutate, hik, hjk, or_self, ↓reduceIte,
      correction_opposite_signs _ _ h, Int.add_zero]
  · exact localMutation_unmixed_triangle_product B A green k i j hik hjk hB hA hs hm

private theorem square_of_natAbs_eq (u v : Int) (h : u.natAbs = v.natAbs) :
    u ^ 2 = v ^ 2 := by
  rcases Int.natAbs_eq_natAbs_iff.mp h with hh | hh
  · rw [hh]
  · rw [hh]
    ring

private theorem mixed_product_of_natAbs (x y z a c : Int) (hx : 0 < x)
    (ha : a.natAbs = z.natAbs) (hc : c.natAbs = y.natAbs)
    (hm : (a + x * c).natAbs = (z + x * y).natAbs) : a * c = z * y := by
  have ha2 := square_of_natAbs_eq a z ha
  have hc2 := square_of_natAbs_eq c y hc
  have hm2 := square_of_natAbs_eq _ _ hm
  have he : (2 * x) * (a * c - z * y) = 0 := by
    linear_combination hm2 - ha2 - x ^ 2 * hc2
  rcases mul_eq_zero.mp he with h | h
  · omega
  · omega

private theorem correction_pos (x y : Int) (hx : 0 < x) (hy : 0 < y) :
    correction x y = x * y := by
  have hx' : max x 0 = x := by omega
  have hy' : max y 0 = y := by omega
  have hnx : max (-x) 0 = 0 := by omega
  have hny : max (-y) 0 = 0 := by omega
  simp [correction, hx', hy', hnx, hny]

/-- The exact updated triangle product on an old directed path. Its proof uses
only the current and next companion magnitudes, without a next sign premise. -/
private theorem localMutation_path_triangle_product
    (B A : Matrix 4) (green : Colors) (k i j : Fin 4)
    (hB : SkewSymmetric B) (hA : QuasiCartanCompanion B A)
    (hs : ArrowSigns B A green)
    (hnew : QuasiCartanCompanion (mutate B k) (localMutation B A green k))
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hx : 0 < B i k) (hy : 0 < B k j) :
    localMutation B A green k k i * localMutation B A green k i j *
        localMutation B A green k j k = B i k * B k j * mutate B k i j := by
  have hki := hB k i
  have hmut : mutate B k i j = B i j + B i k * B k j := by
    simp [mutate, hik, hjk, correction_pos _ _ hx hy]
  have hm := hnew.2.2 i j hij
  rw [hmut] at hm
  cases hk : green k
  · have hti : pivotWeight B green k i = B i k := by
      simp only [pivotWeight, hk, Bool.false_eq_true, ↓reduceIte]
      omega
    have htj : pivotWeight B green k j = 0 := by
      simp only [pivotWeight, hk, Bool.false_eq_true, ↓reduceIte]
      omega
    have hai : A i k = -B i k := by
      rcases pivotWeight_companion B A green k i hik hB hA hs with hz | ha
      · rw [hti] at hz; omega
      · simpa only [hti] using ha
    simp only [localMutation, hik, hjk, ↓reduceIte, hti, htj,
      Int.zero_mul, Int.mul_zero, Int.add_zero] at hm
    have he := mixed_product_of_natAbs (B i k) (B k j) (B i j)
      (A i j) (A k j) hx (hA.2.2 i j hij) (hA.2.2 k j (Ne.symm hjk)) hm
    have hy2 := square_of_natAbs_eq (A k j) (B k j) (hA.2.2 k j (Ne.symm hjk))
    simp only [localMutation, hik, hjk, ↓reduceIte, hti, htj,
      Int.zero_mul, Int.mul_zero, Int.sub_zero, Int.add_zero, hA.2.1 k, hmut]
    rw [hA.1 k i, hA.1 j k, hai]
    linear_combination (B i k) * he + (B i k) ^ 2 * hy2
  · have hti : pivotWeight B green k i = 0 := by
      simp only [pivotWeight, hk, ↓reduceIte]
      omega
    have htj : pivotWeight B green k j = B k j := by
      simp only [pivotWeight, hk, ↓reduceIte]
      omega
    have haj : A k j = -B k j := by
      rw [hA.1 k j]
      rcases pivotWeight_companion B A green k j hjk hB hA hs with hz | ha
      · rw [htj] at hz; omega
      · simpa only [htj] using ha
    simp only [localMutation, hik, hjk, ↓reduceIte, hti, htj,
      Int.zero_mul, Int.add_zero] at hm
    have hm' : (A i j + B k j * A i k).natAbs =
        (B i j + B k j * B i k).natAbs := by
      simpa only [Int.mul_comm] using hm
    have he := mixed_product_of_natAbs (B k j) (B i k) (B i j)
      (A i j) (A i k) hy (hA.2.2 i j hij) (hA.2.2 i k hik) hm'
    have hx2 := square_of_natAbs_eq (A i k) (B i k) (hA.2.2 i k hik)
    simp only [localMutation, hik, hjk, ↓reduceIte, hti, htj,
      Int.zero_mul, Int.sub_zero, Int.add_zero, hA.2.1 k, hmut]
    rw [hA.1 k i, hA.1 j k, haj]
    linear_combination (B k j) * he + (B k j) ^ 2 * hx2

/-- Every updated triangle containing the pivot follows from current skew,
companion, arrow signs and admissibility alone. Next companion magnitudes are
proved from those current data; no next arrow signs or admissibility are assumed.
All ordered and repeated choices of the other vertices are allowed. -/
theorem localMutation_pivot_triangleAdmissible
    (B A : Matrix 4) (green : Colors) (k i j : Fin 4)
    (hB : SkewSymmetric B) (hA : QuasiCartanCompanion B A)
    (hs : ArrowSigns B A green) (ha : CompanionAdmissible4 B A) :
    triangleCompanionAdmissible (mutate B k) (localMutation B A green k) k i j := by
  intro hki hij hjk
  have hBn := mutation_preserves_skew B k hB
  have hik : i ≠ k := by intro he; subst i; have := hBn k k; omega
  have hjk' : j ≠ k := by intro he; subst j; have := hBn k k; omega
  have hij' : i ≠ j := by intro he; subst j; have := hBn i i; omega
  have hAn := localMutation_quasiCartan B A green k hB hA hs ha
  have han1 := companion_nonzero _ _ hAn k i (Ne.symm hik) hki
  have han2 := companion_nonzero _ _ hAn i j hij' hij
  have han3 := companion_nonzero _ _ hAn j k hjk' hjk
  rw [← positive_product_iff_odd _ _ _ han1 han2 han3]
  have hnk : mutate B k k i = B i k := by
    simp only [mutate, true_or, ↓reduceIte]; have := hB k i; omega
  have hnj : mutate B k j k = B k j := by
    simp only [mutate, or_true, ↓reduceIte]; have := hB j k; omega
  have hxz : B i k ≠ 0 := by rwa [hnk] at hki
  have hyz : B k j ≠ 0 := by rwa [hnj] at hjk
  by_cases hx : 0 < B i k
  · by_cases hy : 0 < B k j
    · rw [localMutation_path_triangle_product B A green k i j hB hA hs hAn hij' hik hjk' hx hy]
      have hxy := Int.mul_pos hx hy
      have he : 0 < B i k * B k j * mutate B k i j ↔ 0 < mutate B k i j := by
        constructor
        · intro hp
          by_contra hn
          have := Int.mul_nonpos_of_nonneg_of_nonpos (by omega : 0 ≤ B i k * B k j)
            (by omega : mutate B k i j ≤ 0)
          omega
        · exact fun h => Int.mul_pos hxy h
      rw [he, hnk, hnj]
      omega
    · have hyn : B k j < 0 := by omega
      have hp := localMutation_same_side_triangle_product B A green k i j
        hik hjk' hB hA hs (Or.inl ⟨hx, hyn⟩)
      have hbki : B k i ≠ 0 := by have := hB k i; omega
      have hbjk : B j k ≠ 0 := by have := hB j k; omega
      have hbij : B i j ≠ 0 := by rw [← hp.1]; exact hij
      have hc := companionAdmissible4_triangle B A hB hA.1 ha k i j
        (Ne.symm hik) (Ne.symm hjk') hij' hbki hbij hbjk
      rw [← positive_product_iff_odd _ _ _
        (companion_nonzero B A hA k i (Ne.symm hik) hbki)
        (companion_nonzero B A hA i j hij' hbij)
        (companion_nonzero B A hA j k hjk' hbjk)] at hc
      rw [hp.2, hnk, hnj]
      have hsk := hB k i
      have hsj := hB j k
      have hold : ¬(0 < A k i * A i j * A j k) := by
        intro hp
        rcases hc.mp hp with hh | hh <;> omega
      constructor <;> intro hh
      · exact False.elim (hold hh)
      · rcases hh with hh | hh <;> omega
  · have hxn : B i k < 0 := by omega
    by_cases hy : 0 < B k j
    · have hp := localMutation_same_side_triangle_product B A green k i j
        hik hjk' hB hA hs (Or.inr ⟨hxn, hy⟩)
      have hbki : B k i ≠ 0 := by have := hB k i; omega
      have hbjk : B j k ≠ 0 := by have := hB j k; omega
      have hbij : B i j ≠ 0 := by rw [← hp.1]; exact hij
      have hc := companionAdmissible4_triangle B A hB hA.1 ha k i j
        (Ne.symm hik) (Ne.symm hjk') hij' hbki hbij hbjk
      rw [← positive_product_iff_odd _ _ _
        (companion_nonzero B A hA k i (Ne.symm hik) hbki)
        (companion_nonzero B A hA i j hij' hbij)
        (companion_nonzero B A hA j k hjk' hbjk)] at hc
      rw [hp.2, hnk, hnj]
      have hsk := hB k i
      have hsj := hB j k
      have hold : ¬(0 < A k i * A i j * A j k) := by
        intro hp
        rcases hc.mp hp with hh | hh <;> omega
      constructor <;> intro hh
      · exact False.elim (hold hh)
      · rcases hh with hh | hh <;> omega
    · have hyn : B k j < 0 := by omega
      have hxj : 0 < B j k := by have := hB j k; omega
      have hyi : 0 < B k i := by have := hB k i; omega
      have hp := localMutation_path_triangle_product B A green k j i hB hA hs hAn
        (Ne.symm hij') hjk' hik hxj hyi
      have he : localMutation B A green k k i * localMutation B A green k i j *
          localMutation B A green k j k = localMutation B A green k k j *
            localMutation B A green k j i * localMutation B A green k i k := by
        rw [hAn.1 k i, hAn.1 k j, hAn.1 i j, hAn.1 i k, hAn.1 j k]
        ring
      rw [he, hp]
      have hxy := Int.mul_pos hxj hyi
      have he' : 0 < B j k * B k i * mutate B k j i ↔ 0 < mutate B k j i := by
        constructor
        · intro hp
          by_contra hn
          have := Int.mul_nonpos_of_nonneg_of_nonpos (by omega : 0 ≤ B j k * B k i)
            (by omega : mutate B k j i ≤ 0)
          omega
        · exact fun h => Int.mul_pos hxy h
      rw [he', hnk, hnj]
      have hnj' := hBn j i
      omega

/-- Arbitrary placement of the pivot within an ordered triple. -/
theorem localMutation_triangleAdmissible_of_contains_pivot
    (B A : Matrix 4) (green : Colors) (k i j l : Fin 4)
    (hB : SkewSymmetric B) (hA : QuasiCartanCompanion B A)
    (hs : ArrowSigns B A green) (ha : CompanionAdmissible4 B A)
    (hpivot : k = i ∨ k = j ∨ k = l) :
    triangleCompanionAdmissible (mutate B k) (localMutation B A green k) i j l := by
  rcases hpivot with hi | hj | hl
  · subst k
    exact localMutation_pivot_triangleAdmissible B A green i j l hB hA hs ha
  · subst k
    have h := localMutation_pivot_triangleAdmissible B A green j l i hB hA hs ha
    exact triangleCompanionAdmissible_rotate _ _ l i j
      (triangleCompanionAdmissible_rotate _ _ j l i h)
  · subst k
    exact triangleCompanionAdmissible_rotate _ _ l i j
      (localMutation_pivot_triangleAdmissible B A green l i j hB hA hs ha)

/-- The actual coefficient Gram companion version, using current strict
coherence solely for the exact Gram update identity. No future state premise is used. -/
theorem coefficientMutation_triangleAdmissible_of_contains_pivot
    (B₀ B C : Matrix 4) (k i j l : Fin 4)
    (hB : SkewSymmetric B)
    (hA : QuasiCartanCompanion B (coefficientCompanion B₀ C))
    (hs : ArrowSigns B (coefficientCompanion B₀ C) (columnColor C))
    (ha : CompanionAdmissible4 B (coefficientCompanion B₀ C))
    (hC : SignCoherent C)
    (hpivot : k = i ∨ k = j ∨ k = l) :
    triangleCompanionAdmissible (mutate B k)
      (coefficientCompanion B₀ (mutateCoefficients B C k)) i j l := by
  have hg : columnColor C k = true → ∀ i, 0 ≤ C i k :=
    fun h => ((color_iff_green hC k).mp h).1
  have hr : columnColor C k = false → ∀ i, C i k ≤ 0 :=
    fun h => ((color_iff_red hC k).mp h).1
  have he := coefficientCompanion_mutation_local B₀ B C (columnColor C) k hg hr
  rw [he]
  exact localMutation_triangleAdmissible_of_contains_pivot B _ _ k i j l
    hB hA hs ha hpivot

end QuiverProofs.MAExistenceTeamCTrianglePivot
