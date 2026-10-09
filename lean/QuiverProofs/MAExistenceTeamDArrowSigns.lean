import QuiverProofs.MAExistenceTeamCRootSigns
import QuiverProofs.MAExistenceTeamBCompanionClosure

/-! Partial, noncircular actual companion arrow-sign preservation.

The incident law uses current real-root data through the independently proved
strict sign-coherence theorem. A complete mutation law is proved for
monochromatic current columns, including the actual first principal mutation.
The general nonincident law remains open; no future ArrowSigns or admissibility
premise is silently stored in these statements. Zero edges, disconnected
supports, singular matrices and arbitrary integer weights remain unrestricted.
-/
namespace QuiverProofs.MAExistenceTeamDArrowSigns
open MAExistenceLiterature MAExistenceCoefficients MAExistenceCompanions
open MAExistenceTeamBRootPositivity
set_option maxHeartbeats 0

theorem columnColor_mutation_zero_weight (B C : Matrix 4) (k j : Fin 4)
    (hC : SignCoherent C) (hjk : j ≠ k)
    (ht : pivotWeight B (columnColor C) k j = 0) :
    columnColor (mutateCoefficients B C k) j = columnColor C j := by
  have hg : columnColor C k = true → ∀ i, 0 ≤ C i k :=
    fun h => ((color_iff_green hC k).mp h).1
  have hr : columnColor C k = false → ∀ i, C i k ≤ 0 :=
    fun h => ((color_iff_red hC k).mp h).1
  have he := coefficientMutation_zero_weight B C (columnColor C) k j hjk hg hr ht
  unfold columnColor
  congr 1
  apply propext
  constructor
  · intro h i
    have hi := congrFun he i
    change mutateCoefficients B C k i j = C i j at hi
    rw [← hi]
    exact h i
  · intro h i
    have hi := congrFun he i
    change mutateCoefficients B C k i j = C i j at hi
    rw [hi]
    exact h i

private theorem companion_ne_zero (B A : Matrix 4)
    (hA : QuasiCartanCompanion B A) (i j : Fin 4) (hij : i ≠ j)
    (hb : B i j ≠ 0) : A i j ≠ 0 := by
  intro hz
  have h := hA.2.2 i j hij
  rw [hz, Int.natAbs_zero] at h
  exact hb (Int.natAbs_eq_zero.mp h.symm)

theorem localMutation_incident_arrowSigns (B A C : Matrix 4) (k : Fin 4)
    (hB : SkewSymmetric B) (hA : QuasiCartanCompanion B A)
    (hs : ArrowSigns B A (columnColor C)) (hC : SignCoherent C) :
    ∀ i j, i = k ∨ j = k → 0 < mutate B k i j →
      (0 < localMutation B A (columnColor C) k i j ↔
        columnColor (mutateCoefficients B C k) i = false ∧
        columnColor (mutateCoefficients B C k) j = true) := by
  have hp := pivot_color_flips B C k (hC k)
  intro i j hinc hb
  have hij : i ≠ j := by
    intro h; subst j
    have := mutation_preserves_skew B k hB i i
    omega
  rcases hinc with hi | hj
  · subst i
    have hjk : j ≠ k := Ne.symm hij
    have hn : B k j < 0 := by simpa [mutate] using hb
    have hrev : 0 < B j k := by have := hB j k; omega
    cases hk : columnColor C k
    · have ht : pivotWeight B (columnColor C) k j = -B k j := by
        simp only [pivotWeight, hk, Bool.false_eq_true, ↓reduceIte]
        omega
      have ha : A k j = B k j := by
        rcases pivotWeight_companion B A (columnColor C) k j hjk hB hA hs with hz | ha
        · rw [ht] at hz; omega
        · rw [hA.1 k j]
          rw [ht] at ha
          omega
      simp only [localMutation, if_true, hjk, if_false, hA.2.1 k, ht, hp, hk,
        Bool.not_false, Bool.true_eq_false, false_and, iff_false]
      omega
    · have ht : pivotWeight B (columnColor C) k j = 0 := by
        simp only [pivotWeight, hk, ↓reduceIte]
        omega
      have hc := columnColor_mutation_zero_weight B C k j hC hjk ht
      have ha := hs j k hrev
      rw [←hA.1 k j, hk] at ha
      have haz := companion_ne_zero B A hA k j hij (by omega)
      simp only [localMutation, if_true, hjk, if_false, hA.2.1 k, ht,
        Int.zero_mul, Int.sub_zero, hp, hk, Bool.not_true, hc,
        true_and]
      cases hj : columnColor C j <;> simp_all <;> omega
  · subst j
    have hik : i ≠ k := hij
    have hn : B i k < 0 := by simpa [mutate] using hb
    have hrev : 0 < B k i := by have := hB k i; omega
    cases hk : columnColor C k
    · have ht : pivotWeight B (columnColor C) k i = 0 := by
        simp only [pivotWeight, hk, Bool.false_eq_true, ↓reduceIte]
        omega
      have hc := columnColor_mutation_zero_weight B C k i hC hik ht
      have ha := hs k i hrev
      rw [hA.1 k i, hk] at ha
      have haz := companion_ne_zero B A hA i k hik (by omega)
      simp only [localMutation, hik, if_false, if_true, hA.2.1 k, ht,
        Int.zero_mul, Int.sub_zero, hp, hk, Bool.not_false, hc,
        and_true]
      cases hi : columnColor C i <;> simp_all <;> omega
    · have ht : pivotWeight B (columnColor C) k i = B k i := by
        simp only [pivotWeight, hk, ↓reduceIte]
        omega
      have ha : A i k = -B k i := by
        rcases pivotWeight_companion B A (columnColor C) k i hik hB hA hs with hz | ha
        · rw [ht] at hz; omega
        · simpa only [ht] using ha
      simp only [localMutation, hik, if_false, if_true, hA.2.1 k, ht, hp, hk,
        Bool.not_true, Bool.false_eq_true, and_false, iff_false]
      omega
end QuiverProofs.MAExistenceTeamDArrowSigns
namespace QuiverProofs.MAExistenceTeamDArrowSigns
open MAExistenceLiterature MAExistenceCoefficients MAExistenceCompanions

private theorem companion_offDiagonal_nonpos_of_same_color (B A C : Matrix 4)
    (hB : SkewSymmetric B) (hA : QuasiCartanCompanion B A)
    (hs : ArrowSigns B A (columnColor C)) (i j : Fin 4) (hij : i ≠ j)
    (hc : columnColor C i = columnColor C j) : A i j ≤ 0 := by
  by_cases hz : B i j = 0
  · have hh := hA.2.2 i j hij
    simp only [hz, Int.natAbs_zero] at hh
    have := Int.natAbs_eq_zero.mp hh
    omega
  · by_cases hp : 0 < B i j
    · have hh := hs i j hp
      rw [hc] at hh
      cases columnColor C j <;> simp_all
    · have hr : 0 < B j i := by have := hB j i; omega
      have hh := hs j i hr
      rw [←hc, ←hA.1 i j] at hh
      cases columnColor C i <;> simp_all

/-- A monochromatic current coefficient basis has the complete next arrow-sign
law. Strict coherence supplies the actual retained colors and flipped pivot;
no admissibility or future seed data is used. -/
theorem monochromatic_mutation_arrowSigns (B A C : Matrix 4) (k : Fin 4)
    (hB : SkewSymmetric B) (hA : QuasiCartanCompanion B A)
    (hs : ArrowSigns B A (columnColor C)) (hC : SignCoherent C)
    (hc : ∀ j, columnColor C j = columnColor C k) :
    ArrowSigns (mutate B k) (localMutation B A (columnColor C) k)
      (columnColor (mutateCoefficients B C k)) := by
  have hret : ∀ j, j ≠ k →
      columnColor (mutateCoefficients B C k) j = columnColor C k := by
    intro j hj
    cases hk : columnColor C k
    · have hkR := (color_iff_red hC k).mp hk
      have hjR := (color_iff_red hC j).mp ((hc j).trans hk)
      exact color_red (red_retained B C k j hj hkR hjR)
    · have hkG := (color_iff_green hC k).mp hk
      have hjG := (color_iff_green hC j).mp ((hc j).trans hk)
      exact color_green (green_retained B C k j hj hkG hjG)
  intro i j hb
  by_cases hik : i = k
  · exact localMutation_incident_arrowSigns B A C k hB hA hs hC i j (.inl hik) hb
  by_cases hjk : j = k
  · exact localMutation_incident_arrowSigns B A C k hB hA hs hC i j (.inr hjk) hb
  have hij : i ≠ j := by
    intro h; subst j
    have := mutation_preserves_skew B k hB i i
    omega
  have haij := companion_offDiagonal_nonpos_of_same_color B A C hB hA hs i j hij
    ((hc i).trans (hc j).symm)
  have hakj := companion_offDiagonal_nonpos_of_same_color B A C hB hA hs k j
    (Ne.symm hjk) (hc j).symm
  have haik := companion_offDiagonal_nonpos_of_same_color B A C hB hA hs i k hik (hc i)
  have hti : 0 ≤ pivotWeight B (columnColor C) k i := by unfold pivotWeight; omega
  have htj : 0 ≤ pivotWeight B (columnColor C) k j := by unfold pivotWeight; omega
  have hn : localMutation B A (columnColor C) k i j ≤ 0 := by
    by_cases hzero : pivotWeight B (columnColor C) k i = 0 ↔
        pivotWeight B (columnColor C) k j = 0
    · rw [localMutation_unmixed B A (columnColor C) k i j hik hjk hB hA hs hzero]
      exact haij
    · have hz : pivotWeight B (columnColor C) k i = 0 ∨
          pivotWeight B (columnColor C) k j = 0 := by
        by_cases hi : pivotWeight B (columnColor C) k i = 0
        · exact .inl hi
        · by_cases hj : pivotWeight B (columnColor C) k j = 0
          · exact .inr hj
          · exact False.elim (hzero (by simp [hi, hj]))
      simp only [localMutation, hik, hjk, if_false, hA.2.1 k]
      rcases hz with hi | hj
      · simp only [hi, Int.zero_mul]
        have := Int.mul_nonpos_of_nonneg_of_nonpos htj haik
        omega
      · simp only [hj, Int.zero_mul, Int.mul_zero, Int.add_zero]
        have := Int.mul_nonpos_of_nonneg_of_nonpos hti hakj
        omega
  rw [hret i hik, hret j hjk]
  cases columnColor C k <;> simp_all

/-- The actual first principal-coefficient mutation satisfies ArrowSigns for
all skew inputs, with no support or weight restrictions. -/
theorem firstMutation_arrowSigns (B₀ : Matrix 4) (hB₀ : SkewSymmetric B₀) (k : Fin 4) :
    ArrowSigns (mutate B₀ k)
      (coefficientCompanion B₀ (mutateCoefficients B₀ identityCoefficients k))
      (columnColor (mutateCoefficients B₀ identityCoefficients k)) := by
  have hc : columnColor (identityCoefficients : Matrix 4) = fun _ => true := by
    funext j
    exact color_green (identity_green j)
  have hgram : coefficientCompanion B₀ identityCoefficients = initialCompanion B₀ :=
    coefficientCompanion_initial B₀
  have hA : QuasiCartanCompanion B₀ (coefficientCompanion B₀ identityCoefficients) := by
    rw [hgram]
    exact initialCompanion_quasiCartan B₀ hB₀
  have hs : ArrowSigns B₀ (coefficientCompanion B₀ identityCoefficients)
      (columnColor identityCoefficients) := by
    rw [hgram, hc]
    exact initialCompanion_arrowSigns B₀ hB₀
  rw [coefficientCompanion_mutation_local B₀ B₀ identityCoefficients
    (columnColor identityCoefficients) k
    (fun _ => (identity_green k).1) (by simp [hc])]
  exact monochromatic_mutation_arrowSigns B₀ _ identityCoefficients k hB₀ hA hs
    identity_signCoherent (by intro j; rw [hc])

end QuiverProofs.MAExistenceTeamDArrowSigns

namespace QuiverProofs.MAExistenceTeamDArrowSigns
open MAExistenceLiterature MAExistenceCoefficients MAExistenceCompanions
open MAExistenceTeamBRootPositivity MAExistenceTeamCRootSigns

/-- Every arrow incident to the pivot has the actual next color law. Current
real-root membership independently supplies coherence; no next root, sign or
admissibility assertion is assumed. -/
theorem coefficientMutation_incident_arrowSigns (B₀ B C : Matrix 4)
    (hB₀ : SkewSymmetric B₀) (hB : SkewSymmetric B) (k : Fin 4)
    (hA : QuasiCartanCompanion B (coefficientCompanion B₀ C))
    (hs : ArrowSigns B (coefficientCompanion B₀ C) (columnColor C))
    (hroots : ∀ j, RealRoot (initialCompanion B₀) (column C j)) :
    ∀ i j, i = k ∨ j = k → 0 < mutate B k i j →
      (0 < coefficientCompanion B₀ (mutateCoefficients B C k) i j ↔
        columnColor (mutateCoefficients B C k) i = false ∧
        columnColor (mutateCoefficients B C k) j = true) := by
  have hC := realRootColumns_signCoherent B₀ C hB₀ hroots
  have hg : columnColor C k = true → ∀ i, 0 ≤ C i k :=
    fun h => ((color_iff_green hC k).mp h).1
  have hr : columnColor C k = false → ∀ i, C i k ≤ 0 :=
    fun h => ((color_iff_red hC k).mp h).1
  rw [coefficientCompanion_mutation_local B₀ B C (columnColor C) k hg hr]
  exact localMutation_incident_arrowSigns B _ C k hB hA hs hC
end QuiverProofs.MAExistenceTeamDArrowSigns

namespace QuiverProofs.MAExistenceTeamDArrowSigns
open MAExistenceLiterature MAExistenceCoefficients MAExistenceCompanions
open MAExistenceTeamBCompanionClosure MAExistenceAuxiliaryOrders
set_option maxHeartbeats 0

/-- In a red-green-red current path, a new arrow from the first red endpoint
has the required actual next sign exactly when the updated last column turns
green. This isolates a coefficient-color assertion, not a future sign premise. -/
theorem green_pivot_red_path_arrow_iff_flip (B A C : Matrix 4) (k i j : Fin 4)
    (hB : SkewSymmetric B) (hA : QuasiCartanCompanion B A)
    (hs : ArrowSigns B A (columnColor C)) (ha : CompanionAdmissible4 B A)
    (hC : SignCoherent C) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hk : columnColor C k = true) (hi : columnColor C i = false)
    (hj : columnColor C j = false) (hx : 0 < B i k) (hy : 0 < B k j)
    (hb' : 0 < mutate B k i j) :
    (0 < localMutation B A (columnColor C) k i j ↔
      columnColor (mutateCoefficients B C k) i = false ∧
      columnColor (mutateCoefficients B C k) j = true) ↔
        columnColor (mutateCoefficients B C k) j = true := by
  have hai : A i k = B i k := by
    have hp := (hs i k hx).mpr ⟨hi, hk⟩
    rcases Int.natAbs_eq_natAbs_iff.mp (hA.2.2 i k hik) with he | he
    · exact he
    · omega
  have htj : pivotWeight B (columnColor C) k j = B k j := by
    simp only [pivotWeight, hk, if_true]
    omega
  have hti : pivotWeight B (columnColor C) k i = 0 := by
    have := hB k i
    simp only [pivotWeight, hk, if_true]
    omega
  have haj : A k j = -B k j := by
    rcases pivotWeight_companion B A (columnColor C) k j hjk hB hA hs with he | he
    · rw [htj] at he; omega
    · rw [hA.1 k j]
      simpa only [htj] using he
  have han : A i j ≤ 0 := by
    by_cases hz : B i j = 0
    · have h := hA.2.2 i j hij
      simp only [hz, Int.natAbs_zero] at h
      have := Int.natAbs_eq_zero.mp h
      omega
    · by_cases hp : 0 < B i j
      · have h := hs i j hp
        simp only [hi, hj, Bool.false_eq_true, and_false, iff_false] at h
        omega
      · have hr : 0 < B j i := by have := hB j i; omega
        have h := hs j i hr
        rw [←hA.1 i j] at h
        simp only [hi, hj, Bool.false_eq_true, and_false, iff_false] at h
        omega
  have hbn : B i j ≤ 0 := by
    by_contra hn
    have hp : 0 < B i j := by omega
    have hap : A i j < 0 := by
      rcases Int.natAbs_eq_natAbs_iff.mp (hA.2.2 i j hij) with he | he <;> omega
    have hprod : 0 < A i j * A k j * A i k := by
      rw [haj, hai]
      exact Int.mul_pos (Int.mul_pos_of_neg_of_neg hap (by omega)) hx
    have htri := companionAdmissible4_trianglePathSigns B A hB hA ha
    have := (htri i j k hij hik hjk hx hy).mp hprod
    omega
  have haij : A i j = B i j := by
    rcases Int.natAbs_eq_natAbs_iff.mp (hA.2.2 i j hij) with he | he <;> omega
  have hcor : correction (B i k) (B k j) = B i k * B k j := by
    unfold correction
    rw [max_eq_left (by omega : 0 ≤ B i k), max_eq_left (by omega : 0 ≤ B k j),
      max_eq_right (by omega : -B i k ≤ 0), max_eq_right (by omega : -B k j ≤ 0)]
    simp
  have he : localMutation B A (columnColor C) k i j = mutate B k i j := by
    simp only [localMutation, mutate, hik, hjk, if_false, or_self, hti, htj,
      Int.zero_mul, Int.add_zero, hcor, haij, hai]
    rw [Int.mul_comm]
  have hc := columnColor_mutation_zero_weight B C k i hC hik hti
  rw [he, hc, hi]
  simp [hb']
end QuiverProofs.MAExistenceTeamDArrowSigns

namespace QuiverProofs.MAExistenceTeamDArrowSigns
open MAExistenceLiterature MAExistenceCoefficients MAExistenceCompanions
set_option maxHeartbeats 0

/-- For the green-green-red current path, a surviving reverse arrow has its
correct updated sign exactly when the last column stays red. -/
theorem green_pivot_green_red_path_arrow_iff_no_flip (B A C : Matrix 4)
    (k i j : Fin 4) (hB : SkewSymmetric B) (hA : QuasiCartanCompanion B A)
    (hs : ArrowSigns B A (columnColor C)) (hC : SignCoherent C)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hk : columnColor C k = true) (hi : columnColor C i = true)
    (hj : columnColor C j = false) (hx : 0 < B i k) (hy : 0 < B k j)
    (hb' : mutate B k i j < 0) :
    (0 < localMutation B A (columnColor C) k j i ↔
      columnColor (mutateCoefficients B C k) j = false ∧
      columnColor (mutateCoefficients B C k) i = true) ↔
        columnColor (mutateCoefficients B C k) j = false := by
  have hti : pivotWeight B (columnColor C) k i = 0 := by
    have := hB k i
    simp only [pivotWeight, hk, if_true]
    omega
  have htj : pivotWeight B (columnColor C) k j = B k j := by
    simp only [pivotWeight, hk, if_true]
    omega
  have hai : A i k = -B i k := by
    have hn : A i k ≤ 0 := by
      have h := hs i k hx
      simp only [hi, hk, Bool.true_eq_false, false_and, iff_false] at h
      omega
    rcases Int.natAbs_eq_natAbs_iff.mp (hA.2.2 i k hik) with he | he <;> omega
  have haij : A i j = -B i j := by
    by_cases hz : B i j = 0
    · have h := hA.2.2 i j hij
      simp only [hz, Int.natAbs_zero] at h
      have := Int.natAbs_eq_zero.mp h
      omega
    · by_cases hp : 0 < B i j
      · have hn : A i j ≤ 0 := by
          have h := hs i j hp
          simp only [hi, hj, Bool.true_eq_false, false_and, iff_false] at h
          omega
        rcases Int.natAbs_eq_natAbs_iff.mp (hA.2.2 i j hij) with he | he <;> omega
      · have hr : 0 < B j i := by have := hB j i; omega
        have hpos : 0 < A i j := by
          rw [hA.1 i j]
          exact (hs j i hr).mpr ⟨hj, hi⟩
        rcases Int.natAbs_eq_natAbs_iff.mp (hA.2.2 i j hij) with he | he <;> omega
  have hcor : correction (B i k) (B k j) = B i k * B k j := by
    unfold correction
    rw [max_eq_left (by omega : 0 ≤ B i k), max_eq_left (by omega : 0 ≤ B k j),
      max_eq_right (by omega : -B i k ≤ 0), max_eq_right (by omega : -B k j ≤ 0)]
    simp
  have he : localMutation B A (columnColor C) k i j = -(mutate B k i j) := by
    simp only [localMutation, mutate, hik, hjk, if_false, or_self, hti, htj,
      Int.zero_mul, Int.add_zero, hcor, haij, hai]
    grind
  have hc := columnColor_mutation_zero_weight B C k i hC hik hti
  rw [←localMutation_symmetric B A (columnColor C) k hA.1 i j, he, hc, hi]
  simp [hb']
end QuiverProofs.MAExistenceTeamDArrowSigns

namespace QuiverProofs.MAExistenceTeamDArrowSigns
open MAExistenceLiterature MAExistenceCoefficients MAExistenceCompanions
open MAExistenceTeamBRootPositivity MAExistenceTeamCRootSigns MAExistenceAuxiliaryOrders
set_option maxHeartbeats 0

/-- The exact red-green-red forced-flip reduction for an actual Gram companion.
Current roots supply coherence. No future sign or admissibility premise occurs. -/
theorem coefficientMutation_red_path_arrow_iff_flip (B₀ B C : Matrix 4)
    (hB₀ : SkewSymmetric B₀) (hB : SkewSymmetric B) (k i j : Fin 4)
    (hA : QuasiCartanCompanion B (coefficientCompanion B₀ C))
    (hs : ArrowSigns B (coefficientCompanion B₀ C) (columnColor C))
    (ha : CompanionAdmissible4 B (coefficientCompanion B₀ C))
    (hroots : ∀ j, RealRoot (initialCompanion B₀) (column C j))
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hk : columnColor C k = true) (hi : columnColor C i = false)
    (hj : columnColor C j = false) (hx : 0 < B i k) (hy : 0 < B k j)
    (hb' : 0 < mutate B k i j) :
    (0 < coefficientCompanion B₀ (mutateCoefficients B C k) i j ↔
      columnColor (mutateCoefficients B C k) i = false ∧
      columnColor (mutateCoefficients B C k) j = true) ↔
        columnColor (mutateCoefficients B C k) j = true := by
  have hC := realRootColumns_signCoherent B₀ C hB₀ hroots
  have hg : columnColor C k = true → ∀ i, 0 ≤ C i k :=
    fun h => ((color_iff_green hC k).mp h).1
  have hr : columnColor C k = false → ∀ i, C i k ≤ 0 :=
    fun h => ((color_iff_red hC k).mp h).1
  rw [coefficientCompanion_mutation_local B₀ B C (columnColor C) k hg hr]
  exact green_pivot_red_path_arrow_iff_flip B _ C k i j hB hA hs ha hC
    hij hik hjk hk hi hj hx hy hb'
end QuiverProofs.MAExistenceTeamDArrowSigns

namespace QuiverProofs.MAExistenceTeamDArrowSigns
open MAExistenceLiterature MAExistenceCoefficients MAExistenceCompanions
set_option maxHeartbeats 0

/-- Every nonincident pair whose two columns receive zero shear has the
complete next arrow law. Both actual colors and both edge entries are retained. -/
theorem zero_weight_pair_mutation_arrowSigns (B A C : Matrix 4) (k i j : Fin 4)
    (hB : SkewSymmetric B) (hA : QuasiCartanCompanion B A)
    (hs : ArrowSigns B A (columnColor C)) (hC : SignCoherent C)
    (hik : i ≠ k) (hjk : j ≠ k)
    (hti : pivotWeight B (columnColor C) k i = 0)
    (htj : pivotWeight B (columnColor C) k j = 0)
    (hb' : 0 < mutate B k i j) :
    0 < localMutation B A (columnColor C) k i j ↔
      columnColor (mutateCoefficients B C k) i = false ∧
      columnColor (mutateCoefficients B C k) j = true := by
  have hcor : correction (B i k) (B k j) = 0 := by
    have hb := hB k i
    cases hk : columnColor C k
    · simp only [pivotWeight, hk, Bool.false_eq_true, if_false] at hti htj
      have hx : B i k ≤ 0 := by omega
      have hy : -B k j ≤ 0 := by omega
      simp [correction, max_eq_right hx, max_eq_right hy]
    · simp only [pivotWeight, hk, if_true] at hti htj
      have hx : -B i k ≤ 0 := by omega
      have hy : B k j ≤ 0 := by omega
      simp [correction, max_eq_right hx, max_eq_right hy]
  have hex : mutate B k i j = B i j := by
    simp [mutate, hik, hjk, hcor]
  have he := localMutation_unmixed B A (columnColor C) k i j hik hjk hB hA hs
    (by simp [hti, htj])
  have hci := columnColor_mutation_zero_weight B C k i hC hik hti
  have hcj := columnColor_mutation_zero_weight B C k j hC hjk htj
  rw [he, hci, hcj]
  rw [hex] at hb'
  exact hs i j hb'
end QuiverProofs.MAExistenceTeamDArrowSigns
