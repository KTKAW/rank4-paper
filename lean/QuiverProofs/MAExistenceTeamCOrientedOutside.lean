import QuiverProofs.MAExistenceTeamCTriangleOutside
import QuiverProofs.MAExistenceTeamDAdmissibility
import QuiverProofs.MAExistenceTeamDMutationSymmetry
import Mathlib.Tactic.LinearCombination

/-! Current-state closure for updated oriented triangles away from the pivot.

Mixed selected/unselected partitions use current triangle product identities;
the double-zero old-chord case uses current induced-square parity. Homogeneous
partitions reuse the reviewed unchanged-entry theorem. Red pivots reuse the
reviewed static exchange/color reversal APIs. Full transitive outside closure
is a separate obligation: the only output-state premise here is a directed
cycle, and no future arrow signs or admissibility are assumed.
-/
namespace QuiverProofs.MAExistenceTeamCOrientedOutside
open MAExistenceLiterature MAExistenceCompanions MAExistenceAuxiliaryOrders
open MAExistenceTeamBCompanionClosure MAExistenceTeamDAdmissibility
open MAExistenceTeamCTriangleOutside MAExistenceTeamDMutationSymmetry MAExistenceCoefficients
set_option maxHeartbeats 0

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

private theorem companion_zero (B A : Matrix 4) (hA : QuasiCartanCompanion B A)
    (i j : Fin 4) (hij : i ≠ j) (hz : B i j = 0) : A i j = 0 := by
  have hm := hA.2.2 i j hij
  rw [hz, Int.natAbs_zero] at hm
  exact Int.natAbs_eq_zero.mp hm

private theorem companion_nonzero (B A : Matrix 4) (hA : QuasiCartanCompanion B A)
    (i j : Fin 4) (hij : i ≠ j) (hb : B i j ≠ 0) : A i j ≠ 0 := by
  intro hz
  have hm := hA.2.2 i j hij
  rw [hz, Int.natAbs_zero] at hm
  exact hb (Int.natAbs_eq_zero.mp hm.symm)

private theorem square_of_natAbs_eq (u v : Int) (h : u.natAbs = v.natAbs) :
    u ^ 2 = v ^ 2 := by
  rcases Int.natAbs_eq_natAbs_iff.mp h with hh | hh
  · rw [hh]
  · rw [hh]; ring

private theorem triangle_product_of_path (B A : Matrix 4)
    (hB : SkewSymmetric B) (hA : QuasiCartanCompanion B A)
    (ha : CompanionAdmissible4 B A) (i j l : Fin 4)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (hx : 0 < B i j) (hy : 0 < B j l) :
    A i j * A j l * A l i = B i j * B j l * B l i := by
  by_cases hz : B l i = 0
  · rw [companion_zero B A hA l i (Ne.symm hil) hz, hz]
    simp
  have hc := companionAdmissible4_triangle B A hB hA.1 ha i j l hij hil hjl
    (by omega) (by omega) hz
  rw [← positive_product_iff_odd _ _ _
    (companion_nonzero B A hA i j hij (by omega))
    (companion_nonzero B A hA j l hjl (by omega))
    (companion_nonzero B A hA l i (Ne.symm hil) hz)] at hc
  have hsign : 0 < A i j * A j l * A l i ↔ 0 < B l i := by rw [hc]; omega
  have hn : (A i j * A j l * A l i).natAbs =
      (B i j * B j l * B l i).natAbs := by
    simp only [Int.natAbs_mul, hA.2.2 i j hij, hA.2.2 j l hjl,
      hA.2.2 l i (Ne.symm hil)]
  rcases Int.natAbs_eq_natAbs_iff.mp hn with he | he
  · exact he
  · by_cases hl : 0 < B l i
    · have hpp := hsign.mpr hl
      have hqq := Int.mul_pos (Int.mul_pos hx hy) hl
      rw [he] at hpp
      omega
    · have hln : B l i < 0 := by omega
      have hqq := Int.mul_neg_of_pos_of_neg (Int.mul_pos hx hy) hln
      have hpp : 0 < A i j * A j l * A l i := by rw [he]; omega
      have := hsign.mp hpp
      omega

private theorem cancel_product_right (a b c : Int) (hc : c ≠ 0)
    (h : a * c = b * c) : a = b := by
  have he : (a - b) * c = 0 := by linear_combination h
  rcases mul_eq_zero.mp he with he | he
  · omega
  · contradiction

private theorem selected_companion (B A : Matrix 4) (g : Colors) (k i : Fin 4)
    (hik : i ≠ k) (hB : SkewSymmetric B) (hA : QuasiCartanCompanion B A)
    (hs : ArrowSigns B A g) (hk : g k = true) (hi : 0 < B k i) :
    A k i = -B k i := by
  have hw : pivotWeight B g k i = B k i := by simp [pivotWeight, hk]; omega
  rw [hA.1 k i]
  rcases pivotWeight_companion B A g k i hik hB hA hs with hz | he
  · rw [hw] at hz; omega
  · simpa only [hw] using he

private theorem current_cross_one_selected (B A : Matrix 4) (g : Colors)
    (k i j : Fin 4) (hik : i ≠ k) (hjk : j ≠ k) (hij : i ≠ j)
    (hB : SkewSymmetric B) (hA : QuasiCartanCompanion B A)
    (hs : ArrowSigns B A g) (ha : CompanionAdmissible4 B A)
    (hk : g k = true) (hy : 0 < B k i) (hx : 0 ≤ B j k) :
    A i j * A j k = -B i j * B j k := by
  by_cases hz : B j k = 0
  · rw [companion_zero B A hA j k hjk hz, hz]; simp
  have hx' : 0 < B j k := by omega
  have hp := triangle_product_of_path B A hB hA ha j k i hjk (Ne.symm hij)
    (Ne.symm hik) hx' hy
  have hai := selected_companion B A g k i hik hB hA hs hk hy
  have he : (A i j * A j k) * B k i = (-B i j * B j k) * B k i := by
    rw [hai] at hp
    linear_combination -hp
  exact cancel_product_right _ _ _ (by omega) he

private theorem negative_product_iff_odd_four (a b c d : Int)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) :
    a * b * c * d < 0 ↔
      (decide (0 < a) ^^ decide (0 < b) ^^ decide (0 < c) ^^ decide (0 < d)) = true := by
  have hs : ∀ x : Int, x ≠ 0 → Int.sign x = if 0 < x then 1 else -1 := by
    intro x hx
    by_cases hp : 0 < x
    · simp only [hp, ↓reduceIte]; exact Int.sign_eq_one_of_pos hp
    · simp only [hp, ↓reduceIte]; exact Int.sign_eq_neg_one_of_neg (by omega)
  rw [← Int.sign_eq_neg_one_iff_neg, Int.sign_mul, Int.sign_mul, Int.sign_mul,
    hs a ha, hs b hb, hs c hc, hs d hd]
  by_cases hpa : 0 < a <;> by_cases hpb : 0 < b <;> by_cases hpc : 0 < c <;>
    by_cases hpd : 0 < d <;> simp [hpa, hpb, hpc, hpd]

private theorem oriented_square_product (B A : Matrix 4)
    (hB : SkewSymmetric B) (hA : QuasiCartanCompanion B A)
    (ha : CompanionAdmissible4 B A) (k i j l : Fin 4)
    (hik : i ≠ k) (hjk : j ≠ k) (hlk : l ≠ k)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (hki : 0 < B k i) (hijB : 0 < B i j) (hjlB : 0 < B j l) (hlkB : 0 < B l k)
    (hkj : B k j = 0) (hilB : B i l = 0) :
    A k i * A i j * A j l * A l k = - (B k i * B i j * B j l * B l k) := by
  have hp := (companionAdmissible4_square B A hB hA.1 ha k i j l
    (Ne.symm hik) (Ne.symm hjk) (Ne.symm hlk) hij hil hjl
    (by omega) (by omega) (by omega) (by omega) hkj hilB).mpr
    (Or.inl ⟨hki, hijB, hjlB, hlkB⟩)
  have hn := (negative_product_iff_odd_four _ _ _ _
    (companion_nonzero B A hA k i (Ne.symm hik) (by omega))
    (companion_nonzero B A hA i j hij (by omega))
    (companion_nonzero B A hA j l hjl (by omega))
    (companion_nonzero B A hA l k hlk (by omega))).mpr hp
  have habs : (A k i * A i j * A j l * A l k).natAbs =
      (B k i * B i j * B j l * B l k).natAbs := by
    simp only [Int.natAbs_mul, hA.2.2 k i (Ne.symm hik), hA.2.2 i j hij,
      hA.2.2 j l hjl, hA.2.2 l k hlk]
  rcases Int.natAbs_eq_natAbs_iff.mp habs with he | he
  · have hpB := Int.mul_pos (Int.mul_pos (Int.mul_pos hki hijB) hjlB) hlkB
    omega
  · exact he

/-- The second mixed term. If the old closing edge and the unselected
pivot edge both vanish, the current induced oriented square supplies its sign. -/
private theorem third_product_one_selected (B A : Matrix 4) (g : Colors)
    (k i j l : Fin 4) (hik : i ≠ k) (hjk : j ≠ k) (hlk : l ≠ k)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (hB : SkewSymmetric B) (hA : QuasiCartanCompanion B A)
    (hs : ArrowSigns B A g) (ha : CompanionAdmissible4 B A)
    (hk : g k = true) (hy : 0 < B k i) (hx : 0 ≤ B j k) (hu : 0 ≤ B l k)
    (hb : 0 < B i j) (hc : 0 < B j l) :
    A i j * A j l * A l k = B i j * B j l * B l k := by
  by_cases hz : B l k = 0
  · rw [companion_zero B A hA l k hlk hz, hz]; simp
  have hu' : 0 < B l k := by omega
  have hout := triangle_product_of_path B A hB hA ha i j l hij hil hjl hb hc
  by_cases hd : B l i = 0
  · by_cases hx0 : B j k = 0
    · have hkj : B k j = 0 := by have := hB k j; omega
      have hilB : B i l = 0 := by have := hB i l; omega
      have hquad := oriented_square_product B A hB hA ha k i j l
        hik hjk hlk hij hil hjl hy hb hc hu' hkj hilB
      rw [selected_companion B A g k i hik hB hA hs hk hy] at hquad
      apply cancel_product_right _ _ _ (by omega : B k i ≠ 0)
      linear_combination -hquad
    · have hx' : 0 < B j k := by omega
      have hcross := current_cross_one_selected B A g k i j hik hjk hij hB hA hs ha hk hy hx
      have htri := triangle_product_of_path B A hB hA ha j l k hjl hjk hlk hc hu'
      have hkj : B k j = -B j k := hB k j
      rw [hA.1 k j, hkj] at htri
      have hsquare := square_of_natAbs_eq (A j k) (B j k) (hA.2.2 j k hjk)
      have he : (A i j * A j l * A l k - B i j * B j l * B l k) * (B j k) ^ 2 = 0 := by
        linear_combination (A j l * A l k * A j k) * hcross -
          (B i j * B j k) * htri - (A i j * A j l * A l k) * hsquare
      rcases mul_eq_zero.mp he with he | he
      · omega
      · have : 0 < (B j k) ^ 2 := by positivity
        omega
  · have hcross := current_cross_one_selected B A g k i l hik hlk hil hB hA hs ha hk hy hu
    have hclose : A l i * A l k = B l i * B l k := by
      rw [hA.1 l i]
      rw [hB i l] at hcross
      simpa only [Int.neg_neg] using hcross
    have hsquare := square_of_natAbs_eq (A l i) (B l i) (hA.2.2 l i (Ne.symm hil))
    have he : (A i j * A j l * A l k - B i j * B j l * B l k) * (B l i) ^ 2 = 0 := by
      linear_combination (A l i * A l k) * hout +
        (B i j * B j l * B l i) * hclose - (A i j * A j l * A l k) * hsquare
    rcases mul_eq_zero.mp he with he | he
    · omega
    · have : (B l i) ^ 2 ≠ 0 := pow_ne_zero _ hd
      contradiction

private theorem correction_nonnegative (x y : Int) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    correction x y = x * y := by
  have hx' : max x 0 = x := by omega
  have hy' : max y 0 = y := by omega
  have hnx : max (-x) 0 = 0 := by omega
  have hny : max (-y) 0 = 0 := by omega
  simp [correction, hx', hy', hnx, hny]

private theorem correction_nonpositive (x y : Int) (hx : x ≤ 0) (hy : y ≤ 0) :
    correction x y = -(x * y) := by
  have hx' : max x 0 = 0 := by omega
  have hy' : max y 0 = 0 := by omega
  have hnx : max (-x) 0 = -x := by omega
  have hny : max (-y) 0 = -y := by omega
  simp [correction, hx', hy', hnx, hny]

/-- One selected vertex. The decreasing output edge retains its old positive
orientation, giving a current outside path and an exact product identity. -/
private theorem one_selected_product (B A : Matrix 4) (g : Colors)
    (k i j l : Fin 4) (hik : i ≠ k) (hjk : j ≠ k) (hlk : l ≠ k)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (hB : SkewSymmetric B) (hA : QuasiCartanCompanion B A)
    (hs : ArrowSigns B A g) (ha : CompanionAdmissible4 B A)
    (hk : g k = true) (hy : 0 < B k i) (hx : 0 ≤ B j k) (hu : 0 ≤ B l k)
    (hb : 0 < mutate B k i j) (hc : 0 < mutate B k j l) :
    localMutation B A g k i j * localMutation B A g k j l *
      localMutation B A g k l i = mutate B k i j * mutate B k j l * mutate B k l i := by
  have hjki := hB k j
  have hlki := hB k l
  have hBji : mutate B k i j = B i j - B k i * B j k := by
    simp only [mutate, hik, hjk, or_self, ↓reduceIte]
    rw [hB i k, hjki, correction_nonpositive _ _ (by omega) (by omega)]
    ring
  have hBjl : mutate B k j l = B j l := by
    have hm : pivotWeight B g k j = 0 ↔ pivotWeight B g k l = 0 := by
      simp only [pivotWeight, hk, ↓reduceIte]; omega
    exact (nonincident_entries_unchanged_of_unmixed_weights B A g k j l hjk hlk hB hA hs hm).1
  have hBli : mutate B k l i = B l i + B k i * B l k := by
    simp only [mutate, hlk, hik, or_self, ↓reduceIte]
    rw [correction_nonnegative _ _ hu (by omega)]
    ring
  have hbo : 0 < B i j := by
    have hn := Int.mul_nonneg (by omega : 0 ≤ B k i) hx
    rw [hBji] at hb
    omega
  have hco : 0 < B j l := by rwa [hBjl] at hc
  have hti : pivotWeight B g k i = B k i := by simp [pivotWeight, hk]; omega
  have htj : pivotWeight B g k j = 0 := by simp only [pivotWeight, hk, ↓reduceIte]; omega
  have htl : pivotWeight B g k l = 0 := by simp only [pivotWeight, hk, ↓reduceIte]; omega
  have hcross := current_cross_one_selected B A g k i j hik hjk hij hB hA hs ha hk hy hx
  have hthird := third_product_one_selected B A g k i j l hik hjk hlk hij hil hjl
    hB hA hs ha hk hy hx hu hbo hco
  have hout := triangle_product_of_path B A hB hA ha i j l hij hil hjl hbo hco
  have hsquare := square_of_natAbs_eq (A i j) (B i j) (hA.2.2 i j hij)
  have he : (A i j + B k i * A j k) * A i j = B i j * (B i j - B k i * B j k) := by
    linear_combination hsquare + (B k i) * hcross
  have ht : A i j * A j l * (A l i + B k i * A l k) =
      B i j * B j l * (B l i + B k i * B l k) := by
    linear_combination hout + (B k i) * hthird
  have hcancel : (B i j) ^ 2 * ((A i j + B k i * A j k) * A j l *
      (A l i + B k i * A l k)) = (B i j) ^ 2 *
      ((B i j - B k i * B j k) * B j l * (B l i + B k i * B l k)) := by
    calc
      _ = ((A i j + B k i * A j k) * A i j) *
          (A i j * A j l * (A l i + B k i * A l k)) := by rw [← hsquare]; ring
      _ = _ := by rw [he, ht]; ring
  have hfinal := cancel_product_right _ _ _ (pow_ne_zero _ (by omega : B i j ≠ 0))
    (by simpa only [Int.mul_comm] using hcancel)
  simp only [localMutation, hik, hjk, hlk, ↓reduceIte, hti, htj, htl,
    Int.zero_mul, Int.mul_zero, Int.add_zero, hBji, hBjl, hBli]
  rw [hA.1 k j]
  convert hfinal using 1 <;> ring

/-- Two selected vertices. Their unchanged edge has negative companion entry;
three current triangle equations give the two mixed terms and constant term. -/
private theorem two_selected_product (B A : Matrix 4) (g : Colors)
    (k i j l : Fin 4) (hik : i ≠ k) (hjk : j ≠ k) (hlk : l ≠ k)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (hB : SkewSymmetric B) (hA : QuasiCartanCompanion B A)
    (hs : ArrowSigns B A g) (ha : CompanionAdmissible4 B A)
    (hk : g k = true) (hy : 0 ≤ B i k) (hx : 0 < B k j) (hu : 0 < B k l)
    (hc : 0 < mutate B k j l) (hd : 0 < mutate B k l i) :
    localMutation B A g k i j * localMutation B A g k j l *
      localMutation B A g k l i = mutate B k i j * mutate B k j l * mutate B k l i := by
  have hti : pivotWeight B g k i = 0 := by
    simp only [pivotWeight, hk, ↓reduceIte]; have := hB k i; omega
  have htj : pivotWeight B g k j = B k j := by simp [pivotWeight, hk]; omega
  have htl : pivotWeight B g k l = B k l := by simp [pivotWeight, hk]; omega
  have hm : pivotWeight B g k j = 0 ↔ pivotWeight B g k l = 0 := by
    rw [htj, htl]; omega
  have hsame := nonincident_entries_unchanged_of_unmixed_weights B A g k j l hjk hlk hB hA hs hm
  have hBji : mutate B k i j = B i j + B i k * B k j := by
    simp only [mutate, hik, hjk, or_self, ↓reduceIte]
    rw [correction_nonnegative _ _ hy (by omega)]
  have hBli : mutate B k l i = B l i - B i k * B k l := by
    simp only [mutate, hlk, hik, or_self, ↓reduceIte]
    rw [hB l k, hB k i, correction_nonpositive _ _ (by omega) (by omega)]
    ring
  have hco : 0 < B j l := by rwa [hsame.1] at hc
  have hdo : 0 < B l i := by
    have hn := Int.mul_nonneg hy (by omega : 0 ≤ B k l)
    rw [hBli] at hd
    omega
  have hjcomp := selected_companion B A g k j hjk hB hA hs hk hx
  have hlcomp := selected_companion B A g k l hlk hB hA hs hk hu
  have htri := triangle_product_of_path B A hB hA ha k j l (Ne.symm hjk)
    (Ne.symm hlk) hjl hx hco
  rw [hjcomp, hA.1 l k, hlcomp, hB l k] at htri
  have hjlcomp : A j l = -B j l := by
    apply cancel_product_right _ _ _ (by exact ne_of_gt (Int.mul_pos hx hu) : B k j * B k l ≠ 0)
    linear_combination htri
  have hout := triangle_product_of_path B A hB hA ha j l i hjl (Ne.symm hij)
    (Ne.symm hil) hco hdo
  rw [hjlcomp] at hout
  have hpair : A i j * A l i = -B i j * B l i := by
    apply cancel_product_right _ _ _ (by omega : B j l ≠ 0)
    linear_combination -hout
  have hcrossj := current_cross_one_selected B A g k j i hjk hik (Ne.symm hij)
    hB hA hs ha hk hx hy
  rw [hA.1 j i, hB j i] at hcrossj
  simp only [Int.neg_neg] at hcrossj
  have hcrossl := current_cross_one_selected B A g k l i hlk hik (Ne.symm hil)
    hB hA hs ha hk hu hy
  have hsquare := square_of_natAbs_eq (A i k) (B i k) (hA.2.2 i k hik)
  rw [hsame.2, hjlcomp, hsame.1, hBji, hBli]
  simp only [localMutation, hik, hjk, hlk, ↓reduceIte, hti, htj, htl,
    Int.zero_mul, Int.mul_zero, Int.add_zero]
  rw [hA.1 k i]
  linear_combination -(B j l) * hpair - (B j l * B k l) * hcrossj -
    (B j l * B k j) * hcrossl - (B j l * B k j * B k l) * hsquare

private theorem homogeneous_cycle_product (B A : Matrix 4) (g : Colors)
    (k i j l : Fin 4) (hik : i ≠ k) (hjk : j ≠ k) (hlk : l ≠ k)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (hB : SkewSymmetric B) (hA : QuasiCartanCompanion B A)
    (hs : ArrowSigns B A g) (ha : CompanionAdmissible4 B A)
    (hwij : pivotWeight B g k i = 0 ↔ pivotWeight B g k j = 0)
    (hwjl : pivotWeight B g k j = 0 ↔ pivotWeight B g k l = 0)
    (hb : 0 < mutate B k i j) (hc : 0 < mutate B k j l) :
    localMutation B A g k i j * localMutation B A g k j l *
      localMutation B A g k l i = mutate B k i j * mutate B k j l * mutate B k l i := by
  have he1 := nonincident_entries_unchanged_of_unmixed_weights B A g k i j
    hik hjk hB hA hs hwij
  have he2 := nonincident_entries_unchanged_of_unmixed_weights B A g k j l
    hjk hlk hB hA hs hwjl
  have he3 := nonincident_entries_unchanged_of_unmixed_weights B A g k l i
    hlk hik hB hA hs (hwij.trans hwjl).symm
  rw [he1.1] at hb
  rw [he2.1] at hc
  rw [he1.1, he1.2, he2.1, he2.2, he3.1, he3.2]
  exact triangle_product_of_path B A hB hA ha i j l hij hil hjl hb hc

private theorem green_positive_cycle_product (B A : Matrix 4) (g : Colors)
    (k i j l : Fin 4) (hik : i ≠ k) (hjk : j ≠ k) (hlk : l ≠ k)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (hB : SkewSymmetric B) (hA : QuasiCartanCompanion B A)
    (hs : ArrowSigns B A g) (ha : CompanionAdmissible4 B A)
    (hk : g k = true)
    (hb : 0 < mutate B k i j) (hc : 0 < mutate B k j l) (hd : 0 < mutate B k l i) :
    localMutation B A g k i j * localMutation B A g k j l *
      localMutation B A g k l i = mutate B k i j * mutate B k j l * mutate B k l i := by
  have hbi := hB i k
  have hbj := hB j k
  have hbl := hB l k
  by_cases hi : 0 < B k i <;> by_cases hj : 0 < B k j <;> by_cases hl : 0 < B k l
  · apply homogeneous_cycle_product B A g k i j l hik hjk hlk hij hil hjl hB hA hs ha
      (by simp only [pivotWeight, hk, ↓reduceIte]; omega)
      (by simp only [pivotWeight, hk, ↓reduceIte]; omega) hb hc
  · have hp := two_selected_product B A g k l i j hlk hik hjk (Ne.symm hil)
      (Ne.symm hjl) hij hB hA hs ha hk (by omega) hi hj hb hc
    simpa only [Int.mul_comm, Int.mul_assoc, Int.mul_left_comm] using hp
  · have hp := two_selected_product B A g k j l i hjk hlk hik hjl
      (Ne.symm hij) (Ne.symm hil) hB hA hs ha hk (by omega) hl hi hd hb
    simpa only [Int.mul_comm, Int.mul_assoc, Int.mul_left_comm] using hp
  · exact one_selected_product B A g k i j l hik hjk hlk hij hil hjl
      hB hA hs ha hk hi (by omega) (by omega) hb hc
  · exact two_selected_product B A g k i j l hik hjk hlk hij hil hjl
      hB hA hs ha hk (by omega) hj hl hc hd
  · have hp := one_selected_product B A g k j l i hjk hlk hik hjl
      (Ne.symm hij) (Ne.symm hil) hB hA hs ha hk hj (by omega) (by omega) hc hd
    simpa only [Int.mul_comm, Int.mul_assoc, Int.mul_left_comm] using hp
  · have hp := one_selected_product B A g k l i j hlk hik hjk (Ne.symm hil)
      (Ne.symm hjl) hij hB hA hs ha hk hl (by omega) (by omega) hd hb
    simpa only [Int.mul_comm, Int.mul_assoc, Int.mul_left_comm] using hp
  · apply homogeneous_cycle_product B A g k i j l hik hjk hlk hij hil hjl hB hA hs ha
      (by simp only [pivotWeight, hk, ↓reduceIte]; omega)
      (by simp only [pivotWeight, hk, ↓reduceIte]; omega) hb hc

/-- An updated directed outside cycle has exactly its positive exchange
product as companion product, from current data alone. -/
theorem localMutation_positive_outside_cycle_product (B A : Matrix 4) (g : Colors)
    (k i j l : Fin 4) (hik : i ≠ k) (hjk : j ≠ k) (hlk : l ≠ k)
    (hB : SkewSymmetric B) (hA : QuasiCartanCompanion B A)
    (hs : ArrowSigns B A g) (ha : CompanionAdmissible4 B A)
    (hb : 0 < mutate B k i j) (hc : 0 < mutate B k j l) (hd : 0 < mutate B k l i) :
    localMutation B A g k i j * localMutation B A g k j l *
      localMutation B A g k l i = mutate B k i j * mutate B k j l * mutate B k l i := by
  have hBn := mutation_preserves_skew B k hB
  have hij : i ≠ j := by intro he; subst j; have := hBn i i; omega
  have hil : i ≠ l := by intro he; subst l; have := hBn i i; omega
  have hjl : j ≠ l := by intro he; subst l; have := hBn j j; omega
  cases hk : g k
  · have hpos1 : 0 < mutate (negMatrix B) k i l := by
      rw [mutate_negMatrix]
      change 0 < -mutate B k i l
      have := hBn i l
      omega
    have hpos2 : 0 < mutate (negMatrix B) k l j := by
      rw [mutate_negMatrix]
      change 0 < -mutate B k l j
      have := hBn l j
      omega
    have hpos3 : 0 < mutate (negMatrix B) k j i := by
      rw [mutate_negMatrix]
      change 0 < -mutate B k j i
      have := hBn j i
      omega
    have he := green_positive_cycle_product (negMatrix B) A (fun a => !g a)
      k i l j hik hlk hjk hil hij (Ne.symm hjl)
      (negMatrix_skew B hB) (quasiCartan_negMatrix B A hA)
      (arrowSigns_negMatrix B A g hB hA.1 hs) (companionAdmissible4_negMatrix B A ha)
      (by simp [hk]) hpos1 hpos2 hpos3
    rw [localMutation_negMatrix, mutate_negMatrix] at he
    simp only [negMatrix] at he
    have hAn := localMutation_symmetric B A g k hA.1
    rw [hAn i l, hAn l j, hAn j i] at he
    rw [hBn i l, hBn l j, hBn j i] at he
    simp only [Int.neg_neg] at he
    simpa only [Int.mul_comm, Int.mul_assoc, Int.mul_left_comm] using he
  · exact green_positive_cycle_product B A g k i j l hik hjk hlk hij hil hjl
      hB hA hs ha hk hb hc hd

/-- Every updated oriented triangle away from the pivot is admissible.
The directed-cycle condition is the only output-state hypothesis. -/
theorem localMutation_oriented_outside_triangleAdmissible
    (B A : Matrix 4) (g : Colors) (k i j l : Fin 4)
    (hik : i ≠ k) (hjk : j ≠ k) (hlk : l ≠ k)
    (hB : SkewSymmetric B) (hA : QuasiCartanCompanion B A)
    (hs : ArrowSigns B A g) (ha : CompanionAdmissible4 B A)
    (hcycle : (0 < mutate B k i j ∧ 0 < mutate B k j l ∧ 0 < mutate B k l i) ∨
      (mutate B k i j < 0 ∧ mutate B k j l < 0 ∧ mutate B k l i < 0)) :
    triangleCompanionAdmissible (mutate B k) (localMutation B A g k) i j l := by
  have hp : 0 < localMutation B A g k i j * localMutation B A g k j l *
      localMutation B A g k l i := by
    rcases hcycle with ⟨hb, hc, hd⟩ | ⟨hb, hc, hd⟩
    · rw [localMutation_positive_outside_cycle_product B A g k i j l hik hjk hlk
        hB hA hs ha hb hc hd]
      exact Int.mul_pos (Int.mul_pos hb hc) hd
    · have hBn := mutation_preserves_skew B k hB
      have hpos1 : 0 < mutate B k i l := by have := hBn i l; omega
      have hpos2 : 0 < mutate B k l j := by have := hBn l j; omega
      have hpos3 : 0 < mutate B k j i := by have := hBn j i; omega
      have he := localMutation_positive_outside_cycle_product B A g k i l j hik hlk hjk
        hB hA hs ha hpos1 hpos2 hpos3
      have hAn := localMutation_symmetric B A g k hA.1
      rw [hAn i l, hAn l j, hAn j i] at he
      have hpp := Int.mul_pos (Int.mul_pos hpos1 hpos2) hpos3
      have he' : localMutation B A g k i j * localMutation B A g k j l *
          localMutation B A g k l i = mutate B k i l * mutate B k l j * mutate B k j i := by
        simpa only [Int.mul_comm, Int.mul_assoc, Int.mul_left_comm] using he
      rwa [he']
  have hn1 : localMutation B A g k i j ≠ 0 := by intro hz; rw [hz] at hp; simp at hp
  have hn2 : localMutation B A g k j l ≠ 0 := by intro hz; rw [hz] at hp; simp at hp
  have hn3 : localMutation B A g k l i ≠ 0 := by intro hz; rw [hz] at hp; simp at hp
  intro _ _ _
  exact ⟨fun _ => hcycle, fun _ => (positive_product_iff_odd _ _ _ hn1 hn2 hn3).mp hp⟩

/-- Actual updated Gram companion version, using current sign coherence for
the exact coefficient mutation identity. No next arrow signs are assumed. -/
theorem coefficientMutation_oriented_outside_triangleAdmissible
    (B₀ B C : Matrix 4) (k i j l : Fin 4)
    (hik : i ≠ k) (hjk : j ≠ k) (hlk : l ≠ k)
    (hB : SkewSymmetric B)
    (hA : QuasiCartanCompanion B (coefficientCompanion B₀ C))
    (hs : ArrowSigns B (coefficientCompanion B₀ C) (columnColor C))
    (ha : CompanionAdmissible4 B (coefficientCompanion B₀ C))
    (hC : SignCoherent C)
    (hcycle : (0 < mutate B k i j ∧ 0 < mutate B k j l ∧ 0 < mutate B k l i) ∨
      (mutate B k i j < 0 ∧ mutate B k j l < 0 ∧ mutate B k l i < 0)) :
    triangleCompanionAdmissible (mutate B k)
      (coefficientCompanion B₀ (mutateCoefficients B C k)) i j l := by
  have hg : columnColor C k = true → ∀ t, 0 ≤ C t k :=
    fun h => ((color_iff_green hC k).mp h).1
  have hr : columnColor C k = false → ∀ t, C t k ≤ 0 :=
    fun h => ((color_iff_red hC k).mp h).1
  rw [coefficientCompanion_mutation_local B₀ B C (columnColor C) k hg hr]
  exact localMutation_oriented_outside_triangleAdmissible B _ _ k i j l hik hjk hlk
    hB hA hs ha hcycle

end QuiverProofs.MAExistenceTeamCOrientedOutside
