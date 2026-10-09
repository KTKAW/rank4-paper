import QuiverProofs.MAExistenceTeamBCompanionClosure
import QuiverProofs.MAExistenceTeamDArrowSigns
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-! Rank-four companion parity interfaces and actual first-step admissibility.

The singleton theorem uses the actual identity-initialized coefficients and
handles arbitrary integer weights, zeros and cancellation. The generic local
converse and pivot law expose their current/next hypotheses. General actual
all-word preservation remains open: no future companion data is hidden in a
state predicate, and no unrestricted oriented-path assertion is assumed.
-/
namespace QuiverProofs.MAExistenceTeamDAdmissibility
open MAExistenceLiterature MAExistenceCompanions MAExistenceAuxiliaryOrders
open MAExistenceTeamBCompanionClosure
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Converse to the mixed scalar magnitude law. Cancellation is included. -/
theorem mixed_triangle_sign_of_natAbs (x y z a c : Int)
    (hx : 0 < x) (hy : 0 < y)
    (ha : a.natAbs = z.natAbs) (hc : c.natAbs = y.natAbs)
    (hm : (a + x * c).natAbs = (z + x * y).natAbs) :
    0 < a * c * (-x) ↔ z < 0 := by
  have hsquare : ∀ u v : Int, u.natAbs = v.natAbs → u ^ 2 = v ^ 2 := by
    intro u v huv
    rcases Int.natAbs_eq_natAbs_iff.mp huv with h | h
    · rw [h]
    · rw [h]
      grind
  have ha2 := hsquare a z ha
  have hc2 := hsquare c y hc
  have hm2 := hsquare _ _ hm
  have he : (2 * x) * (a * c - z * y) = 0 := by
    linear_combination hm2 - ha2 - x ^ 2 * hc2
  have hac : a * c = z * y := by
    rcases mul_eq_zero.mp he with h | h
    · nlinarith
    · omega
  rw [hac]
  constructor
  · intro hp
    by_contra hn
    have hz : 0 ≤ z := by omega
    have hzy : 0 ≤ z * y := Int.mul_nonneg hz (by omega)
    have hprod : z * y * (-x) ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos hzy (by omega)
    omega
  · intro hz
    exact Int.mul_pos_of_neg_of_neg (Int.mul_neg_of_neg_of_pos hz hy) (by omega)

private theorem correction_pos (x y : Int) (hx : 0 < x) (hy : 0 < y) :
    correction x y = x * y := by
  have hx' : max x 0 = x := by omega
  have hy' : max y 0 = y := by omega
  have hnx : max (-x) 0 = 0 := by omega
  have hny : max (-y) 0 = 0 := by omega
  simp [correction, hx', hy', hnx, hny]

/-- Necessity of the numerical triangle relation for an arbitrary mixed pair.
Only current signs and current/updated companion magnitudes are used. -/
theorem trianglePathSign_of_localMutation_quasiCartan
    (B A : Matrix 4) (green : Colors) (k i j : Fin 4)
    (hB : SkewSymmetric B) (hA : QuasiCartanCompanion B A)
    (hs : ArrowSigns B A green)
    (hnew : QuasiCartanCompanion (mutate B k) (localMutation B A green k))
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hx : 0 < B i k) (hy : 0 < B k j) :
    0 < A i j * A k j * A i k ↔ B i j < 0 := by
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
    have hscalar := mixed_triangle_sign_of_natAbs (B i k) (B k j) (B i j)
      (A i j) (A k j) hx hy (hA.2.2 i j hij)
      (hA.2.2 k j (Ne.symm hjk)) hm
    simpa only [hai] using hscalar
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
    have hscalar := mixed_triangle_sign_of_natAbs (B k j) (B i k) (B i j)
      (A i j) (A i k) hy hx (hA.2.2 i j hij) (hA.2.2 i k hik) hm'
    simpa only [haj, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc] using hscalar

/-- All independently supplied one-step companion magnitudes force every
current numerical triangle relation. This is a conditional local bridge. -/
theorem trianglePathSigns_of_oneStep_quasiCartan
    (B A : Matrix 4) (green : Colors) (hB : SkewSymmetric B)
    (hA : QuasiCartanCompanion B A) (hs : ArrowSigns B A green)
    (hnew : ∀ k, QuasiCartanCompanion (mutate B k) (localMutation B A green k)) :
    TrianglePathSigns B A := by
  intro i j k hij hik hjk hx hy
  exact trianglePathSign_of_localMutation_quasiCartan B A green k i j hB hA hs
    (hnew k) hij hik hjk hx hy

/-- Flipping the pivot color and reversing its arrows keeps every selected
shear weight fixed, including a zero incident edge. -/
theorem pivotWeight_mutation_flip (B : Matrix 4) (green next : Colors)
    (k i : Fin 4) (hflip : next k = !green k) :
    pivotWeight (mutate B k) next k i = pivotWeight B green k i := by
  cases hk : green k <;> simp [pivotWeight, mutate, hflip, hk]

/-- The actual local Gram update is involutive when the pivot color flips. -/
theorem localMutation_involutive (B A : Matrix 4) (green next : Colors)
    (k : Fin 4) (hflip : next k = !green k) :
    localMutation (mutate B k) (localMutation B A green k) next k = A := by
  have hw := pivotWeight_mutation_flip B green next k
  funext i j
  by_cases hi : i = k <;> by_cases hj : j = k
  · subst i; subst j; simp [localMutation]
  · subst i; simp only [localMutation, hj, ↓reduceIte, hw j hflip]; grind
  · subst j; simp only [localMutation, hi, ↓reduceIte, hw i hflip]; grind
  · simp only [localMutation, hi, hj, ↓reduceIte, hw i hflip, hw j hflip]
    grind

/-- Independently obtained next arrow signs and both companion magnitude
certificates force the updated numerical triangle law at the pivot. The
remaining triangle away from the pivot and the square clauses are not claimed. -/
theorem updated_pivot_trianglePathSign
    (B A : Matrix 4) (green next : Colors) (k i j : Fin 4)
    (hB : SkewSymmetric B) (hA : QuasiCartanCompanion B A)
    (hnew : QuasiCartanCompanion (mutate B k) (localMutation B A green k))
    (hsnew : ArrowSigns (mutate B k) (localMutation B A green k) next)
    (hflip : next k = !green k)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hx : 0 < mutate B k i k) (hy : 0 < mutate B k k j) :
    0 < localMutation B A green k i j * localMutation B A green k k j *
        localMutation B A green k i k ↔ mutate B k i j < 0 := by
  have hreverse : QuasiCartanCompanion (mutate (mutate B k) k)
      (localMutation (mutate B k) (localMutation B A green k) next k) := by
    rw [mutation_involutive, localMutation_involutive B A green next k hflip]
    exact hA
  exact trianglePathSign_of_localMutation_quasiCartan _ _ next k i j
    (mutation_preserves_skew B k hB) hnew hsnew hreverse hij hik hjk hx hy

/-- The actual colors after one mutation of the identity coefficient matrix. -/
def singleRedColors (k : Fin 4) : Colors := fun i => decide (i ≠ k)

private theorem correction_pos_imp (x y : Int) (h : 0 < correction x y) :
    0 < x ∧ 0 < y := by
  have hm : 0 ≤ max (-x) 0 * max (-y) 0 := Int.mul_nonneg (by omega) (by omega)
  constructor
  · by_contra hx
    have he : max x 0 = 0 := by omega
    simp only [correction, he, Int.zero_mul, Int.zero_sub] at h
    omega
  · by_contra hy
    have he : max y 0 = 0 := by omega
    simp only [correction, he, Int.mul_zero, Int.zero_sub] at h
    omega

/-- One acyclic mutation retains the initial rank on the nonpivot subquiver. -/
theorem acyclic_mutation_nonpivot_rank (B : Matrix 4) (k : Fin 4)
    (rank : Fin 4 → Nat) (hrank : ∀ i j, 0 < B i j → rank i < rank j)
    (i j : Fin 4) (hik : i ≠ k) (hjk : j ≠ k)
    (hij : 0 < mutate B k i j) : rank i < rank j := by
  by_cases h : 0 < B i j
  · exact hrank i j h
  · have hm : 0 < correction (B i k) (B k j) := by
      simp only [mutate, hik, hjk, or_self, ↓reduceIte] at hij
      omega
    have hp := correction_pos_imp _ _ hm
    have := hrank i k hp.1
    have := hrank k j hp.2
    omega

/-- A directed path through the flipped pivot closes to an oriented triangle
in the first mutation of an acyclic seed. Arbitrary weights are allowed. -/
theorem acyclic_mutation_pivot_path_closes (B : Matrix 4) (hB : SkewSymmetric B)
    (k : Fin 4) (rank : Fin 4 → Nat)
    (hrank : ∀ i j, 0 < B i j → rank i < rank j)
    (i j : Fin 4) (hik : i ≠ k) (hjk : j ≠ k)
    (hx : 0 < mutate B k k i) (hy : 0 < mutate B k j k) :
    0 < mutate B k i j := by
  have hki : B k i < 0 := by simpa [mutate] using hx
  have hkj : 0 < B k j := by
    have hjk' : B j k < 0 := by simpa [mutate] using hy
    have := hB k j
    omega
  have hik' : 0 < B i k := by have := hB i k; omega
  have hi := hrank i k hik'
  have hj := hrank k j hkj
  have hij : 0 ≤ B i j := by
    by_contra hn
    have hji : 0 < B j i := by have := hB j i; omega
    have := hrank j i hji
    omega
  have hp := Int.mul_pos hik' hkj
  simp only [mutate, hik, hjk, or_self, ↓reduceIte,
    correction_pos _ _ hik' hkj]
  omega

private theorem triangleColor_rotate (B : Matrix 4) (green : Colors)
    (i j l : Fin 4) (h : triangleColorAdmissible B green i j l) :
    triangleColorAdmissible B green j l i := by
  intro hjl hli hij
  have hc := h hij hjl hli
  have hxor : ∀ a b c : Bool, (a ^^ b ^^ c) = (b ^^ c ^^ a) := by decide
  rw [hxor] at hc
  constructor
  · intro ho
    rcases hc.mp ho with ⟨hij, hjl, hli⟩ | ⟨hij, hjl, hli⟩
    · exact Or.inl ⟨hjl, hli, hij⟩
    · exact Or.inr ⟨hjl, hli, hij⟩
  · intro ho
    apply hc.mpr
    rcases ho with ⟨hjl, hli, hij⟩ | ⟨hjl, hli, hij⟩
    · exact Or.inl ⟨hij, hjl, hli⟩
    · exact Or.inr ⟨hij, hjl, hli⟩

private theorem squareColor_rotate (B : Matrix 4) (green : Colors)
    (i j l m : Fin 4) (hB : SkewSymmetric B)
    (h : squareColorAdmissible B green i j l m) :
    squareColorAdmissible B green j l m i := by
  intro hjl hlm hmi hij hjm hli
  have hil : B i l = 0 := by have := hB i l; omega
  have hc := h hij hjl hlm hmi hil hjm
  have hxor : ∀ a b c d : Bool, (a ^^ b ^^ c ^^ d) = (b ^^ c ^^ d ^^ a) := by decide
  rw [hxor] at hc
  constructor
  · intro ho
    rcases hc.mp ho with ⟨hij, hjl, hlm, hmi⟩ | ⟨hij, hjl, hlm, hmi⟩
    · exact Or.inl ⟨hjl, hlm, hmi, hij⟩
    · exact Or.inr ⟨hjl, hlm, hmi, hij⟩
  · intro ho
    apply hc.mpr
    rcases ho with ⟨hjl, hlm, hmi, hij⟩ | ⟨hjl, hlm, hmi, hij⟩
    · exact Or.inl ⟨hij, hjl, hlm, hmi⟩
    · exact Or.inr ⟨hij, hjl, hlm, hmi⟩

private theorem singleRed_triangle (B : Matrix 4) (hB : SkewSymmetric B)
    (k i j : Fin 4) (hik : i ≠ k) (hjk : j ≠ k)
    (hclose : ∀ a b, a ≠ k → b ≠ k → 0 < B k a → 0 < B b k → 0 < B a b) :
    triangleColorAdmissible B (singleRedColors k) k i j := by
  intro hki hij hjk'
  have hsk := hB k j
  have hsi := hB i k
  have hsj := hB j i
  by_cases hx : 0 < B k i <;> by_cases hz : 0 < B j k
  · have hm := hclose i j hik hjk hx hz
    have hn : ¬0 < B k j := by omega
    simp [positiveColorEdge, singleRedColors, hik, hjk, hx, hz, hn, hm]
  · have hn : 0 < B k j := by omega
    have hzn : B j k < 0 := by omega
    simp [positiveColorEdge, singleRedColors, hik, hjk, hx, hz, hn, hzn]; omega
  · have hn : 0 < B i k := by omega
    have hxn : B k i < 0 := by omega
    simp [positiveColorEdge, singleRedColors, hik, hjk, hx, hz, hxn]; omega
  · have hn : 0 < B k j := by omega
    have hi : 0 < B i k := by omega
    have hm := hclose j i hjk hik hn hi
    have hneg : B i j < 0 := by omega
    have hxn : B k i < 0 := by omega
    have hzn : B j k < 0 := by omega
    simp [positiveColorEdge, singleRedColors, hik, hjk, hx, hz, hn, hneg, hxn, hzn]

private theorem singleRed_square (B : Matrix 4) (hB : SkewSymmetric B)
    (k i j l : Fin 4) (hik : i ≠ k) (hjk : j ≠ k) (hlk : l ≠ k)
    (hclose : ∀ a b, a ≠ k → b ≠ k → 0 < B k a → 0 < B b k → 0 < B a b) :
    squareColorAdmissible B (singleRedColors k) k i j l := by
  intro hki hij hjl hlk' hkj hil
  have hs := hB k l
  have hsi := hB i k
  have hsil := hB i l
  by_cases hx : 0 < B k i <;> by_cases hz : 0 < B l k
  · have hm := hclose i l hik hlk hx hz
    omega
  · have hn : 0 < B k l := by omega
    have hzn : B l k < 0 := by omega
    simp [positiveColorEdge, singleRedColors, hik, hjk, hlk, hx, hz, hn, hzn]; omega
  · have hxn : B k i < 0 := by omega
    simp [positiveColorEdge, singleRedColors, hik, hjk, hlk, hx, hz, hxn]; omega
  · have hn : 0 < B k l := by omega
    have hi : 0 < B i k := by omega
    have hm := hclose l i hlk hik hn hi
    omega

/-- Every first mutation of an acyclic skew input has the cycle color
parities. The red pivot cannot lie internally on an induced square. -/
theorem firstMutation_colorAdmissible (B : Matrix 4) (hB : SkewSymmetric B)
    (hAc : Acyclic B) (k : Fin 4) :
    ColorAdmissible (mutate B k) (singleRedColors k) := by
  obtain ⟨rank, hrank⟩ := hAc
  let T := mutate B k
  have hT : SkewSymmetric T := mutation_preserves_skew B k hB
  have hclose : ∀ i j, i ≠ k → j ≠ k → 0 < T k i → 0 < T j k → 0 < T i j :=
    fun i j hi hj hx hy => acyclic_mutation_pivot_path_closes B hB k rank hrank i j hi hj hx hy
  have hRank : ∀ i j, i ≠ k → j ≠ k → 0 < T i j → rank i < rank j :=
    fun i j hi hj hx => acyclic_mutation_nonpivot_rank B k rank hrank i j hi hj hx
  have tri : ∀ i j l : Fin 4, i ≠ j → i ≠ l → j ≠ l →
      triangleColorAdmissible T (singleRedColors k) i j l := by
    intro i j l hij hil hjl
    by_cases hi : i = k
    · subst i
      exact singleRed_triangle T hT k j l (Ne.symm hij) (Ne.symm hil) hclose
    by_cases hj : j = k
    · subst j
      have ht := singleRed_triangle T hT k l i (Ne.symm hjl) hi hclose
      exact triangleColor_rotate T _ l i k (triangleColor_rotate T _ k l i ht)
    by_cases hl : l = k
    · subst l
      exact triangleColor_rotate T _ k i j (singleRed_triangle T hT k i j hi hj hclose)
    intro he1 he2 he3
    simp only [positiveColorEdge, singleRedColors, ne_eq, hi, hj, hl, not_false_eq_true,
      decide_true, Bool.true_eq_false, false_and, and_false, false_or, decide_false,
      Bool.xor_false, Bool.false_eq_true, false_iff]
    rintro (⟨hp1, hp2, hp3⟩ | ⟨hp1, hp2, hp3⟩)
    · have := hRank i j hi hj hp1
      have := hRank j l hj hl hp2
      have := hRank l i hl hi hp3
      omega
    · have hjipos : 0 < T j i := by have := hT j i; omega
      have hljpos : 0 < T l j := by have := hT l j; omega
      have hilpos : 0 < T i l := by have := hT i l; omega
      have := hRank j i hj hi hjipos
      have := hRank l j hl hj hljpos
      have := hRank i l hi hl hilpos
      omega
  have sq : ∀ i j l m : Fin 4, i ≠ j → i ≠ l → i ≠ m →
      j ≠ l → j ≠ m → l ≠ m → squareColorAdmissible T (singleRedColors k) i j l m := by
    intro i j l m hij hil him hjl hjm hlm
    have hcover : k = i ∨ k = j ∨ k = l ∨ k = m := by omega
    rcases hcover with he | he | he | he
    · subst k
      exact singleRed_square T hT i j l m (Ne.symm hij) (Ne.symm hil) (Ne.symm him) hclose
    · subst k
      have ht := singleRed_square T hT j l m i (Ne.symm hjl) (Ne.symm hjm) hij hclose
      have ht1 := squareColor_rotate T _ j l m i hT ht
      have ht2 := squareColor_rotate T _ l m i j hT ht1
      exact squareColor_rotate T _ m i j l hT ht2
    · subst k
      have ht := singleRed_square T hT l m i j (Ne.symm hlm) hil hjl hclose
      exact squareColor_rotate T _ m i j l hT (squareColor_rotate T _ l m i j hT ht)
    · subst k
      exact squareColor_rotate T _ m i j l hT
        (singleRed_square T hT m i j l him hjm hlm hclose)
  exact ⟨tri 0 1 2 (by decide) (by decide) (by decide),
    tri 0 1 3 (by decide) (by decide) (by decide),
    tri 0 2 3 (by decide) (by decide) (by decide),
    tri 1 2 3 (by decide) (by decide) (by decide),
    sq 0 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    sq 0 1 3 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    sq 0 2 1 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)⟩

/-- The independently supplied color parities and actual arrow signs recover
ordinary companion parity on all seven rank-four chordless cycles. -/
theorem color_companionAdmissible (B A : Matrix 4) (hB : SkewSymmetric B)
    (hA : ∀ i j, A i j = A j i) (green : Colors)
    (hs : ArrowSigns B A green) (ha : ColorAdmissible B green) :
    CompanionAdmissible4 B A := by
  have tri : ∀ i j k, triangleColorAdmissible B green i j k →
      triangleCompanionAdmissible B A i j k := by
    intro i j k h hij hjk hki
    have hc := h hij hjk hki
    rw [positiveColorEdge_companion B A hB hA green hs i j hij,
      positiveColorEdge_companion B A hB hA green hs j k hjk,
      positiveColorEdge_companion B A hB hA green hs k i hki] at hc
    exact hc
  have square : ∀ i j k l, squareColorAdmissible B green i j k l →
      squareCompanionAdmissible B A i j k l := by
    intro i j k l h hij hjk hkl hli hik hjl
    have hc := h hij hjk hkl hli hik hjl
    rw [positiveColorEdge_companion B A hB hA green hs i j hij,
      positiveColorEdge_companion B A hB hA green hs j k hjk,
      positiveColorEdge_companion B A hB hA green hs k l hkl,
      positiveColorEdge_companion B A hB hA green hs l i hli] at hc
    exact hc
  exact ⟨tri 0 1 2 ha.1, tri 0 1 3 ha.2.1, tri 0 2 3 ha.2.2.1,
    tri 1 2 3 ha.2.2.2.1, square 0 1 2 3 ha.2.2.2.2.1,
    square 0 1 3 2 ha.2.2.2.2.2.1, square 0 2 1 3 ha.2.2.2.2.2.2⟩

/-- Genuine updated admissibility for every singleton principal word, with
unrestricted integer weights, disconnected support and singular matrices. -/
theorem firstMutation_companionAdmissible (B : Matrix 4) (hB : SkewSymmetric B)
    (hAc : Acyclic B) (k : Fin 4) :
    CompanionAdmissible4 (mutate B k)
      (coefficientCompanion B (mutateCoefficients B MAExistenceCoefficients.identityCoefficients k)) := by
  have hc : MAExistenceCoefficients.columnColor
      (mutateCoefficients B MAExistenceCoefficients.identityCoefficients k) = singleRedColors k := by
    funext j
    by_cases hj : j = k
    · subst j
      rw [MAExistenceCoefficients.pivot_color_flips B _ k
        (Or.inl (MAExistenceCoefficients.identity_green k)),
        MAExistenceCoefficients.color_green (MAExistenceCoefficients.identity_green k)]
      simp [singleRedColors]
    · rw [MAExistenceCoefficients.color_green
        (MAExistenceCoefficients.green_retained B _ k j hj
          (MAExistenceCoefficients.identity_green k) (MAExistenceCoefficients.identity_green j))]
      simp [singleRedColors, hj]
  have hs := MAExistenceTeamDArrowSigns.firstMutation_arrowSigns B hB k
  rw [hc] at hs
  exact color_companionAdmissible _ _ (mutation_preserves_skew B k hB)
    (coefficientCompanion_symmetric B _ hB) (singleRedColors k) hs
    (firstMutation_colorAdmissible B hB hAc k)

private def witnessExchange : Matrix 4 := ofSix (-4) 4 (-1) 0 1 1
private def witnessColors : Colors := fun i => i = 0 ∨ i = 2
private def witnessNextColors : Colors := fun i => i = 0
private def witnessCompanion : Matrix 4 := fun i j =>
  if i = j then 2
  else if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then 4
  else if (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) then -4
  else if (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) then 1
  else if (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) then 0
  else -1

/-- Current and next arrow signs do not by themselves preserve admissibility.
This example makes no actual principal-origin or real-root assertion. -/
theorem current_next_arrowSigns_not_admissibility :
    ∃ (B A : Matrix 4) (green next : Colors) (k : Fin 4),
      SkewSymmetric B ∧ QuasiCartanCompanion B A ∧
      ArrowSigns B A green ∧ CompanionAdmissible4 B A ∧
      QuasiCartanCompanion (mutate B k) (localMutation B A green k) ∧
      ArrowSigns (mutate B k) (localMutation B A green k) next ∧
      next k = !green k ∧
      (∀ i, i ≠ k →
        (pivotWeight B green k i = 0 ∨ green i = green k) → next i = green i) ∧
      ¬CompanionAdmissible4 (mutate B k) (localMutation B A green k) := by
  refine ⟨witnessExchange, witnessCompanion, witnessColors, witnessNextColors, 2, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold SkewSymmetric
    decide
  · unfold QuasiCartanCompanion
    decide
  · unfold ArrowSigns
    decide
  · simp [CompanionAdmissible4, triangleCompanionAdmissible, squareCompanionAdmissible,
      witnessCompanion, witnessExchange, ofSix]
  · unfold QuasiCartanCompanion
    decide
  · unfold ArrowSigns
    decide
  · decide
  · decide
  · simp [CompanionAdmissible4, triangleCompanionAdmissible, squareCompanionAdmissible,
      witnessCompanion, witnessExchange, witnessColors, localMutation, pivotWeight,
      mutate, correction, ofSix]
end QuiverProofs.MAExistenceTeamDAdmissibility

/-! General local square preservation from previous-state data. -/

namespace QuiverProofs.MAExistenceTeamDAdmissibility
open MAExistenceLiterature MAExistenceCompanions MAExistenceAuxiliaryOrders
open MAExistenceTeamBCompanionClosure
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

private theorem companion_zero (B A : Matrix 4) (hA : QuasiCartanCompanion B A)
    (i j : Fin 4) (hij : i ≠ j) (hz : B i j = 0) : A i j = 0 := by
  have h := hA.2.2 i j hij
  rw [hz, Int.natAbs_zero] at h
  exact Int.natAbs_eq_zero.mp h

private theorem companion_ne_zero (B A : Matrix 4) (hA : QuasiCartanCompanion B A)
    (i j : Fin 4) (hij : i ≠ j) (hz : B i j ≠ 0) : A i j ≠ 0 := by
  intro he
  have h := hA.2.2 i j hij
  rw [he, Int.natAbs_zero] at h
  exact hz (Int.natAbs_eq_zero.mp h.symm)

private theorem localMutation_zero_pivot_edge (B A : Matrix 4) (green : Colors)
    (k i j : Fin 4) (hi : i ≠ k) (hj : j ≠ k)
    (hA : QuasiCartanCompanion B A) (hz : B k j = 0) :
    localMutation B A green k i j = A i j := by
  have haz : A k j = 0 := companion_zero B A hA k j (Ne.symm hj) hz
  have ht : pivotWeight B green k j = 0 := by simp [pivotWeight, hz]
  simp [localMutation, hi, hj, ht, haz]

private theorem incident_entry (B A : Matrix 4) (green : Colors) (k i : Fin 4)
    (hik : i ≠ k) (hB : SkewSymmetric B) (hA : QuasiCartanCompanion B A)
    (hs : ArrowSigns B A green) :
    localMutation B A green k k i =
      if pivotWeight B green k i = 0 then -A k i else A k i := by
  rcases pivotWeight_companion B A green k i hik hB hA hs with ht | ha
  · simp [localMutation, hik, hA.2.1 k, ht]
  · by_cases ht : pivotWeight B green k i = 0
    · simp [localMutation, hik, hA.2.1 k, ht]
    · simp only [localMutation, if_true, hik, if_false, hA.2.1 k, ht]
      rw [hA.1 k i, ha]
      grind

private theorem sign_neg (a : Int) (ha : a ≠ 0) :
    decide (0 < -a) = !decide (0 < a) := by
  by_cases hp : 0 < a
  · simp [hp]; omega
  · simp [hp]; omega

private theorem incident_sign (B A : Matrix 4) (green : Colors) (k i : Fin 4)
    (hik : i ≠ k) (hB : SkewSymmetric B) (hA : QuasiCartanCompanion B A)
    (hs : ArrowSigns B A green) (hz : B k i ≠ 0) :
    decide (0 < localMutation B A green k k i) =
      (decide (0 < A k i) ^^ decide (pivotWeight B green k i = 0)) := by
  rw [incident_entry B A green k i hik hB hA hs]
  have ha := companion_ne_zero B A hA k i (Ne.symm hik) hz
  by_cases ht : pivotWeight B green k i = 0
  · simp only [ht, if_true, decide_true, Bool.xor_true]
    exact sign_neg (A k i) ha
  · simp [ht]

private theorem xor_incident (B A : Matrix 4) (green : Colors) (k i l : Fin 4)
    (hik : i ≠ k) (hlk : l ≠ k) (hB : SkewSymmetric B)
    (hA : QuasiCartanCompanion B A) (hs : ArrowSigns B A green)
    (hki : B k i ≠ 0) (hkl : B k l ≠ 0) :
    (decide (0 < localMutation B A green k k i) ^^
      decide (0 < localMutation B A green k l k)) =
      ((decide (0 < A k i) ^^ decide (0 < A l k)) ^^
        decide ((0 < B k i ∧ B k l < 0) ∨ (B k i < 0 ∧ 0 < B k l))) := by
  rw [localMutation_symmetric B A green k hA.1 l k,
    incident_sign B A green k i hik hB hA hs hki,
    incident_sign B A green k l hlk hB hA hs hkl, hA.1 l k]
  have hbool : ∀ a b c d : Bool, ((a ^^ b) ^^ (c ^^ d)) = ((a ^^ c) ^^ (b ^^ d)) := by decide
  rw [hbool]
  congr 1
  cases hg : green k <;>
    by_cases hi : 0 < B k i <;> by_cases hl : 0 < B k l <;>
    simp only [pivotWeight, hg, Bool.false_eq_true, ↓reduceIte]
  all_goals have hi0 : max (B k i) 0 = 0 ↔ ¬0 < B k i := by omega
  all_goals have hl0 : max (B k l) 0 = 0 ↔ ¬0 < B k l := by omega
  all_goals have hin0 : max (-B k i) 0 = 0 ↔ 0 < B k i := by omega
  all_goals have hln0 : max (-B k l) 0 = 0 ↔ 0 < B k l := by omega
  all_goals by_cases hni : B k i < 0 <;> by_cases hnl : B k l < 0 <;>
    simp [hi0, hl0, hin0, hln0, hi, hl, hni, hnl] <;> omega

private theorem cancellation_sign_cases (x y z : Int) (hx : x ≠ 0) (hy : y ≠ 0)
    (he : z + correction (-x) y = 0) :
    (0 < x ∧ 0 < y ∧ z = 0) ∨ (x < 0 ∧ y < 0 ∧ z = 0) ∨
    (0 < x ∧ y < 0 ∧ 0 < z) ∨ (x < 0 ∧ 0 < y ∧ z < 0) := by
  by_cases hxp : 0 < x <;> by_cases hyp : 0 < y
  · have hnx : max (-x) 0 = 0 := by omega
    have hny : max (-y) 0 = 0 := by omega
    simp only [correction, hnx, hny, Int.neg_neg, Int.zero_mul, Int.mul_zero,
      Int.sub_zero, Int.add_zero] at he
    exact Or.inl ⟨hxp, hyp, he⟩
  · have hyn : y < 0 := by omega
    have hnx : max (-x) 0 = 0 := by omega
    have hx' : max x 0 = x := by omega
    have hy' : max y 0 = 0 := by omega
    have hny : max (-y) 0 = -y := by omega
    simp only [correction, Int.neg_neg, hnx, hx', hy', hny, Int.zero_mul] at he
    have hp := Int.mul_pos hxp (show 0 < -y by omega)
    exact Or.inr (Or.inr (Or.inl ⟨hxp, hyn, by omega⟩))
  · have hxn : x < 0 := by omega
    have hnx : max (-x) 0 = -x := by omega
    have hx' : max x 0 = 0 := by omega
    have hy' : max y 0 = y := by omega
    simp only [correction, Int.neg_neg, hnx, hx', hy', Int.zero_mul, Int.sub_zero] at he
    have hp := Int.mul_pos (show 0 < -x by omega) hyp
    exact Or.inr (Or.inr (Or.inr ⟨hxn, hyp, by omega⟩))
  · have hxn : x < 0 := by omega
    have hyn : y < 0 := by omega
    have hx' : max x 0 = 0 := by omega
    have hy' : max y 0 = 0 := by omega
    simp only [correction, Int.neg_neg, hx', hy', Int.zero_mul, Int.mul_zero,
      Int.sub_zero, Int.add_zero] at he
    exact Or.inr (Or.inl ⟨hxn, hyn, he⟩)

/-- Updated square parity at the pivot follows entirely from current cycle
parities. No actual-origin, frozen or next-state sign hypothesis is needed. -/
theorem squareCompanionAdmissible_mutation_pivot
    (B A : Matrix 4) (green : Colors) (k i j l : Fin 4)
    (hki : k ≠ i) (hkj : k ≠ j) (hkl : k ≠ l)
    (_hij : i ≠ j) (_hil : i ≠ l) (_hjl : j ≠ l)
    (hB : SkewSymmetric B) (hA : QuasiCartanCompanion B A)
    (hs : ArrowSigns B A green)
    (htki : triangleCompanionAdmissible B A k i l)
    (htij : triangleCompanionAdmissible B A i j l)
    (hsq : squareCompanionAdmissible B A k i j l) :
    squareCompanionAdmissible (mutate B k) (localMutation B A green k) k i j l := by
  intro he1 he2 he3 he4 hz1 hz2
  have hzij : B k j = 0 := by simpa [mutate] using hz1
  have hzjk : B j k = 0 := by have := hB j k; omega
  have hki0 : B k i ≠ 0 := by simpa [mutate] using he1
  have hkl0 : B k l ≠ 0 := by
    have hlt : B l k ≠ 0 := by simpa [mutate] using he4
    have := hB k l
    omega
  have hBij : mutate B k i j = B i j := by
    simp [mutate, Ne.symm hki, Ne.symm hkj, hzij, correction]
  have hBjl : mutate B k j l = B j l := by
    simp [mutate, Ne.symm hkj, Ne.symm hkl, hzjk, correction]
  have hAij : localMutation B A green k i j = A i j :=
    localMutation_zero_pivot_edge B A green k i j (Ne.symm hki) (Ne.symm hkj) hA hzij
  have hAjl : localMutation B A green k j l = A j l := by
    rw [localMutation_symmetric B A green k hA.1 j l]
    rw [localMutation_zero_pivot_edge B A green k l j (Ne.symm hkl) (Ne.symm hkj) hA hzij]
    exact hA.1 l j
  have hij0 : B i j ≠ 0 := by rwa [hBij] at he2
  have hjl0 : B j l ≠ 0 := by rwa [hBjl] at he3
  have hlk0 : B l k ≠ 0 := by have := hB l k; omega
  have hcancel : B i l + correction (-B k i) (B k l) = 0 := by
    have h := hz2
    simp only [mutate, Ne.symm hki, Ne.symm hkl, or_self, ↓reduceIte] at h
    rwa [hB i k] at h
  have hfour : ∀ a b c d : Bool, (a ^^ b ^^ c ^^ d) = ((a ^^ d) ^^ (b ^^ c)) := by decide
  have hnextpar :
      (decide (0 < localMutation B A green k k i) ^^ decide (0 < localMutation B A green k i j) ^^
        decide (0 < localMutation B A green k j l) ^^ decide (0 < localMutation B A green k l k)) =
      (((decide (0 < A k i) ^^ decide (0 < A l k)) ^^
        decide ((0 < B k i ∧ B k l < 0) ∨ (B k i < 0 ∧ 0 < B k l))) ^^
          (decide (0 < A i j) ^^ decide (0 < A j l))) := by
    rw [hAij, hAjl, hfour, xor_incident B A green k i l (Ne.symm hki) (Ne.symm hkl) hB hA hs hki0 hkl0]
  rw [hnextpar, hBij, hBjl]
  simp only [mutate, true_or, or_true, ↓reduceIte]
  have hski := hB i k
  have hskl := hB l k
  rcases cancellation_sign_cases (B k i) (B k l) (B i l) hki0 hkl0 hcancel with
    ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩
  · have hc := hsq hki0 hij0 hjl0 hlk0 hzij hz
    rw [hfour] at hc
    have hmask : ¬((0 < B k i ∧ B k l < 0) ∨ (B k i < 0 ∧ 0 < B k l)) := by omega
    simp only [hmask, decide_false, Bool.xor_false]
    rw [hc]
    omega
  · have hc := hsq hki0 hij0 hjl0 hlk0 hzij hz
    rw [hfour] at hc
    have hmask : ¬((0 < B k i ∧ B k l < 0) ∨ (B k i < 0 ∧ 0 < B k l)) := by omega
    simp only [hmask, decide_false, Bool.xor_false]
    rw [hc]
    omega
  · have hmask : (0 < B k i ∧ B k l < 0) ∨ (B k i < 0 ∧ 0 < B k l) := Or.inl ⟨hx, hy⟩
    have hposlk : 0 < B l k := by omega
    have hp := (htki hki0 (by omega) hlk0).mpr (Or.inl ⟨hx, hz, hposlk⟩)
    have hcomp : ((decide (0 < A k i) ^^ decide (0 < A l k)) ^^ true) = decide (0 < A i l) := by
      have hb : ∀ a b c : Bool, (a ^^ b ^^ c) = true → ((a ^^ c) ^^ true) = b := by decide
      exact hb _ _ _ hp
    have hzli : B l i ≠ 0 := by have := hB l i; omega
    have hc := htij hij0 hjl0 hzli
    have hthree : ∀ a b c : Bool, (c ^^ (a ^^ b)) = (a ^^ b ^^ c) := by decide
    simp only [hmask, decide_true]
    rw [hcomp, hthree, hA.1 i l, hc]
    have := hB l i
    omega
  · have hmask : (0 < B k i ∧ B k l < 0) ∨ (B k i < 0 ∧ 0 < B k l) := Or.inr ⟨hx, hy⟩
    have hneglk : B l k < 0 := by omega
    have hp := (htki hki0 (by omega) hlk0).mpr (Or.inr ⟨hx, hz, hneglk⟩)
    have hcomp : ((decide (0 < A k i) ^^ decide (0 < A l k)) ^^ true) = decide (0 < A i l) := by
      have hb : ∀ a b c : Bool, (a ^^ b ^^ c) = true → ((a ^^ c) ^^ true) = b := by decide
      exact hb _ _ _ hp
    have hzli : B l i ≠ 0 := by have := hB l i; omega
    have hc := htij hij0 hjl0 hzli
    have hthree : ∀ a b c : Bool, (c ^^ (a ^^ b)) = (a ^^ b ^^ c) := by decide
    simp only [hmask, decide_true]
    rw [hcomp, hthree, hA.1 i l, hc]
    have := hB l i
    omega

private theorem square_parity_rotate (B A : Matrix 4)
    (hB : SkewSymmetric B) (i j l m : Fin 4)
    (h : squareCompanionAdmissible B A i j l m) :
    squareCompanionAdmissible B A j l m i := by
  intro hjl hlm hmi hij hjm hli
  have hil : B i l = 0 := by have := hB i l; omega
  have hc := h hij hjl hlm hmi hil hjm
  have hx : ∀ a b c d : Bool, (a ^^ b ^^ c ^^ d) = (b ^^ c ^^ d ^^ a) := by decide
  rw [hx] at hc
  constructor
  · intro ho
    rcases hc.mp ho with ⟨hij, hjl, hlm, hmi⟩ | ⟨hij, hjl, hlm, hmi⟩
    · exact Or.inl ⟨hjl, hlm, hmi, hij⟩
    · exact Or.inr ⟨hjl, hlm, hmi, hij⟩
  · intro ho
    apply hc.mpr
    rcases ho with ⟨hjl, hlm, hmi, hij⟩ | ⟨hjl, hlm, hmi, hij⟩
    · exact Or.inl ⟨hij, hjl, hlm, hmi⟩
    · exact Or.inr ⟨hij, hjl, hlm, hmi⟩

private theorem square_parity_reverse (B A : Matrix 4)
    (hB : SkewSymmetric B) (hA : ∀ i j, A i j = A j i)
    (i j l m : Fin 4) (h : squareCompanionAdmissible B A i j l m) :
    squareCompanionAdmissible B A m l j i := by
  intro hml hlj hji him hmj hli
  have hij : B i j ≠ 0 := by have := hB i j; omega
  have hjl : B j l ≠ 0 := by have := hB j l; omega
  have hlm : B l m ≠ 0 := by have := hB l m; omega
  have hmi : B m i ≠ 0 := by have := hB m i; omega
  have hil : B i l = 0 := by have := hB i l; omega
  have hjm : B j m = 0 := by have := hB j m; omega
  have hc := h hij hjl hlm hmi hil hjm
  have hx : ∀ a b c d : Bool, (a ^^ b ^^ c ^^ d) = (c ^^ b ^^ a ^^ d) := by decide
  rw [hA m l, hA l j, hA j i, hA i m, ←hx, hc]
  have := hB i j
  have := hB j l
  have := hB l m
  have := hB m i
  omega

private theorem square_parity_permutations (B A : Matrix 4)
    (hB : SkewSymmetric B) (hA : ∀ i j, A i j = A j i)
    (i j l m : Fin 4) (h : squareCompanionAdmissible B A i j l m) :
    squareCompanionAdmissible B A i j l m ∧
    squareCompanionAdmissible B A j l m i ∧
    squareCompanionAdmissible B A l m i j ∧
    squareCompanionAdmissible B A m i j l ∧
    squareCompanionAdmissible B A m l j i ∧
    squareCompanionAdmissible B A l j i m ∧
    squareCompanionAdmissible B A j i m l ∧
    squareCompanionAdmissible B A i m l j := by
  have h1 := square_parity_rotate B A hB i j l m h
  have h2 := square_parity_rotate B A hB j l m i h1
  have h3 := square_parity_rotate B A hB l m i j h2
  have hr := square_parity_reverse B A hB hA i j l m h
  have hr1 := square_parity_rotate B A hB m l j i hr
  have hr2 := square_parity_rotate B A hB l j i m hr1
  have hr3 := square_parity_rotate B A hB j i m l hr2
  exact ⟨h, h1, h2, h3, hr, hr1, hr2, hr3⟩

/-- The three stored induced-square clauses supply every ordered square on
four distinct labels. -/
theorem companionAdmissible4_square (B A : Matrix 4)
    (hB : SkewSymmetric B) (hA : ∀ i j, A i j = A j i)
    (ha : CompanionAdmissible4 B A) (i j l m : Fin 4)
    (hij : i ≠ j) (hil : i ≠ l) (him : i ≠ m)
    (hjl : j ≠ l) (hjm : j ≠ m) (hlm : l ≠ m) :
    squareCompanionAdmissible B A i j l m := by
  rcases square_parity_permutations B A hB hA 0 1 2 3 ha.2.2.2.2.1 with
    ⟨h0123, h1230, h2301, h3012, h3210, h2103, h1032, h0321⟩
  rcases square_parity_permutations B A hB hA 0 1 3 2 ha.2.2.2.2.2.1 with
    ⟨h0132, h1320, h3201, h2013, h2310, h3102, h1023, h0231⟩
  rcases square_parity_permutations B A hB hA 0 2 1 3 ha.2.2.2.2.2.2 with
    ⟨h0213, h2130, h1302, h3021, h3120, h1203, h2031, h0312⟩
  have fin4 : ∀ v : Fin 4, v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 := by intro v; omega
  rcases fin4 i with rfl | rfl | rfl | rfl <;>
    rcases fin4 j with rfl | rfl | rfl | rfl <;>
    rcases fin4 l with rfl | rfl | rfl | rfl <;>
    rcases fin4 m with rfl | rfl | rfl | rfl
  all_goals first | contradiction | assumption

/-- Every induced square survives every local companion mutation on rank
four, using only previous-state companion/arrow/parity data. -/
theorem localMutation_squareCompanionAdmissible (B A : Matrix 4) (green : Colors)
    (k i j l m : Fin 4) (hB : SkewSymmetric B)
    (hA : QuasiCartanCompanion B A) (hs : ArrowSigns B A green)
    (ha : CompanionAdmissible4 B A)
    (hij : i ≠ j) (hil : i ≠ l) (him : i ≠ m)
    (hjl : j ≠ l) (hjm : j ≠ m) (hlm : l ≠ m) :
    squareCompanionAdmissible (mutate B k) (localMutation B A green k) i j l m := by
  have hT := mutation_preserves_skew B k hB
  have pivot : ∀ a b c, k ≠ a → k ≠ b → k ≠ c →
      a ≠ b → a ≠ c → b ≠ c →
      squareCompanionAdmissible (mutate B k) (localMutation B A green k) k a b c := by
    intro a b c hka hkb hkc hab hac hbc
    exact squareCompanionAdmissible_mutation_pivot B A green k a b c hka hkb hkc hab hac hbc
      hB hA hs
      (companionAdmissible4_triangle B A hB hA.1 ha k a c hka hkc hac)
      (companionAdmissible4_triangle B A hB hA.1 ha a b c hab hac hbc)
      (companionAdmissible4_square B A hB hA.1 ha k a b c hka hkb hkc hab hac hbc)
  have hcover : k = i ∨ k = j ∨ k = l ∨ k = m := by omega
  rcases hcover with he | he | he | he
  · subst k
    exact pivot j l m hij hil him hjl hjm hlm
  · subst k
    have hp := pivot l m i hjl hjm (Ne.symm hij) hlm (Ne.symm hil) (Ne.symm him)
    have hp1 := square_parity_rotate _ _ hT j l m i hp
    have hp2 := square_parity_rotate _ _ hT l m i j hp1
    exact square_parity_rotate _ _ hT m i j l hp2
  · subst k
    have hp := pivot m i j hlm (Ne.symm hil) (Ne.symm hjl) (Ne.symm him) (Ne.symm hjm) hij
    exact square_parity_rotate _ _ hT m i j l (square_parity_rotate _ _ hT l m i j hp)
  · subst k
    exact square_parity_rotate _ _ hT m i j l
      (pivot i j l (Ne.symm him) (Ne.symm hjm) (Ne.symm hlm) hij hil hjl)

/-- All three stored square clauses are preserved, including absent chords
and chord cancellation. Triangle preservation is a separate obligation. -/
theorem localMutation_admissible_squares (B A : Matrix 4) (green : Colors)
    (k : Fin 4) (hB : SkewSymmetric B) (hA : QuasiCartanCompanion B A)
    (hs : ArrowSigns B A green) (ha : CompanionAdmissible4 B A) :
    squareCompanionAdmissible (mutate B k) (localMutation B A green k) 0 1 2 3 ∧
    squareCompanionAdmissible (mutate B k) (localMutation B A green k) 0 1 3 2 ∧
    squareCompanionAdmissible (mutate B k) (localMutation B A green k) 0 2 1 3 := by
  refine ⟨?_, ?_, ?_⟩
  · exact localMutation_squareCompanionAdmissible B A green k 0 1 2 3 hB hA hs ha
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact localMutation_squareCompanionAdmissible B A green k 0 1 3 2 hB hA hs ha
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact localMutation_squareCompanionAdmissible B A green k 0 2 1 3 hB hA hs ha
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The square package applies to the actual updated Gram companion after
current root data has independently supplied strict coefficient coherence. -/
theorem coefficientMutation_admissible_squares (B₀ B C : Matrix 4) (k : Fin 4)
    (hB : SkewSymmetric B)
    (hA : QuasiCartanCompanion B (coefficientCompanion B₀ C))
    (hs : ArrowSigns B (coefficientCompanion B₀ C) (MAExistenceCoefficients.columnColor C))
    (ha : CompanionAdmissible4 B (coefficientCompanion B₀ C))
    (hC : MAExistenceCoefficients.SignCoherent C) :
    squareCompanionAdmissible (mutate B k)
      (coefficientCompanion B₀ (mutateCoefficients B C k)) 0 1 2 3 ∧
    squareCompanionAdmissible (mutate B k)
      (coefficientCompanion B₀ (mutateCoefficients B C k)) 0 1 3 2 ∧
    squareCompanionAdmissible (mutate B k)
      (coefficientCompanion B₀ (mutateCoefficients B C k)) 0 2 1 3 := by
  have hg : MAExistenceCoefficients.columnColor C k = true → ∀ i, 0 ≤ C i k :=
    fun h => ((MAExistenceCoefficients.color_iff_green hC k).mp h).1
  have hr : MAExistenceCoefficients.columnColor C k = false → ∀ i, C i k ≤ 0 :=
    fun h => ((MAExistenceCoefficients.color_iff_red hC k).mp h).1
  rw [coefficientCompanion_mutation_local B₀ B C (MAExistenceCoefficients.columnColor C) k hg hr]
  exact localMutation_admissible_squares B _ _ k hB hA hs ha

end QuiverProofs.MAExistenceTeamDAdmissibility
