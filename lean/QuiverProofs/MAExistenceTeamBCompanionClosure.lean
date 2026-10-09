import QuiverProofs.MAExistenceCompanions
import QuiverProofs.MAExistenceCompanionTriangles
import QuiverProofs.MAExistenceAuxiliaryOrders

/-! Local companion closure. Triangle path signs are explicit current-state
data; no all-word sign coherence or admissibility is assumed. -/
namespace QuiverProofs.MAExistenceTeamBCompanionClosure
open MAExistenceLiterature MAExistenceCompanions MAExistenceCompanionTriangles
open MAExistenceAuxiliaryOrders

set_option maxHeartbeats 0

/-- The exact triangle-product sign relation needed in a mixed shear case. -/
def TrianglePathSigns (B A : Matrix 4) : Prop :=
  ∀ i j k : Fin 4, i ≠ j → i ≠ k → j ≠ k →
    0 < B i k → 0 < B k j →
    (0 < A i j * A k j * A i k ↔ B i j < 0)

private theorem companion_zero (B A : Matrix 4)
    (hA : QuasiCartanCompanion B A) (i j : Fin 4) (hij : i ≠ j)
    (hz : B i j = 0) : A i j = 0 := by
  have h := hA.2.2 i j hij
  simp only [hz, Int.natAbs_zero] at h
  exact Int.natAbs_eq_zero.mp h

private theorem correction_pos (x y : Int) (hx : 0 < x) (hy : 0 < y) :
    correction x y = x * y := by
  have hx' : max x 0 = x := by omega
  have hy' : max y 0 = y := by omega
  have hnx : max (-x) 0 = 0 := by omega
  have hny : max (-y) 0 = 0 := by omega
  simp [correction, hx', hy', hnx, hny]

private theorem localMutation_path_natAbs
    (B A : Matrix 4) (green : Colors) (k i j : Fin 4)
    (hB : SkewSymmetric B) (hA : QuasiCartanCompanion B A)
    (hs : ArrowSigns B A green) (htri : TrianglePathSigns B A)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hx : 0 < B i k) (hy : 0 < B k j) :
    (localMutation B A green k i j).natAbs = (mutate B k i j).natAbs := by
  have hki := hB k i
  have hpath := htri i j k hij hik hjk hx hy
  have hmut : mutate B k i j = B i j + B i k * B k j := by
    simp [mutate, hik, hjk, correction_pos _ _ hx hy]
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
    have hscalar := mixed_triangle_natAbs (B i k) (B k j) (B i j)
      (A i j) (A k j) hx hy (hA.2.2 i j hij)
      (hA.2.2 k j (Ne.symm hjk)) (by simpa only [hai] using hpath)
    simpa only [localMutation, hik, hjk, ↓reduceIte, hti, htj,
      Int.zero_mul, Int.mul_zero, Int.add_zero, hmut] using hscalar
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
    have hscalar := mixed_triangle_natAbs (B k j) (B i k) (B i j)
      (A i j) (A i k) hy hx (hA.2.2 i j hij)
      (hA.2.2 i k hik) (by
        simpa only [haj, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc] using hpath)
    simpa only [localMutation, hik, hjk, ↓reduceIte, hti, htj,
      Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero, hmut,
      Int.mul_comm] using hscalar

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

private theorem localMutation_opposite_signs_natAbs
    (B A : Matrix 4) (green : Colors) (k i j : Fin 4)
    (hB : SkewSymmetric B) (hA : QuasiCartanCompanion B A)
    (hs : ArrowSigns B A green) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (h : (0 < B i k ∧ B k j < 0) ∨ (B i k < 0 ∧ 0 < B k j)) :
    (localMutation B A green k i j).natAbs = (mutate B k i j).natAbs := by
  have hki := hB k i
  have hm : pivotWeight B green k i = 0 ↔ pivotWeight B green k j = 0 := by
    cases hk : green k <;>
      simp only [pivotWeight, hk, Bool.false_eq_true, ↓reduceIte] <;>
      rcases h with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> omega
  rw [localMutation_unmixed B A green k i j hik hjk hB hA hs hm]
  simp only [mutate, hik, hjk, or_self, ↓reduceIte,
    correction_opposite_signs _ _ h, Int.add_zero]
  exact hA.2.2 i j hij

private theorem localMutation_distinct_natAbs
    (B A : Matrix 4) (green : Colors) (k i j : Fin 4)
    (hB : SkewSymmetric B) (hA : QuasiCartanCompanion B A)
    (hs : ArrowSigns B A green) (htri : TrianglePathSigns B A)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (localMutation B A green k i j).natAbs = (mutate B k i j).natAbs := by
  by_cases hxz : B i k = 0
  · have haz := companion_zero B A hA i k hik hxz
    have hkiz : B k i = 0 := by have := hB k i; omega
    have hti : pivotWeight B green k i = 0 := by simp [pivotWeight, hkiz]
    simpa only [localMutation, hik, hjk, ↓reduceIte, hti, haz,
      Int.zero_mul, Int.mul_zero, Int.add_zero, mutate, or_self, hxz,
      correction, Int.neg_zero, Int.max_self, Int.zero_sub] using hA.2.2 i j hij
  by_cases hyz : B k j = 0
  · have haz := companion_zero B A hA k j (Ne.symm hjk) hyz
    have htj : pivotWeight B green k j = 0 := by simp [pivotWeight, hyz]
    simpa only [localMutation, hik, hjk, ↓reduceIte, htj, haz,
      Int.zero_mul, Int.mul_zero, Int.add_zero, mutate, or_self, hyz,
      correction, Int.neg_zero, Int.max_self, Int.zero_sub] using hA.2.2 i j hij
  by_cases hx : 0 < B i k
  · by_cases hy : 0 < B k j
    · exact localMutation_path_natAbs B A green k i j hB hA hs htri hij hik hjk hx hy
    · exact localMutation_opposite_signs_natAbs B A green k i j hB hA hs hij hik hjk
        (Or.inl ⟨hx, by omega⟩)
  · have hxn : B i k < 0 := by omega
    by_cases hy : 0 < B k j
    · exact localMutation_opposite_signs_natAbs B A green k i j hB hA hs hij hik hjk
        (Or.inr ⟨hxn, hy⟩)
    · have hyj : 0 < B j k := by have := hB j k; omega
      have hyi : 0 < B k i := by have := hB k i; omega
      have hreverse := localMutation_path_natAbs B A green k j i hB hA hs htri
        (Ne.symm hij) hjk hik hyj hyi
      rw [localMutation_symmetric B A green k hA.1 i j]
      rw [mutation_preserves_skew B k hB i j, Int.natAbs_neg]
      exact hreverse

/-- Current triangle path signs finish the local companion magnitude proof.
Every integer weight and cancellation case is included. -/
theorem localMutation_quasiCartan_from_trianglePathSigns
    (B A : Matrix 4) (green : Colors) (k : Fin 4)
    (hB : SkewSymmetric B) (hA : QuasiCartanCompanion B A)
    (hs : ArrowSigns B A green) (htri : TrianglePathSigns B A) :
    QuasiCartanCompanion (mutate B k) (localMutation B A green k) := by
  refine ⟨localMutation_symmetric B A green k hA.1,
    localMutation_diagonal B A green k hB hA hs, ?_⟩
  intro i j hij
  by_cases hik : i = k
  · subst i
    have hjk : j ≠ k := Ne.symm hij
    rw [localMutation_symmetric B A green k hA.1 k j]
    rw [mutation_preserves_skew B k hB k j, Int.natAbs_neg]
    exact localMutation_incident_natAbs B A green k j hjk hB hA hs
  by_cases hjk : j = k
  · subst j
    exact localMutation_incident_natAbs B A green k i hik hB hA hs
  exact localMutation_distinct_natAbs B A green k i j hB hA hs htri hij hik hjk

/-- Acyclic initial data supplies the triangle path signs without any support,
weight, connectedness or nonsingularity assumption. -/
theorem initialCompanion_trianglePathSigns (B : Matrix 4)
    (hB : SkewSymmetric B) (hAc : Acyclic B) :
    TrianglePathSigns B (initialCompanion B) := by
  obtain ⟨rank, hrank⟩ := hAc
  intro i j k hij hik hjk hx hy
  have ha := initialCompanion_offDiagonal_nonpos B i j hij
  have hc := initialCompanion_offDiagonal_nonpos B k j (Ne.symm hjk)
  have hd := initialCompanion_offDiagonal_nonpos B i k hik
  have hp : initialCompanion B i j * initialCompanion B k j *
      initialCompanion B i k ≤ 0 :=
    Int.mul_nonpos_of_nonneg_of_nonpos
      (Int.mul_nonneg_of_nonpos_of_nonpos ha hc) hd
  constructor
  · intro hpos
    omega
  · intro hneg
    have hji : 0 < B j i := by have := hB j i; omega
    have := hrank i k hx
    have := hrank k j hy
    have := hrank j i hji
    omega

/-- The first simultaneous mutation of every acyclic skew initial matrix has
an actual quasi-Cartan companion. This is a one-step statement. -/
theorem firstMutation_quasiCartan (B : Matrix 4)
    (hB : SkewSymmetric B) (hAc : Acyclic B) (k : Fin 4) :
    QuasiCartanCompanion (mutate B k)
      (localMutation B (initialCompanion B) (fun _ => true) k) :=
  localMutation_quasiCartan_from_trianglePathSigns B (initialCompanion B)
    (fun _ => true) k hB (initialCompanion_quasiCartan B hB)
    (initialCompanion_arrowSigns B hB) (initialCompanion_trianglePathSigns B hB hAc)

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

/-- Convert a directed triangle's cycle parity to the numerical product sign
used by the scalar shear identity. Zero closing edges need no parity premise. -/
theorem triangle_path_sign_of_cycle_parity (B A : Matrix 4)
    (hB : SkewSymmetric B) (hA : QuasiCartanCompanion B A)
    (i j k : Fin 4) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hx : 0 < B i k) (hy : 0 < B k j)
    (hpar : B i k ≠ 0 → B k j ≠ 0 → B j i ≠ 0 →
      ((decide (0 < A i k) ^^ decide (0 < A k j) ^^ decide (0 < A j i)) = true ↔
        (0 < B i k ∧ 0 < B k j ∧ 0 < B j i) ∨
        (B i k < 0 ∧ B k j < 0 ∧ B j i < 0))) :
    0 < A i j * A k j * A i k ↔ B i j < 0 := by
  by_cases hz : B i j = 0
  · have haz := companion_zero B A hA i j hij hz
    simp [haz, hz]
  have hzi : B j i ≠ 0 := by have := hB j i; omega
  have hix : A i k ≠ 0 := by
    intro he
    have := hA.2.2 i k hik
    rw [he, Int.natAbs_zero] at this
    have := Int.natAbs_eq_zero.mp this.symm
    omega
  have hky : A k j ≠ 0 := by
    intro he
    have := hA.2.2 k j (Ne.symm hjk)
    rw [he, Int.natAbs_zero] at this
    have := Int.natAbs_eq_zero.mp this.symm
    omega
  have hiz : A i j ≠ 0 := by
    intro he
    have := hA.2.2 i j hij
    rw [he, Int.natAbs_zero] at this
    exact hz (Int.natAbs_eq_zero.mp this.symm)
  have hcycle := hpar (by omega) (by omega) hzi
  have hxor : ∀ a b c : Bool, (a ^^ b ^^ c) = (c ^^ b ^^ a) := by decide
  rw [positive_product_iff_odd _ _ _ hiz hky hix]
  rw [hxor, ← hA.1 j i]
  rw [hcycle]
  have hji := hB j i
  omega

private theorem triangle_parity_rotate (B A : Matrix 4) (i j k : Fin 4)
    (h : triangleCompanionAdmissible B A i j k) :
    triangleCompanionAdmissible B A j k i := by
  intro hjk hki hij
  have hc := h hij hjk hki
  have hxor : ∀ a b c : Bool, (a ^^ b ^^ c) = (b ^^ c ^^ a) := by decide
  rw [hxor] at hc
  constructor
  · intro ho
    rcases hc.mp ho with ⟨hij, hjk, hki⟩ | ⟨hij, hjk, hki⟩
    · exact Or.inl ⟨hjk, hki, hij⟩
    · exact Or.inr ⟨hjk, hki, hij⟩
  · intro ho
    apply hc.mpr
    rcases ho with ⟨hjk, hki, hij⟩ | ⟨hjk, hki, hij⟩
    · exact Or.inl ⟨hij, hjk, hki⟩
    · exact Or.inr ⟨hij, hjk, hki⟩

private theorem triangle_parity_reverse (B A : Matrix 4)
    (hB : SkewSymmetric B) (hA : ∀ i j, A i j = A j i)
    (i j k : Fin 4) (h : triangleCompanionAdmissible B A i j k) :
    triangleCompanionAdmissible B A k j i := by
  intro hkj hji hik
  have hij : B i j ≠ 0 := by have := hB i j; omega
  have hjk : B j k ≠ 0 := by have := hB j k; omega
  have hki : B k i ≠ 0 := by have := hB k i; omega
  have hc := h hij hjk hki
  have hxor : ∀ a b c : Bool, (a ^^ b ^^ c) = (b ^^ a ^^ c) := by decide
  rw [hA k j, hA j i, hA i k, hxor, hc]
  have := hB i j
  have := hB j k
  have := hB k i
  omega

private theorem triangle_parity_permutations (B A : Matrix 4)
    (hB : SkewSymmetric B) (hA : ∀ i j, A i j = A j i)
    (i j k : Fin 4) (h : triangleCompanionAdmissible B A i j k) :
    triangleCompanionAdmissible B A i j k ∧
    triangleCompanionAdmissible B A j k i ∧
    triangleCompanionAdmissible B A k i j ∧
    triangleCompanionAdmissible B A k j i ∧
    triangleCompanionAdmissible B A j i k ∧
    triangleCompanionAdmissible B A i k j := by
  have hr := triangle_parity_rotate B A i j k h
  have hrr := triangle_parity_rotate B A j k i hr
  have hv := triangle_parity_reverse B A hB hA i j k h
  have hvr := triangle_parity_rotate B A k j i hv
  have hvrr := triangle_parity_rotate B A j i k hvr
  exact ⟨h, hr, hrr, hv, hvr, hvrr⟩

/-- The four recorded unordered triangles supply the cycle parity at every
ordered triple of distinct vertices. -/
theorem companionAdmissible4_triangle (B A : Matrix 4)
    (hB : SkewSymmetric B) (hA : ∀ i j, A i j = A j i)
    (ha : CompanionAdmissible4 B A) (i j k : Fin 4)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    triangleCompanionAdmissible B A i j k := by
  rcases triangle_parity_permutations B A hB hA 0 1 2 ha.1 with
    ⟨h012, h120, h201, h210, h102, h021⟩
  rcases triangle_parity_permutations B A hB hA 0 1 3 ha.2.1 with
    ⟨h013, h130, h301, h310, h103, h031⟩
  rcases triangle_parity_permutations B A hB hA 0 2 3 ha.2.2.1 with
    ⟨h023, h230, h302, h320, h203, h032⟩
  rcases triangle_parity_permutations B A hB hA 1 2 3 ha.2.2.2.1 with
    ⟨h123, h231, h312, h321, h213, h132⟩
  have fin4 : ∀ v : Fin 4, v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 := by intro v; omega
  rcases fin4 i with rfl | rfl | rfl | rfl <;>
    rcases fin4 j with rfl | rfl | rfl | rfl <;>
    rcases fin4 k with rfl | rfl | rfl | rfl <;>
    first | contradiction | assumption

/-- Actual current companion admissibility supplies the numerical triangle
sign relation needed for every mixed pair. -/
theorem companionAdmissible4_trianglePathSigns (B A : Matrix 4)
    (hB : SkewSymmetric B) (hA : QuasiCartanCompanion B A)
    (ha : CompanionAdmissible4 B A) : TrianglePathSigns B A := by
  intro i j k hij hik hjk hx hy
  exact triangle_path_sign_of_cycle_parity B A hB hA i j k hij hik hjk hx hy
    (companionAdmissible4_triangle B A hB hA.1 ha i k j hik hij (Ne.symm hjk))

/-- A supplied admissible current companion and arrow signs suffice for the
entire local quasi-Cartan mutation law. No future-state premise is used. -/
theorem localMutation_quasiCartan (B A : Matrix 4) (green : Colors) (k : Fin 4)
    (hB : SkewSymmetric B) (hA : QuasiCartanCompanion B A)
    (hs : ArrowSigns B A green) (ha : CompanionAdmissible4 B A) :
    QuasiCartanCompanion (mutate B k) (localMutation B A green k) :=
  localMutation_quasiCartan_from_trianglePathSigns B A green k hB hA hs
    (companionAdmissible4_trianglePathSigns B A hB hA ha)

end QuiverProofs.MAExistenceTeamBCompanionClosure
