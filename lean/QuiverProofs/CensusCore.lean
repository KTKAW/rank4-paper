import QuiverProofs.CensusData
import QuiverProofs.CensusMA

namespace QuiverProofs.Census

private theorem fin4_cases (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega

theorem codeMatrix_skew (n : Nat) : SkewSymmetric (codeMatrix n) :=
  ofSix_skew _ _ _ _ _ _

theorem codeMatrix_bounded (n : Nat) : BoundedTwo (codeMatrix n) := by
  intro i j
  have h₁ : n/3125%5 < 5 := Nat.mod_lt _ (by decide)
  have h₂ : n/625%5 < 5 := Nat.mod_lt _ (by decide)
  have h₃ : n/125%5 < 5 := Nat.mod_lt _ (by decide)
  have h₄ : n/25%5 < 5 := Nat.mod_lt _ (by decide)
  have h₅ : n/5%5 < 5 := Nat.mod_lt _ (by decide)
  have h₆ : n%5 < 5 := Nat.mod_lt _ (by decide)
  rcases fin4_cases i with rfl | rfl | rfl | rfl <;>
    rcases fin4_cases j with rfl | rfl | rfl | rfl <;>
    simp only [codeMatrix, ofSix] <;> omega

theorem bounded_matrix_code_lt (B : Matrix 4) (h : BoundedTwo B) : matrixCode B < 15625 := by
  have h₁ := h 0 1
  have h₂ := h 0 2
  have h₃ := h 0 3
  have h₄ := h 1 2
  have h₅ := h 1 3
  have h₆ := h 2 3
  unfold matrixCode
  omega

theorem bounded_matrix_decode (B : Matrix 4) (hskew : SkewSymmetric B)
    (h : BoundedTwo B) : codeMatrix (matrixCode B) = B := by
  have h₁ := h 0 1
  have h₂ := h 0 2
  have h₃ := h 0 3
  have h₄ := h 1 2
  have h₅ := h 1 3
  have h₆ := h 2 3
  rw [← ofSix_reconstruct B hskew]
  funext i j
  rcases fin4_cases i with rfl | rfl | rfl | rfl <;>
    rcases fin4_cases j with rfl | rfl | rfl | rfl <;>
    simp only [codeMatrix, matrixCode, ofSix] <;> omega

/-- The 24 explicitly tabulated permutations exhaust all vertex relabelings. -/
theorem permutation_exhaustive (p : Relabeling 4) :
    ∃ k : Fin 24, p.toFun = (permutation k).toFun := by
  have h01 : p.toFun 0 ≠ p.toFun 1 := fun h => by have := p.injective h; contradiction
  have h02 : p.toFun 0 ≠ p.toFun 2 := fun h => by have := p.injective h; contradiction
  have h03 : p.toFun 0 ≠ p.toFun 3 := fun h => by have := p.injective h; contradiction
  have h12 : p.toFun 1 ≠ p.toFun 2 := fun h => by have := p.injective h; contradiction
  have h13 : p.toFun 1 ≠ p.toFun 3 := fun h => by have := p.injective h; contradiction
  have h23 : p.toFun 2 ≠ p.toFun 3 := fun h => by have := p.injective h; contradiction
  have ht : ∃ k : Fin 24,
      p.toFun 0 = permFun k.val 0 ∧ p.toFun 1 = permFun k.val 1 ∧
      p.toFun 2 = permFun k.val 2 ∧ p.toFun 3 = permFun k.val 3 := by
    rcases fin4_cases (p.toFun 0) with h0 | h0 | h0 | h0 <;>
      rcases fin4_cases (p.toFun 1) with h1 | h1 | h1 | h1 <;>
      rcases fin4_cases (p.toFun 2) with h2 | h2 | h2 | h2 <;>
      rcases fin4_cases (p.toFun 3) with h3 | h3 | h3 | h3 <;>
      simp_all <;> decide
  obtain ⟨k,h0,h1,h2,h3⟩ := ht
  refine ⟨k, ?_⟩
  funext i
  rcases fin4_cases i with rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3

end QuiverProofs.Census
