import QuiverProofs.Mutation

namespace QuiverProofs

def matrixPfaffian (B : Matrix 4) : Int :=
  B 0 1 * B 2 3 - B 0 2 * B 1 3 + B 0 3 * B 1 2

/-- The signed Pfaffian flips under every labeled rank-four mutation. -/
theorem pfaffian_mutation (a b c d e f : Int) (k : Fin 4) :
    matrixPfaffian (mutate (ofSix a b c d e f) k) =
      -matrixPfaffian (ofSix a b c d e f) := by
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp [matrixPfaffian, mutate, ofSix, correction, Int.max_def] <;>
    grind

theorem pfaffian_square_mutation (a b c d e f : Int) (k : Fin 4) :
    matrixPfaffian (mutate (ofSix a b c d e f) k)^2 =
      matrixPfaffian (ofSix a b c d e f)^2 := by
  rw [pfaffian_mutation]
  grind

theorem pfaffian_square_mutation_skew (B : Matrix 4) (k : Fin 4)
    (hB : SkewSymmetric B) :
    matrixPfaffian (mutate B k)^2 = matrixPfaffian B^2 := by
  conv => lhs; rw [← ofSix_reconstruct B hB]
  rw [pfaffian_square_mutation]
  rfl

/-- Pfaffian-square invariance for every finite mutation word, with no bound. -/
theorem pfaffian_square_word (B : Matrix 4) (word : List (Fin 4))
    (hB : SkewSymmetric B) :
    matrixPfaffian (applyWord B word)^2 = matrixPfaffian B^2 := by
  induction word generalizing B with
  | nil => rfl
  | cons k ks ih =>
    simp only [applyWord]
    rw [ih (mutate B k) (mutation_preserves_skew B k hB)]
    exact pfaffian_square_mutation_skew B k hB

end QuiverProofs
