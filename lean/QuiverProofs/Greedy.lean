import QuiverProofs.Mutation

/-!
The parametric greedy-descent counterexample from
`rank4_general_research/technical_note.tex`, Proposition `prop:greedy-failure`.
All statements quantify over arbitrary positive integers a and b.
-/
namespace QuiverProofs.Greedy

def quiver (a b : Int) : Matrix 4 := ofSix (-a) 0 1 (-b) 0 (-1)

private theorem fin4_cases (i : Fin 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega

theorem mutation_zero (a b : Int) (ha : 0 < a) :
    mutate (quiver a b) 0 = ofSix a 0 (-1) (-b) a (-1) := by
  funext i j
  rcases fin4_cases i with rfl | rfl | rfl | rfl <;>
    rcases fin4_cases j with rfl | rfl | rfl | rfl <;>
    simp [quiver, mutate, ofSix, correction] <;> grind

theorem mutation_one (a b : Int) (ha : 0 < a) (hb : 0 < b) :
    mutate (quiver a b) 1 = ofSix a (-a*b) 1 b 0 (-1) := by
  funext i j
  rcases fin4_cases i with rfl | rfl | rfl | rfl <;>
    rcases fin4_cases j with rfl | rfl | rfl | rfl <;>
    simp [quiver, mutate, ofSix, correction] <;> grind

theorem mutation_two (a b : Int) (hb : 0 < b) :
    mutate (quiver a b) 2 = ofSix (-a) 0 1 b (-b) 1 := by
  funext i j
  rcases fin4_cases i with rfl | rfl | rfl | rfl <;>
    rcases fin4_cases j with rfl | rfl | rfl | rfl <;>
    simp [quiver, mutate, ofSix, correction] <;> grind

theorem mutation_three (a b : Int) :
    mutate (quiver a b) 3 = ofSix (-a) 1 (-1) (-b) 0 1 := by
  funext i j
  rcases fin4_cases i with rfl | rfl | rfl | rfl <;>
    rcases fin4_cases j with rfl | rfl | rfl | rfl <;>
    simp [quiver, mutate, ofSix, correction] <;> grind

/-- Chronological word [2,3], as in the manuscript. -/
theorem word_two_three (a b : Int) (hb : 0 < b) :
    applyWord (quiver a b) [2,3] = ofSix (b-a) 0 (-1) 0 b (-1) := by
  simp only [applyWord, mutation_two a b hb]
  funext i j
  rcases fin4_cases i with rfl | rfl | rfl | rfl <;>
    rcases fin4_cases j with rfl | rfl | rfl | rfl <;>
    simp [mutate, ofSix, correction] <;> grind

theorem word_two_three_zero (a b : Int) (hb : 0 < b) (hba : a < b) :
    applyWord (quiver a b) [2,3,0] = ofSix (a-b) 0 1 0 a (-1) := by
  have hw : ([2,3,0] : List (Fin 4)) = [2,3] ++ [0] := rfl
  rw [hw, applyWord_append, word_two_three a b hb]
  simp only [applyWord]
  funext i j
  rcases fin4_cases i with rfl | rfl | rfl | rfl <;>
    rcases fin4_cases j with rfl | rfl | rfl | rfl <;>
    simp [mutate, ofSix, correction] <;> grind

/-- The family is cyclic: 1 → 0 → 3 → 2 → 1. -/
theorem not_acyclic (a b : Int) (ha : 0 < a) (hb : 0 < b) :
    ¬ Acyclic (quiver a b) := by
  rintro ⟨rank, hrank⟩
  have h10 := hrank 1 0 (by simpa [quiver, ofSix] using ha)
  have h03 := hrank 0 3 (by simp [quiver, ofSix])
  have h32 := hrank 3 2 (by simp [quiver, ofSix])
  have h21 := hrank 2 1 (by simpa [quiver, ofSix] using hb)
  omega

/-- Every member is mutation-acyclic, by a word of length at most three. -/
theorem mutation_acyclic (a b : Int) (ha : 0 < a) (hb : 0 < b) :
    MutationAcyclic (quiver a b) := by
  by_cases hab : b ≤ a
  · refine ⟨[2,3], ?_⟩
    rw [word_two_three a b hb]
    refine ⟨(fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 3 | _ => 1), ?_⟩
    intro i j
    rcases fin4_cases i with rfl | rfl | rfl | rfl <;>
      rcases fin4_cases j with rfl | rfl | rfl | rfl <;>
      simp [ofSix] <;> omega
  · have hba : a < b := by omega
    refine ⟨[2,3,0], ?_⟩
    rw [word_two_three_zero a b hb hba]
    refine ⟨(fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | _ => 2), ?_⟩
    intro i j
    rcases fin4_cases i with rfl | rfl | rfl | rfl <;>
      rcases fin4_cases j with rfl | rfl | rfl | rfl <;>
      simp [ofSix] <;> omega

/-- Absolute edge magnitude, expressed over unbounded integers. -/
def magnitude (x : Int) : Int := max x (-x)

/-- Total arrow multiplicity, counting each unordered pair once. -/
def totalWeight (B : Matrix 4) : Int :=
  magnitude (B 0 1) + magnitude (B 0 2) + magnitude (B 0 3) +
  magnitude (B 1 2) + magnitude (B 1 3) + magnitude (B 2 3)

theorem initial_weight (a b : Int) (ha : 0 < a) (hb : 0 < b) :
    totalWeight (quiver a b) = a+b+2 := by
  simp [totalWeight, quiver, ofSix, magnitude] <;> omega

theorem mutation_weights (a b : Int) (ha : 0 < a) (hb : 0 < b) :
    totalWeight (mutate (quiver a b) 0) = a+b+2+a ∧
    totalWeight (mutate (quiver a b) 1) = a+b+2+a*b ∧
    totalWeight (mutate (quiver a b) 2) = a+b+2+b ∧
    totalWeight (mutate (quiver a b) 3) = a+b+2+1 := by
  rw [mutation_zero a b ha, mutation_one a b ha hb,
    mutation_two a b hb, mutation_three a b]
  have hab := Int.mul_pos ha hb
  simp [totalWeight, ofSix, magnitude] <;> grind

/-- Every one-step mutation strictly increases total multiplicity. -/
theorem every_mutation_increases_weight (a b : Int) (ha : 0 < a) (hb : 0 < b)
    (k : Fin 4) : totalWeight (quiver a b) < totalWeight (mutate (quiver a b) k) := by
  have h := mutation_weights a b ha hb
  have hab := Int.mul_pos ha hb
  rw [initial_weight a b ha hb]
  rcases fin4_cases k with rfl | rfl | rfl | rfl <;> omega

/-- The cyclic MA family consists entirely of strict one-step weight minima. -/
theorem greedy_failure (a b : Int) (ha : 0 < a) (hb : 0 < b) :
    ¬ Acyclic (quiver a b) ∧ MutationAcyclic (quiver a b) ∧
    ∀ k : Fin 4, totalWeight (quiver a b) < totalWeight (mutate (quiver a b) k) := by
  exact ⟨not_acyclic a b ha hb, mutation_acyclic a b ha hb,
    every_mutation_increases_weight a b ha hb⟩

/-- Coordinatewise edge-magnitude dominance with at least one strict increase. -/
def MagnitudeIncreases (B B' : Matrix 4) : Prop :=
  (∀ i j, i < j → magnitude (B i j) ≤ magnitude (B' i j)) ∧
    ∃ i j, i < j ∧ magnitude (B i j) < magnitude (B' i j)

theorem every_mutation_increases_magnitudes (a b : Int)
    (ha : 0 < a) (hb : 0 < b) (k : Fin 4) :
    MagnitudeIncreases (quiver a b) (mutate (quiver a b) k) := by
  have hab := Int.mul_pos ha hb
  rcases fin4_cases k with rfl | rfl | rfl | rfl
  · rw [mutation_zero a b ha]
    constructor
    · intro i j hij
      rcases fin4_cases i with rfl | rfl | rfl | rfl <;>
        rcases fin4_cases j with rfl | rfl | rfl | rfl <;>
        simp [quiver, ofSix, magnitude] <;> grind
    · exact ⟨1, 3, by decide, by simp [quiver, ofSix, magnitude]; omega⟩
  · rw [mutation_one a b ha hb]
    constructor
    · intro i j hij
      rcases fin4_cases i with rfl | rfl | rfl | rfl <;>
        rcases fin4_cases j with rfl | rfl | rfl | rfl <;>
        simp [quiver, ofSix, magnitude] <;> grind
    · exact ⟨0, 2, by decide, by simp [quiver, ofSix, magnitude]; grind⟩
  · rw [mutation_two a b hb]
    constructor
    · intro i j hij
      rcases fin4_cases i with rfl | rfl | rfl | rfl <;>
        rcases fin4_cases j with rfl | rfl | rfl | rfl <;>
        simp [quiver, ofSix, magnitude] <;> grind
    · exact ⟨1, 3, by decide, by simp [quiver, ofSix, magnitude]; omega⟩
  · rw [mutation_three a b]
    constructor
    · intro i j hij
      rcases fin4_cases i with rfl | rfl | rfl | rfl <;>
        rcases fin4_cases j with rfl | rfl | rfl | rfl <;>
        simp [quiver, ofSix, magnitude] <;> grind
    · exact ⟨0, 2, by decide, by simp [quiver, ofSix, magnitude]; decide⟩

/-- The failure holds for every complexity strictly increasing under
coordinatewise edge-magnitude increases, with values in any ordered type. -/
theorem every_mutation_increases_complexity {α : Type} [LT α]
    (complexity : Matrix 4 → α)
    (hcomplexity : ∀ B B', MagnitudeIncreases B B' → complexity B < complexity B')
    (a b : Int) (ha : 0 < a) (hb : 0 < b) (k : Fin 4) :
    complexity (quiver a b) < complexity (mutate (quiver a b) k) := by
  exact hcomplexity _ _ (every_mutation_increases_magnitudes a b ha hb k)

end QuiverProofs.Greedy
