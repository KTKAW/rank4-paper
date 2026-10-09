import Lean

/-!
Exact, labeled Fomin--Zelevinsky mutation over unbounded integers.
The conventions match both research notes: B i j > 0 means i → j.
No floating point, bounded search, or external mathematical axioms occur here.
-/
namespace QuiverProofs

abbrev Matrix (n : Nat) := Fin n → Fin n → Int

def correction (x y : Int) : Int :=
  max x 0 * max y 0 - max (-x) 0 * max (-y) 0

def mutate {n : Nat} (B : Matrix n) (k : Fin n) : Matrix n :=
  fun i j => if i = k ∨ j = k then -B i j
    else B i j + correction (B i k) (B k j)

def SkewSymmetric {n : Nat} (B : Matrix n) : Prop :=
  ∀ i j, B i j = -B j i

theorem correction_neg (x y : Int) :
    correction (-x) (-y) = -correction x y := by
  simp only [correction, Int.neg_neg]
  omega

theorem correction_skew (x y : Int) :
    correction (-y) (-x) = -correction x y := by
  simp only [correction, Int.neg_neg]
  grind

theorem mutation_involutive {n : Nat} (B : Matrix n) (k : Fin n) :
    mutate (mutate B k) k = B := by
  funext i j
  by_cases h : i = k ∨ j = k
  · simp [mutate, h]
  · simp only [mutate, h, ↓reduceIte, or_true, true_or]
    rw [correction_neg]
    omega

theorem mutation_preserves_skew {n : Nat} (B : Matrix n) (k : Fin n)
    (hB : SkewSymmetric B) : SkewSymmetric (mutate B k) := by
  intro i j
  by_cases h : i = k ∨ j = k
  · have h' : j = k ∨ i = k := h.symm
    simp only [mutate, h, h', ↓reduceIte]
    have := hB i j
    omega
  · have h' : ¬(j = k ∨ i = k) := by omega
    simp only [mutate, h, h', ↓reduceIte]
    rw [hB j k, hB k i, correction_skew]
    have := hB i j
    omega

def applyWord {n : Nat} (B : Matrix n) : List (Fin n) → Matrix n
  | [] => B
  | k :: ks => applyWord (mutate B k) ks

/-- A strict natural-valued ranking of all arrows: a topological ordering.
For a finite directed graph, this is the usual characterization of acyclicity.
-/
def Acyclic {n : Nat} (B : Matrix n) : Prop :=
  ∃ rank : Fin n → Nat, ∀ i j, 0 < B i j → rank i < rank j

def MutationAcyclic {n : Nat} (B : Matrix n) : Prop :=
  ∃ word : List (Fin n), Acyclic (applyWord B word)

/-- A nonempty directed walk, permitting repeated vertices. -/
inductive DirectedWalk {n : Nat} (B : Matrix n) : Fin n → Fin n → Prop
  | edge {i j} : 0 < B i j → DirectedWalk B i j
  | extend {i j k} : DirectedWalk B i j → 0 < B j k → DirectedWalk B i k

/-- The ranking definition really excludes every directed cycle. -/
theorem acyclic_no_closed_walk {n : Nat} (B : Matrix n) (h : Acyclic B)
    (i : Fin n) : ¬ DirectedWalk B i i := by
  obtain ⟨rank, hr⟩ := h
  have increasing : ∀ {j k}, DirectedWalk B j k → rank j < rank k := by
    intro j k path
    induction path with
    | edge hij => exact hr _ _ hij
    | extend _ hjk ih => exact Nat.lt_trans ih (hr _ _ hjk)
  intro path
  have := increasing path
  omega

theorem acyclic_is_mutationAcyclic {n : Nat} (B : Matrix n)
    (h : Acyclic B) : MutationAcyclic B := ⟨[], h⟩

theorem applyWord_append {n : Nat} (B : Matrix n)
    (u v : List (Fin n)) :
    applyWord B (u ++ v) = applyWord (applyWord B u) v := by
  induction u generalizing B with
  | nil => rfl
  | cons k ks ih => exact ih (mutate B k)

/-- Reachability is invariant under changing the starting point by one mutation. -/
theorem mutationAcyclic_iff {n : Nat} (B : Matrix n) (k : Fin n) :
    MutationAcyclic (mutate B k) ↔ MutationAcyclic B := by
  constructor
  · rintro ⟨word, h⟩
    exact ⟨k :: word, h⟩
  · rintro ⟨word, h⟩
    refine ⟨k :: word, ?_⟩
    simpa only [applyWord, mutation_involutive] using h

/-- Upper coordinates 01,02,03,12,13,23, including the negative lower triangle. -/
def ofSix (a b c d e f : Int) : Matrix 4 := fun i j =>
  match i.val, j.val with
  | 0, 1 => a | 0, 2 => b | 0, 3 => c
  | 1, 2 => d | 1, 3 => e | 2, 3 => f
  | 1, 0 => -a | 2, 0 => -b | 3, 0 => -c
  | 2, 1 => -d | 3, 1 => -e | 3, 2 => -f
  | _, _ => 0

theorem ofSix_skew (a b c d e f : Int) : SkewSymmetric (ofSix a b c d e f) := by
  intro i j
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases hi with rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl <;> simp [ofSix]

theorem ofSix_reconstruct (B : Matrix 4) (hB : SkewSymmetric B) :
    ofSix (B 0 1) (B 0 2) (B 0 3) (B 1 2) (B 1 3) (B 2 3) = B := by
  funext i j
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  unfold SkewSymmetric at hB
  rcases hi with rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl <;> simp [ofSix] <;> grind

end QuiverProofs
