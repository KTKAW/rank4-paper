import QuiverProofs.MAExistenceLiterature
import QuiverProofs.Cosquare

/-! Exact principal-coefficient evolution and local color laws.
`B i j > 0` means `i → j`, and `C i j` is frozen-to-mutable.
No all-word sign-coherence or root-theoretic existence premise is hidden here.
-/
namespace QuiverProofs.MAExistenceCoefficients
open MAExistenceLiterature

def identityCoefficients {n : Nat} : Matrix n :=
  fun i j => if i = j then 1 else 0

abbrev Seed (n : Nat) := Matrix n × Matrix n

def mutateSeed {n : Nat} (S : Seed n) (k : Fin n) : Seed n :=
  (mutate S.1 k, mutateCoefficients S.1 S.2 k)

def evolve {n : Nat} (B C : Matrix n) : List (Fin n) → Seed n
  | [] => (B, C)
  | k :: ks => evolve (mutate B k) (mutateCoefficients B C k) ks

def principalSeed {n : Nat} (B : Matrix n) (w : List (Fin n)) : Seed n :=
  evolve B identityCoefficients w

theorem evolve_exchange {n : Nat} (B C : Matrix n) (w : List (Fin n)) :
    (evolve B C w).1 = applyWord B w := by
  induction w generalizing B C with
  | nil => rfl
  | cons k ks ih => exact ih _ _

theorem evolve_append {n : Nat} (B C : Matrix n) (u v : List (Fin n)) :
    evolve B C (u ++ v) = evolve (evolve B C u).1 (evolve B C u).2 v := by
  induction u generalizing B C with
  | nil => rfl
  | cons k ks ih => exact ih _ _

theorem evolve_append_singleton {n : Nat} (B C : Matrix n)
    (w : List (Fin n)) (k : Fin n) :
    evolve B C (w ++ [k]) = mutateSeed (evolve B C w) k := by
  rw [evolve_append]
  rfl

theorem mutateCoefficients_involutive {n : Nat} (B C : Matrix n) (k : Fin n) :
    mutateCoefficients (mutate B k) (mutateCoefficients B C k) k = C := by
  funext i j
  by_cases hj : j = k
  · simp [mutateCoefficients, hj]
  · simp only [mutateCoefficients, hj, if_false, if_true,
      mutate, true_or, if_true]
    rw [correction_neg]
    omega

theorem mutateSeed_involutive {n : Nat} (S : Seed n) (k : Fin n) :
    mutateSeed (mutateSeed S k) k = S := by
  cases S with
  | mk B C =>
    simp only [mutateSeed, mutation_involutive, mutateCoefficients_involutive]

/-- Strict witnesses exclude the zero column from both colors. -/
def ColumnGreen {n : Nat} (C : Matrix n) (j : Fin n) : Prop :=
  (∀ i, 0 ≤ C i j) ∧ ∃ i, 0 < C i j

def ColumnRed {n : Nat} (C : Matrix n) (j : Fin n) : Prop :=
  (∀ i, C i j ≤ 0) ∧ ∃ i, C i j < 0

def SignCoherent {n : Nat} (C : Matrix n) : Prop :=
  ∀ j, ColumnGreen C j ∨ ColumnRed C j

def NonzeroColumns {n : Nat} (C : Matrix n) : Prop :=
  ∀ j, ∃ i, C i j ≠ 0

def columnColor {n : Nat} (C : Matrix n) (j : Fin n) : Bool :=
  decide (∀ i, 0 ≤ C i j)

theorem green_not_red {n : Nat} {C : Matrix n} {j : Fin n}
    (hg : ColumnGreen C j) : ¬ ColumnRed C j := by
  intro hr
  obtain ⟨i, hi⟩ := hg.2
  have := hr.1 i
  omega

theorem signCoherent_nonzero {n : Nat} {C : Matrix n}
    (h : SignCoherent C) : NonzeroColumns C := by
  intro j
  rcases h j with hg | hr
  · obtain ⟨i, hi⟩ := hg.2
    exact ⟨i, by omega⟩
  · obtain ⟨i, hi⟩ := hr.2
    exact ⟨i, by omega⟩

theorem color_green {n : Nat} {C : Matrix n} {j : Fin n}
    (h : ColumnGreen C j) : columnColor C j = true := by
  simp only [columnColor, decide_eq_true_eq]
  exact h.1

theorem color_red {n : Nat} {C : Matrix n} {j : Fin n}
    (h : ColumnRed C j) : columnColor C j = false := by
  simp only [columnColor, decide_eq_false_iff_not]
  intro hg
  obtain ⟨i, hi⟩ := h.2
  have := hg i
  omega

theorem color_iff_green {n : Nat} {C : Matrix n} (h : SignCoherent C)
    (j : Fin n) : columnColor C j = true ↔ ColumnGreen C j := by
  constructor
  · intro hc
    rcases h j with hg | hr
    · exact hg
    · rw [color_red hr] at hc
      cases hc
  · exact color_green

theorem color_iff_red {n : Nat} {C : Matrix n} (h : SignCoherent C)
    (j : Fin n) : columnColor C j = false ↔ ColumnRed C j := by
  constructor
  · intro hc
    rcases h j with hg | hr
    · rw [color_green hg] at hc
      cases hc
    · exact hr
  · exact color_red

theorem identity_green {n : Nat} (j : Fin n) :
    ColumnGreen (identityCoefficients : Matrix n) j := by
  constructor
  · intro i; simp only [identityCoefficients]; split <;> omega
  · exact ⟨j, by simp [identityCoefficients]⟩

theorem identity_signCoherent {n : Nat} :
    SignCoherent (identityCoefficients : Matrix n) :=
  fun j => Or.inl (identity_green j)

theorem pivot_green_iff_red {n : Nat} (B C : Matrix n) (k : Fin n) :
    ColumnGreen (mutateCoefficients B C k) k ↔ ColumnRed C k := by
  simp only [ColumnGreen, ColumnRed, mutateCoefficients, if_true,
    Int.neg_nonneg, Int.neg_pos]

theorem pivot_red_iff_green {n : Nat} (B C : Matrix n) (k : Fin n) :
    ColumnRed (mutateCoefficients B C k) k ↔ ColumnGreen C k := by
  simp only [ColumnGreen, ColumnRed, mutateCoefficients, if_true]
  constructor
  · rintro ⟨h, i, hi⟩
    refine ⟨(fun j => ?_), i, by omega⟩
    have := h j
    omega
  · rintro ⟨h, i, hi⟩
    refine ⟨(fun j => ?_), i, by omega⟩
    have := h j
    omega

theorem pivot_color_flips {n : Nat} (B C : Matrix n) (k : Fin n)
    (h : ColumnGreen C k ∨ ColumnRed C k) :
    columnColor (mutateCoefficients B C k) k = !(columnColor C k) := by
  rcases h with hg | hr
  · rw [color_green hg, color_red ((pivot_red_iff_green B C k).2 hg)]
    rfl
  · rw [color_red hr, color_green ((pivot_green_iff_red B C k).2 hr)]
    rfl

theorem green_retained {n : Nat} (B C : Matrix n) (k j : Fin n)
    (hkj : j ≠ k) (hk : ColumnGreen C k) (hj : ColumnGreen C j) :
    ColumnGreen (mutateCoefficients B C k) j := by
  have hm : 0 ≤ max (B k j) 0 := by omega
  constructor
  · intro i
    rw [mutateCoefficients_green B C k hk.1, if_neg hkj]
    have hmul := Int.mul_nonneg (hk.1 i) hm
    have := hj.1 i
    omega
  · obtain ⟨i, hi⟩ := hj.2
    refine ⟨i, ?_⟩
    rw [mutateCoefficients_green B C k hk.1, if_neg hkj]
    have hmul := Int.mul_nonneg (hk.1 i) hm
    omega

theorem red_retained {n : Nat} (B C : Matrix n) (k j : Fin n)
    (hkj : j ≠ k) (hk : ColumnRed C k) (hj : ColumnRed C j) :
    ColumnRed (mutateCoefficients B C k) j := by
  have hm : 0 ≤ max (-B k j) 0 := by omega
  constructor
  · intro i
    rw [mutateCoefficients_red B C k hk.1, if_neg hkj]
    have hmul := Int.mul_nonpos_of_nonpos_of_nonneg (hk.1 i) hm
    have := hj.1 i
    omega
  · obtain ⟨i, hi⟩ := hj.2
    refine ⟨i, ?_⟩
    rw [mutateCoefficients_red B C k hk.1, if_neg hkj]
    have hmul := Int.mul_nonpos_of_nonpos_of_nonneg (hk.1 i) hm
    omega

theorem firstMutation_signCoherent {n : Nat} (B : Matrix n) (k : Fin n) :
    SignCoherent (mutateCoefficients B identityCoefficients k) := by
  intro j
  by_cases h : j = k
  · subst j
    exact Or.inr ((pivot_red_iff_green B identityCoefficients k).2 (identity_green k))
  · exact Or.inl (green_retained B identityCoefficients k j h
      (identity_green k) (identity_green j))

/-- An elementary integral basis change for one coherent pivot column. -/
def coefficientChange (B : Matrix 4) (green : Bool) (k : Fin 4) : Matrix 4 :=
  fun i j => if i = k then
    (if j = k then -1 else max (if green then B k j else -B k j) 0)
    else if i = j then 1 else 0

private theorem fin4 (i : Fin 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega

theorem mul_coefficientChange (B C : Matrix 4) (green : Bool) (k i j : Fin 4) :
    Cosquare.mul C (coefficientChange B green k) i j =
      if j = k then -C i j
      else C i j + C i k * max (if green then B k j else -B k j) 0 := by
  rcases fin4 k with rfl | rfl | rfl | rfl <;>
    rcases fin4 j with rfl | rfl | rfl | rfl <;>
    simp [Cosquare.mul, coefficientChange] <;> omega

theorem coefficientChange_involutive (B : Matrix 4) (green : Bool) (k : Fin 4) :
    Cosquare.mul (coefficientChange B green k) (coefficientChange B green k) =
      Cosquare.one := by
  funext i j
  rw [mul_coefficientChange]
  by_cases hi : i = k <;> by_cases hj : j = k <;> by_cases hij : i = j <;>
    simp_all [coefficientChange, Cosquare.one, eq_comm]
  all_goals omega

theorem mutateCoefficients_as_basisChange (B C : Matrix 4) (k : Fin 4)
    (h : ColumnGreen C k ∨ ColumnRed C k) :
    mutateCoefficients B C k =
      Cosquare.mul C (coefficientChange B (columnColor C k) k) := by
  funext i j
  rw [mul_coefficientChange]
  rcases h with hg | hr
  · rw [color_green hg]
    exact mutateCoefficients_green B C k hg.1 i j
  · rw [color_red hr]
    exact mutateCoefficients_red B C k hr.1 i j

def IntegralBasis (C : Matrix 4) : Prop :=
  ∃ D : Matrix 4, Cosquare.mul D C = Cosquare.one ∧
    Cosquare.mul C D = Cosquare.one

theorem identity_integralBasis : IntegralBasis identityCoefficients := by
  refine ⟨Cosquare.one, ?_, ?_⟩
  all_goals change Cosquare.mul Cosquare.one Cosquare.one = Cosquare.one
  all_goals exact Cosquare.one_mul _

theorem integralBasis_mutation (B C : Matrix 4) (k : Fin 4)
    (hC : IntegralBasis C) (hk : ColumnGreen C k ∨ ColumnRed C k) :
    IntegralBasis (mutateCoefficients B C k) := by
  obtain ⟨D, hDC, hCD⟩ := hC
  let T := coefficientChange B (columnColor C k) k
  have hTT : Cosquare.mul T T = Cosquare.one := coefficientChange_involutive _ _ _
  rw [mutateCoefficients_as_basisChange B C k hk]
  refine ⟨Cosquare.mul T D, ?_, ?_⟩
  · change Cosquare.mul (Cosquare.mul T D) (Cosquare.mul C T) = Cosquare.one
    rw [Cosquare.mul_assoc, ← Cosquare.mul_assoc D, hDC, Cosquare.one_mul, hTT]
  · change Cosquare.mul (Cosquare.mul C T) (Cosquare.mul T D) = Cosquare.one
    rw [Cosquare.mul_assoc, ← Cosquare.mul_assoc T, hTT, Cosquare.one_mul, hCD]

theorem integralBasis_nonzero (C : Matrix 4) (hC : IntegralBasis C) :
    NonzeroColumns C := by
  classical
  obtain ⟨D, hDC, _⟩ := hC
  intro j
  by_cases h : ∃ i, C i j ≠ 0
  · exact h
  · have hz : ∀ i, C i j = 0 := by
      intro i
      exact Classical.not_not.mp (fun hi => h ⟨i, hi⟩)
    have he := congrFun (congrFun hDC j) j
    simp [Cosquare.mul, Cosquare.one, hz] at he

/-- Sign coherence alone, even together with an integral basis and acyclic
exchange matrix, is not a mutation-closed invariant. This example does not
claim that its coefficient matrix is reachable from the identity. -/
def mixedUpdateExample : Matrix 4 := fun i j =>
  if i = j then (if j = 1 then -1 else 1) else 0

theorem mixedUpdateExample_signCoherent : SignCoherent mixedUpdateExample := by
  intro j
  by_cases hj : j = 1
  · subst j
    right
    constructor
    · intro i; simp only [mixedUpdateExample]; split <;> simp <;> omega
    · exact ⟨1, by simp [mixedUpdateExample]⟩
  · left
    constructor
    · intro i; simp only [mixedUpdateExample, hj, if_false]; split <;> omega
    · exact ⟨j, by simp [mixedUpdateExample, hj]⟩

theorem mixedUpdateExample_integralBasis : IntegralBasis mixedUpdateExample := by
  have h : Cosquare.mul mixedUpdateExample mixedUpdateExample = Cosquare.one := by
    funext i j
    rcases fin4 i with rfl | rfl | rfl | rfl <;>
      rcases fin4 j with rfl | rfl | rfl | rfl <;>
      simp [Cosquare.mul, Cosquare.one, mixedUpdateExample]
  exact ⟨mixedUpdateExample, h, h⟩

theorem mixedUpdateExample_exchange_acyclic : Acyclic (ofSix 1 0 0 0 0 0) := by
  refine ⟨Fin.val, ?_⟩
  intro i j hij
  rcases fin4 i with rfl | rfl | rfl | rfl <;>
    rcases fin4 j with rfl | rfl | rfl | rfl <;>
    simp [ofSix] at hij ⊢

theorem mixedUpdateExample_not_preserved :
    ¬ SignCoherent (mutateCoefficients (ofSix 1 0 0 0 0 0) mixedUpdateExample 0) := by
  intro h
  rcases h 1 with hg | hr
  · have hi := hg.1 1
    simp [mutateCoefficients, correction, ofSix, mixedUpdateExample] at hi
  · have hi := hr.1 0
    simp [mutateCoefficients, correction, ofSix, mixedUpdateExample] at hi
    change (1 : Int) ≤ 0 at hi
    omega

/-- The sign-coherent counterexample fails the required Gram arrow-sign law:
its arrow `0 → 1` goes from green to red but its companion entry is positive. -/
theorem mixedUpdateExample_gram_wrong_sign :
    Cosquare.mul
      (Cosquare.mul (Cosquare.transpose mixedUpdateExample)
        (initialCompanion (ofSix 1 0 0 0 0 0))) mixedUpdateExample 0 1 = 1 := by
  simp [Cosquare.mul, Cosquare.transpose, mixedUpdateExample, initialCompanion, ofSix]

theorem mixedUpdateExample_colors :
    columnColor mixedUpdateExample 0 = true ∧
      columnColor mixedUpdateExample 1 = false := by
  constructor
  · apply color_green
    constructor
    · intro i; simp only [mixedUpdateExample]; split <;> simp <;> omega
    · exact ⟨0, by simp [mixedUpdateExample]⟩
  · apply color_red
    constructor
    · intro i; simp only [mixedUpdateExample]; split <;> simp <;> omega
    · exact ⟨1, by simp [mixedUpdateExample]⟩

/-- A connected, acyclic arbitrary-weight Cartan form has a mixed-sign
integer vector of norm two. Thus replacing real-root membership by the
diagonal Gram condition loses precisely the positivity information. -/
def mixedNormTwoVector : Fin 4 → Int := fun i =>
  if i = 0 ∨ i = 1 then 1 else if i = 2 then -1 else 0

def mixedNormTwoColumn : Matrix 4 := fun i j =>
  if j = 0 then mixedNormTwoVector i else 0

theorem mixedNormTwoVector_mixed :
    mixedNormTwoVector 0 = 1 ∧ mixedNormTwoVector 2 = -1 := by
  simp [mixedNormTwoVector]

theorem mixedNormTwoVector_norm :
    Cosquare.mul
      (Cosquare.mul (Cosquare.transpose mixedNormTwoColumn)
        (initialCompanion (ofSix 4 1 1 1 1 1))) mixedNormTwoColumn 0 0 = 2 := by
  simp [Cosquare.mul, Cosquare.transpose, mixedNormTwoColumn,
    mixedNormTwoVector, initialCompanion, ofSix]

theorem mixedNormTwoVector_exchange_acyclic : Acyclic (ofSix 4 1 1 1 1 1) := by
  refine ⟨Fin.val, ?_⟩
  intro i j hij
  rcases fin4 i with rfl | rfl | rfl | rfl <;>
    rcases fin4 j with rfl | rfl | rfl | rfl <;>
    simp [ofSix] at hij ⊢
  all_goals omega

end QuiverProofs.MAExistenceCoefficients
