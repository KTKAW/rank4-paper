import QuiverProofs.MAExistenceTeamBRootPositivity
import QuiverProofs.MAExistenceRankTwoRelations
import Mathlib.Data.Nat.Find
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.Perm.Basic

/-! Coordinate-sign prerequisites for the actual integral reflection orbit.
The all-root sign dichotomy is a separate obligation from identifying the
principal coefficient columns with that orbit. -/
namespace QuiverProofs.MAExistenceTeamCRootSigns
open MAExistenceLiterature MAExistenceCompanions MAExistenceCoefficients
open MAExistenceTeamBRootPositivity

set_option maxHeartbeats 0

private theorem fin4 (i : Fin 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega

def CoordinateNonnegative (x : Vector4) : Prop := ∀ i, 0 ≤ x i
def CoordinateNonpositive (x : Vector4) : Prop := ∀ i, x i ≤ 0
def CoordinateDichotomy (x : Vector4) : Prop :=
  CoordinateNonnegative x ∨ CoordinateNonpositive x

theorem simpleReflection_apply_ne (A : Matrix 4) (k i : Fin 4)
    (hik : i ≠ k) (x : Vector4) : simpleReflection A k x i = x i := by
  simp [simpleReflection, reflection, simple, hik]

theorem pairing_simple (A : Matrix 4) (k : Fin 4) (x : Vector4) :
    pairing A (simple k) x =
      A k 0 * x 0 + A k 1 * x 1 + A k 2 * x 2 + A k 3 * x 3 := by
  rcases fin4 k with rfl | rfl | rfl | rfl <;> simp [pairing, simple]

theorem simpleReflection_apply_self (A : Matrix 4) (k : Fin 4) (x : Vector4) :
    simpleReflection A k x k = x k -
      (A k 0 * x 0 + A k 1 * x 1 + A k 2 * x 2 + A k 3 * x 3) := by
  simp [simpleReflection, reflection, simple, pairing_simple]

def neighborSum (B : Matrix 4) (k : Fin 4) (x : Vector4) : Int :=
  (if k = 0 then 0 else (B k 0).natAbs * x 0) +
  (if k = 1 then 0 else (B k 1).natAbs * x 1) +
  (if k = 2 then 0 else (B k 2).natAbs * x 2) +
  (if k = 3 then 0 else (B k 3).natAbs * x 3)

theorem initial_simpleReflection_pivot (B : Matrix 4) (k : Fin 4) (x : Vector4) :
    simpleReflection (initialCompanion B) k x k = -x k + neighborSum B k x := by
  rw [simpleReflection_apply_self]
  rcases fin4 k with rfl | rfl | rfl | rfl <;> simp [initialCompanion, neighborSum] <;> grind

theorem initial_simpleReflection_nonnegative (B : Matrix 4) (k : Fin 4)
    (x : Vector4) (hx : CoordinateNonnegative x)
    (hk : x k ≤ neighborSum B k x) :
    CoordinateNonnegative (simpleReflection (initialCompanion B) k x) := by
  intro i
  by_cases hik : i = k
  · subst i
    rw [initial_simpleReflection_pivot]
    omega
  · rw [simpleReflection_apply_ne _ _ _ hik]
    exact hx i

theorem rootDichotomy_signCoherent (B₀ C : Matrix 4)
    (hB₀ : SkewSymmetric B₀)
    (hdichotomy : ∀ r, RealRoot (initialCompanion B₀) r → CoordinateDichotomy r)
    (hroots : ∀ j, RealRoot (initialCompanion B₀) (column C j)) :
    SignCoherent C := by
  have hA := initialCompanion_quasiCartan B₀ hB₀
  intro j
  obtain ⟨i, hi⟩ := realRoot_nonzero _ hA.1 hA.2.1 (hroots j)
  rcases hdichotomy _ (hroots j) with hg | hr
  · exact Or.inl ⟨hg, i, by have := hg i; change C i j ≠ 0 at hi; change 0 ≤ C i j at this; omega⟩
  · exact Or.inr ⟨hr, i, by have := hr i; change C i j ≠ 0 at hi; change C i j ≤ 0 at this; omega⟩

/-! Minimal word length in the actual reflection group. This construction does
not assume an abstract Coxeter presentation is faithful. -/

def simplePerm (A : Matrix 4) (hd : ∀ i, A i i = 2) (k : Fin 4) :
    Equiv.Perm Vector4 where
  toFun := simpleReflection A k
  invFun := simpleReflection A k
  left_inv x := reflection_involutive A (simple k) x (by rw [pairing_simple_self, hd])
  right_inv x := reflection_involutive A (simple k) x (by rw [pairing_simple_self, hd])

@[simp] theorem simplePerm_apply (A : Matrix 4) (hd : ∀ i, A i i = 2)
    (k : Fin 4) (x : Vector4) : simplePerm A hd k x = simpleReflection A k x := rfl

@[simp] theorem simplePerm_inv (A : Matrix 4) (hd : ∀ i, A i i = 2) (k : Fin 4) :
    (simplePerm A hd k)⁻¹ = simplePerm A hd k := rfl

@[simp] theorem simplePerm_sq (A : Matrix 4) (hd : ∀ i, A i i = 2) (k : Fin 4) :
    simplePerm A hd k * simplePerm A hd k = 1 := by
  rw [←simplePerm_inv A hd k]
  exact inv_mul_cancel _

def wordPerm (A : Matrix 4) (hd : ∀ i, A i i = 2) : List (Fin 4) → Equiv.Perm Vector4
  | [] => 1
  | k :: w => simplePerm A hd k * wordPerm A hd w

@[simp] theorem wordPerm_nil (A : Matrix 4) (hd : ∀ i, A i i = 2) :
    wordPerm A hd [] = 1 := rfl

@[simp] theorem wordPerm_cons (A : Matrix 4) (hd : ∀ i, A i i = 2)
    (k : Fin 4) (w : List (Fin 4)) :
    wordPerm A hd (k :: w) = simplePerm A hd k * wordPerm A hd w := rfl

@[simp] theorem wordPerm_append (A : Matrix 4) (hd : ∀ i, A i i = 2)
    (u v : List (Fin 4)) : wordPerm A hd (u ++ v) = wordPerm A hd u * wordPerm A hd v := by
  induction u with
  | nil => simp
  | cons k u ih => simp [ih, mul_assoc]

theorem wordPerm_reverse (A : Matrix 4) (hd : ∀ i, A i i = 2) (w : List (Fin 4)) :
    wordPerm A hd w.reverse = (wordPerm A hd w)⁻¹ := by
  induction w with
  | nil => simp
  | cons k w ih => simp [List.reverse_cons, ih]

def reflectionGroup (A : Matrix 4) (hd : ∀ i, A i i = 2) : Subgroup (Equiv.Perm Vector4) where
  carrier := {g | ∃ w, wordPerm A hd w = g}
  one_mem' := ⟨[], rfl⟩
  mul_mem' := by
    rintro x y ⟨u, rfl⟩ ⟨v, rfl⟩
    exact ⟨u ++ v, wordPerm_append A hd u v⟩
  inv_mem' := by
    rintro x ⟨u, rfl⟩
    exact ⟨u.reverse, wordPerm_reverse A hd u⟩

abbrev ReflectionGroup (A : Matrix 4) (hd : ∀ i, A i i = 2) := reflectionGroup A hd

def generator (A : Matrix 4) (hd : ∀ i, A i i = 2) (k : Fin 4) : ReflectionGroup A hd :=
  ⟨simplePerm A hd k, [k], by simp⟩

def wordElement (A : Matrix 4) (hd : ∀ i, A i i = 2)
    (w : List (Fin 4)) : ReflectionGroup A hd := ⟨wordPerm A hd w, w, rfl⟩

@[simp] theorem generator_sq (A : Matrix 4) (hd : ∀ i, A i i = 2) (k : Fin 4) :
    generator A hd k * generator A hd k = 1 := by
  apply Subtype.ext
  exact simplePerm_sq A hd k

@[simp] theorem wordElement_nil (A : Matrix 4) (hd : ∀ i, A i i = 2) :
    wordElement A hd [] = 1 := rfl

@[simp] theorem wordElement_cons (A : Matrix 4) (hd : ∀ i, A i i = 2)
    (k : Fin 4) (w : List (Fin 4)) :
    wordElement A hd (k :: w) = generator A hd k * wordElement A hd w := rfl

@[simp] theorem wordElement_append (A : Matrix 4) (hd : ∀ i, A i i = 2)
    (u v : List (Fin 4)) : wordElement A hd (u ++ v) = wordElement A hd u * wordElement A hd v := by
  apply Subtype.ext
  exact wordPerm_append A hd u v

theorem wordElement_surjective (A : Matrix 4) (hd : ∀ i, A i i = 2)
    (g : ReflectionGroup A hd) : ∃ w, wordElement A hd w = g := by
  obtain ⟨w, hw⟩ := g.property
  exact ⟨w, Subtype.ext hw⟩

noncomputable def wordLength (A : Matrix 4) (hd : ∀ i, A i i = 2)
    (g : ReflectionGroup A hd) : Nat := by
  classical
  exact Nat.find (show ∃ n, ∃ w, w.length = n ∧ wordElement A hd w = g from by
    obtain ⟨w, hw⟩ := wordElement_surjective A hd g
    exact ⟨w.length, w, rfl, hw⟩)

theorem exists_minimal_word (A : Matrix 4) (hd : ∀ i, A i i = 2)
    (g : ReflectionGroup A hd) :
    ∃ w, w.length = wordLength A hd g ∧ wordElement A hd w = g := by
  classical
  unfold wordLength
  exact Nat.find_spec (p := fun n => ∃ w, w.length = n ∧ wordElement A hd w = g) _

theorem wordLength_le (A : Matrix 4) (hd : ∀ i, A i i = 2) (w : List (Fin 4)) :
    wordLength A hd (wordElement A hd w) ≤ w.length := by
  classical
  unfold wordLength
  exact Nat.find_min' _ ⟨w, rfl, rfl⟩

@[simp] theorem wordLength_one (A : Matrix 4) (hd : ∀ i, A i i = 2) :
    wordLength A hd 1 = 0 := by
  simpa using wordLength_le A hd []

theorem wordLength_eq_zero (A : Matrix 4) (hd : ∀ i, A i i = 2)
    (g : ReflectionGroup A hd) (h : wordLength A hd g = 0) : g = 1 := by
  obtain ⟨w, hw, he⟩ := exists_minimal_word A hd g
  have : w = [] := List.length_eq_zero_iff.mp (hw.trans h)
  simpa [this] using he.symm

theorem wordLength_mul_le (A : Matrix 4) (hd : ∀ i, A i i = 2)
    (g h : ReflectionGroup A hd) :
    wordLength A hd (g * h) ≤ wordLength A hd g + wordLength A hd h := by
  obtain ⟨u, hu, rfl⟩ := exists_minimal_word A hd g
  obtain ⟨v, hv, rfl⟩ := exists_minimal_word A hd h
  have := wordLength_le A hd (u ++ v)
  simpa [hu, hv] using this

theorem wordLength_mul_generator_le (A : Matrix 4) (hd : ∀ i, A i i = 2)
    (g : ReflectionGroup A hd) (k : Fin 4) :
    wordLength A hd (g * generator A hd k) ≤ wordLength A hd g + 1 := by
  have h := wordLength_mul_le A hd g (generator A hd k)
  have hk : wordLength A hd (generator A hd k) ≤ 1 := by
    simpa using wordLength_le A hd [k]
  omega

theorem wordLength_descent (A : Matrix 4) (hd : ∀ i, A i i = 2)
    (g : ReflectionGroup A hd) (k : Fin 4)
    (hk : wordLength A hd (g * generator A hd k) < wordLength A hd g) :
    wordLength A hd (g * generator A hd k) + 1 = wordLength A hd g := by
  have h := wordLength_mul_generator_le A hd (g * generator A hd k) k
  simp only [mul_assoc, generator_sq, mul_one] at h
  omega

theorem exists_right_descent (A : Matrix 4) (hd : ∀ i, A i i = 2)
    (g : ReflectionGroup A hd) (hg : 0 < wordLength A hd g) :
    ∃ k, wordLength A hd (g * generator A hd k) < wordLength A hd g := by
  obtain ⟨w, hw, he⟩ := exists_minimal_word A hd g
  have hn : w ≠ [] := by intro h; simp [h] at hw; omega
  obtain ⟨v, k, hv⟩ : ∃ v k, w = v ++ [k] := by
    cases hr : w.reverse with
    | nil => exact False.elim (hn (by simpa using congrArg List.reverse hr))
    | cons k v =>
      exact ⟨v.reverse, k, by simpa using congrArg List.reverse hr⟩
  have hbound := wordLength_le A hd v
  have heq : g * generator A hd k = wordElement A hd v := by
    rw [←he, hv]
    simp [mul_assoc]
  refine ⟨k, ?_⟩
  rw [heq]
  simp [hv] at hw
  omega

/-- Remove right descents belonging to a chosen pair until both generators
are ascents. The tail remains a minimal word in the full actual group. -/
theorem twoGenerator_decomposition (A : Matrix 4) (hd : ∀ i, A i i = 2)
    (g : ReflectionGroup A hd) (s t : Fin 4) :
    ∃ x : ReflectionGroup A hd, ∃ u : List (Fin 4),
      g = x * wordElement A hd u ∧
      wordLength A hd g = wordLength A hd x + u.length ∧
      (∀ k ∈ u, k = s ∨ k = t) ∧
      wordLength A hd x ≤ wordLength A hd (x * generator A hd s) ∧
      wordLength A hd x ≤ wordLength A hd (x * generator A hd t) := by
  have inductionLemma : ∀ n, ∀ g : ReflectionGroup A hd, wordLength A hd g = n →
      ∃ x : ReflectionGroup A hd, ∃ u : List (Fin 4),
        g = x * wordElement A hd u ∧
        wordLength A hd g = wordLength A hd x + u.length ∧
        (∀ k ∈ u, k = s ∨ k = t) ∧
        wordLength A hd x ≤ wordLength A hd (x * generator A hd s) ∧
        wordLength A hd x ≤ wordLength A hd (x * generator A hd t) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro g hg
      by_cases hs : wordLength A hd (g * generator A hd s) < wordLength A hd g
      · obtain ⟨x, u, he, hl, hu, hxs, hxt⟩ :=
          ih _ (by omega) (g * generator A hd s) rfl
        have hdrop := wordLength_descent A hd g s hs
        refine ⟨x, u ++ [s], ?_, ?_, ?_, hxs, hxt⟩
        · calc
            g = (g * generator A hd s) * generator A hd s := by
              simp [mul_assoc]
            _ = x * wordElement A hd (u ++ [s]) := by rw [he]; simp [mul_assoc]
        · simp only [List.length_append, List.length_singleton]
          omega
        · intro k hk
          rcases List.mem_append.mp hk with hk | hk
          · exact hu k hk
          · exact Or.inl (List.mem_singleton.mp hk)
      · by_cases ht : wordLength A hd (g * generator A hd t) < wordLength A hd g
        · obtain ⟨x, u, he, hl, hu, hxs, hxt⟩ :=
            ih _ (by omega) (g * generator A hd t) rfl
          have hdrop := wordLength_descent A hd g t ht
          refine ⟨x, u ++ [t], ?_, ?_, ?_, hxs, hxt⟩
          · calc
              g = (g * generator A hd t) * generator A hd t := by
                simp [mul_assoc]
              _ = x * wordElement A hd (u ++ [t]) := by rw [he]; simp [mul_assoc]
          · simp only [List.length_append, List.length_singleton]
            omega
          · intro k hk
            rcases List.mem_append.mp hk with hk | hk
            · exact hu k hk
            · exact Or.inr (List.mem_singleton.mp hk)
        · exact ⟨g, [], by simp, by simp, by simp, by omega, by omega⟩
  exact inductionLemma _ g rfl

theorem decomposition_tail_minimal (A : Matrix 4) (hd : ∀ i, A i i = 2)
    (g x : ReflectionGroup A hd) (u : List (Fin 4))
    (he : g = x * wordElement A hd u)
    (hl : wordLength A hd g = wordLength A hd x + u.length) :
    wordLength A hd (wordElement A hd u) = u.length := by
  have h := wordLength_mul_le A hd x (wordElement A hd u)
  have hb := wordLength_le A hd u
  rw [←he] at h
  omega

theorem simpleReflection_combination (A : Matrix 4) (k : Fin 4)
    (x y : Vector4) (a b : Int) :
    simpleReflection A k (fun i => a * x i + b * y i) =
      fun i => a * simpleReflection A k x i + b * simpleReflection A k y i := by
  funext i
  simp only [simpleReflection, reflection, pairing_simple]
  grind

theorem wordPerm_combination (A : Matrix 4) (hd : ∀ i, A i i = 2)
    (w : List (Fin 4)) (x y : Vector4) (a b : Int) :
    wordPerm A hd w (fun i => a * x i + b * y i) =
      fun i => a * wordPerm A hd w x i + b * wordPerm A hd w y i := by
  induction w with
  | nil => rfl
  | cons k w ih =>
      simp only [wordPerm_cons, Equiv.Perm.mul_apply, simplePerm_apply]
      rw [ih, simpleReflection_combination]

theorem group_combination (A : Matrix 4) (hd : ∀ i, A i i = 2)
    (g : ReflectionGroup A hd) (x y : Vector4) (a b : Int) :
    g.val (fun i => a * x i + b * y i) =
      fun i => a * g.val x i + b * g.val y i := by
  obtain ⟨w, hw⟩ := g.property
  rw [←hw]
  exact wordPerm_combination A hd w x y a b

theorem pairing_simples (A : Matrix 4) (k j : Fin 4) :
    pairing A (simple k) (simple j) = A k j := by
  rcases fin4 k with rfl | rfl | rfl | rfl <;>
    rcases fin4 j with rfl | rfl | rfl | rfl <;> simp [pairing, simple]

theorem simpleReflection_simple (A : Matrix 4) (k j : Fin 4) :
    simpleReflection A k (simple j) =
      fun i => simple j i - A k j * simple k i := by
  funext i
  simp only [simpleReflection, MAExistenceTeamBRootPositivity.reflection, pairing_simples]

theorem simpleReflection_simple_self (A : Matrix 4) (hd : ∀ i, A i i = 2)
    (k : Fin 4) : simpleReflection A k (simple k) = fun i => -simple k i := by
  rw [simpleReflection_simple, hd]
  funext i
  omega

theorem realRoot_word (A : Matrix 4) (hd : ∀ i, A i i = 2)
    {r : Vector4} (hr : RealRoot A r) :
    ∃ w : List (Fin 4), ∃ k, r = wordPerm A hd w (simple k) := by
  induction hr with
  | simple k => exact ⟨[], k, rfl⟩
  | reflect j hr ih =>
      obtain ⟨w, k, rfl⟩ := ih
      exact ⟨j :: w, k, rfl⟩

/-- An alternating word whose rightmost letter is `t`. -/
def alternatingTail (s t : Fin 4) : Nat → List (Fin 4)
  | 0 => []
  | n + 1 => alternatingTail t s n ++ [t]

@[simp] theorem alternatingTail_length (s t : Fin 4) (n : Nat) :
    (alternatingTail s t n).length = n := by
  induction n generalizing s t with
  | zero => rfl
  | succ n ih => simp [alternatingTail, ih]

theorem alternatingTail_left (s t : Fin 4) (n : Nat) :
    alternatingTail s t (n + 1) =
      (if n % 2 = 0 then t else s) :: alternatingTail s t n := by
  induction n generalizing s t with
  | zero => simp [alternatingTail]
  | succ n ih =>
      rw [alternatingTail, ih t s]
      by_cases hn : n % 2 = 0
      · have hnext : (n + 1) % 2 ≠ 0 := by omega
        simp [hn, hnext, alternatingTail]
      · have hnext : (n + 1) % 2 = 0 := by omega
        simp [hn, hnext, alternatingTail]

private theorem exists_last {u : List (Fin 4)} (hu : u ≠ []) :
    ∃ v k, u = v ++ [k] := by
  cases hr : u.reverse with
  | nil => exact False.elim (hu (by simpa using congrArg List.reverse hr))
  | cons k v => exact ⟨v.reverse, k, by simpa using congrArg List.reverse hr⟩

/-- A minimal two-letter word which is an ascent at `s` alternates and ends
in the other letter. This is an ambient-group statement, with no assumption
that a dihedral subgroup has a Coxeter presentation. -/
theorem twoGenerator_ascent_word (A : Matrix 4) (hd : ∀ i, A i i = 2)
    (s t : Fin 4) (u : List (Fin 4))
    (hu : ∀ k ∈ u, k = s ∨ k = t)
    (hmin : wordLength A hd (wordElement A hd u) = u.length)
    (hasc : wordLength A hd (wordElement A hd u) ≤
      wordLength A hd (wordElement A hd u * generator A hd s)) :
    u = alternatingTail s t u.length := by
  have aux : ∀ n, ∀ s t, ∀ u : List (Fin 4), u.length = n →
      (∀ k ∈ u, k = s ∨ k = t) →
      wordLength A hd (wordElement A hd u) = u.length →
      wordLength A hd (wordElement A hd u) ≤
        wordLength A hd (wordElement A hd u * generator A hd s) →
      u = alternatingTail s t u.length := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s t u hn hu hmin hasc
      by_cases hnil : u = []
      · simp [hnil, alternatingTail]
      · obtain ⟨v, k, rfl⟩ := exists_last hnil
        have hvbound := wordLength_le A hd v
        have hvstep := wordLength_mul_generator_le A hd (wordElement A hd v) k
        simp only [wordElement_append, wordElement_cons, wordElement_nil, mul_one,
          List.length_append, List.length_singleton] at hn hmin hasc
        have hvmin : wordLength A hd (wordElement A hd v) = v.length := by omega
        have hk := hu k (by simp)
        rcases hk with hks | hkt
        · subst k
          simp only [mul_assoc, generator_sq, mul_one] at hasc
          omega
        · subst k
          have hv : v = alternatingTail t s v.length :=
            ih v.length (by omega) t s v rfl
              (by intro j hj; exact (hu j (List.mem_append_left _ hj)).symm)
              hvmin (by omega)
          simp only [List.length_append, List.length_singleton]
          change v ++ [t] = alternatingTail t s (v.length) ++ [t]
          exact congrArg (fun w => w ++ [t]) hv
  exact aux u.length s t u rfl hu hmin hasc

theorem rankTwo_reflect_first (A : Matrix 4) (hd : ∀ i, A i i = 2)
    (s t : Fin 4) (a b : Int) :
    simpleReflection A s (fun i => a * simple s i + b * simple t i) =
      fun i => (-a - A s t * b) * simple s i + b * simple t i := by
  rw [simpleReflection_combination, simpleReflection_simple_self A hd,
    simpleReflection_simple]
  funext i
  grind

theorem rankTwo_reflect_second (A : Matrix 4) (hd : ∀ i, A i i = 2)
    (s t : Fin 4) (a b : Int) :
    simpleReflection A t (fun i => a * simple s i + b * simple t i) =
      fun i => a * simple s i + (-b - A t s * a) * simple t i := by
  rw [simpleReflection_combination, simpleReflection_simple_self A hd,
    simpleReflection_simple]
  funext i
  grind

/-- The infinite-dihedral case keeps a nonnegative dominant coefficient after
each alternating reflection, for every integral edge magnitude at least two. -/
theorem alternatingTail_nonnegative_large (A : Matrix 4)
    (hA : ∀ i j, A i j = A j i) (hd : ∀ i, A i i = 2)
    (s t : Fin 4) (hlarge : 2 ≤ -A s t) (n : Nat) :
    ∃ a b : Int, 0 ≤ a ∧ 0 ≤ b ∧
      (if n % 2 = 0 then b ≤ a else a ≤ b) ∧
      wordPerm A hd (alternatingTail s t n) (simple s) =
        fun i => a * simple s i + b * simple t i := by
  induction n with
  | zero => exact ⟨1, 0, by omega, by omega, by simp, by simp [alternatingTail]⟩
  | succ n ih =>
      obtain ⟨a, b, ha, hb, hdom, he⟩ := ih
      rw [alternatingTail_left]
      simp only [wordPerm_cons, Equiv.Perm.mul_apply, simplePerm_apply, he]
      have hsym := hA t s
      by_cases hn : n % 2 = 0
      · have hnext : (n + 1) % 2 ≠ 0 := by omega
        simp only [hn, if_true] at hdom ⊢
        rw [rankTwo_reflect_second A hd]
        refine ⟨a, -b - A t s * a, ha, ?_, ?_, rfl⟩
        · rw [hsym]
          have hm : a * 2 ≤ a * (-A s t) := Int.mul_le_mul_of_nonneg_left hlarge ha
          grind
        · simp only [hnext, if_false]
          rw [hsym]
          have hm : a * 2 ≤ a * (-A s t) := Int.mul_le_mul_of_nonneg_left hlarge ha
          grind
      · have hnext : (n + 1) % 2 = 0 := by omega
        simp only [hn, if_false] at hdom ⊢
        rw [rankTwo_reflect_first A hd]
        refine ⟨-a - A s t * b, b, ?_, hb, ?_, rfl⟩
        · have hm : b * 2 ≤ b * (-A s t) := Int.mul_le_mul_of_nonneg_left hlarge hb
          grind
        · simp only [hnext, if_true]
          have hm : b * 2 ≤ b * (-A s t) := Int.mul_le_mul_of_nonneg_left hlarge hb
          grind

theorem alternatingTail_three (A : Matrix 4) (hd : ∀ i, A i i = 2)
    (s t : Fin 4) (n : Nat) :
    wordElement A hd (alternatingTail s t (n + 3)) =
      wordElement A hd (alternatingTail t s n) *
        (generator A hd t * generator A hd s * generator A hd t) := by
  simp [alternatingTail, mul_assoc]

theorem alternatingTail_four (A : Matrix 4) (hd : ∀ i, A i i = 2)
    (s t : Fin 4) (n : Nat) :
    wordElement A hd (alternatingTail s t (n + 4)) =
      wordElement A hd (alternatingTail s t n) *
        (generator A hd s * generator A hd t * generator A hd s * generator A hd t) := by
  simp [alternatingTail, mul_assoc]

theorem alternatingTail_length_le_two_of_commute (A : Matrix 4)
    (hd : ∀ i, A i i = 2) (s t : Fin 4) (n : Nat)
    (hc : generator A hd s * generator A hd t = generator A hd t * generator A hd s)
    (hmin : wordLength A hd (wordElement A hd (alternatingTail s t n)) = n) : n ≤ 2 := by
  by_contra hn
  have he : n = (n - 3) + 3 := by omega
  have hcancel : generator A hd t * generator A hd s * generator A hd t = generator A hd s := by
    rw [←hc]
    simp [mul_assoc]
  have helem : wordElement A hd (alternatingTail s t n) =
      wordElement A hd (alternatingTail t s (n - 3) ++ [s]) := by
    rw [he, alternatingTail_three, hcancel]
    simp
  have hb := wordLength_le A hd (alternatingTail t s (n - 3) ++ [s])
  rw [←helem, hmin] at hb
  simp only [List.length_append, alternatingTail_length, List.length_singleton] at hb
  omega

theorem alternatingTail_length_le_three_of_braid (A : Matrix 4)
    (hd : ∀ i, A i i = 2) (s t : Fin 4) (n : Nat)
    (hb : generator A hd s * generator A hd t * generator A hd s =
      generator A hd t * generator A hd s * generator A hd t)
    (hmin : wordLength A hd (wordElement A hd (alternatingTail s t n)) = n) : n ≤ 3 := by
  by_contra hn
  have he : n = (n - 4) + 4 := by omega
  have hcancel : generator A hd s * generator A hd t * generator A hd s * generator A hd t =
      generator A hd t * generator A hd s := by
    rw [hb]
    simp [mul_assoc]
  have helem : wordElement A hd (alternatingTail s t n) =
      wordElement A hd (alternatingTail s t (n - 4) ++ [t, s]) := by
    rw [he, alternatingTail_four, hcancel]
    simp
  have hbound := wordLength_le A hd (alternatingTail s t (n - 4) ++ [t, s])
  rw [←helem, hmin] at hbound
  simp only [List.length_append, alternatingTail_length, List.length_cons, List.length_nil] at hbound
  omega

theorem rankTwo_ascent_nonnegative (A : Matrix 4)
    (hA : ∀ i j, A i j = A j i) (hd : ∀ i, A i i = 2)
    (s t : Fin 4) (hnonpos : A s t ≤ 0)
    (hc : A s t = 0 → generator A hd s * generator A hd t = generator A hd t * generator A hd s)
    (hb : A s t = -1 → generator A hd s * generator A hd t * generator A hd s =
      generator A hd t * generator A hd s * generator A hd t)
    (u : List (Fin 4)) (hu : ∀ k ∈ u, k = s ∨ k = t)
    (hmin : wordLength A hd (wordElement A hd u) = u.length)
    (hasc : wordLength A hd (wordElement A hd u) ≤
      wordLength A hd (wordElement A hd u * generator A hd s)) :
    ∃ a b : Int, 0 ≤ a ∧ 0 ≤ b ∧
      wordPerm A hd u (simple s) = fun i => a * simple s i + b * simple t i := by
  have halt := twoGenerator_ascent_word A hd s t u hu hmin hasc
  have hmintail : wordLength A hd (wordElement A hd (alternatingTail s t u.length)) = u.length := by
    rw [←halt]
    exact hmin
  have hasctail : wordLength A hd (wordElement A hd (alternatingTail s t u.length)) ≤
      wordLength A hd (wordElement A hd (alternatingTail s t u.length) * generator A hd s) := by
    rw [←halt]
    exact hasc
  rw [halt]
  have hsym := hA t s
  by_cases hz : A s t = 0
  · have hcomm := hc hz
    have hn := alternatingTail_length_le_two_of_commute A hd s t u.length hcomm hmintail
    have hlen : u.length = 0 ∨ u.length = 1 ∨ u.length = 2 := by omega
    rcases hlen with hlen | hlen | hlen
    · exact ⟨1, 0, by omega, by omega, by simp [hlen, alternatingTail]⟩
    · refine ⟨1, 0, by omega, by omega, ?_⟩
      simp only [hlen, alternatingTail, List.nil_append, wordPerm_cons, wordPerm_nil,
        Equiv.Perm.mul_apply, Equiv.Perm.one_apply, simplePerm_apply]
      rw [simpleReflection_simple, hsym, hz]
      funext i
      simp
    · have hcancel : wordElement A hd (alternatingTail s t 2) * generator A hd s =
          generator A hd t := by
        simp only [alternatingTail, List.nil_append,
          List.cons_append, wordElement_cons, wordElement_nil, mul_one]
        rw [hcomm]
        simp [mul_assoc]
      rw [hlen, hcancel] at hasctail
      rw [hlen] at hmintail
      have hbound : wordLength A hd (generator A hd t) ≤ 1 := by simpa using wordLength_le A hd [t]
      omega
  · by_cases ho : A s t = -1
    · have hbraid := hb ho
      have hn := alternatingTail_length_le_three_of_braid A hd s t u.length hbraid hmintail
      have hlen : u.length = 0 ∨ u.length = 1 ∨ u.length = 2 ∨ u.length = 3 := by omega
      rcases hlen with hlen | hlen | hlen | hlen
      · exact ⟨1, 0, by omega, by omega, by simp [hlen, alternatingTail]⟩
      · refine ⟨1, 1, by omega, by omega, ?_⟩
        simp only [hlen, alternatingTail, List.nil_append, wordPerm_cons, wordPerm_nil,
          Equiv.Perm.mul_apply, Equiv.Perm.one_apply, simplePerm_apply]
        rw [simpleReflection_simple, hsym, ho]
        funext i
        grind
      · refine ⟨0, 1, by omega, by omega, ?_⟩
        simp only [hlen, alternatingTail, List.nil_append, List.cons_append,
          wordPerm_cons, wordPerm_nil, Equiv.Perm.mul_apply, Equiv.Perm.one_apply, simplePerm_apply]
        have hroot : simpleReflection A t (simple s) = fun i => simple s i + simple t i := by
          rw [simpleReflection_simple, hsym, ho]
          funext i
          grind
        rw [hroot]
        have hcomb : (fun i => simple s i + simple t i) = fun i => 1 * simple s i + 1 * simple t i := by
          funext i
          simp
        rw [hcomb, rankTwo_reflect_first A hd, ho]
        funext i
        grind
      · have hcancel : wordElement A hd (alternatingTail s t 3) * generator A hd s =
            wordElement A hd [s, t] := by
          simp only [alternatingTail, List.nil_append, List.cons_append,
            wordElement_cons, wordElement_nil, mul_one]
          rw [←mul_assoc (generator A hd t) (generator A hd s) (generator A hd t), ←hbraid]
          simp [mul_assoc]
        rw [hlen, hcancel] at hasctail
        rw [hlen] at hmintail
        have hbound := wordLength_le A hd [s, t]
        simp only [List.length_cons, List.length_nil] at hbound
        omega
    · obtain ⟨a, b, ha, hb, hdom, he⟩ := alternatingTail_nonnegative_large A hA hd s t (by omega) u.length
      exact ⟨a, b, ha, hb, he⟩

theorem group_ascent_nonnegative (A : Matrix 4)
    (hA : ∀ i j, A i j = A j i) (hd : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0)
    (hc : ∀ s t, A s t = 0 → generator A hd s * generator A hd t = generator A hd t * generator A hd s)
    (hb : ∀ s t, A s t = -1 → generator A hd s * generator A hd t * generator A hd s =
      generator A hd t * generator A hd s * generator A hd t)
    (g : ReflectionGroup A hd) (s : Fin 4)
    (hasc : wordLength A hd g ≤ wordLength A hd (g * generator A hd s)) :
    CoordinateNonnegative (g.val (simple s)) := by
  have aux : ∀ n, ∀ g : ReflectionGroup A hd, wordLength A hd g = n →
      ∀ s, wordLength A hd g ≤ wordLength A hd (g * generator A hd s) →
        CoordinateNonnegative (g.val (simple s)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro g hn s hasc
      by_cases hz : wordLength A hd g = 0
      · have he := wordLength_eq_zero A hd g hz
        subst g
        intro i
        change 0 ≤ simple s i
        by_cases hi : i = s <;> simp [simple, hi]
      · obtain ⟨t, ht⟩ := exists_right_descent A hd g (by omega)
        have hst : s ≠ t := by intro he; subst t; omega
        obtain ⟨x, u, he, hl, hu, hxs, hxt⟩ := twoGenerator_decomposition A hd g s t
        have hmin := decomposition_tail_minimal A hd g x u he hl
        have hxsmall : wordLength A hd x < wordLength A hd g := by
          by_contra hsmall
          have hnil : u = [] := List.length_eq_zero_iff.mp (by omega)
          have heg : g = x := by simpa [hnil] using he
          rw [heg] at ht
          omega
        have hxu : wordLength A hd (wordElement A hd u) ≤
            wordLength A hd (wordElement A hd u * generator A hd s) := by
          have hbound := wordLength_mul_le A hd x (wordElement A hd u * generator A hd s)
          have hge : g * generator A hd s = x * (wordElement A hd u * generator A hd s) := by
            rw [he, mul_assoc]
          rw [←hge] at hbound
          omega
        have hxspos := ih _ (by omega) x rfl s hxs
        have hxtpos := ih _ (by omega) x rfl t hxt
        obtain ⟨a, b, ha, hb', hcomb⟩ := rankTwo_ascent_nonnegative A hA hd s t
          (hoff s t hst) (hc s t) (hb s t) u hu hmin hxu
        rw [he]
        change CoordinateNonnegative ((x.val * wordPerm A hd u) (simple s))
        rw [Equiv.Perm.mul_apply, hcomb, group_combination]
        intro i
        change 0 ≤ a * x.val (simple s) i + b * x.val (simple t) i
        have hfirst := Int.mul_nonneg ha (hxspos i)
        have hsecond := Int.mul_nonneg hb' (hxtpos i)
        omega
  exact aux _ g rfl s hasc

theorem group_neg (A : Matrix 4) (hd : ∀ i, A i i = 2)
    (g : ReflectionGroup A hd) (x : Vector4) :
    g.val (fun i => -x i) = fun i => -g.val x i := by
  simpa using group_combination A hd g x x (-1) 0

theorem group_simple_neg (A : Matrix 4) (hd : ∀ i, A i i = 2)
    (g : ReflectionGroup A hd) (s : Fin 4) :
    (g * generator A hd s).val (simple s) = fun i => -g.val (simple s) i := by
  change g.val (simpleReflection A s (simple s)) = _
  rw [simpleReflection_simple_self A hd, group_neg]

theorem group_coordinateDichotomy (A : Matrix 4)
    (hA : ∀ i j, A i j = A j i) (hd : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0)
    (hc : ∀ s t, A s t = 0 → generator A hd s * generator A hd t = generator A hd t * generator A hd s)
    (hb : ∀ s t, A s t = -1 → generator A hd s * generator A hd t * generator A hd s =
      generator A hd t * generator A hd s * generator A hd t)
    (g : ReflectionGroup A hd) (s : Fin 4) : CoordinateDichotomy (g.val (simple s)) := by
  by_cases hasc : wordLength A hd g ≤ wordLength A hd (g * generator A hd s)
  · exact Or.inl (group_ascent_nonnegative A hA hd hoff hc hb g s hasc)
  · have hback : wordLength A hd (g * generator A hd s) ≤
        wordLength A hd ((g * generator A hd s) * generator A hd s) := by
      simp only [mul_assoc, generator_sq, mul_one]
      omega
    have hpos := group_ascent_nonnegative A hA hd hoff hc hb (g * generator A hd s) s hback
    have he := group_simple_neg A hd g s
    refine Or.inr ?_
    intro i
    have hp := hpos i
    rw [he] at hp
    change 0 ≤ -g.val (simple s) i at hp
    omega

theorem generator_commute_of_zero (A : Matrix 4)
    (hA : ∀ i j, A i j = A j i) (hd : ∀ i, A i i = 2)
    (s t : Fin 4) (hentry : A s t = 0) :
    generator A hd s * generator A hd t = generator A hd t * generator A hd s := by
  have hst : s ≠ t := by intro he; subst t; rw [hd] at hentry; omega
  apply Subtype.ext
  apply Equiv.ext
  intro x
  exact MAExistenceRankTwoRelations.simpleReflection_commute_of_zero A hA hd s t hst hentry x

theorem generator_braid_of_neg_one (A : Matrix 4)
    (hA : ∀ i j, A i j = A j i) (hd : ∀ i, A i i = 2)
    (s t : Fin 4) (hentry : A s t = -1) :
    generator A hd s * generator A hd t * generator A hd s =
      generator A hd t * generator A hd s * generator A hd t := by
  have hst : s ≠ t := by intro he; subst t; rw [hd] at hentry; omega
  apply Subtype.ext
  apply Equiv.ext
  intro x
  exact MAExistenceRankTwoRelations.simpleReflection_braid_of_neg_one A hA hd s t hst hentry x

/-- Genuine coordinate dichotomy for every actual real root of any symmetric
integral generalized Cartan matrix of size four. No positivity of the form,
nonsingularity, finite type, or root-base sign field is assumed. -/
theorem realRoot_coordinateDichotomy (A : Matrix 4)
    (hA : ∀ i j, A i j = A j i) (hd : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0)
    {r : Vector4} (hr : RealRoot A r) : CoordinateDichotomy r := by
  obtain ⟨w, s, rfl⟩ := realRoot_word A hd hr
  exact group_coordinateDichotomy A hA hd hoff
    (generator_commute_of_zero A hA hd) (generator_braid_of_neg_one A hA hd)
    (wordElement A hd w) s

/-- The desired root sign theorem for the initial companion of every skew
integer quiver. In particular acyclicity is not required for root signs. -/
theorem initial_realRoot_coordinateDichotomy (B : Matrix 4)
    (hB : SkewSymmetric B) {r : Vector4}
    (hr : RealRoot (initialCompanion B) r) :
    (∀ i, 0 ≤ r i) ∨ (∀ i, r i ≤ 0) := by
  have hA := initialCompanion_quasiCartan B hB
  exact realRoot_coordinateDichotomy _ hA.1 hA.2.1
    (initialCompanion_offDiagonal_nonpos B) hr

/-- Real-root membership alone now supplies strict coefficient sign coherence,
using the independently proved nonzero theorem for the genuine orbit. -/
theorem realRootColumns_signCoherent (B₀ C : Matrix 4)
    (hB₀ : SkewSymmetric B₀)
    (hroots : ∀ j, RealRoot (initialCompanion B₀) (column C j)) :
    SignCoherent C :=
  rootDichotomy_signCoherent B₀ C hB₀
    (fun _ hr => initial_realRoot_coordinateDichotomy B₀ hB₀ hr) hroots

end QuiverProofs.MAExistenceTeamCRootSigns
