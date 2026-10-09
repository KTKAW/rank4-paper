import QuiverProofs.Cosquare

/-! Integral change of basis for ordinary exchange-matrix mutation.
This concerns the skew-symmetric exchange matrix itself, not an ordered
unipotent companion and not proper-mutation transport. -/
namespace QuiverProofs.MutationCongruence

open Cosquare

/-- The elementary integral change of basis: column k changes, all other
columns are standard basis vectors. Its square is the identity. -/
def basisChange (B : Matrix 4) (k : Fin 4) : Matrix 4 := fun i j =>
  if j = k then (if i = k then -1 else max (B i k) 0)
  else if i = j then 1 else 0

private theorem fin4 (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega

theorem basisChange_mul_entry (B A : Matrix 4) (k i j : Fin 4) :
    mul (basisChange B k) A i j =
      if i=k then -A k j else A i j + max (B i k) 0 * A k j := by
  rcases fin4 k with rfl|rfl|rfl|rfl <;>
    rcases fin4 i with rfl|rfl|rfl|rfl <;>
    simp [mul,basisChange] <;> omega

theorem mul_transpose_basisChange_entry (A B : Matrix 4) (k i j : Fin 4) :
    mul A (transpose (basisChange B k)) i j =
      if j=k then -A i k else A i j + A i k * max (B j k) 0 := by
  rcases fin4 k with rfl|rfl|rfl|rfl <;>
    rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [mul,basisChange,transpose] <;> omega

theorem basisChange_involutive (B : Matrix 4) (k : Fin 4) :
    mul (basisChange B k) (basisChange B k) = one := by
  funext i j
  rw [basisChange_mul_entry]
  by_cases hi : i=k <;> by_cases hj : j=k <;> by_cases hij : i=j <;>
    simp_all [basisChange,one,eq_comm]
  all_goals omega

theorem basisChange_determinant (B : Matrix 4) (k : Fin 4) :
    determinant (basisChange B k) = -1 := by
  rcases fin4 k with rfl|rfl|rfl|rfl <;>
    simp [determinant,Algebra.det4,Algebra.det3,basisChange]

theorem correction_linear (x y : Int) :
    correction x y = max x 0 * y + x * max (-y) 0 := by
  unfold correction
  grind

/-- Ordinary mutation is integral congruence via an explicitly unimodular
matrix. Both singular and nonsingular exchange matrices are covered. -/
theorem mutation_congruence (B : Matrix 4) (k : Fin 4) (hB : SkewSymmetric B) :
    mutate B k = mul (mul (basisChange B k) B) (transpose (basisChange B k)) := by
  have hkk : B k k = 0 := by have := hB k k; omega
  funext i j
  rw [mul_transpose_basisChange_entry]
  simp only [basisChange_mul_entry]
  by_cases hi : i=k
  · subst i
    by_cases hj : j=k <;> simp [mutate,hj,hkk]
  · by_cases hj : j=k
    · subst j
      simp [mutate,hi,hkk]
    · rw [hB j k]
      simp only [mutate,hi,hj,or_self,↓reduceIte,hkk,Int.mul_zero,Int.add_zero]
      rw [correction_linear]
      grind

/-- Integral congruence with a supplied two-sided inverse. -/
def IntegralCongruence (A B : Matrix 4) : Prop :=
  ∃ P Pinv : Matrix 4, mul P Pinv = one ∧ mul Pinv P = one ∧
    B = mul (mul P A) (transpose P)

theorem integralCongruence_mutate (B : Matrix 4) (k : Fin 4)
    (hB : SkewSymmetric B) : IntegralCongruence B (mutate B k) :=
  ⟨basisChange B k,basisChange B k,basisChange_involutive B k,
    basisChange_involutive B k,mutation_congruence B k hB⟩

theorem transpose_mul (A B : Matrix 4) :
    transpose (mul A B) = mul (transpose B) (transpose A) := by
  funext i j
  simp only [transpose,mul]
  grind

theorem integralCongruence_refl (A : Matrix 4) : IntegralCongruence A A := by
  refine ⟨one,one,one_mul one,one_mul one,?_⟩
  have ht : transpose one = one := by
    funext i j
    simp [transpose,one,eq_comm]
  rw [one_mul,ht,mul_one]

theorem integralCongruence_trans (A B C : Matrix 4)
    (hAB : IntegralCongruence A B) (hBC : IntegralCongruence B C) :
    IntegralCongruence A C := by
  obtain ⟨P,Pi,hp,hpi,hB⟩ := hAB
  obtain ⟨Q,Qi,hq,hqi,hC⟩ := hBC
  refine ⟨mul Q P,mul Pi Qi,?_,?_,?_⟩
  · rw [mul_assoc,←mul_assoc P Pi,hp,one_mul,hq]
  · rw [mul_assoc,←mul_assoc Qi Q,hqi,one_mul,hpi]
  · rw [hC,hB,transpose_mul]
    simp only [mul_assoc]

/-- Every finite mutation word preserves the exchange matrix's integral
congruence class. No bound on word length or matrix entries occurs. -/
theorem applyWord_integralCongruence (B : Matrix 4) (hB : SkewSymmetric B)
    (word : List (Fin 4)) : IntegralCongruence B (applyWord B word) := by
  induction word generalizing B with
  | nil => exact integralCongruence_refl B
  | cons k ks ih =>
    exact integralCongruence_trans B (mutate B k) (applyWord (mutate B k) ks)
      (integralCongruence_mutate B k hB)
      (ih _ (mutation_preserves_skew B k hB))

/-- Common entry divisors in any rank, before choosing a normalization for gcd. -/
def EntryDivisor {n : Nat} (d : Int) (B : Matrix n) : Prop := ∀ i j, d ∣ B i j

theorem dvd_max_zero (d x : Int) (h : d ∣ x) : d ∣ max x 0 := by
  by_cases hx : x ≤ 0
  · have he : max x 0 = 0 := by omega
    simp [he]
  · have he : max x 0 = x := by omega
    simpa [he] using h

theorem entryDivisor_mutate {n : Nat} (d : Int) (B : Matrix n) (k : Fin n)
    (h : EntryDivisor d B) : EntryDivisor d (mutate B k) := by
  intro i j
  by_cases hk : i=k ∨ j=k
  · simp only [mutate,hk,↓reduceIte]
    exact Int.dvd_neg.mpr (h i j)
  · simp only [mutate,hk,↓reduceIte,correction]
    apply Int.dvd_add (h i j)
    apply Int.dvd_sub
    · obtain ⟨a, ha⟩ := dvd_max_zero d (B i k) (h i k)
      exact ⟨a * max (B k j) 0, by rw [ha]; grind⟩
    · obtain ⟨a, ha⟩ := dvd_max_zero d (-B i k) (Int.dvd_neg.mpr (h i k))
      exact ⟨a * max (-B k j) 0, by rw [ha]; grind⟩

theorem entryDivisor_mutate_iff {n : Nat} (d : Int) (B : Matrix n) (k : Fin n) :
    EntryDivisor d (mutate B k) ↔ EntryDivisor d B := by
  constructor
  · intro h
    simpa only [mutation_involutive] using entryDivisor_mutate d (mutate B k) k h
  · exact entryDivisor_mutate d B k

/-- All common divisors, including zero and negative divisors, are unchanged
by any finite mutation word. This does not require skew symmetry. -/
theorem entryDivisor_applyWord_iff {n : Nat} (d : Int) (B : Matrix n)
    (word : List (Fin n)) : EntryDivisor d (applyWord B word) ↔ EntryDivisor d B := by
  induction word generalizing B with
  | nil => rfl
  | cons k ks ih =>
    exact (ih (mutate B k)).trans (entryDivisor_mutate_iff d B k)

/-- Nonnegative gcd of the six independent exchange entries; it is zero
exactly for the zero skew-symmetric exchange matrix. -/
def entryGcd (B : Matrix 4) : Nat :=
  Nat.gcd (B 0 1).natAbs (Nat.gcd (B 0 2).natAbs (Nat.gcd (B 0 3).natAbs
    (Nat.gcd (B 1 2).natAbs (Nat.gcd (B 1 3).natAbs (B 2 3).natAbs))))

theorem entryDivisor_ofSix_iff (a b c d e f r : Int) :
    EntryDivisor r (ofSix a b c d e f) ↔
      r ∣ a ∧ r ∣ b ∧ r ∣ c ∧ r ∣ d ∧ r ∣ e ∧ r ∣ f := by
  constructor
  · intro h
    exact ⟨h 0 1,h 0 2,h 0 3,h 1 2,h 1 3,h 2 3⟩
  · rintro ⟨ha,hb,hc,hd,he,hf⟩ i j
    rcases fin4 i with rfl|rfl|rfl|rfl <;>
      rcases fin4 j with rfl|rfl|rfl|rfl <;> simp [ofSix,ha,hb,hc,hd,he,hf]

theorem entryGcd_dvd_iff (B : Matrix 4) (hB : SkewSymmetric B) (d : Nat) :
    d ∣ entryGcd B ↔ EntryDivisor (d : Int) B := by
  rw [←ofSix_reconstruct B hB,entryDivisor_ofSix_iff]
  simp only [entryGcd,ofSix,Nat.dvd_gcd_iff,←Int.ofNat_dvd_left]

theorem entryGcd_mutate (B : Matrix 4) (hB : SkewSymmetric B) (k : Fin 4) :
    entryGcd (mutate B k) = entryGcd B := by
  apply Nat.dvd_antisymm
  · apply (entryGcd_dvd_iff B hB _).mpr
    apply (entryDivisor_mutate_iff _ B k).mp
    exact (entryGcd_dvd_iff _ (mutation_preserves_skew B k hB) _).mp (Nat.dvd_refl _)
  · apply (entryGcd_dvd_iff _ (mutation_preserves_skew B k hB) _).mpr
    apply (entryDivisor_mutate_iff _ B k).mpr
    exact (entryGcd_dvd_iff B hB _).mp (Nat.dvd_refl _)

/-- The exact integer gcd invariant for every rank-four mutation word. -/
theorem entryGcd_applyWord (B : Matrix 4) (hB : SkewSymmetric B)
    (word : List (Fin 4)) : entryGcd (applyWord B word) = entryGcd B := by
  induction word generalizing B with
  | nil => rfl
  | cons k ks ih =>
    exact (ih _ (mutation_preserves_skew B k hB)).trans (entryGcd_mutate B hB k)

end QuiverProofs.MutationCongruence
