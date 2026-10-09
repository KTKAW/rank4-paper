import QuiverProofs.MAExistenceTeamBAdjacentHurwitz
import QuiverProofs.MAExistenceTeamDJointSeed
import Mathlib.Tactic.FinCases
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Fin

/-! Full finite-sweep chronology bridge. The primitive at positions
0,1 belongs to B. This file extends the actual ordered update to all ten
rightward and all ten leftward pivot intervals at rank four. No color-order
or no-Euler-cycle preservation conclusion is asserted. -/
namespace QuiverProofs.MAExistenceSupportChronology
open QuiverProofs MAExistenceLiterature MAExistenceCoefficients
open MAExistenceCompanions MAExistenceTeamBRootPositivity
open MAExistenceTeamBAdjacentHurwitz MAExistenceTeamDJointSeed
open MAExistenceTeamCCertificateTransport Cosquare
set_option maxHeartbeats 0
set_option maxRecDepth 10000

def rightMove (U D : Matrix 4) (t : Fin 4) : Matrix 4 := fun a j =>
  if j = t then D a (t+1) - pairing U (column D t) (column D (t+1)) * D a t
  else if j = t+1 then D a t else D a j

def leftMove (U D : Matrix 4) (t : Fin 4) : Matrix 4 := fun a j =>
  if j = t then D a (t+1)
  else if j = t+1 then D a t - pairing U (column D t) (column D (t+1)) * D a (t+1)
  else D a j

@[simp] theorem rightMove_pivot_column (U D : Matrix 4) (t : Fin 4) :
    column (rightMove U D t) t = fun a => column D (t+1) a -
      pairing U (column D t) (column D (t+1)) * column D t a := by
  funext a; simp [column, rightMove]

@[simp] theorem rightMove_next_column (U D : Matrix 4) (t : Fin 4) :
    column (rightMove U D t) (t+1) = column D t := by
  fin_cases t <;> funext a <;> simp [column, rightMove]

@[simp] theorem rightMove_other_column (U D : Matrix 4) (t j : Fin 4)
    (hjt : j ≠ t) (hjn : j ≠ t+1) :
    column (rightMove U D t) j = column D j := by
  funext a; simp [column, rightMove, hjt, hjn]

@[simp] theorem leftMove_pivot_column (U D : Matrix 4) (t : Fin 4) :
    column (leftMove U D t) t = column D (t+1) := by
  funext a; simp [column, leftMove]

@[simp] theorem leftMove_next_column (U D : Matrix 4) (t : Fin 4) :
    column (leftMove U D t) (t+1) = fun a => column D t a -
      pairing U (column D t) (column D (t+1)) * column D (t+1) a := by
  fin_cases t <;> funext a <;> simp [column, leftMove]

@[simp] theorem leftMove_other_column (U D : Matrix 4) (t j : Fin 4)
    (hjt : j ≠ t) (hjn : j ≠ t+1) :
    column (leftMove U D t) j = column D j := by
  funext a; simp [column, leftMove, hjt, hjn]

@[simp] theorem rightMove_0_next (U D : Matrix 4) :
    column (rightMove U D 0) 1 = column D 0 := by
  simpa using rightMove_next_column U D 0

@[simp] theorem rightMove_1_next (U D : Matrix 4) :
    column (rightMove U D 1) 2 = column D 1 := by
  simpa using rightMove_next_column U D 1

@[simp] theorem rightMove_2_next (U D : Matrix 4) :
    column (rightMove U D 2) 3 = column D 2 := by
  simpa using rightMove_next_column U D 2

@[simp] theorem leftMove_0_next (U D : Matrix 4) :
    column (leftMove U D 0) 1 = fun a => column D 0 a -
      pairing U (column D 0) (column D 1) * column D 1 a := by
  simpa using leftMove_next_column U D 0

@[simp] theorem leftMove_1_next (U D : Matrix 4) :
    column (leftMove U D 1) 2 = fun a => column D 1 a -
      pairing U (column D 1) (column D 2) * column D 2 a := by
  simpa using leftMove_next_column U D 1

@[simp] theorem leftMove_2_next (U D : Matrix 4) :
    column (leftMove U D 2) 3 = fun a => column D 2 a -
      pairing U (column D 2) (column D 3) * column D 3 a := by
  simpa using leftMove_next_column U D 2

theorem rightMove_zero_eq_B_primitive (U D : Matrix 4) :
    rightMove U D 0 = frame U D := by
  funext a j
  fin_cases j <;> simp [rightMove, frame, change, weight, mul, mat4] <;> ring

def rightSweep (U D : Matrix 4) (t s : Fin 4) : Matrix 4 :=
  if t=0 then
    if s=0 then D else if s=1 then rightMove U D 0
    else if s=2 then rightMove U (rightMove U D 0) 1
    else rightMove U (rightMove U (rightMove U D 0) 1) 2
  else if t=1 then
    if s=1 then D else if s=2 then rightMove U D 1
    else rightMove U (rightMove U D 1) 2
  else if t=2 then if s=2 then D else rightMove U D 2
  else D

def leftSweep (U D : Matrix 4) (t s : Fin 4) : Matrix 4 :=
  if t=3 then
    if s=3 then D else if s=2 then leftMove U D 2
    else if s=1 then leftMove U (leftMove U D 2) 1
    else leftMove U (leftMove U (leftMove U D 2) 1) 0
  else if t=2 then
    if s=2 then D else if s=1 then leftMove U D 1
    else leftMove U (leftMove U D 1) 0
  else if t=1 then if s=1 then D else leftMove U D 0
  else D

def rightIndex (t s j : Fin 4) : Fin 4 :=
  if j=s then t else if t ≤ j ∧ j < s then j+1 else j

def leftIndex (t s j : Fin 4) : Fin 4 :=
  if j=s then t else if s < j ∧ j ≤ t then j-1 else j

def negateColumn (D : Matrix 4) (s : Fin 4) : Matrix 4 := fun a j =>
  if j=s then -D a j else D a j

def columnRelabel (D : Matrix 4) (p : Relabeling 4) : Matrix 4 :=
  fun a j => D a (p.toFun j)

theorem rightSweep_entries (U D : Matrix 4) (t s : Fin 4) (hts : t ≤ s)
    (a j : Fin 4) :
    rightSweep U D t s a j =
      if j=s then D a t else if t ≤ j ∧ j < s then
        D a (j+1) - pairing U (column D t) (column D (j+1)) * D a t
      else D a j := by
  fin_cases t <;> fin_cases s <;> fin_cases j <;>
    simp_all [rightSweep, rightMove]

theorem leftSweep_entries (U D : Matrix 4) (t s : Fin 4) (hst : s ≤ t)
    (a j : Fin 4) :
    leftSweep U D t s a j =
      if j=s then D a t else if s < j ∧ j ≤ t then
        D a (j-1) - pairing U (column D (j-1)) (column D t) * D a t
      else D a j := by
  fin_cases t <;> fin_cases s <;> fin_cases j <;>
    simp_all [leftSweep, leftMove]

theorem rightIndex_inverse (t s : Fin 4) (hts : t ≤ s) (j : Fin 4) :
    leftIndex s t (rightIndex t s j) = j ∧
      rightIndex t s (leftIndex s t j) = j := by
  fin_cases t <;> fin_cases s <;> fin_cases j <;>
    simp_all [rightIndex, leftIndex]

def rightPermutation (t s : Fin 4) (hts : t ≤ s) : Relabeling 4 :=
  ⟨rightIndex t s, leftIndex s t,
    fun j => (rightIndex_inverse t s hts j).1,
    fun j => (rightIndex_inverse t s hts j).2⟩

def leftPermutation (t s : Fin 4) (hst : s ≤ t) : Relabeling 4 :=
  (rightPermutation s t hst).symm

/-- All ten green rightward intervals, with zero-weight crossings allowed.
The hypotheses say precisely that the interval contains every positive pivot
entry and contains no negative entry. -/
theorem green_rightSweep_coefficients (U B D : Matrix 4)
    (t s : Fin 4) (hts : t ≤ s)
    (hg : ∀ a, 0 ≤ D a t)
    (he : ∀ j, t < j → pairing U (column D t) (column D j) = -B t j)
    (hin : ∀ j, t < j → j ≤ s → 0 ≤ B t j)
    (hout : ∀ j, j ≠ t → ¬ (t < j ∧ j ≤ s) → B t j ≤ 0) :
    negateColumn (rightSweep U D t s) s =
      columnRelabel (mutateCoefficients B D t) (rightPermutation t s hts) := by
  have hmax : ∀ j, j ≠ t → max (B t j) 0 =
      if t < j ∧ j ≤ s then B t j else 0 := by
    intro j hj
    by_cases h : t < j ∧ j ≤ s
    · rw [if_pos h]
      exact max_eq_left (hin j h.1 h.2)
    · rw [if_neg h]
      exact max_eq_right (hout j hj h)
  funext a j
  rw [show columnRelabel (mutateCoefficients B D t) (rightPermutation t s hts) a j =
    mutateCoefficients B D t a (rightIndex t s j) from rfl]
  rw [mutateCoefficients_green B D t hg]
  simp only [negateColumn]
  rw [rightSweep_entries U D t s hts]
  fin_cases t <;> fin_cases s <;> fin_cases j <;>
    simp_all [rightIndex, hmax] <;> ring

/-- All ten red leftward intervals, with zero-weight crossings allowed. -/
theorem red_leftSweep_coefficients (U B D : Matrix 4)
    (hB : SkewSymmetric B) (t s : Fin 4) (hst : s ≤ t)
    (hr : ∀ a, D a t ≤ 0)
    (he : ∀ j, j < t → pairing U (column D j) (column D t) = -B j t)
    (hin : ∀ j, s ≤ j → j < t → B t j ≤ 0)
    (hout : ∀ j, j ≠ t → ¬ (s ≤ j ∧ j < t) → 0 ≤ B t j) :
    negateColumn (leftSweep U D t s) s =
      columnRelabel (mutateCoefficients B D t) (leftPermutation t s hst) := by
  have hmax : ∀ j, j ≠ t → max (-B t j) 0 =
      if s ≤ j ∧ j < t then -B t j else 0 := by
    intro j hj
    by_cases h : s ≤ j ∧ j < t
    · rw [if_pos h]
      exact max_eq_left (by have := hin j h.1 h.2; omega)
    · rw [if_neg h]
      exact max_eq_right (by have := hout j hj h; omega)
  have he' : ∀ j, j < t → pairing U (column D j) (column D t) = B t j := by
    intro j hj
    rw [he j hj, hB j t]
    omega
  funext a j
  rw [show columnRelabel (mutateCoefficients B D t) (leftPermutation t s hst) a j =
    mutateCoefficients B D t a (leftIndex t s j) from rfl]
  rw [mutateCoefficients_red B D t hr]
  simp only [negateColumn]
  rw [leftSweep_entries U D t s hst]
  fin_cases t <;> fin_cases s <;> fin_cases j <;>
    simp_all [leftIndex, hmax] <;> ring



/-- Lift B's Euler-preserving primitive to every adjacent position. -/
theorem rightMove_euler_unit_upper (U D : Matrix 4) (t : Fin 4)
    (ht : t < 3) (hD : EulerUnitUpper U D) :
    EulerUnitUpper U (rightMove U D t) := by
  have h00 := hD.1 0; have h11 := hD.1 1
  have h22 := hD.1 2; have h33 := hD.1 3
  have h10 := hD.2 1 0 (by decide)
  have h20 := hD.2 2 0 (by decide)
  have h21 := hD.2 2 1 (by decide)
  have h30 := hD.2 3 0 (by decide)
  have h31 := hD.2 3 1 (by decide)
  have h32 := hD.2 3 2 (by decide)
  fin_cases t <;> try omega
  all_goals
    constructor
    · intro i
      fin_cases i <;>
        simp only [rightMove_pivot_column, rightMove_0_next, rightMove_1_next,
          rightMove_2_next, rightMove_other_column, pairing_sub_smul_left,
          pairing_sub_smul_right] <;>
        simp_all [column] <;> ring
    · intro i j hij
      fin_cases i <;> fin_cases j <;> try omega
      all_goals
        simp only [rightMove_pivot_column, rightMove_0_next, rightMove_1_next,
          rightMove_2_next, rightMove_other_column, pairing_sub_smul_left,
          pairing_sub_smul_right] <;>
        simp_all [column] <;> ring

private theorem pairing_coordinate_sub_left (U D : Matrix 4) (i j : Fin 4)
    (z : Vector4) (a : Int) :
    pairing U (fun r => D r i - a * D r j) z =
      pairing U (column D i) z - a * pairing U (column D j) z :=
  pairing_sub_smul_left U (column D i) (column D j) z a

private theorem pairing_coordinate_sub_right (U D : Matrix 4) (j k : Fin 4)
    (x : Vector4) (a : Int) :
    pairing U x (fun r => D r j - a * D r k) =
      pairing U x (column D j) - a * pairing U x (column D k) :=
  pairing_sub_smul_right U x (column D j) (column D k) a

private theorem pairing_coordinate_sub_both (U D : Matrix 4)
    (i j k l : Fin 4) (a b : Int) :
    pairing U (fun r => D r i - a * D r j) (fun r => D r k - b * D r l) =
      pairing U (column D i) (column D k) - b * pairing U (column D i) (column D l) -
        a * pairing U (column D j) (column D k) +
        a * b * pairing U (column D j) (column D l) := by
  simp only [pairing, column]
  ring

/-- The inverse adjacent move has the same unrestricted Euler-order law. -/
theorem leftMove_euler_unit_upper (U D : Matrix 4) (t : Fin 4)
    (ht : t < 3) (hD : EulerUnitUpper U D) :
    EulerUnitUpper U (leftMove U D t) := by
  have h00 := hD.1 0; have h11 := hD.1 1
  have h22 := hD.1 2; have h33 := hD.1 3
  have h10 := hD.2 1 0 (by decide)
  have h20 := hD.2 2 0 (by decide)
  have h21 := hD.2 2 1 (by decide)
  have h30 := hD.2 3 0 (by decide)
  have h31 := hD.2 3 1 (by decide)
  have h32 := hD.2 3 2 (by decide)
  fin_cases t <;> try omega
  all_goals
    constructor
    · intro i
      fin_cases i <;>
        simp only [leftMove_pivot_column, leftMove_0_next, leftMove_1_next,
          leftMove_2_next, leftMove_other_column] <;>
        simp_all [column, pairing_coordinate_sub_both, pairing_coordinate_sub_left,
          pairing_coordinate_sub_right] <;> ring
    · intro i j hij
      fin_cases i <;> fin_cases j <;> try omega
      all_goals
        simp only [leftMove_pivot_column, leftMove_0_next, leftMove_1_next,
          leftMove_2_next, leftMove_other_column] <;>
        simp_all [column, pairing_coordinate_sub_both, pairing_coordinate_sub_left,
          pairing_coordinate_sub_right] <;> ring


def changeAt (t : Fin 4) (a : Int) : Matrix 4 := fun i j =>
  if j=t then if i=t then -a else if i=t+1 then 1 else 0
  else if j=t+1 then if i=t then 1 else 0
  else if i=j then 1 else 0

def inverseChangeAt (t : Fin 4) (a : Int) : Matrix 4 := fun i j =>
  if j=t then if i=t+1 then 1 else 0
  else if j=t+1 then if i=t then 1 else if i=t+1 then a else 0
  else if i=j then 1 else 0

theorem changeAt_inverse (t : Fin 4) (ht : t < 3) (a : Int) :
    mul (inverseChangeAt t a) (changeAt t a) = one ∧
      mul (changeAt t a) (inverseChangeAt t a) = one := by
  fin_cases t <;> try omega
  all_goals
    constructor <;> funext i j <;> fin_cases i <;> fin_cases j <;>
      simp [inverseChangeAt, changeAt, mul, one]

theorem rightMove_matrix (U D : Matrix 4) (t : Fin 4) (ht : t < 3) :
    rightMove U D t = mul D (changeAt t (pairing U (column D t) (column D (t+1)))) := by
  fin_cases t <;> try omega
  all_goals
    funext a j
    fin_cases j <;> simp [rightMove, changeAt, mul] <;> ring

theorem leftMove_matrix (U D : Matrix 4) (t : Fin 4) (ht : t < 3) :
    leftMove U D t = mul D (inverseChangeAt t (-pairing U (column D t) (column D (t+1)))) := by
  fin_cases t <;> try omega
  all_goals
    funext a j
    fin_cases j <;> simp [leftMove, inverseChangeAt, mul] <;> ring

theorem rightMove_integralBasis (U D : Matrix 4) (t : Fin 4) (ht : t < 3)
    (hD : IntegralBasis D) : IntegralBasis (rightMove U D t) := by
  obtain ⟨Di, hl, hr⟩ := hD
  let a := pairing U (column D t) (column D (t+1))
  have hi := changeAt_inverse t ht a
  rw [rightMove_matrix U D t ht]
  refine ⟨mul (inverseChangeAt t a) Di, ?_, ?_⟩
  · rw [Cosquare.mul_assoc, ← Cosquare.mul_assoc Di, hl, Cosquare.one_mul, hi.1]
  · rw [Cosquare.mul_assoc, ← Cosquare.mul_assoc (changeAt t a), hi.2,
      Cosquare.one_mul, hr]

theorem leftMove_integralBasis (U D : Matrix 4) (t : Fin 4) (ht : t < 3)
    (hD : IntegralBasis D) : IntegralBasis (leftMove U D t) := by
  obtain ⟨Di, hl, hr⟩ := hD
  let a := -pairing U (column D t) (column D (t+1))
  have hi := changeAt_inverse t ht a
  rw [leftMove_matrix U D t ht]
  refine ⟨mul (changeAt t a) Di, ?_, ?_⟩
  · rw [Cosquare.mul_assoc, ← Cosquare.mul_assoc Di, hl, Cosquare.one_mul, hi.2]
  · rw [Cosquare.mul_assoc, ← Cosquare.mul_assoc (inverseChangeAt t a), hi.1,
      Cosquare.one_mul, hr]


theorem rightMove_realRoot_columns (B U D : Matrix 4) (hB : SkewSymmetric B)
    (hU : ∀ i j, U i j + U j i = initialCompanion B i j)
    (t : Fin 4) (ht : t < 3)
    (hroots : ∀ j, RealRoot (initialCompanion B) (column D j))
    (hupper : ∀ i j, j < i → pairing U (column D i) (column D j) = 0) :
    ∀ j, RealRoot (initialCompanion B) (column (rightMove U D t) j) := by
  have htn : t < t+1 := by fin_cases t <;> simp_all
  have hz := hupper (t+1) t htn
  have hp := pairing_symmetric_part (initialCompanion B) U hU
    (column D t) (column D (t+1))
  rw [hz, add_zero] at hp
  intro j
  by_cases hjt : j=t
  · subst j
    have he : column (rightMove U D t) t =
        reflection (initialCompanion B) (column D t) (column D (t+1)) := by
      rw [rightMove_pivot_column]
      funext a
      simp only [reflection, hp]
    rw [he]
    exact realRoot_reflection _ (initialCompanion_quasiCartan B hB).1
      (initialCompanion_quasiCartan B hB).2.1 (hroots t) (hroots (t+1))
  · by_cases hjn : j=t+1
    · subst j
      rw [rightMove_next_column]
      exact hroots t
    · rw [rightMove_other_column U D t j hjt hjn]
      exact hroots j

theorem leftMove_realRoot_columns (B U D : Matrix 4) (hB : SkewSymmetric B)
    (hU : ∀ i j, U i j + U j i = initialCompanion B i j)
    (t : Fin 4) (ht : t < 3)
    (hroots : ∀ j, RealRoot (initialCompanion B) (column D j))
    (hupper : ∀ i j, j < i → pairing U (column D i) (column D j) = 0) :
    ∀ j, RealRoot (initialCompanion B) (column (leftMove U D t) j) := by
  have htn : t < t+1 := by fin_cases t <;> simp_all
  have hz := hupper (t+1) t htn
  have hp := pairing_symmetric_part (initialCompanion B) U hU
    (column D (t+1)) (column D t)
  rw [hz, zero_add] at hp
  intro j
  by_cases hjt : j=t
  · subst j
    rw [leftMove_pivot_column]
    exact hroots (t+1)
  · by_cases hjn : j=t+1
    · subst j
      have he : column (leftMove U D t) (t+1) =
          reflection (initialCompanion B) (column D (t+1)) (column D t) := by
        rw [leftMove_next_column]
        funext a
        simp only [reflection, hp]
      rw [he]
      exact realRoot_reflection _ (initialCompanion_quasiCartan B hB).1
        (initialCompanion_quasiCartan B hB).2.1 (hroots (t+1)) (hroots t)
    · rw [leftMove_other_column U D t j hjt hjn]
      exact hroots j

/-- Properness and the green pivot side select a full rightward interval. -/
theorem proper_green_has_rightInterval (B : Matrix 4) (hB : SkewSymmetric B)
    (t : Fin 4) (hp : ProperOrder.ProperVertex B (.identity 4) t)
    (hside : ∀ j, 0 < B t j → t < j) :
    ∃ s : Fin 4, t ≤ s ∧
      (∀ j, t < j → j ≤ s → 0 ≤ B t j) ∧
      (∀ j, j ≠ t → ¬ (t < j ∧ j ≤ s) → B t j ≤ 0) := by
  classical
  let S := Finset.univ.filter (fun j => j=t ∨ 0 < B t j)
  have ht : t ∈ S := by simp [S]
  obtain ⟨s, hs, hmax⟩ := Finset.exists_max_image S id ⟨t, ht⟩
  have hs' : s=t ∨ 0 < B t s := by simpa [S] using hs
  refine ⟨s, hmax t ht, ?_, ?_⟩
  · intro j htj hjs
    by_contra hn
    have hn' : 0 < B j t := by have := hB j t; omega
    rcases hs' with rfl | hspos
    · omega
    · have hcyc := hp j s hn' hspos
      simp only [ProperOrder.Between, ProperOrder.Clockwise, Relabeling.identity,
        id_eq] at hcyc
      omega
  · intro j hjt hnot
    by_contra hn
    have hpj : 0 < B t j := by omega
    have hmem : j ∈ S := by simp [S, hpj]
    exact hnot ⟨hside j hpj, hmax j hmem⟩

/-- Properness and the red pivot side select the inverse leftward interval. -/
theorem proper_red_has_leftInterval (B : Matrix 4) (hB : SkewSymmetric B)
    (t : Fin 4) (hp : ProperOrder.ProperVertex B (.identity 4) t)
    (hside : ∀ j, 0 < B j t → j < t) :
    ∃ s : Fin 4, s ≤ t ∧
      (∀ j, s ≤ j → j < t → B t j ≤ 0) ∧
      (∀ j, j ≠ t → ¬ (s ≤ j ∧ j < t) → 0 ≤ B t j) := by
  classical
  let S := Finset.univ.filter (fun j => j=t ∨ 0 < B j t)
  have ht : t ∈ S := by simp [S]
  obtain ⟨s, hs, hmin⟩ := Finset.exists_min_image S id ⟨t, ht⟩
  have hs' : s=t ∨ 0 < B s t := by simpa [S] using hs
  refine ⟨s, hmin t ht, ?_, ?_⟩
  · intro j hsj hjt
    by_contra hn
    have hn' : 0 < B t j := by omega
    rcases hs' with rfl | hspos
    · omega
    · have hcyc := hp s j hspos hn'
      simp only [ProperOrder.Between, ProperOrder.Clockwise, Relabeling.identity,
        id_eq] at hcyc
      omega
  · intro j hjt hnot
    by_contra hn
    have hpj : 0 < B j t := by have := hB j t; omega
    have hmem : j ∈ S := by simp [S, hpj]
    exact hnot ⟨hmin j hmem, hside j hpj⟩

theorem columnRelabel_mutateCoefficients (B C : Matrix 4)
    (p : Relabeling 4) (t : Fin 4) :
    columnRelabel (mutateCoefficients B C (p.toFun t)) p =
      mutateCoefficients (relabel B p) (columnRelabel C p) t := by
  funext a j
  have h : p.toFun j = p.toFun t ↔ j=t := ⟨p.injective, congrArg p.toFun⟩
  simp [columnRelabel, mutateCoefficients, relabel, h]

theorem columnRelabel_trans (C : Matrix 4) (p q : Relabeling 4) :
    columnRelabel (columnRelabel C p) q = columnRelabel C (p.trans q) := rfl

private theorem proper_ordered (B : Matrix 4) (p : ProperOrder.CyclicOrder)
    (k : Fin 4) (hp : ProperOrder.ProperVertex B p k) :
    ProperOrder.ProperVertex (relabel B p) (.identity 4) (p.invFun k) := by
  intro u v hut htv
  have hu : 0 < B (p.toFun u) k := by simpa [relabel, p.right_inv] using hut
  have hv : 0 < B k (p.toFun v) := by simpa [relabel, p.right_inv] using htv
  have hcyc := hp (p.toFun u) (p.toFun v) hu hv
  simpa only [ProperOrder.Between, p.left_inv, Relabeling.identity, id_eq] using hcyc

private theorem pairing_columnRelabel (U C : Matrix 4) (p : Relabeling 4)
    (i j : Fin 4) :
    pairing U (column (columnRelabel C p) i) (column (columnRelabel C p) j) =
      coefficientBilinear U C (p.toFun i) (p.toFun j) := by
  simp only [pairing, column, columnRelabel, coefficientBilinear, mul, transpose]
  ring

private theorem ordered_Euler_forward (B U C : Matrix 4) (p : Relabeling 4)
    (he : coefficientBilinear U C = MAExistenceTeamBOrderMutation.labeledUnipotent B p)
    (i j : Fin 4) (hij : i < j) :
    pairing U (column (columnRelabel C p) i) (column (columnRelabel C p) j) =
      -(relabel B p) i j := by
  have hne : p.toFun i ≠ p.toFun j := fun h => by have := p.injective h; omega
  rw [pairing_columnRelabel, he]
  simp [MAExistenceTeamBOrderMutation.labeledUnipotent, p.left_inv, hij, hne, relabel]


/-- Exact full chronological green mutation: all selected neighbors are crossed
rightward, zero edges may be crossed, and the terminal pivot is negated. The
interval is constructed from the current compatible color-block proper order;
no interval-selection, next ArrowSigns, or next admissibility is supplied. -/
theorem principalSeed_green_rightSweep (B₀ U₀ : Matrix 4)
    (hB₀ : SkewSymmetric B₀)
    (hs₀ : add U₀ (transpose U₀) = initialCompanion B₀)
    (ha₀ : add U₀ (scale (-1) (transpose U₀)) = reverse B₀)
    (w : List (Fin 4)) (h : SeedInv B₀ w) (k : Fin 4)
    (hk : columnColor (principalSeed B₀ w).2 k = true) :
    ∃ (p : ProperOrder.CyclicOrder) (s : Fin 4) (hts : p.invFun k ≤ s),
      Compatible (principalSeed B₀ w).1 (columnColor (principalSeed B₀ w).2) k p ∧
      GreenBeforeRed (columnColor (principalSeed B₀ w).2) p ∧
      negateColumn (rightSweep U₀ (columnRelabel (principalSeed B₀ w).2 p)
        (p.invFun k) s) s =
        columnRelabel (principalSeed B₀ (w ++ [k])).2
          (p.trans (rightPermutation (p.invFun k) s hts)) := by
  let B := (principalSeed B₀ w).1
  let C := (principalSeed B₀ w).2
  have hB := principalSeed_skew B₀ hB₀ w
  have hc := seedInv_signCoherent B₀ hB₀ w h
  have hcol := MAExistenceAuxiliaryOrders.companion_colorAdmissible B _ hB
    h.companion.1 (columnColor C) h.arrowSigns h.admissible
  obtain ⟨p, hp, hcolors⟩ := MAExistenceAuxiliaryOrders.colorAdmissible_has_extensions
    B hB (columnColor C) hcol k
  have hproper := compatible_colorBlock_proper B (columnColor C) k p hp hcolors
  have hside : ∀ j, 0 < (relabel B p) (p.invFun k) j → p.invFun k < j := by
    intro j hj
    have hb : 0 < B k (p.toFun j) := by simpa [relabel, p.right_inv] using hj
    have hh : p.invFun k < p.invFun (p.toFun j) := by
      cases hcolor : columnColor C (p.toFun j)
      · exact hcolors k (p.toFun j) hk hcolor
      · exact hp k (p.toFun j) (Or.inl ⟨hb, by change columnColor C k = _ at hk; simp [hk, hcolor]⟩)
    simpa only [p.left_inv] using hh
  obtain ⟨s, hts, hin, hout⟩ := proper_green_has_rightInterval (relabel B p)
    (relabel_skew B p hB) (p.invFun k) (proper_ordered B p k hproper) hside
  have heuler := coefficientBilinear_eq_compatible B₀ U₀ B C hB hs₀ ha₀
    h.exchangeOrigin h.companion (columnColor C) h.arrowSigns k p hp
  have hg : ∀ a, 0 ≤ columnRelabel C p a (p.invFun k) := by
    simpa [columnRelabel, p.right_inv, C] using ((color_iff_green hc k).mp hk).1
  have he := green_rightSweep_coefficients U₀ (relabel B p) (columnRelabel C p)
    (p.invFun k) s hts hg (fun j hj => ordered_Euler_forward B U₀ C p heuler _ _ hj)
    hin hout
  have hn : (principalSeed B₀ (w ++ [k])).2 = mutateCoefficients B C k := by
    rw [principalSeed, evolve_append_singleton]
    rfl
  refine ⟨p, s, hts, hp, hcolors, ?_⟩
  rw [hn]
  rw [← columnRelabel_trans]
  have hrel := columnRelabel_mutateCoefficients B C p (p.invFun k)
  simp only [p.right_inv] at hrel
  rw [hrel]
  exact he

/-- Exact full chronological red mutation uses inverse moves to the left from
its current color-block proper order. It retains the actual +I start and does
not invoke an unauthorized green-only reversal argument. -/
theorem principalSeed_red_leftSweep (B₀ U₀ : Matrix 4)
    (hB₀ : SkewSymmetric B₀)
    (hs₀ : add U₀ (transpose U₀) = initialCompanion B₀)
    (ha₀ : add U₀ (scale (-1) (transpose U₀)) = reverse B₀)
    (w : List (Fin 4)) (h : SeedInv B₀ w) (k : Fin 4)
    (hk : columnColor (principalSeed B₀ w).2 k = false) :
    ∃ (p : ProperOrder.CyclicOrder) (s : Fin 4) (hst : s ≤ p.invFun k),
      Compatible (principalSeed B₀ w).1 (columnColor (principalSeed B₀ w).2) k p ∧
      GreenBeforeRed (columnColor (principalSeed B₀ w).2) p ∧
      negateColumn (leftSweep U₀ (columnRelabel (principalSeed B₀ w).2 p)
        (p.invFun k) s) s =
        columnRelabel (principalSeed B₀ (w ++ [k])).2
          (p.trans (leftPermutation (p.invFun k) s hst)) := by
  let B := (principalSeed B₀ w).1
  let C := (principalSeed B₀ w).2
  have hB := principalSeed_skew B₀ hB₀ w
  have hc := seedInv_signCoherent B₀ hB₀ w h
  have hcol := MAExistenceAuxiliaryOrders.companion_colorAdmissible B _ hB
    h.companion.1 (columnColor C) h.arrowSigns h.admissible
  obtain ⟨p, hp, hcolors⟩ := MAExistenceAuxiliaryOrders.colorAdmissible_has_extensions
    B hB (columnColor C) hcol k
  have hproper := compatible_colorBlock_proper B (columnColor C) k p hp hcolors
  have hside : ∀ j, 0 < (relabel B p) j (p.invFun k) → j < p.invFun k := by
    intro j hj
    have hb : 0 < B (p.toFun j) k := by simpa [relabel, p.right_inv] using hj
    have hh : p.invFun (p.toFun j) < p.invFun k := by
      cases hcolor : columnColor C (p.toFun j)
      · exact hp (p.toFun j) k (Or.inl ⟨hb, by change columnColor C k = _ at hk; simp [hk, hcolor]⟩)
      · exact hcolors (p.toFun j) k hcolor hk
    simpa only [p.left_inv] using hh
  obtain ⟨s, hst, hin, hout⟩ := proper_red_has_leftInterval (relabel B p)
    (relabel_skew B p hB) (p.invFun k) (proper_ordered B p k hproper) hside
  have heuler := coefficientBilinear_eq_compatible B₀ U₀ B C hB hs₀ ha₀
    h.exchangeOrigin h.companion (columnColor C) h.arrowSigns k p hp
  have hr : ∀ a, columnRelabel C p a (p.invFun k) ≤ 0 := by
    simpa [columnRelabel, p.right_inv, C] using ((color_iff_red hc k).mp hk).1
  have he := red_leftSweep_coefficients U₀ (relabel B p) (columnRelabel C p)
    (relabel_skew B p hB) (p.invFun k) s hst hr
    (fun j hj => ordered_Euler_forward B U₀ C p heuler _ _ hj) hin hout
  have hn : (principalSeed B₀ (w ++ [k])).2 = mutateCoefficients B C k := by
    rw [principalSeed, evolve_append_singleton]
    rfl
  refine ⟨p, s, hst, hp, hcolors, ?_⟩
  rw [hn]
  rw [← columnRelabel_trans]
  have hrel := columnRelabel_mutateCoefficients B C p (p.invFun k)
  simp only [p.right_inv] at hrel
  rw [hrel]
  exact he

/- The following conjunction contains only current frame data. It does not
assert any color, graph-cycle, or future mutation property. -/
def OrderedRootFrame (B U D : Matrix 4) : Prop :=
  (∀ j, RealRoot (initialCompanion B) (column D j)) ∧
    IntegralBasis D ∧ EulerUnitUpper U D

theorem rightMove_orderedRootFrame (B U D : Matrix 4) (hB : SkewSymmetric B)
    (hU : ∀ i j, U i j + U j i = initialCompanion B i j)
    (t : Fin 4) (ht : t < 3) (hD : OrderedRootFrame B U D) :
    OrderedRootFrame B U (rightMove U D t) :=
  ⟨rightMove_realRoot_columns B U D hB hU t ht hD.1 hD.2.2.2,
    rightMove_integralBasis U D t ht hD.2.1,
    rightMove_euler_unit_upper U D t ht hD.2.2⟩

theorem leftMove_orderedRootFrame (B U D : Matrix 4) (hB : SkewSymmetric B)
    (hU : ∀ i j, U i j + U j i = initialCompanion B i j)
    (t : Fin 4) (ht : t < 3) (hD : OrderedRootFrame B U D) :
    OrderedRootFrame B U (leftMove U D t) :=
  ⟨leftMove_realRoot_columns B U D hB hU t ht hD.1 hD.2.2.2,
    leftMove_integralBasis U D t ht hD.2.1,
    leftMove_euler_unit_upper U D t ht hD.2.2⟩

theorem rightSweep_orderedRootFrame (B U D : Matrix 4) (hB : SkewSymmetric B)
    (hU : ∀ i j, U i j + U j i = initialCompanion B i j)
    (t s : Fin 4) (hts : t ≤ s) (hD : OrderedRootFrame B U D) :
    OrderedRootFrame B U (rightSweep U D t s) := by
  fin_cases t <;> fin_cases s <;> try omega
  all_goals simp only [rightSweep, Fin.reduceFinMk, ↓reduceIte]
  all_goals
    repeat first
      | exact hD
      | apply rightMove_orderedRootFrame B U _ hB hU _ (by decide)

theorem leftSweep_orderedRootFrame (B U D : Matrix 4) (hB : SkewSymmetric B)
    (hU : ∀ i j, U i j + U j i = initialCompanion B i j)
    (t s : Fin 4) (hst : s ≤ t) (hD : OrderedRootFrame B U D) :
    OrderedRootFrame B U (leftSweep U D t s) := by
  fin_cases t <;> fin_cases s <;> try omega
  all_goals simp only [leftSweep, Fin.reduceFinMk, ↓reduceIte]
  all_goals
    repeat first
      | exact hD
      | apply leftMove_orderedRootFrame B U _ hB hU _ (by decide)

private def signAt (s : Fin 4) : Matrix 4 := fun i j =>
  if i=j then if j=s then -1 else 1 else 0

private theorem signAt_inverse (s : Fin 4) : mul (signAt s) (signAt s) = one := by
  funext i j
  fin_cases s <;> fin_cases i <;> fin_cases j <;> simp [signAt, mul, one]

private theorem negateColumn_mul (D : Matrix 4) (s : Fin 4) :
    negateColumn D s = mul D (signAt s) := by
  funext i j
  fin_cases s <;> fin_cases j <;> simp [negateColumn, mul, signAt]

theorem negateColumn_integralBasis (D : Matrix 4) (s : Fin 4)
    (hD : IntegralBasis D) : IntegralBasis (negateColumn D s) := by
  obtain ⟨Di, hl, hr⟩ := hD
  rw [negateColumn_mul]
  refine ⟨mul (signAt s) Di, ?_, ?_⟩
  · rw [Cosquare.mul_assoc, ← Cosquare.mul_assoc Di, hl, Cosquare.one_mul,
      signAt_inverse]
  · rw [Cosquare.mul_assoc, ← Cosquare.mul_assoc (signAt s), signAt_inverse,
      Cosquare.one_mul, hr]

private theorem negateColumn_column (D : Matrix 4) (s j : Fin 4) :
    column (negateColumn D s) j = if j=s then (fun a => -column D j a)
      else column D j := by
  funext a
  by_cases hj : j=s <;> simp [column, negateColumn, hj]

private theorem pairing_neg_left (U : Matrix 4) (x y : Vector4) :
    pairing U (fun a => -x a) y = -pairing U x y := by
  simp only [pairing]; ring

private theorem pairing_neg_right (U : Matrix 4) (x y : Vector4) :
    pairing U x (fun a => -y a) = -pairing U x y := by
  simp only [pairing]; ring

theorem negateColumn_orderedRootFrame (B U D : Matrix 4) (hB : SkewSymmetric B)
    (s : Fin 4) (hD : OrderedRootFrame B U D) :
    OrderedRootFrame B U (negateColumn D s) := by
  refine ⟨?_, negateColumn_integralBasis D s hD.2.1, ?_⟩
  · intro j
    rw [negateColumn_column]
    by_cases hj : j=s
    · simp only [hj, ↓reduceIte]
      exact realRoot_neg _ (initialCompanion_quasiCartan B hB).1
        (initialCompanion_quasiCartan B hB).2.1 (hD.1 s)
    · simpa only [hj, ↓reduceIte] using hD.1 j
  · constructor
    · intro i
      rw [negateColumn_column]
      by_cases hi : i=s <;> simpa only [hi, ↓reduceIte, pairing_neg_left,
        pairing_neg_right, neg_neg] using hD.2.2.1 i
    · intro i j hij
      have hz := hD.2.2.2 i j hij
      rw [negateColumn_column, negateColumn_column]
      by_cases hi : i=s <;> by_cases hj : j=s
      all_goals simp only [hi, hj] at hz
      all_goals simp only [hi, hj, ↓reduceIte, pairing_neg_left, pairing_neg_right,
        neg_neg, hz, neg_zero]

private theorem four_sum_columnRelabel (p : Relabeling 4) (f : Fin 4 → Int) :
    f (p.toFun 0) + f (p.toFun 1) + f (p.toFun 2) + f (p.toFun 3) =
      f 0 + f 1 + f 2 + f 3 := by
  let e : Fin 4 ≃ Fin 4 := ⟨p.toFun, p.invFun, p.left_inv, p.right_inv⟩
  simpa only [Fin.sum_univ_four, e] using e.sum_comp f

theorem columnRelabel_integralBasis (C : Matrix 4) (p : Relabeling 4)
    (hC : IntegralBasis C) : IntegralBasis (columnRelabel C p) := by
  obtain ⟨Ci, hl, hr⟩ := hC
  refine ⟨(fun i j => Ci (p.toFun i) j), ?_, ?_⟩
  · funext i j
    have h := congrFun (congrFun hl (p.toFun i)) (p.toFun j)
    have he : p.toFun i = p.toFun j ↔ i=j := ⟨p.injective, congrArg p.toFun⟩
    simpa only [mul, columnRelabel, one, he] using h
  · funext i j
    change C i (p.toFun 0) * Ci (p.toFun 0) j +
      C i (p.toFun 1) * Ci (p.toFun 1) j +
      C i (p.toFun 2) * Ci (p.toFun 2) j +
      C i (p.toFun 3) * Ci (p.toFun 3) j = one i j
    rw [four_sum_columnRelabel p (fun k => C i k * Ci k j)]
    exact congrFun (congrFun hr i) j

theorem seedInv_compatible_orderedRootFrame (B₀ U₀ : Matrix 4)
    (hB₀ : SkewSymmetric B₀)
    (hs₀ : add U₀ (transpose U₀) = initialCompanion B₀)
    (ha₀ : add U₀ (scale (-1) (transpose U₀)) = reverse B₀)
    (w : List (Fin 4)) (h : SeedInv B₀ w) (k : Fin 4) (p : ProperOrder.CyclicOrder)
    (hp : Compatible (principalSeed B₀ w).1 (columnColor (principalSeed B₀ w).2) k p) :
    OrderedRootFrame B₀ U₀ (columnRelabel (principalSeed B₀ w).2 p) := by
  let B := (principalSeed B₀ w).1
  let C := (principalSeed B₀ w).2
  have he := coefficientBilinear_eq_compatible B₀ U₀ B C
    (principalSeed_skew B₀ hB₀ w) hs₀ ha₀
    h.exchangeOrigin h.companion (columnColor C) h.arrowSigns k p hp
  refine ⟨(fun j => h.roots (p.toFun j)), columnRelabel_integralBasis C p h.basis, ?_⟩
  constructor
  · intro i
    rw [pairing_columnRelabel, he]
    simp [MAExistenceTeamBOrderMutation.labeledUnipotent]
  · intro i j hij
    have hne : p.toFun i ≠ p.toFun j := fun heq => by
      have := p.injective heq; omega
    rw [pairing_columnRelabel, he]
    simp [MAExistenceTeamBOrderMutation.labeledUnipotent, p.left_inv, hne,
      show ¬ i < j by omega]

/-- Every intermediate frame in the actual green sweep and its final signed
frame have genuine initial roots, an integral basis, and unit upper Euler
Gram matrix. The last equality includes the exact chronological next seed
and full permutation. This theorem has current SeedInv premises only. -/
theorem principalSeed_green_fullFrameSweep (B₀ U₀ : Matrix 4)
    (hB₀ : SkewSymmetric B₀)
    (hs₀ : add U₀ (transpose U₀) = initialCompanion B₀)
    (ha₀ : add U₀ (scale (-1) (transpose U₀)) = reverse B₀)
    (w : List (Fin 4)) (h : SeedInv B₀ w) (k : Fin 4)
    (hk : columnColor (principalSeed B₀ w).2 k = true) :
    ∃ (p : ProperOrder.CyclicOrder) (s : Fin 4) (hts : p.invFun k ≤ s),
      Compatible (principalSeed B₀ w).1 (columnColor (principalSeed B₀ w).2) k p ∧
      GreenBeforeRed (columnColor (principalSeed B₀ w).2) p ∧
      OrderedRootFrame B₀ U₀ (columnRelabel (principalSeed B₀ w).2 p) ∧
      (∀ r : Fin 4, p.invFun k ≤ r → r ≤ s →
        OrderedRootFrame B₀ U₀ (rightSweep U₀
          (columnRelabel (principalSeed B₀ w).2 p) (p.invFun k) r)) ∧
      OrderedRootFrame B₀ U₀ (columnRelabel (principalSeed B₀ (w ++ [k])).2
        (p.trans (rightPermutation (p.invFun k) s hts))) ∧
      negateColumn (rightSweep U₀ (columnRelabel (principalSeed B₀ w).2 p)
        (p.invFun k) s) s =
        columnRelabel (principalSeed B₀ (w ++ [k])).2
          (p.trans (rightPermutation (p.invFun k) s hts)) := by
  obtain ⟨p, s, hts, hp, hcolors, he⟩ :=
    principalSeed_green_rightSweep B₀ U₀ hB₀ hs₀ ha₀ w h k hk
  have hsource := seedInv_compatible_orderedRootFrame B₀ U₀ hB₀ hs₀ ha₀ w h k p hp
  have hU : ∀ i j, U₀ i j + U₀ j i = initialCompanion B₀ i j := by
    intro i j
    exact congrFun (congrFun hs₀ i) j
  have hprefix := fun r (htr : p.invFun k ≤ r) =>
    rightSweep_orderedRootFrame B₀ U₀ _ hB₀ hU _ r htr hsource
  refine ⟨p, s, hts, hp, hcolors, hsource, (fun r htr _ => hprefix r htr), ?_, he⟩
  rw [← he]
  exact negateColumn_orderedRootFrame B₀ U₀ _ hB₀ s (hprefix s hts)

/-- The red mutation has the inverse leftward full sweep, with the same exact
intermediate and terminal frame controls. The resulting order need not be
a GreenBeforeRed order for the next colors. -/
theorem principalSeed_red_fullFrameSweep (B₀ U₀ : Matrix 4)
    (hB₀ : SkewSymmetric B₀)
    (hs₀ : add U₀ (transpose U₀) = initialCompanion B₀)
    (ha₀ : add U₀ (scale (-1) (transpose U₀)) = reverse B₀)
    (w : List (Fin 4)) (h : SeedInv B₀ w) (k : Fin 4)
    (hk : columnColor (principalSeed B₀ w).2 k = false) :
    ∃ (p : ProperOrder.CyclicOrder) (s : Fin 4) (hst : s ≤ p.invFun k),
      Compatible (principalSeed B₀ w).1 (columnColor (principalSeed B₀ w).2) k p ∧
      GreenBeforeRed (columnColor (principalSeed B₀ w).2) p ∧
      OrderedRootFrame B₀ U₀ (columnRelabel (principalSeed B₀ w).2 p) ∧
      (∀ r : Fin 4, s ≤ r → r ≤ p.invFun k →
        OrderedRootFrame B₀ U₀ (leftSweep U₀
          (columnRelabel (principalSeed B₀ w).2 p) (p.invFun k) r)) ∧
      OrderedRootFrame B₀ U₀ (columnRelabel (principalSeed B₀ (w ++ [k])).2
        (p.trans (leftPermutation (p.invFun k) s hst))) ∧
      negateColumn (leftSweep U₀ (columnRelabel (principalSeed B₀ w).2 p)
        (p.invFun k) s) s =
        columnRelabel (principalSeed B₀ (w ++ [k])).2
          (p.trans (leftPermutation (p.invFun k) s hst)) := by
  obtain ⟨p, s, hst, hp, hcolors, he⟩ :=
    principalSeed_red_leftSweep B₀ U₀ hB₀ hs₀ ha₀ w h k hk
  have hsource := seedInv_compatible_orderedRootFrame B₀ U₀ hB₀ hs₀ ha₀ w h k p hp
  have hU : ∀ i j, U₀ i j + U₀ j i = initialCompanion B₀ i j := by
    intro i j
    exact congrFun (congrFun hs₀ i) j
  have hprefix := fun r (hrt : r ≤ p.invFun k) =>
    leftSweep_orderedRootFrame B₀ U₀ _ hB₀ hU _ r hrt hsource
  refine ⟨p, s, hst, hp, hcolors, hsource, (fun r _ hrt => hprefix r hrt), ?_, he⟩
  rw [← he]
  exact negateColumn_orderedRootFrame B₀ U₀ _ hB₀ s (hprefix s hst)

end QuiverProofs.MAExistenceSupportChronology
