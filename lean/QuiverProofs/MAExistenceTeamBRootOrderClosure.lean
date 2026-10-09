import QuiverProofs.MAExistenceTeamDJointSeed

/-! Root-height foundations and explicit conditional Euler projections.

Positive genuine initial roots admit height descent without acyclicity,
connectedness, or nonsingularity assumptions. The actual forced-flip and
retention projections require an explicit next-basis NoEulerThreeCycle
hypothesis; that global root-frame theorem remains open. These projections
cover strict green-pivot paths, not exhaustive arrow-sign preservation.
No all-word closure theorem or initialized/preserved stronger invariant is
asserted by this module.
-/
namespace QuiverProofs.MAExistenceTeamBRootOrderClosure
open QuiverProofs QuiverProofs.MAExistenceLiterature
open QuiverProofs.MAExistenceTeamBRootPositivity
open QuiverProofs.MAExistenceTeamCRootSigns
set_option maxHeartbeats 0

def height (x : Vector4) : Int := x 0 + x 1 + x 2 + x 3

theorem norm_as_simple_pairings (A : Matrix 4) (x : Vector4) :
    pairing A x x =
      x 0 * pairing A (simple 0) x + x 1 * pairing A (simple 1) x +
      x 2 * pairing A (simple 2) x + x 3 * pairing A (simple 3) x := by
  simp [pairing, simple]

theorem nonnegative_norm_two_positive_simple_pairing (A : Matrix 4) (x : Vector4)
    (hx : CoordinateNonnegative x) (hn : pairing A x x = 2) :
    ∃ k, 0 < pairing A (simple k) x := by
  by_contra h
  have hp : ∀ k, pairing A (simple k) x ≤ 0 := by
    intro k
    by_contra hk
    exact h ⟨k, by omega⟩
  have h₀ := Int.mul_nonpos_of_nonneg_of_nonpos (hx 0) (hp 0)
  have h₁ := Int.mul_nonpos_of_nonneg_of_nonpos (hx 1) (hp 1)
  have h₂ := Int.mul_nonpos_of_nonneg_of_nonpos (hx 2) (hp 2)
  have h₃ := Int.mul_nonpos_of_nonneg_of_nonpos (hx 3) (hp 3)
  rw [norm_as_simple_pairings] at hn
  omega

theorem nonnegative_norm_two_single_support (A : Matrix 4)
    (hd : ∀ i, A i i = 2) (x : Vector4) (k : Fin 4)
    (hx : CoordinateNonnegative x) (hn : pairing A x x = 2)
    (hz : ∀ i, i ≠ k → x i = 0) : x = simple k := by
  have hxk := hx k
  have hs : x k * x k = 1 := by
    have hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases hk with rfl|rfl|rfl|rfl
    all_goals
      have h₀ := hz 0
      have h₁ := hz 1
      have h₂ := hz 2
      have h₃ := hz 3
      simp only [pairing, hd] at hn
      simp_all
      grind
  have hpos : 0 < x k := by
    by_contra h
    have hz : x k = 0 := by omega
    rw [hz] at hs
    omega
  have hone : x k = 1 := by
    by_contra h
    have htwo : 2 ≤ x k := by omega
    have hm := Int.mul_le_mul htwo htwo (by omega : 0 ≤ (2 : Int)) (by omega : 0 ≤ x k)
    rw [hs] at hm
    omega
  funext i
  by_cases hik : i = k
  · subst i
    simp [simple, hone]
  · simp [simple, hik, hz i hik]

theorem nonsimple_positive_other_coordinate (A : Matrix 4)
    (hd : ∀ i, A i i = 2) (x : Vector4)
    (hx : CoordinateNonnegative x) (hn : pairing A x x = 2)
    (hns : ∀ k, x ≠ simple k) (k : Fin 4) :
    ∃ i, i ≠ k ∧ 0 < x i := by
  by_contra h
  have hz : ∀ i, i ≠ k → x i = 0 := by
    intro i hik
    have hx := hx i
    by_contra hi
    exact h ⟨i, hik, by omega⟩
  exact hns k (nonnegative_norm_two_single_support A hd x k hx hn hz)

theorem simple_reflection_height (A : Matrix 4) (x : Vector4) (k : Fin 4) :
    height (simpleReflection A k x) = height x - pairing A (simple k) x := by
  have hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
  rcases hk with rfl|rfl|rfl|rfl <;>
    simp [height, simpleReflection, reflection, simple] <;> grind

theorem positive_realRoot_reflection_nonpositive_iff (B : Matrix 4)
    (hB : SkewSymmetric B) (x : Vector4) (k : Fin 4)
    (hr : RealRoot (initialCompanion B) x) (hx : CoordinateNonnegative x) :
    CoordinateNonpositive (simpleReflection (initialCompanion B) k x) ↔
      x = simple k := by
  have hA := initialCompanion_quasiCartan B hB
  have hn := realRoot_norm_two _ hA.1 hA.2.1 hr
  constructor
  · intro hy
    have hz : ∀ i, i ≠ k → x i = 0 := by
      intro i hik
      have hn := hy i
      have hp := hx i
      rw [simpleReflection_apply_ne _ k i hik] at hn
      omega
    exact nonnegative_norm_two_single_support _ hA.2.1 x k hx hn hz
  · intro h
    rw [h, simpleReflection_simple_self _ hA.2.1]
    intro i
    simp [simple]
    split_ifs <;> omega

theorem nonsimple_positive_realRoot_simple_reflection (B : Matrix 4)
    (hB : SkewSymmetric B) (x : Vector4) (k : Fin 4)
    (hr : RealRoot (initialCompanion B) x) (hx : CoordinateNonnegative x)
    (hk : x ≠ simple k) :
    CoordinateNonnegative (simpleReflection (initialCompanion B) k x) := by
  rcases initial_realRoot_coordinateDichotomy B hB (RealRoot.reflect k hr) with hp | hn
  · exact hp
  · exact False.elim (hk ((positive_realRoot_reflection_nonpositive_iff B hB x k hr hx).mp hn))

/-- Every positive genuine initial orbit root which is not simple has a
positive height-decreasing simple reflection. No frame ranking or future
coefficient/companion condition is used. -/
theorem positive_realRoot_height_descent (B : Matrix 4) (hB : SkewSymmetric B)
    (x : Vector4) (hr : RealRoot (initialCompanion B) x)
    (hx : CoordinateNonnegative x) (hns : ∀ k, x ≠ simple k) :
    ∃ k, RealRoot (initialCompanion B) (simpleReflection (initialCompanion B) k x) ∧
      CoordinateNonnegative (simpleReflection (initialCompanion B) k x) ∧
      height (simpleReflection (initialCompanion B) k x) < height x := by
  have hA := initialCompanion_quasiCartan B hB
  have hn := realRoot_norm_two _ hA.1 hA.2.1 hr
  obtain ⟨k, hk⟩ := nonnegative_norm_two_positive_simple_pairing _ x hx hn
  have hr' := RealRoot.reflect k hr
  obtain ⟨i, hik, hi⟩ := nonsimple_positive_other_coordinate _ hA.2.1 x hx hn hns k
  have hx' : CoordinateNonnegative (simpleReflection (initialCompanion B) k x) := by
    rcases initial_realRoot_coordinateDichotomy B hB hr' with hp | hn
    · exact hp
    · have h := hn i
      rw [simpleReflection_apply_ne _ k i hik] at h
      omega
  refine ⟨k, hr', hx', ?_⟩
  rw [simple_reflection_height]
  omega


open QuiverProofs QuiverProofs.MAExistenceTeamBRootPositivity
open QuiverProofs.MAExistenceCoefficients
open QuiverProofs.MAExistenceLiterature QuiverProofs.MAExistenceCompanions
open QuiverProofs.MAExistenceTeamCCertificateTransport
set_option maxHeartbeats 0

def positiveColumn (C : Matrix 4) (j : Fin 4) : Vector4 :=
  if columnColor C j then column C j else fun a => -C a j

def EulerEdge (U : Matrix 4) (x y : Vector4) : Prop :=
  0 < pairing U x y ∨ pairing U y x < 0

def NoEulerThreeCycle (U C : Matrix 4) : Prop :=
  ∀ i k j : Fin 4, i ≠ k → k ≠ j → j ≠ i →
    EulerEdge U (positiveColumn C i) (positiveColumn C k) →
    EulerEdge U (positiveColumn C k) (positiveColumn C j) →
    EulerEdge U (positiveColumn C j) (positiveColumn C i) → False

def EulerParts (U B A C : Matrix 4) : Prop :=
  ∀ i j, pairing U (column C i) (column C j) +
      pairing U (column C j) (column C i) = A i j ∧
    pairing U (column C i) (column C j) -
      pairing U (column C j) (column C i) = -B i j

theorem eulerParts_of_origin (B₀ U B C : Matrix 4)
    (hs : Cosquare.add U (Cosquare.transpose U) = initialCompanion B₀)
    (ha : Cosquare.add U (Cosquare.scale (-1) (Cosquare.transpose U)) = reverse B₀)
    (he : B = Cosquare.mul (Cosquare.mul (Cosquare.transpose C) B₀) C) :
    EulerParts U B (coefficientCompanion B₀ C) C := by
  have hp := coefficientBilinear_parts B₀ U B C hs ha he
  have hpair : ∀ i j, pairing U (column C i) (column C j) =
      coefficientBilinear U C i j := by
    intro i j
    simp only [pairing, column, coefficientBilinear, Cosquare.mul, Cosquare.transpose]
    grind
  intro i j
  have h₁ := congrFun (congrFun hp.1 i) j
  have h₂ := congrFun (congrFun hp.2 i) j
  simp only [Cosquare.add, Cosquare.transpose, Cosquare.scale, reverse] at h₁ h₂
  rw [hpair i j, hpair j i]
  constructor <;> omega

private theorem euler_nonpos_pair (U B A C : Matrix 4)
    (hp : EulerParts U B A C) (hA : QuasiCartanCompanion B A)
    (i j : Fin 4) (hij : i ≠ j) (hpos : 0 < B i j) (han : A i j ≤ 0) :
    pairing U (column C i) (column C j) = -B i j ∧
    pairing U (column C j) (column C i) = 0 := by
  have hparts := hp i j
  rcases Int.natAbs_eq_natAbs_iff.mp (hA.2.2 i j hij) with he | he <;> omega

private theorem euler_pos_pair (U B A C : Matrix 4)
    (hp : EulerParts U B A C) (hA : QuasiCartanCompanion B A)
    (i j : Fin 4) (hij : i ≠ j) (hpos : 0 < B i j) (han : 0 < A i j) :
    pairing U (column C i) (column C j) = 0 ∧
    pairing U (column C j) (column C i) = B i j := by
  have hparts := hp i j
  rcases Int.natAbs_eq_natAbs_iff.mp (hA.2.2 i j hij) with he | he <;> omega

private theorem positiveColumn_mutation_pivot (B C : Matrix 4) (k : Fin 4)
    (hc : SignCoherent C) (hk : columnColor C k = true) :
    positiveColumn (mutateCoefficients B C k) k = column C k := by
  have hg := (color_iff_green hc k).mp hk
  have hr := (pivot_red_iff_green B C k).mpr hg
  have hn := color_red hr
  funext a
  simp [positiveColumn, hn, column, mutateCoefficients]

private theorem positiveColumn_mutation_zero (B C : Matrix 4) (k i : Fin 4)
    (hc : SignCoherent C) (hik : i ≠ k)
    (ht : pivotWeight B (columnColor C) k i = 0) :
    positiveColumn (mutateCoefficients B C k) i = positiveColumn C i := by
  have hcolor := QuiverProofs.MAExistenceTeamDArrowSigns.columnColor_mutation_zero_weight
    B C k i hc hik ht
  have hg : columnColor C k = true → ∀ a, 0 ≤ C a k :=
    fun h => ((color_iff_green hc k).mp h).1
  have hr : columnColor C k = false → ∀ a, C a k ≤ 0 :=
    fun h => ((color_iff_red hc k).mp h).1
  have he := coefficientMutation_zero_weight B C (columnColor C) k i hik hg hr ht
  simp only [positiveColumn, hcolor]
  split
  · exact he
  · funext a
    have h := congrFun he a
    simp only [column] at h ⊢
    omega

private theorem green_shear_column (B C : Matrix 4) (k j : Fin 4)
    (hc : SignCoherent C) (hk : columnColor C k = true)
    (hjk : j ≠ k) (hn : 0 < B k j) :
    column (mutateCoefficients B C k) j =
      fun a => B k j * C a k - (-C a j) := by
  have hg := ((color_iff_green hc k).mp hk).1
  funext a
  have ha := hg a
  simp only [column, mutateCoefficients, hjk, ↓reduceIte, correction]
  rw [max_eq_left ha, max_eq_left (by omega : 0 ≤ B k j),
    max_eq_right (by omega : -C a k ≤ 0), max_eq_right (by omega : -B k j ≤ 0)]
  grind

private theorem pairing_neg_left (U : Matrix 4) (x y : Vector4) :
    pairing U (fun a => -x a) y = -pairing U x y := by
  simp only [pairing]
  grind

private theorem pairing_neg_right (U : Matrix 4) (x y : Vector4) :
    pairing U x (fun a => -y a) = -pairing U x y := by
  simp only [pairing]
  grind

private theorem pairing_smul_sub_right (U : Matrix 4) (x y z : Vector4) (n : Int) :
    pairing U x (fun a => n * y a - z a) =
      n * pairing U x y - pairing U x z := by
  simp only [pairing]
  grind

private theorem pairing_smul_sub_left (U : Matrix 4) (x y z : Vector4) (n : Int) :
    pairing U (fun a => n * x a - y a) z =
      n * pairing U x z - pairing U y z := by
  simp only [pairing]
  grind

theorem forced_flip_witness_of_noCycle
    (U D : Matrix 4) (α β γ : Vector4) (m n c : Int)
    (i k j : Fin 4) (hik : i ≠ k) (hkj : k ≠ j) (hji : j ≠ i)
    (hm : 0 < m) (hn : 0 < n) (houter : c < m * n)
    (hi : positiveColumn D i = α) (hk : positiveColumn D k = β)
    (hj : column D j = fun a => n * β a - γ a)
    (hba : pairing U β α = -m)
    (hgb : pairing U γ β = 0) (hbb : pairing U β β = 1)
    (hga : pairing U γ α = -c)
    (hcoh : SignCoherent D) (hno : NoEulerThreeCycle U D) :
    ∃ a, 0 < D a j := by
  rcases hcoh j with hg | hr
  · exact hg.2
  · have hc := color_red hr
    have hjp : positiveColumn D j = fun a => γ a - n * β a := by
      simp only [positiveColumn, hc, Bool.false_eq_true, ↓reduceIte]
      funext a
      have h := congrFun hj a
      simp only [column] at h
      omega
    apply False.elim
    apply hno i k j hik hkj hji
    · rw [hi, hk]
      exact Or.inr (by rw [hba]; omega)
    · rw [hk, hjp]
      right
      rw [pairing_sub_smul_left, hgb, hbb]
      omega
    · rw [hjp, hi]
      left
      rw [pairing_sub_smul_left, hga, hba]
      grind

theorem forced_retention_witness_of_noCycle
    (U D : Matrix 4) (α β γ : Vector4) (m n c : Int)
    (i k j : Fin 4) (hik : i ≠ k) (hkj : k ≠ j) (hji : j ≠ i)
    (hm : 0 < m) (hn : 0 < n) (houter : m * n < c)
    (hi : positiveColumn D i = α) (hk : positiveColumn D k = β)
    (hj : column D j = fun a => n * β a - γ a)
    (hab : pairing U α β = -m)
    (hgb : pairing U γ β = 0) (hbb : pairing U β β = 1)
    (hag : pairing U α γ = -c)
    (hcoh : SignCoherent D) (hno : NoEulerThreeCycle U D) :
    ∃ a, D a j < 0 := by
  rcases hcoh j with hg | hr
  · have hc := color_green hg
    have hjp : positiveColumn D j = fun a => n * β a - γ a := by
      simp only [positiveColumn, hc, ↓reduceIte]
      exact hj
    apply False.elim
    apply hno k i j (Ne.symm hik) (Ne.symm hji) (Ne.symm hkj)
    · rw [hi, hk]
      exact Or.inr (by rw [hab]; omega)
    · rw [hi, hjp]
      left
      rw [pairing_smul_sub_right, hab, hag]
      grind
    · rw [hjp, hk]
      left
      rw [pairing_smul_sub_left, hbb, hgb]
      omega
  · exact hr.2

theorem green_red_path_retention_of_euler_noCycle
    (U B A C : Matrix 4) (k i j : Fin 4)
    (hB : SkewSymmetric B) (hA : QuasiCartanCompanion B A)
    (hs : ArrowSigns B A (columnColor C)) (hp : EulerParts U B A C)
    (hc : SignCoherent C) (hnext : SignCoherent (mutateCoefficients B C k))
    (hno : NoEulerThreeCycle U (mutateCoefficients B C k))
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hk : columnColor C k = true) (hi : columnColor C i = true)
    (hj : columnColor C j = false) (hx : 0 < B i k) (hy : 0 < B k j)
    (houter : mutate B k i j < 0) :
    ∃ a, C a j + C a k * B k j < 0 := by
  have hti : pivotWeight B (columnColor C) k i = 0 := by
    have := hB k i
    simp only [pivotWeight, hk, if_true]
    omega
  have hcor : correction (B i k) (B k j) = B i k * B k j := by
    simp only [correction]
    rw [max_eq_left (by omega : 0 ≤ B i k), max_eq_left (by omega : 0 ≤ B k j),
      max_eq_right (by omega : -B i k ≤ 0), max_eq_right (by omega : -B k j ≤ 0)]
    simp
  have hmut : mutate B k i j = B i j + B i k * B k j := by
    simp [mutate, hik, hjk, hcor]
  have hprod : 0 < B i k * B k j := Int.mul_pos hx hy
  have hbij : B i j < 0 := by rw [hmut] at houter; omega
  have hAik : A i k ≤ 0 := by
    have h := hs i k hx
    simp only [hi, hk, Bool.true_eq_false, false_and, iff_false] at h
    omega
  have hAkj : A k j ≤ 0 := by
    have h := hs k j hy
    simp only [hk, hj, Bool.true_eq_false, Bool.false_eq_true, false_and, iff_false] at h
    omega
  have hAij : A i j = -B i j := by
    have hji : 0 < B j i := by have := hB j i; omega
    have hapos : 0 < A i j := by
      rw [hA.1 i j]
      exact (hs j i hji).mpr ⟨hj, hi⟩
    rcases Int.natAbs_eq_natAbs_iff.mp (hA.2.2 i j hij) with he | he <;> omega
  have hikE := euler_nonpos_pair U B A C hp hA i k hik hx hAik
  have hkjE := euler_nonpos_pair U B A C hp hA k j (Ne.symm hjk) hy hAkj
  have hdiag : pairing U (column C k) (column C k) = 1 := by
    have h := (hp k k).1
    rw [hA.2.1 k] at h
    omega
  have houterE : pairing U (column C i) (column C j) = -B i j := by
    have h := hp i j
    rw [hAij] at h
    omega
  have h₁ : positiveColumn (mutateCoefficients B C k) i = column C i := by
    rw [positiveColumn_mutation_zero B C k i hc hik hti]
    simp [positiveColumn, hi]
  have h₂ := positiveColumn_mutation_pivot B C k hc hk
  have h₃ := green_shear_column B C k j hc hk hjk hy
  have hw := forced_retention_witness_of_noCycle U (mutateCoefficients B C k)
    (column C i) (column C k) (fun a => -C a j)
    (B i k) (B k j) (-B i j) i k j hik (Ne.symm hjk) (Ne.symm hij)
    hx hy (by rw [hmut] at houter; omega) h₁ h₂ h₃ hikE.1
    (by
      change pairing U (fun a => -(column C j) a) (column C k) = 0
      rw [pairing_neg_left, hkjE.2]
      omega)
    hdiag (by simpa only [column, pairing_neg_right] using congrArg Neg.neg houterE)
    hnext hno
  obtain ⟨a, ha⟩ := hw
  have h := congrFun h₃ a
  simp only [column] at h
  exact ⟨a, by grind⟩

theorem red_path_flip_of_euler_noCycle
    (U B A C : Matrix 4) (k i j : Fin 4)
    (hB : SkewSymmetric B) (hA : QuasiCartanCompanion B A)
    (hs : ArrowSigns B A (columnColor C)) (hp : EulerParts U B A C)
    (htri : QuiverProofs.MAExistenceTeamBCompanionClosure.TrianglePathSigns B A)
    (hc : SignCoherent C) (hnext : SignCoherent (mutateCoefficients B C k))
    (hno : NoEulerThreeCycle U (mutateCoefficients B C k))
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hk : columnColor C k = true) (hi : columnColor C i = false)
    (hj : columnColor C j = false) (hx : 0 < B i k) (hy : 0 < B k j)
    (houter : 0 < mutate B k i j) :
    ∃ a, 0 < C a j + C a k * B k j := by
  have hti : pivotWeight B (columnColor C) k i = 0 := by
    have := hB k i
    simp only [pivotWeight, hk, if_true]
    omega
  have hcor : correction (B i k) (B k j) = B i k * B k j := by
    simp only [correction]
    rw [max_eq_left (by omega : 0 ≤ B i k), max_eq_left (by omega : 0 ≤ B k j),
      max_eq_right (by omega : -B i k ≤ 0), max_eq_right (by omega : -B k j ≤ 0)]
    simp
  have hmut : mutate B k i j = B i j + B i k * B k j := by
    simp [mutate, hik, hjk, hcor]
  have hAik : 0 < A i k := (hs i k hx).mpr ⟨hi, hk⟩
  have hAkj : A k j = -B k j := by
    have h := hs k j hy
    simp only [hk, hj, Bool.true_eq_false, Bool.false_eq_true, false_and, iff_false] at h
    rcases Int.natAbs_eq_natAbs_iff.mp (hA.2.2 k j (Ne.symm hjk)) with he | he <;> omega
  have hAijN : A i j ≤ 0 := by
    by_cases hz : B i j = 0
    · have h := hA.2.2 i j hij
      simp only [hz, Int.natAbs_zero] at h
      have := Int.natAbs_eq_zero.mp h
      omega
    · by_cases hpos : 0 < B i j
      · have h := hs i j hpos
        simp only [hi, hj, Bool.false_eq_true, and_false, iff_false] at h
        omega
      · have hpos : 0 < B j i := by have := hB j i; omega
        have h := hs j i hpos
        rw [←hA.1 i j] at h
        simp only [hi, hj, Bool.false_eq_true, and_false, iff_false] at h
        omega
  have hbij : B i j ≤ 0 := by
    by_contra hn
    have hpos : 0 < B i j := by omega
    have hAn : A i j < 0 := by
      rcases Int.natAbs_eq_natAbs_iff.mp (hA.2.2 i j hij) with he | he <;> omega
    have hprod : 0 < A i j * A k j * A i k := by
      rw [hAkj]
      exact Int.mul_pos (Int.mul_pos_of_neg_of_neg hAn (by omega)) hAik
    have := (htri i j k hij hik hjk hx hy).mp hprod
    omega
  have hAij : A i j = B i j := by
    rcases Int.natAbs_eq_natAbs_iff.mp (hA.2.2 i j hij) with he | he <;> omega
  have hikE := euler_pos_pair U B A C hp hA i k hik hx hAik
  have hkjE := euler_nonpos_pair U B A C hp hA k j (Ne.symm hjk) hy (by omega)
  have hdiag : pairing U (column C k) (column C k) = 1 := by
    have h := (hp k k).1
    rw [hA.2.1 k] at h
    omega
  have houterE : pairing U (column C j) (column C i) = B i j := by
    have h := hp i j
    rw [hAij] at h
    omega
  have h₁ : positiveColumn (mutateCoefficients B C k) i = fun a => -C a i := by
    rw [positiveColumn_mutation_zero B C k i hc hik hti]
    simp [positiveColumn, hi]
  have h₂ := positiveColumn_mutation_pivot B C k hc hk
  have h₃ := green_shear_column B C k j hc hk hjk hy
  have hw := forced_flip_witness_of_noCycle U (mutateCoefficients B C k)
    (fun a => -C a i) (column C k) (fun a => -C a j)
    (B i k) (B k j) (-B i j) i k j hik (Ne.symm hjk) (Ne.symm hij)
    hx hy (by rw [hmut] at houter; omega) h₁ h₂ h₃
    (by
      change pairing U (column C k) (fun a => -(column C i) a) = -B i k
      rw [pairing_neg_right, hikE.2])
    (by
      change pairing U (fun a => -(column C j) a) (column C k) = 0
      rw [pairing_neg_left, hkjE.2]
      omega)
    hdiag
    (by
      change pairing U (fun a => -(column C j) a) (fun a => -(column C i) a) = -(-B i j)
      rw [pairing_neg_left, pairing_neg_right, houterE])
    hnext hno
  obtain ⟨a, ha⟩ := hw
  have h := congrFun h₃ a
  simp only [column] at h
  exact ⟨a, by grind⟩

open QuiverProofs.MAExistenceTeamDJointSeed QuiverProofs.MAExistenceTeamCSeedStep

theorem actual_red_path_flip_of_euler_noCycle
    (B₀ U : Matrix 4) (hB₀ : SkewSymmetric B₀) (w : List (Fin 4))
    (hinv : SeedInv B₀ w)
    (hs₀ : Cosquare.add U (Cosquare.transpose U) = initialCompanion B₀)
    (ha₀ : Cosquare.add U (Cosquare.scale (-1) (Cosquare.transpose U)) = reverse B₀)
    (k i j : Fin 4) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hk : columnColor (principalSeed B₀ w).2 k = true)
    (hi : columnColor (principalSeed B₀ w).2 i = false)
    (hj : columnColor (principalSeed B₀ w).2 j = false)
    (hx : 0 < (principalSeed B₀ w).1 i k) (hy : 0 < (principalSeed B₀ w).1 k j)
    (houter : 0 < mutate (principalSeed B₀ w).1 k i j)
    (hno : NoEulerThreeCycle U (principalSeed B₀ (w ++ [k])).2) :
    ∃ a, 0 < (principalSeed B₀ w).2 a j +
      (principalSeed B₀ w).2 a k * (principalSeed B₀ w).1 k j := by
  have hB := principalSeed_skew B₀ hB₀ w
  have hc := seedInv_signCoherent B₀ hB₀ w hinv
  have hn := coefficientMutation_rooted_signCoherent_quasiCartan B₀
    (principalSeed B₀ w).1 (principalSeed B₀ w).2 hB₀ hB k
    hinv.companion hinv.arrowSigns hinv.admissible hinv.roots
  have he : principalSeed B₀ (w ++ [k]) = mutateSeed (principalSeed B₀ w) k :=
    evolve_append_singleton B₀ identityCoefficients w k
  have hp := eulerParts_of_origin B₀ U (principalSeed B₀ w).1
    (principalSeed B₀ w).2 hs₀ ha₀ hinv.exchangeOrigin
  exact red_path_flip_of_euler_noCycle U (principalSeed B₀ w).1
    (coefficientCompanion B₀ (principalSeed B₀ w).2) (principalSeed B₀ w).2 k i j
    hB hinv.companion hinv.arrowSigns hp
    (QuiverProofs.MAExistenceTeamBCompanionClosure.companionAdmissible4_trianglePathSigns
      _ _ hB hinv.companion hinv.admissible)
    hc hn.2.1 (by simpa only [he, mutateSeed] using hno)
    hij hik hjk hk hi hj hx hy houter

theorem actual_green_red_path_retention_of_euler_noCycle
    (B₀ U : Matrix 4) (hB₀ : SkewSymmetric B₀) (w : List (Fin 4))
    (hinv : SeedInv B₀ w)
    (hs₀ : Cosquare.add U (Cosquare.transpose U) = initialCompanion B₀)
    (ha₀ : Cosquare.add U (Cosquare.scale (-1) (Cosquare.transpose U)) = reverse B₀)
    (k i j : Fin 4) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hk : columnColor (principalSeed B₀ w).2 k = true)
    (hi : columnColor (principalSeed B₀ w).2 i = true)
    (hj : columnColor (principalSeed B₀ w).2 j = false)
    (hx : 0 < (principalSeed B₀ w).1 i k) (hy : 0 < (principalSeed B₀ w).1 k j)
    (houter : mutate (principalSeed B₀ w).1 k i j < 0)
    (hno : NoEulerThreeCycle U (principalSeed B₀ (w ++ [k])).2) :
    ∃ a, (principalSeed B₀ w).2 a j +
      (principalSeed B₀ w).2 a k * (principalSeed B₀ w).1 k j < 0 := by
  have hB := principalSeed_skew B₀ hB₀ w
  have hc := seedInv_signCoherent B₀ hB₀ w hinv
  have hn := coefficientMutation_rooted_signCoherent_quasiCartan B₀
    (principalSeed B₀ w).1 (principalSeed B₀ w).2 hB₀ hB k
    hinv.companion hinv.arrowSigns hinv.admissible hinv.roots
  have he : principalSeed B₀ (w ++ [k]) = mutateSeed (principalSeed B₀ w) k :=
    evolve_append_singleton B₀ identityCoefficients w k
  have hp := eulerParts_of_origin B₀ U (principalSeed B₀ w).1
    (principalSeed B₀ w).2 hs₀ ha₀ hinv.exchangeOrigin
  exact green_red_path_retention_of_euler_noCycle U (principalSeed B₀ w).1
    (coefficientCompanion B₀ (principalSeed B₀ w).2) (principalSeed B₀ w).2 k i j
    hB hinv.companion hinv.arrowSigns hp hc hn.2.1
    (by simpa only [he, mutateSeed] using hno)
    hij hik hjk hk hi hj hx hy houter

end QuiverProofs.MAExistenceTeamBRootOrderClosure
