import QuiverProofs.Mutation
import QuiverProofs.Algebra

/-! The rank-three Markov region, proved directly from integer mutation. -/
namespace QuiverProofs

/-- Positive cyclic orientation 0 → 1 → 2 → 0. -/
def cycleThree (x y z : Int) : Matrix 3 := fun i j =>
  match i.val, j.val with
  | 0, 1 => x | 1, 2 => y | 2, 0 => z
  | 1, 0 => -x | 2, 1 => -y | 0, 2 => -z
  | _, _ => 0

def reverseMatrix {n : Nat} (B : Matrix n) : Matrix n := fun i j => - B i j

def triangleMarkov (x y z : Int) : Int := x^2 + y^2 + z^2 - x*y*z

def TriangleRegion (x y z : Int) : Prop :=
  2 ≤ x ∧ 2 ≤ y ∧ 2 ≤ z ∧ triangleMarkov x y z ≤ 4

theorem reverseMatrix_involutive {n : Nat} (B : Matrix n) :
    reverseMatrix (reverseMatrix B) = B := by
  funext i j
  simp [reverseMatrix]

theorem mutate_reverseMatrix {n : Nat} (B : Matrix n) (k : Fin n) :
    mutate (reverseMatrix B) k = reverseMatrix (mutate B k) := by
  funext i j
  by_cases h : i = k ∨ j = k
  · simp [mutate, reverseMatrix, h]
  · simp [mutate, reverseMatrix, h, correction_neg]
    omega

theorem triangleMarkov_mutation (x y z : Int) :
    triangleMarkov x y (x*y-z) = triangleMarkov x y z := by
  unfold triangleMarkov
  grind

theorem triangleMarkov_swap (x y z : Int) :
    triangleMarkov y x z = triangleMarkov x y z := by
  unfold triangleMarkov
  grind

theorem triangleMarkov_rotate (x y z : Int) :
    triangleMarkov y z x = triangleMarkov x y z := by
  unfold triangleMarkov
  grind

/-- No mutation in the Markov region can produce weight 1 or break the cycle. -/
theorem triangleRegion_new_weight (x y z : Int) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hC : triangleMarkov x y z ≤ 4) : 2 ≤ x*y-z := by
  have hxy : 4 ≤ x*y := by
    have := Int.mul_le_mul hx hy (by decide : (0:Int) ≤ 2) (by omega : 0 ≤ x)
    omega
  have hxs : 4 ≤ x^2 := Algebra.square_monotone 2 x (by decide) hx
  have hys : 4 ≤ y^2 := Algebra.square_monotone 2 y (by decide) hy
  have hs := Algebra.square_nonnegative (x*y-z)
  have hid := triangleMarkov_mutation x y z
  by_cases ht : x*y-z ≤ 0
  · have hm := Int.mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ x*y by omega) ht
    unfold triangleMarkov at hid hC
    omega
  · have hd := Algebra.square_nonnegative (x-y)
    by_cases heq : x*y-z = 1
    · have he : triangleMarkov x y z = (x-y)^2+x*y+1 := by
        rw [← triangleMarkov_mutation, heq]
        unfold triangleMarkov
        grind
      omega
    · omega

theorem triangleRegion_mutate_z (x y z : Int) (h : TriangleRegion x y z) :
    TriangleRegion x y (x*y-z) := by
  rcases h with ⟨hx,hy,hz,hC⟩
  exact ⟨hx,hy,triangleRegion_new_weight x y z hx hy hC,
    by rw [triangleMarkov_mutation]; exact hC⟩

theorem triangleRegion_rotate (x y z : Int) (h : TriangleRegion x y z) :
    TriangleRegion y z x := by
  rcases h with ⟨hx,hy,hz,hC⟩
  exact ⟨hy,hz,hx,by rw [triangleMarkov_rotate]; exact hC⟩

theorem triangleRegion_mutate_x (x y z : Int) (h : TriangleRegion x y z) :
    TriangleRegion (y*z-x) y z := by
  have := triangleRegion_mutate_z y z x (triangleRegion_rotate x y z h)
  exact triangleRegion_rotate z (y*z-x) y (triangleRegion_rotate y z (y*z-x) this)

theorem triangleRegion_mutate_y (x y z : Int) (h : TriangleRegion x y z) :
    TriangleRegion x (x*z-y) z := by
  have h' := triangleRegion_rotate y z x (triangleRegion_rotate x y z h)
  have h'' := triangleRegion_mutate_z z x y h'
  have hr := triangleRegion_rotate z x (z*x-y) h''
  have he : z*x-y = x*z-y := by grind
  rwa [he] at hr

theorem cycleThree_mutate_zero (x y z : Int) (hx : 0 ≤ x) (hz : 0 ≤ z) :
    mutate (cycleThree x y z) 0 = reverseMatrix (cycleThree x (x*z-y) z) := by
  funext i j
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hi with rfl|rfl|rfl <;> rcases hj with rfl|rfl|rfl <;>
    simp [mutate, cycleThree, reverseMatrix, correction] <;> grind

theorem cycleThree_mutate_one (x y z : Int) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    mutate (cycleThree x y z) 1 = reverseMatrix (cycleThree x y (x*y-z)) := by
  funext i j
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hi with rfl|rfl|rfl <;> rcases hj with rfl|rfl|rfl <;>
    simp [mutate, cycleThree, reverseMatrix, correction] <;> grind

theorem cycleThree_mutate_two (x y z : Int) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    mutate (cycleThree x y z) 2 = reverseMatrix (cycleThree (y*z-x) y z) := by
  funext i j
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hi with rfl|rfl|rfl <;> rcases hj with rfl|rfl|rfl <;>
    simp [mutate, cycleThree, reverseMatrix, correction] <;> grind

/-- Either orientation is kept in the cyclic Markov region. -/
def InTriangleRegion (B : Matrix 3) : Prop :=
  ∃ x y z, TriangleRegion x y z ∧
    (B = cycleThree x y z ∨ B = reverseMatrix (cycleThree x y z))

theorem inTriangleRegion_reverse (B : Matrix 3) (h : InTriangleRegion B) :
    InTriangleRegion (reverseMatrix B) := by
  rcases h with ⟨x,y,z,hr,h|h⟩
  · exact ⟨x,y,z,hr,Or.inr (congrArg reverseMatrix h)⟩
  · refine ⟨x,y,z,hr,Or.inl ?_⟩
    rw [h, reverseMatrix_involutive]

theorem cycleThree_mutate_in_region (x y z : Int) (h : TriangleRegion x y z)
    (k : Fin 3) : InTriangleRegion (mutate (cycleThree x y z) k) := by
  have hk : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hk with rfl|rfl|rfl
  · exact ⟨x,x*z-y,z,triangleRegion_mutate_y x y z h,
      Or.inr (cycleThree_mutate_zero x y z (by have := h.1; omega) (by have := h.2.2.1; omega))⟩
  · exact ⟨x,y,x*y-z,triangleRegion_mutate_z x y z h,
      Or.inr (cycleThree_mutate_one x y z (by have := h.1; omega) (by have := h.2.1; omega))⟩
  · exact ⟨y*z-x,y,z,triangleRegion_mutate_x x y z h,
      Or.inr (cycleThree_mutate_two x y z (by have := h.2.1; omega) (by have := h.2.2.1; omega))⟩

theorem inTriangleRegion_mutate (B : Matrix 3) (h : InTriangleRegion B)
    (k : Fin 3) : InTriangleRegion (mutate B k) := by
  rcases h with ⟨x,y,z,hr,rfl|rfl⟩
  · exact cycleThree_mutate_in_region x y z hr k
  · rw [mutate_reverseMatrix]
    exact inTriangleRegion_reverse _ (cycleThree_mutate_in_region x y z hr k)

theorem inTriangleRegion_applyWord (B : Matrix 3) (h : InTriangleRegion B)
    (word : List (Fin 3)) : InTriangleRegion (applyWord B word) := by
  induction word generalizing B with
  | nil => exact h
  | cons k ks ih => exact ih _ (inTriangleRegion_mutate B h k)

theorem inTriangleRegion_not_acyclic (B : Matrix 3) (h : InTriangleRegion B) :
    ¬ Acyclic B := by
  rcases h with ⟨x,y,z,⟨hx,hy,hz,_⟩,rfl|rfl⟩ <;> rintro ⟨rank,hr⟩
  · have h01 := hr 0 1 (show 0 < cycleThree x y z 0 1 by simp [cycleThree]; omega)
    have h12 := hr 1 2 (show 0 < cycleThree x y z 1 2 by simp [cycleThree]; omega)
    have h20 := hr 2 0 (show 0 < cycleThree x y z 2 0 by simp [cycleThree]; omega)
    omega
  · have h10 := hr 1 0 (show 0 < reverseMatrix (cycleThree x y z) 1 0 by simp [cycleThree, reverseMatrix]; omega)
    have h21 := hr 2 1 (show 0 < reverseMatrix (cycleThree x y z) 2 1 by simp [cycleThree, reverseMatrix]; omega)
    have h02 := hr 0 2 (show 0 < reverseMatrix (cycleThree x y z) 0 2 by simp [cycleThree, reverseMatrix]; omega)
    omega

/-- Quantifies over every finite mutation word, with no search-depth bound. -/
theorem inTriangleRegion_NMA (B : Matrix 3) (h : InTriangleRegion B) :
    ¬ MutationAcyclic B := by
  rintro ⟨word,ha⟩
  exact inTriangleRegion_not_acyclic _ (inTriangleRegion_applyWord B h word) ha

theorem rankThree_cycle_NMA (x y z : Int) (hx : 2 ≤ x) (hy : 2 ≤ y) (hz : 2 ≤ z)
    (hC : triangleMarkov x y z ≤ 4) : ¬ MutationAcyclic (cycleThree x y z) :=
  inTriangleRegion_NMA _ ⟨x,y,z,⟨hx,hy,hz,hC⟩,Or.inl rfl⟩

theorem rankThree_reverse_cycle_NMA (x y z : Int) (hx : 2 ≤ x) (hy : 2 ≤ y) (hz : 2 ≤ z)
    (hC : triangleMarkov x y z ≤ 4) : ¬ MutationAcyclic (reverseMatrix (cycleThree x y z)) :=
  inTriangleRegion_NMA _ ⟨x,y,z,⟨hx,hy,hz,hC⟩,Or.inr rfl⟩


/-- Reversal commutes with an arbitrary chronological mutation word. -/
theorem applyWord_reverseMatrix {n : Nat} (B : Matrix n) (word : List (Fin n)) :
    applyWord (reverseMatrix B) word = reverseMatrix (applyWord B word) := by
  induction word generalizing B with
  | nil => rfl
  | cons k ks ih => simp only [applyWord, mutate_reverseMatrix, ih]


theorem cycleThree_skew (x y z : Int) : SkewSymmetric (cycleThree x y z) := by
  intro i j
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hi with rfl|rfl|rfl <;> rcases hj with rfl|rfl|rfl <;> simp [cycleThree]

theorem rankThree_word_skew (B : Matrix 3) (h : SkewSymmetric B) (word : List (Fin 3)) :
    SkewSymmetric (applyWord B word) := by
  induction word generalizing B with
  | nil => exact h
  | cons k ks ih => exact ih _ (mutation_preserves_skew B k h)

theorem acyclic_reverse_three (B : Matrix 3) (hB : SkewSymmetric B) (h : Acyclic B) :
    Acyclic (reverseMatrix B) := by
  rcases h with ⟨rank,hr⟩
  refine ⟨fun i => rank 0 + rank 1 + rank 2 - rank i, ?_⟩
  intro i j hij
  have hji : 0 < B j i := by
    have hs := hB i j
    simp only [reverseMatrix] at hij
    omega
  have hijrank := hr j i hji
  have hibound : rank i ≤ rank 0 + rank 1 + rank 2 := by
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hi with rfl|rfl|rfl <;> omega
  have hjbound : rank j ≤ rank 0 + rank 1 + rank 2 := by
    have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hj with rfl|rfl|rfl <;> omega
  dsimp
  omega

theorem mutationAcyclic_reverse_three (B : Matrix 3) (hB : SkewSymmetric B)
    (h : MutationAcyclic B) : MutationAcyclic (reverseMatrix B) := by
  rcases h with ⟨word,ha⟩
  refine ⟨word, ?_⟩
  rw [applyWord_reverseMatrix]
  exact acyclic_reverse_three _ (rankThree_word_skew B hB word) ha

/-- Largest-edge mutation is a strict descent outside the Markov region. -/
theorem triangle_sorted_descent (x y z : Int) (hx : 2 ≤ x) (hxy : x ≤ y)
    (hyz : y ≤ z) (hC : 4 < triangleMarkov x y z) : x*y < 2*z := by
  apply Int.lt_of_not_ge
  intro h
  have hbound : 2*z ≤ x*y := by omega
  have hprod := Int.mul_nonpos_of_nonneg_of_nonpos
    (show 0 ≤ z-y by omega) (show z+y-x*y ≤ 0 by omega)
  have hid : triangleMarkov x y z - (x^2+(2-x)*y^2) = (z-y)*(z+y-x*y) := by
    unfold triangleMarkov
    grind
  have htop : triangleMarkov x y z ≤ x^2+(2-x)*y^2 := by omega
  by_cases heq : x = 2
  · subst x
    simp at htop
    omega
  · have hx3 : 3 ≤ x := by omega
    have hsq := Algebra.square_monotone x y (by omega) hxy
    have hm := Int.mul_nonpos_of_nonpos_of_nonneg
      (show 2-x ≤ 0 by omega) (show 0 ≤ y^2-x^2 by omega)
    have hn := Int.mul_nonpos_of_nonneg_of_nonpos (Algebra.square_nonnegative x)
      (show 3-x ≤ 0 by omega)
    have hpoly : x^2+(2-x)*y^2 = (2-x)*(y^2-x^2)+x^2*(3-x) := by grind
    omega

theorem triangle_largest_descent (x y z : Int) (hx : 0 < x) (hy : 0 < y)
    (hz : 0 < z) (hxz : x ≤ z) (hyz : y ≤ z) (h : ¬ TriangleRegion x y z) :
    x*y ≤ z ∨ (0 < x*y-z ∧ x*y-z < z ∧ ¬ TriangleRegion x y (x*y-z)) := by
  by_cases he : x*y ≤ z
  · exact Or.inl he
  · have hx2 : 2 ≤ x := by
      by_cases hh : 2 ≤ x
      · exact hh
      have hx1 : x = 1 := by omega
      subst x
      simp at he
      omega
    have hy2 : 2 ≤ y := by
      by_cases hh : 2 ≤ y
      · exact hh
      have hy1 : y = 1 := by omega
      subst y
      simp at he
      omega
    have hz2 : 2 ≤ z := by omega
    have hC : 4 < triangleMarkov x y z := by
      apply Int.lt_of_not_ge
      intro hh
      exact h ⟨hx2,hy2,hz2,by omega⟩
    have hdes : x*y < 2*z := by
      cases Int.le_total x y with
      | inl hxy => exact triangle_sorted_descent x y z hx2 hxy hyz hC
      | inr hyx =>
        have hs := triangle_sorted_descent y x z hy2 hyx hxz
          (by rw [triangleMarkov_swap]; exact hC)
        grind
    refine Or.inr ⟨by omega, by omega, ?_⟩
    intro hh
    have hhC := hh.2.2.2
    rw [triangleMarkov_mutation] at hhC
    omega

theorem cycleThree_acyclic_z_nonpos (x y z : Int) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hz : z ≤ 0) : Acyclic (cycleThree x y z) := by
  refine ⟨fun i => i.val, ?_⟩
  intro i j
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hi with rfl|rfl|rfl <;> rcases hj with rfl|rfl|rfl <;> simp [cycleThree] <;> omega

theorem cycleThree_acyclic_y_nonpos (x y z : Int) (hx : 0 ≤ x) (hy : y ≤ 0)
    (hz : 0 ≤ z) : Acyclic (cycleThree x y z) := by
  refine ⟨fun i => match i.val with | 2 => 0 | 0 => 1 | _ => 2, ?_⟩
  intro i j
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hi with rfl|rfl|rfl <;> rcases hj with rfl|rfl|rfl <;> simp [cycleThree] <;> omega

theorem cycleThree_acyclic_x_nonpos (x y z : Int) (hx : x ≤ 0) (hy : 0 ≤ y)
    (hz : 0 ≤ z) : Acyclic (cycleThree x y z) := by
  refine ⟨fun i => match i.val with | 1 => 0 | 2 => 1 | _ => 2, ?_⟩
  intro i j
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hi with rfl|rfl|rfl <;> rcases hj with rfl|rfl|rfl <;> simp [cycleThree] <;> omega

/-- Constructive strong induction: every positive cyclic triangle outside the
invariant region has an actual finite word ending at an acyclic matrix. -/
theorem rankThree_cycle_MA_of_not_region (x y z : Int)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : ¬ TriangleRegion x y z) :
    MutationAcyclic (cycleThree x y z) := by
  generalize hm : (x+y+z).toNat = m
  induction m using Nat.strongRecOn generalizing x y z with
  | ind m ih =>
    by_cases hzm : x ≤ z ∧ y ≤ z
    · have hd := triangle_largest_descent x y z hx hy hz hzm.1 hzm.2 h
      apply (mutationAcyclic_iff _ 1).mp
      rw [cycleThree_mutate_one x y z (by omega) (by omega)]
      apply mutationAcyclic_reverse_three _ (cycleThree_skew _ _ _)
      rcases hd with he|⟨ht,hlt,hr⟩
      · exact acyclic_is_mutationAcyclic _ (cycleThree_acyclic_z_nonpos x y (x*y-z) (by omega) (by omega) (by omega))
      · apply ih (x+y+(x*y-z)).toNat (by omega) x y (x*y-z) hx hy ht hr rfl
    · by_cases hym : x ≤ y ∧ z ≤ y
      · have hr : ¬ TriangleRegion z x y := by
          intro hh
          exact h (triangleRegion_rotate z x y hh)
        have hd := triangle_largest_descent z x y hz hx hy hym.2 hym.1 hr
        have he : z*x-y = x*z-y := by grind
        apply (mutationAcyclic_iff _ 0).mp
        rw [cycleThree_mutate_zero x y z (by omega) (by omega)]
        apply mutationAcyclic_reverse_three _ (cycleThree_skew _ _ _)
        rcases hd with hh|⟨ht,hlt,hreg⟩
        · exact acyclic_is_mutationAcyclic _ (cycleThree_acyclic_y_nonpos x (x*z-y) z (by omega) (by grind) (by omega))
        · have hnr : ¬ TriangleRegion x (x*z-y) z := by
            intro hh
            apply hreg
            have hh' := triangleRegion_rotate (x*z-y) z x (triangleRegion_rotate x (x*z-y) z hh)
            rwa [he]
          apply ih (x+(x*z-y)+z).toNat (by omega) x (x*z-y) z hx (by omega) hz hnr rfl
      · have hxmax : y ≤ x ∧ z ≤ x := by omega
        have hr : ¬ TriangleRegion y z x := by
          intro hh
          exact h (triangleRegion_rotate z x y (triangleRegion_rotate y z x hh))
        have hd := triangle_largest_descent y z x hy hz hx hxmax.1 hxmax.2 hr
        apply (mutationAcyclic_iff _ 2).mp
        rw [cycleThree_mutate_two x y z (by omega) (by omega)]
        apply mutationAcyclic_reverse_three _ (cycleThree_skew _ _ _)
        rcases hd with hh|⟨ht,hlt,hreg⟩
        · exact acyclic_is_mutationAcyclic _ (cycleThree_acyclic_x_nonpos (y*z-x) y z (by omega) (by omega) (by omega))
        · have hnr : ¬ TriangleRegion (y*z-x) y z := by
            intro hh
            exact hreg (triangleRegion_rotate (y*z-x) y z hh)
          apply ih ((y*z-x)+y+z).toNat (by omega) (y*z-x) y z ht hy hz hnr rfl

/-- Complete semantic rank-three classification, including both implications. -/
theorem rankThree_cycle_NMA_iff (x y z : Int) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    ¬ MutationAcyclic (cycleThree x y z) ↔ TriangleRegion x y z := by
  constructor
  · intro hn
    by_cases hr : TriangleRegion x y z
    · exact hr
    · exact False.elim (hn (rankThree_cycle_MA_of_not_region x y z hx hy hz hr))
  · intro hr
    exact rankThree_cycle_NMA x y z hr.1 hr.2.1 hr.2.2.1 hr.2.2.2


/-- Embed a triangle as the first three vertices and add an isolated vertex. -/
def extendThree (B : Matrix 3) : Matrix 4 := fun i j =>
  match i.val, j.val with
  | 0,0 => B 0 0 | 0,1 => B 0 1 | 0,2 => B 0 2
  | 1,0 => B 1 0 | 1,1 => B 1 1 | 1,2 => B 1 2
  | 2,0 => B 2 0 | 2,1 => B 2 1 | 2,2 => B 2 2
  | _,_ => 0

theorem extendThree_mutate_zero (B : Matrix 3) :
    mutate (extendThree B) 0 = extendThree (mutate B 0) := by
  funext i j
  have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  have hj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
  rcases hi with rfl|rfl|rfl|rfl <;> rcases hj with rfl|rfl|rfl|rfl <;>
    simp [mutate, extendThree, correction]

theorem extendThree_mutate_one (B : Matrix 3) :
    mutate (extendThree B) 1 = extendThree (mutate B 1) := by
  funext i j
  have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  have hj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
  rcases hi with rfl|rfl|rfl|rfl <;> rcases hj with rfl|rfl|rfl|rfl <;>
    simp [mutate, extendThree, correction]

theorem extendThree_mutate_two (B : Matrix 3) :
    mutate (extendThree B) 2 = extendThree (mutate B 2) := by
  funext i j
  have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  have hj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
  rcases hi with rfl|rfl|rfl|rfl <;> rcases hj with rfl|rfl|rfl|rfl <;>
    simp [mutate, extendThree, correction]

theorem extendThree_mutate_isolated (B : Matrix 3) :
    mutate (extendThree B) 3 = extendThree B := by
  funext i j
  have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  have hj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
  rcases hi with rfl|rfl|rfl|rfl <;> rcases hj with rfl|rfl|rfl|rfl <;>
    simp [mutate, extendThree, correction]

def restrictThreeVertex (k : Fin 4) : Option (Fin 3) :=
  match k.val with | 0 => some 0 | 1 => some 1 | 2 => some 2 | _ => none

theorem extendThree_applyWord (B : Matrix 3) (word : List (Fin 4)) :
    applyWord (extendThree B) word =
      extendThree (applyWord B (word.filterMap restrictThreeVertex)) := by
  induction word generalizing B with
  | nil => rfl
  | cons k ks ih =>
    have hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases hk with rfl|rfl|rfl|rfl <;>
      simp only [applyWord, List.filterMap_cons, restrictThreeVertex,
        extendThree_mutate_zero, extendThree_mutate_one,
        extendThree_mutate_two, extendThree_mutate_isolated] <;>
      exact ih _

theorem extendThree_acyclic_restrict (B : Matrix 3) (h : Acyclic (extendThree B)) :
    Acyclic B := by
  rcases h with ⟨rank,hr⟩
  refine ⟨fun i => match i.val with | 0 => rank 0 | 1 => rank 1 | _ => rank 2, ?_⟩
  intro i j hij
  have hi : i=0 ∨ i=1 ∨ i=2 := by omega
  have hj : j=0 ∨ j=1 ∨ j=2 := by omega
  rcases hi with rfl|rfl|rfl <;> rcases hj with rfl|rfl|rfl
  all_goals first
    | exact hr 0 0 hij
    | exact hr 0 1 hij
    | exact hr 0 2 hij
    | exact hr 1 0 hij
    | exact hr 1 1 hij
    | exact hr 1 2 hij
    | exact hr 2 0 hij
    | exact hr 2 1 hij
    | exact hr 2 2 hij

/-- Isolated vertices may be mutated arbitrarily without changing the triangle. -/
theorem extendThree_NMA (B : Matrix 3) (h : ¬ MutationAcyclic B) :
    ¬ MutationAcyclic (extendThree B) := by
  rintro ⟨word,ha⟩
  rw [extendThree_applyWord] at ha
  exact h ⟨word.filterMap restrictThreeVertex, extendThree_acyclic_restrict _ ha⟩

theorem extendThree_cycle (x y z : Int) :
    extendThree (cycleThree x y z) = ofSix x (-z) 0 y 0 0 := by
  funext i j
  have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  have hj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
  rcases hi with rfl|rfl|rfl|rfl <;> rcases hj with rfl|rfl|rfl|rfl <;>
    simp [extendThree, cycleThree, ofSix]

theorem extendThree_reverse_cycle (x y z : Int) :
    extendThree (reverseMatrix (cycleThree x y z)) = ofSix (-x) z 0 (-y) 0 0 := by
  funext i j
  have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  have hj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
  rcases hi with rfl|rfl|rfl|rfl <;> rcases hj with rfl|rfl|rfl|rfl <;>
    simp [extendThree, cycleThree, reverseMatrix, ofSix]

theorem isolated_triangle_NMA (x y z : Int) (hx : 2 ≤ x) (hy : 2 ≤ y) (hz : 2 ≤ z)
    (hC : triangleMarkov x y z ≤ 4) : ¬ MutationAcyclic (ofSix x (-z) 0 y 0 0) := by
  rw [← extendThree_cycle]
  exact extendThree_NMA _ (rankThree_cycle_NMA x y z hx hy hz hC)

theorem isolated_reverse_triangle_NMA (x y z : Int) (hx : 2 ≤ x) (hy : 2 ≤ y) (hz : 2 ≤ z)
    (hC : triangleMarkov x y z ≤ 4) : ¬ MutationAcyclic (ofSix (-x) z 0 (-y) 0 0) := by
  rw [← extendThree_reverse_cycle]
  exact extendThree_NMA _ (rankThree_reverse_cycle_NMA x y z hx hy hz hC)


private theorem triangle_bounded_step (B : Matrix 3) (k : Fin 3) (budget : Int)
    (h : ∃ word : List (Fin 3), (word.length : Int) < budget ∧ Acyclic (applyWord (mutate B k) word)) :
    ∃ word : List (Fin 3), (word.length : Int) ≤ budget ∧ Acyclic (applyWord B word) := by
  rcases h with ⟨word,hlen,ha⟩
  refine ⟨k::word,?_,ha⟩
  simp only [List.length_cons, Int.natCast_add, Int.natCast_one]
  omega

private theorem triangle_bounded_reverse (B : Matrix 3) (hB : SkewSymmetric B) (budget : Int)
    (h : ∃ word : List (Fin 3), (word.length : Int) < budget ∧ Acyclic (applyWord B word)) :
    ∃ word : List (Fin 3), (word.length : Int) < budget ∧ Acyclic (applyWord (reverseMatrix B) word) := by
  rcases h with ⟨word,hlen,ha⟩
  refine ⟨word,hlen,?_⟩
  rw [applyWord_reverseMatrix]
  exact acyclic_reverse_three _ (rankThree_word_skew B hB word) ha

/-- The manuscript's precise mutation-count bound S−2, proved for every
positive integer cyclic triangle outside the invariant region. -/
theorem rankThree_cycle_bounded_MA (x y z : Int)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : ¬ TriangleRegion x y z) :
    ∃ word : List (Fin 3), (word.length : Int) ≤ x+y+z-2 ∧
      Acyclic (applyWord (cycleThree x y z) word) := by
  generalize hm : (x+y+z).toNat = m
  induction m using Nat.strongRecOn generalizing x y z with
  | ind m ih =>
    by_cases hzm : x ≤ z ∧ y ≤ z
    · have hd := triangle_largest_descent x y z hx hy hz hzm.1 hzm.2 h
      apply triangle_bounded_step _ 1
      rw [cycleThree_mutate_one x y z (by omega) (by omega)]
      apply triangle_bounded_reverse _ (cycleThree_skew _ _ _)
      rcases hd with he|⟨ht,hlt,hr⟩
      · exact ⟨[],by simp; omega, cycleThree_acyclic_z_nonpos x y (x*y-z) (by omega) (by omega) (by omega)⟩
      · rcases ih (x+y+(x*y-z)).toNat (by omega) x y (x*y-z) hx hy ht hr rfl with ⟨word,hlen,ha⟩
        exact ⟨word,by omega,ha⟩
    · by_cases hym : x ≤ y ∧ z ≤ y
      · have hr : ¬ TriangleRegion z x y := by
          intro hh
          exact h (triangleRegion_rotate z x y hh)
        have hd := triangle_largest_descent z x y hz hx hy hym.2 hym.1 hr
        have he : z*x-y = x*z-y := by grind
        apply triangle_bounded_step _ 0
        rw [cycleThree_mutate_zero x y z (by omega) (by omega)]
        apply triangle_bounded_reverse _ (cycleThree_skew _ _ _)
        rcases hd with hh|⟨ht,hlt,hreg⟩
        · exact ⟨[],by simp; omega,cycleThree_acyclic_y_nonpos x (x*z-y) z (by omega) (by grind) (by omega)⟩
        · have hnr : ¬ TriangleRegion x (x*z-y) z := by
            intro hh
            apply hreg
            have hh' := triangleRegion_rotate (x*z-y) z x (triangleRegion_rotate x (x*z-y) z hh)
            rwa [he]
          rcases ih (x+(x*z-y)+z).toNat (by omega) x (x*z-y) z hx (by omega) hz hnr rfl with ⟨word,hlen,ha⟩
          exact ⟨word,by omega,ha⟩
      · have hxmax : y ≤ x ∧ z ≤ x := by omega
        have hr : ¬ TriangleRegion y z x := by
          intro hh
          exact h (triangleRegion_rotate z x y (triangleRegion_rotate y z x hh))
        have hd := triangle_largest_descent y z x hy hz hx hxmax.1 hxmax.2 hr
        apply triangle_bounded_step _ 2
        rw [cycleThree_mutate_two x y z (by omega) (by omega)]
        apply triangle_bounded_reverse _ (cycleThree_skew _ _ _)
        rcases hd with hh|⟨ht,hlt,hreg⟩
        · exact ⟨[],by simp; omega,cycleThree_acyclic_x_nonpos (y*z-x) y z (by omega) (by omega) (by omega)⟩
        · have hnr : ¬ TriangleRegion (y*z-x) y z := by
            intro hh
            exact hreg (triangleRegion_rotate (y*z-x) y z hh)
          rcases ih ((y*z-x)+y+z).toNat (by omega) (y*z-x) y z ht hy hz hnr rfl with ⟨word,hlen,ha⟩
          exact ⟨word,by omega,ha⟩


theorem rankThree_reverse_cycle_NMA_iff (x y z : Int) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    ¬ MutationAcyclic (reverseMatrix (cycleThree x y z)) ↔ TriangleRegion x y z := by
  constructor
  · intro hn
    by_cases hr : TriangleRegion x y z
    · exact hr
    · exact False.elim (hn (mutationAcyclic_reverse_three _ (cycleThree_skew x y z)
        (rankThree_cycle_MA_of_not_region x y z hx hy hz hr)))
  · intro hr
    exact rankThree_reverse_cycle_NMA x y z hr.1 hr.2.1 hr.2.2.1 hr.2.2.2

theorem rankThree_reverse_cycle_bounded_MA (x y z : Int)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : ¬ TriangleRegion x y z) :
    ∃ word : List (Fin 3), (word.length : Int) ≤ x+y+z-2 ∧
      Acyclic (applyWord (reverseMatrix (cycleThree x y z)) word) := by
  rcases rankThree_cycle_bounded_MA x y z hx hy hz h with ⟨word,hlen,ha⟩
  refine ⟨word,hlen,?_⟩
  rw [applyWord_reverseMatrix]
  exact acyclic_reverse_three _ (rankThree_word_skew _ (cycleThree_skew x y z) word) ha

def liftThreeVertex (k : Fin 3) : Fin 4 := ⟨k.val, by omega⟩

theorem extendThree_mutate_lift (B : Matrix 3) (k : Fin 3) :
    mutate (extendThree B) (liftThreeVertex k) = extendThree (mutate B k) := by
  have hk : k=0 ∨ k=1 ∨ k=2 := by omega
  rcases hk with rfl|rfl|rfl
  · exact extendThree_mutate_zero B
  · exact extendThree_mutate_one B
  · exact extendThree_mutate_two B

theorem extendThree_applyWord_lift (B : Matrix 3) (word : List (Fin 3)) :
    applyWord (extendThree B) (word.map liftThreeVertex) = extendThree (applyWord B word) := by
  induction word generalizing B with
  | nil => rfl
  | cons k ks ih => simp only [List.map_cons,applyWord,extendThree_mutate_lift,ih]

theorem extendThree_acyclic (B : Matrix 3) (h : Acyclic B) : Acyclic (extendThree B) := by
  rcases h with ⟨rank,hr⟩
  refine ⟨fun i => match i.val with | 0 => rank 0 | 1 => rank 1 | 2 => rank 2 | _ => 0, ?_⟩
  intro i j hij
  have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  have hj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
  rcases hi with rfl|rfl|rfl|rfl <;> rcases hj with rfl|rfl|rfl|rfl
  all_goals first
    | exact hr 0 0 hij
    | exact hr 0 1 hij
    | exact hr 0 2 hij
    | exact hr 1 0 hij
    | exact hr 1 1 hij
    | exact hr 1 2 hij
    | exact hr 2 0 hij
    | exact hr 2 1 hij
    | exact hr 2 2 hij
    | exact False.elim (by simp [extendThree] at hij)

theorem extendThree_MA_iff (B : Matrix 3) :
    MutationAcyclic (extendThree B) ↔ MutationAcyclic B := by
  constructor
  · rintro ⟨word,ha⟩
    rw [extendThree_applyWord] at ha
    exact ⟨word.filterMap restrictThreeVertex, extendThree_acyclic_restrict _ ha⟩
  · rintro ⟨word,ha⟩
    refine ⟨word.map liftThreeVertex,?_⟩
    rw [extendThree_applyWord_lift]
    exact extendThree_acyclic _ ha

/-- Complete disconnected cyclic-component criterion on the actual rank-four matrix. -/
theorem isolated_triangle_NMA_iff (x y z : Int) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    ¬ MutationAcyclic (ofSix x (-z) 0 y 0 0) ↔ TriangleRegion x y z := by
  rw [← extendThree_cycle,extendThree_MA_iff]
  exact rankThree_cycle_NMA_iff x y z hx hy hz

theorem isolated_reverse_triangle_NMA_iff (x y z : Int) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    ¬ MutationAcyclic (ofSix (-x) z 0 (-y) 0 0) ↔ TriangleRegion x y z := by
  rw [← extendThree_reverse_cycle,extendThree_MA_iff]
  exact rankThree_reverse_cycle_NMA_iff x y z hx hy hz

theorem isolated_triangle_bounded_MA (x y z : Int)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : ¬ TriangleRegion x y z) :
    ∃ word : List (Fin 4), (word.length : Int) ≤ x+y+z-2 ∧
      Acyclic (applyWord (ofSix x (-z) 0 y 0 0) word) := by
  rcases rankThree_cycle_bounded_MA x y z hx hy hz h with ⟨word,hlen,ha⟩
  refine ⟨word.map liftThreeVertex,by simpa using hlen,?_⟩
  rw [← extendThree_cycle,extendThree_applyWord_lift]
  exact extendThree_acyclic _ ha

theorem isolated_reverse_triangle_bounded_MA (x y z : Int)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : ¬ TriangleRegion x y z) :
    ∃ word : List (Fin 4), (word.length : Int) ≤ x+y+z-2 ∧
      Acyclic (applyWord (ofSix (-x) z 0 (-y) 0 0) word) := by
  rcases rankThree_reverse_cycle_bounded_MA x y z hx hy hz h with ⟨word,hlen,ha⟩
  refine ⟨word.map liftThreeVertex,by simpa using hlen,?_⟩
  rw [← extendThree_reverse_cycle,extendThree_applyWord_lift]
  exact extendThree_acyclic _ ha

end QuiverProofs
