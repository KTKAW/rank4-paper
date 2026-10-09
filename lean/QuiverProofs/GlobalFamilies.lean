import QuiverProofs.Box
import QuiverProofs.ResidualFamily
import QuiverProofs.TriangleRegions

/-! Global triangle avoidance for the two unbounded parameter families. -/
namespace QuiverProofs.GlobalFamilies
open TriangleRegions

private theorem fin3 (i : Fin 3) : i=0 ∨ i=1 ∨ i=2 := by omega

private theorem cycleThree_negate (x y z : Int) :
    reverse (cycleThree (-x) (-y) (-z)) = cycleThree x y z := by
  funext i j
  rcases fin3 i with rfl | rfl | rfl <;> rcases fin3 j with rfl | rfl | rfl <;>
    simp [reverse,cycleThree]

private theorem MA_negate (x y z : Int)
    (h : MutationAcyclic (cycleThree (-x) (-y) (-z))) :
    MutationAcyclic (cycleThree x y z) := by
  rw [←cycleThree_negate]
  exact (MA_reverse_iff _ (cycleThree_skew _ _ _)).mpr h

private theorem nonnegative_weak_triangle_MA (x y z : Int)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hw : x≤1 ∨ y≤1 ∨ z≤1) : MutationAcyclic (cycleThree x y z) := by
  by_cases h0 : x=0
  · exact acyclic_is_mutationAcyclic _ (cycleThree_acyclic_x_nonpos x y z (by omega) hy hz)
  by_cases h1 : y=0
  · exact acyclic_is_mutationAcyclic _ (cycleThree_acyclic_y_nonpos x y z hx (by omega) hz)
  by_cases h2 : z=0
  · exact acyclic_is_mutationAcyclic _ (cycleThree_acyclic_z_nonpos x y z hx hy (by omega))
  apply rankThree_cycle_MA_of_not_region x y z (by omega) (by omega) (by omega)
  intro hr
  obtain ⟨hxx,hyy,hzz,_⟩ := hr
  omega

/-- Any oriented triangle with a zero or unit edge is mutation-acyclic.
This is semantic MA, including every choice of signs for the other edges. -/
theorem weak_triangle_MA (x y z : Int)
    (hw : (-1≤x ∧ x≤1) ∨ (-1≤y ∧ y≤1) ∨ (-1≤z ∧ z≤1)) :
    MutationAcyclic (cycleThree x y z) := by
  rcases Int.le_total 0 x with hx | hx <;>
    rcases Int.le_total 0 y with hy | hy <;>
    rcases Int.le_total 0 z with hz | hz
  · exact nonnegative_weak_triangle_MA x y z hx hy hz (by omega)
  · exact acyclic_is_mutationAcyclic _ (cycleThree_acyclic_z_nonpos x y z hx hy hz)
  · exact acyclic_is_mutationAcyclic _ (cycleThree_acyclic_y_nonpos x y z hx hy hz)
  · apply MA_negate
    exact acyclic_is_mutationAcyclic _ (cycleThree_acyclic_x_nonpos (-x) (-y) (-z)
      (by omega) (by omega) (by omega))
  · exact acyclic_is_mutationAcyclic _ (cycleThree_acyclic_x_nonpos x y z hx hy hz)
  · apply MA_negate
    exact acyclic_is_mutationAcyclic _ (cycleThree_acyclic_y_nonpos (-x) (-y) (-z)
      (by omega) (by omega) (by omega))
  · apply MA_negate
    exact acyclic_is_mutationAcyclic _ (cycleThree_acyclic_z_nonpos (-x) (-y) (-z)
      (by omega) (by omega) (by omega))
  · apply MA_negate
    exact nonnegative_weak_triangle_MA (-x) (-y) (-z)
      (by omega) (by omega) (by omega) (by omega)

private theorem positive_markov_triangle_MA (x y z : Int)
    (hx : 0<x) (hy : 0<y) (hz : 0<z) (hC : 4 < triangleMarkov x y z) :
    MutationAcyclic (cycleThree x y z) := by
  apply rankThree_cycle_MA_of_not_region x y z hx hy hz
  intro h
  have := h.2.2.2
  omega

theorem box_core_triangles (a b : Int) (ha : 2≤a) (hb : 2≤b) (i : Fin 2) :
    AllTrianglesMA (Box.node a b i) := by
  have hprod := Int.mul_pos (show 0<a by omega) (show 0<b by omega)
  have hasq := Algebra.square_monotone 2 a (by decide) ha
  have hbsq := Algebra.square_monotone 2 b (by decide) hb
  have hi : i=0 ∨ i=1 := by omega
  rcases hi with rfl | rfl
  · change AllTrianglesMA (ofSix a 0 (-b) b 0 a)
    apply ofSix_allTrianglesMA <;> apply weak_triangle_MA <;> omega
  · change AllTrianglesMA (ofSix (-a) 0 b b (-a*b) a)
    apply ofSix_allTrianglesMA
    · apply positive_markov_triangle_MA _ _ _ (by omega) (by omega) (by grind)
      unfold triangleMarkov
      grind
    · apply weak_triangle_MA; omega
    · apply MA_negate
      apply positive_markov_triangle_MA _ _ _ (by omega) (by grind) (by omega)
      unfold triangleMarkov
      grind
    · apply weak_triangle_MA; omega

theorem residual_core_triangles (a b c : Int) (i : Fin 14) :
    AllTrianglesMA (ResidualFamily.node a b c i) := by
  have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨
    i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 := by omega
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [ResidualFamily.node]
  all_goals apply ofSix_allTrianglesMA <;> apply weak_triangle_MA <;> omega


/-- All alternating boxes avoid non-MA triangles after every mutation word. -/
theorem box_global_triangle_avoidance (a b : Int) (ha : 2≤a) (hb : 2≤b)
    (word : List (Fin 4)) : AllTrianglesMA (applyWord (Box.box a b) word) := by
  apply framed_region_all_triangles_MA (Box.node a b) ?_
    (box_core_triangles a b ha hb) (Box.core_edges a b ha hb) 0 word
  intro i
  have hi : i=0 ∨ i=1 := by omega
  rcases hi with rfl | rfl <;> exact ofSix_skew _ _ _ _ _ _

theorem residual_core_global_triangles (a b c : Int) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c)
    (i : Fin 14) (word : List (Fin 4)) :
    AllTrianglesMA (applyWord (ResidualFamily.node a b c i) word) :=
  framed_region_all_triangles_MA (ResidualFamily.node a b c)
    (ResidualFamily.all_skew a b c) (residual_core_triangles a b c)
    (ResidualFamily.all_edges a b c ha hb hc) i word

private theorem global_triangles_of_relabel (Q : Matrix 4) (p : Relabeling 4)
    (h : ∀ word, AllTrianglesMA (applyWord (relabel Q p) word)) (word : List (Fin 4)) :
    AllTrianglesMA (applyWord Q word) := by
  have hh := h (word.map p.invFun)
  have hmap : (word.map p.invFun).map p.toFun=word := by
    clear hh
    induction word with
    | nil => rfl
    | cons k ks ih => simp only [List.map_cons,p.right_inv,ih]
  rw [word_relabel,hmap] at hh
  exact (triangles_relabel_iff _ p).mp hh

/-- The entire three-parameter residual family is globally triangle-avoiding,
for every a,b,c ≥ 2 and every finite mutation word. -/
theorem residual_global_triangle_avoidance (a b c : Int)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (word : List (Fin 4)) :
    AllTrianglesMA (applyWord (ofSix (-a) (-b) (-c) (-1) 1 (-1)) word) := by
  apply global_triangles_of_relabel _ ResidualFamily.perm5 ?_ word
  have he : relabel (ofSix (-a) (-b) (-c) (-1) 1 (-1)) ResidualFamily.perm5 =
      ResidualFamily.node a b c 0 := by
    funext i j
    have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
    have hj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
    rcases hi with rfl | rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl | rfl <;>
      simp [relabel,ResidualFamily.perm5,ResidualFamily.node,ofSix]
  intro w
  rw [he]
  exact residual_core_global_triangles a b c ha hb hc 0 w

theorem residual_diagonal_global_triangle_avoidance (t : Int) (ht : 2≤t)
    (word : List (Fin 4)) :
    AllTrianglesMA (applyWord (ofSix (-t) (-t) (-t) (-1) 1 (-1)) word) :=
  residual_global_triangle_avoidance t t t ht ht ht word

end QuiverProofs.GlobalFamilies
