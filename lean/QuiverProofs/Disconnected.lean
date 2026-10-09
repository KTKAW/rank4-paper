import QuiverProofs.RankThree
import QuiverProofs.Symmetry

namespace QuiverProofs

/-- A genuine nontrivial support partition; all cross-block entries vanish. -/
def DisconnectedSupport (B : Matrix 4) : Prop :=
  ∃ side : Fin 4 → Bool, (∃ i, side i = true) ∧ (∃ j, side j = false) ∧
    ∀ i j, side i ≠ side j → B i j = 0

/-- All possible nontrivial cuts of a four-vertex support, modulo complement. -/
def DisconnectedCut (B : Matrix 4) : Prop :=
  (B 0 1=0 ∧ B 0 2=0 ∧ B 0 3=0) ∨
  (B 0 1=0 ∧ B 1 2=0 ∧ B 1 3=0) ∨
  (B 0 2=0 ∧ B 1 2=0 ∧ B 2 3=0) ∨
  (B 0 3=0 ∧ B 1 3=0 ∧ B 2 3=0) ∨
  (B 0 2=0 ∧ B 0 3=0 ∧ B 1 2=0 ∧ B 1 3=0) ∨
  (B 0 1=0 ∧ B 0 3=0 ∧ B 1 2=0 ∧ B 2 3=0) ∨
  (B 0 1=0 ∧ B 0 2=0 ∧ B 1 3=0 ∧ B 2 3=0)

theorem disconnected_support_cut (B : Matrix 4) (h : DisconnectedSupport B) :
    DisconnectedCut B := by
  rcases h with ⟨side,⟨i,hi⟩,⟨j,hj⟩,cross⟩
  have h01 := cross 0 1
  have h02 := cross 0 2
  have h03 := cross 0 3
  have h12 := cross 1 2
  have h13 := cross 1 3
  have h23 := cross 2 3
  have he : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  have hf : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
  cases h0 : side 0 <;> cases h1 : side 1 <;> cases h2 : side 2 <;> cases h3 : side 3
  all_goals simp_all [DisconnectedCut]
  all_goals grind

/-- Cyclic signed weights in either orientation. -/
def SignedTriangleRegion (x y z : Int) : Prop :=
  TriangleRegion x y z ∨ TriangleRegion (-x) (-y) (-z)

theorem cycleThree_neg (x y z : Int) :
    cycleThree (-x) (-y) (-z) = reverseMatrix (cycleThree x y z) := by
  funext i j
  have hi : i=0 ∨ i=1 ∨ i=2 := by omega
  have hj : j=0 ∨ j=1 ∨ j=2 := by omega
  rcases hi with rfl|rfl|rfl <;> rcases hj with rfl|rfl|rfl <;>
    simp [cycleThree,reverseMatrix]

theorem cycleThree_mixed_acyclic (x y z : Int)
    (hp : ¬ (0<x ∧ 0<y ∧ 0<z)) (hn : ¬ (x<0 ∧ y<0 ∧ z<0)) :
    Acyclic (cycleThree x y z) := by
  have signs (a : Int) : a<0 ∨ a=0 ∨ 0<a := by omega
  rcases signs x with hx|rfl|hx <;> rcases signs y with hy|rfl|hy <;> rcases signs z with hz|rfl|hz
  all_goals first
    | exact False.elim (hp ⟨by omega,by omega,by omega⟩)
    | exact False.elim (hn ⟨by omega,by omega,by omega⟩)
    | exact cycleThree_acyclic_x_nonpos _ _ _ (by omega) (by omega) (by omega)
    | exact cycleThree_acyclic_y_nonpos _ _ _ (by omega) (by omega) (by omega)
    | exact cycleThree_acyclic_z_nonpos _ _ _ (by omega) (by omega) (by omega)
    | apply (acyclic_reverse_iff _ (cycleThree_skew _ _ _)).mp
      change Acyclic (reverseMatrix (cycleThree _ _ _))
      rw [← cycleThree_neg]
      first
        | exact cycleThree_acyclic_x_nonpos _ _ _ (by omega) (by omega) (by omega)
        | exact cycleThree_acyclic_y_nonpos _ _ _ (by omega) (by omega) (by omega)
        | exact cycleThree_acyclic_z_nonpos _ _ _ (by omega) (by omega) (by omega)

theorem signed_triangle_NMA_iff (x y z : Int) :
    ¬ MutationAcyclic (cycleThree x y z) ↔ SignedTriangleRegion x y z := by
  by_cases hp : 0<x ∧ 0<y ∧ 0<z
  · have hn : ¬ TriangleRegion (-x) (-y) (-z) := by intro h; have := h.1; omega
    simpa [SignedTriangleRegion,hn] using rankThree_cycle_NMA_iff x y z hp.1 hp.2.1 hp.2.2
  · by_cases hn : x<0 ∧ y<0 ∧ z<0
    · have hpos : ¬ TriangleRegion x y z := by intro h; have := h.1; omega
      have hrev : cycleThree x y z = reverseMatrix (cycleThree (-x) (-y) (-z)) := by
        rw [cycleThree_neg,reverseMatrix_involutive]
      rw [hrev]
      simpa [SignedTriangleRegion,hpos] using
        rankThree_reverse_cycle_NMA_iff (-x) (-y) (-z) (by omega) (by omega) (by omega)
    · have ha := acyclic_is_mutationAcyclic _ (cycleThree_mixed_acyclic x y z hp hn)
      have hp' : ¬ TriangleRegion x y z := by
        intro h
        exact hp ⟨by have := h.1; omega,by have := h.2.1; omega,by have := h.2.2.1; omega⟩
      have hn' : ¬ TriangleRegion (-x) (-y) (-z) := by
        intro h
        exact hn ⟨by have := h.1; omega,by have := h.2.1; omega,by have := h.2.2.1; omega⟩
      simp [SignedTriangleRegion,hp',hn',ha]


def moveIsolatedZero : Relabeling 4 where
  toFun i := match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | _ => 0
  invFun i := match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | _ => 2
  left_inv := by decide
  right_inv := by decide

def moveIsolatedOne : Relabeling 4 where
  toFun i := match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | _ => 1
  invFun i := match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | _ => 2
  left_inv := by decide
  right_inv := by decide

def moveIsolatedTwo : Relabeling 4 where
  toFun i := match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | _ => 2
  invFun i := match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | _ => 2
  left_inv := by decide
  right_inv := by decide

theorem isolate_zero_normalization (d e f : Int) :
    relabel (ofSix 0 0 0 d e f) moveIsolatedZero = ofSix d e 0 f 0 0 := by
  funext i j
  have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  have hj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
  rcases hi with rfl|rfl|rfl|rfl <;> rcases hj with rfl|rfl|rfl|rfl <;>
    simp [relabel,moveIsolatedZero,ofSix]

theorem isolate_one_normalization (b c f : Int) :
    relabel (ofSix 0 b c 0 0 f) moveIsolatedOne = ofSix b c 0 f 0 0 := by
  funext i j
  have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  have hj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
  rcases hi with rfl|rfl|rfl|rfl <;> rcases hj with rfl|rfl|rfl|rfl <;>
    simp [relabel,moveIsolatedOne,ofSix]

theorem isolate_two_normalization (a c e : Int) :
    relabel (ofSix a 0 c 0 e 0) moveIsolatedTwo = ofSix a c 0 e 0 0 := by
  funext i j
  have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  have hj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
  rcases hi with rfl|rfl|rfl|rfl <;> rcases hj with rfl|rfl|rfl|rfl <;>
    simp [relabel,moveIsolatedTwo,ofSix]

theorem signed_isolated_triangle_NMA_iff (a b d : Int) :
    ¬ MutationAcyclic (ofSix a b 0 d 0 0) ↔ SignedTriangleRegion a d (-b) := by
  have he : ofSix a b 0 d 0 0 = extendThree (cycleThree a d (-b)) := by
    rw [extendThree_cycle,Int.neg_neg]
  rw [he,extendThree_MA_iff]
  exact signed_triangle_NMA_iff a d (-b)

/-- Disconnected 2+2 components are acyclic for arbitrary signed weights. -/
theorem two_pairs_01_23_acyclic (a f : Int) : Acyclic (ofSix a 0 0 0 0 f) := by
  refine ⟨fun i => match i.val with
    | 0 => if 0<a then 0 else 1 | 1 => if 0<a then 1 else 0
    | 2 => if 0<f then 0 else 1 | _ => if 0<f then 1 else 0, ?_⟩
  intro i j
  have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  have hj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
  rcases hi with rfl|rfl|rfl|rfl <;> rcases hj with rfl|rfl|rfl|rfl <;>
    simp [ofSix] <;> split <;> omega

theorem two_pairs_02_13_acyclic (b e : Int) : Acyclic (ofSix 0 b 0 0 e 0) := by
  refine ⟨fun i => match i.val with
    | 0 => if 0<b then 0 else 1 | 2 => if 0<b then 1 else 0
    | 1 => if 0<e then 0 else 1 | _ => if 0<e then 1 else 0, ?_⟩
  intro i j
  have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  have hj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
  rcases hi with rfl|rfl|rfl|rfl <;> rcases hj with rfl|rfl|rfl|rfl <;>
    simp [ofSix] <;> split <;> omega

theorem two_pairs_03_12_acyclic (c d : Int) : Acyclic (ofSix 0 0 c d 0 0) := by
  refine ⟨fun i => match i.val with
    | 0 => if 0<c then 0 else 1 | 3 => if 0<c then 1 else 0
    | 1 => if 0<d then 0 else 1 | _ => if 0<d then 1 else 0, ?_⟩
  intro i j
  have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  have hj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
  rcases hi with rfl|rfl|rfl|rfl <;> rcases hj with rfl|rfl|rfl|rfl <;>
    simp [ofSix] <;> split <;> omega

@[simp] theorem signedTriangleRegion_zero_left (y z : Int) : ¬ SignedTriangleRegion 0 y z := by
  simp [SignedTriangleRegion,TriangleRegion]

@[simp] theorem signedTriangleRegion_zero_middle (x z : Int) : ¬ SignedTriangleRegion x 0 z := by
  simp [SignedTriangleRegion,TriangleRegion]

@[simp] theorem signedTriangleRegion_zero_right (x y : Int) : ¬ SignedTriangleRegion x y 0 := by
  simp [SignedTriangleRegion,TriangleRegion]

def TriangleObstruction4 (B : Matrix 4) : Prop :=
  SignedTriangleRegion (B 0 1) (B 1 2) (-B 0 2) ∨
  SignedTriangleRegion (B 0 1) (B 1 3) (-B 0 3) ∨
  SignedTriangleRegion (B 0 2) (B 2 3) (-B 0 3) ∨
  SignedTriangleRegion (B 1 2) (B 2 3) (-B 1 3)

/-- Complete criterion for every disconnected integral skew-symmetric 4×4
matrix. The proof uses the seven support cuts and no hereditary-MA theorem. -/
theorem disconnected_NMA_iff (B : Matrix 4) (hs : SkewSymmetric B)
    (hd : DisconnectedSupport B) :
    ¬ MutationAcyclic B ↔ TriangleObstruction4 B := by
  have hc := disconnected_support_cut B hd
  have he := ofSix_reconstruct B hs
  rcases hc with h|h|h|h|h|h|h
  · rcases h with ⟨h01,h02,h03⟩
    rw [h01,h02,h03] at he
    rw [← he]
    have ht := signed_isolated_triangle_NMA_iff (B 1 2) (B 1 3) (B 2 3)
    rw [← isolate_zero_normalization, MA_relabel_iff] at ht
    simpa [TriangleObstruction4,ofSix] using ht
  · rcases h with ⟨h01,h12,h13⟩
    rw [h01,h12,h13] at he
    rw [← he]
    have ht := signed_isolated_triangle_NMA_iff (B 0 2) (B 0 3) (B 2 3)
    rw [← isolate_one_normalization, MA_relabel_iff] at ht
    simpa [TriangleObstruction4,ofSix] using ht
  · rcases h with ⟨h02,h12,h23⟩
    rw [h02,h12,h23] at he
    rw [← he]
    have ht := signed_isolated_triangle_NMA_iff (B 0 1) (B 0 3) (B 1 3)
    rw [← isolate_two_normalization, MA_relabel_iff] at ht
    simpa [TriangleObstruction4,ofSix] using ht
  · rcases h with ⟨h03,h13,h23⟩
    rw [h03,h13,h23] at he
    rw [← he]
    simpa [TriangleObstruction4,ofSix] using signed_isolated_triangle_NMA_iff (B 0 1) (B 0 2) (B 1 2)
  · rcases h with ⟨h02,h03,h12,h13⟩
    rw [h02,h03,h12,h13] at he
    rw [← he]
    have ha := acyclic_is_mutationAcyclic _ (two_pairs_01_23_acyclic (B 0 1) (B 2 3))
    simp [ha,TriangleObstruction4,ofSix]
  · rcases h with ⟨h01,h03,h12,h23⟩
    rw [h01,h03,h12,h23] at he
    rw [← he]
    have ha := acyclic_is_mutationAcyclic _ (two_pairs_02_13_acyclic (B 0 2) (B 1 3))
    simp [ha,TriangleObstruction4,ofSix]
  · rcases h with ⟨h01,h02,h13,h23⟩
    rw [h01,h02,h13,h23] at he
    rw [← he]
    have ha := acyclic_is_mutationAcyclic _ (two_pairs_03_12_acyclic (B 0 3) (B 1 2))
    simp [ha,TriangleObstruction4,ofSix]


instance triangleRegionDecidable (x y z : Int) : Decidable (TriangleRegion x y z) := by
  unfold TriangleRegion
  infer_instance

instance signedTriangleRegionDecidable (x y z : Int) : Decidable (SignedTriangleRegion x y z) := by
  unfold SignedTriangleRegion
  infer_instance

instance triangleObstruction4Decidable (B : Matrix 4) : Decidable (TriangleObstruction4 B) := by
  unfold TriangleObstruction4
  infer_instance

/-- Total executable arithmetic decision function; true means MA. Its correctness
is asserted exactly on the disconnected skew-symmetric domain below. -/
def disconnectedMA (B : Matrix 4) : Bool := !(decide (TriangleObstruction4 B))

theorem disconnectedMA_false_iff (B : Matrix 4) (hs : SkewSymmetric B)
    (hd : DisconnectedSupport B) :
    disconnectedMA B = false ↔ ¬ MutationAcyclic B := by
  simp only [disconnectedMA,Bool.not_eq_false',decide_eq_true_eq]
  exact (disconnected_NMA_iff B hs hd).symm

theorem disconnectedMA_true_iff (B : Matrix 4) (hs : SkewSymmetric B)
    (hd : DisconnectedSupport B) :
    disconnectedMA B = true ↔ MutationAcyclic B := by
  have hf := disconnectedMA_false_iff B hs hd
  constructor
  · intro ht
    apply Classical.byContradiction
    intro hn
    have := hf.mpr hn
    simp_all
  · intro hm
    cases he : disconnectedMA B
    · exact False.elim ((hf.mp he) hm)
    · rfl

/-- The last previously unverified disconnected source certificate. -/
theorem nma_qd019 : ¬ MutationAcyclic (ofSix (-2) 0 2 0 (-2) 0) := by
  have hn := isolated_reverse_triangle_NMA 2 2 2 (by decide) (by decide) (by decide) (by decide)
  rw [← isolate_two_normalization,MA_relabel_iff] at hn
  exact hn


/-- The finite cut list has exactly the semantic support-partition meaning. -/
theorem disconnected_cut_support (B : Matrix 4) (hs : SkewSymmetric B)
    (h : DisconnectedCut B) : DisconnectedSupport B := by
  rcases h with h|h|h|h|h|h|h
  · refine ⟨(fun i => match i.val with | 0 => true | 1 => false | 2 => false | _ => false),⟨0,rfl⟩,⟨1,rfl⟩,?_⟩
    intro i j hij
    have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
    have hj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
    have hsij := hs i j
    clear hs
    rcases hi with rfl|rfl|rfl|rfl <;> rcases hj with rfl|rfl|rfl|rfl <;>
      simp_all <;> omega
  · refine ⟨(fun i => match i.val with | 0 => false | 1 => true | 2 => false | _ => false),⟨1,rfl⟩,⟨0,rfl⟩,?_⟩
    intro i j hij
    have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
    have hj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
    have hsij := hs i j
    clear hs
    rcases hi with rfl|rfl|rfl|rfl <;> rcases hj with rfl|rfl|rfl|rfl <;>
      simp_all <;> omega
  · refine ⟨(fun i => match i.val with | 0 => false | 1 => false | 2 => true | _ => false),⟨2,rfl⟩,⟨0,rfl⟩,?_⟩
    intro i j hij
    have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
    have hj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
    have hsij := hs i j
    clear hs
    rcases hi with rfl|rfl|rfl|rfl <;> rcases hj with rfl|rfl|rfl|rfl <;>
      simp_all <;> omega
  · refine ⟨(fun i => match i.val with | 0 => false | 1 => false | 2 => false | _ => true),⟨3,rfl⟩,⟨0,rfl⟩,?_⟩
    intro i j hij
    have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
    have hj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
    have hsij := hs i j
    clear hs
    rcases hi with rfl|rfl|rfl|rfl <;> rcases hj with rfl|rfl|rfl|rfl <;>
      simp_all <;> omega
  · refine ⟨(fun i => match i.val with | 0 => true | 1 => true | 2 => false | _ => false),⟨0,rfl⟩,⟨2,rfl⟩,?_⟩
    intro i j hij
    have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
    have hj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
    have hsij := hs i j
    clear hs
    rcases hi with rfl|rfl|rfl|rfl <;> rcases hj with rfl|rfl|rfl|rfl <;>
      simp_all <;> omega
  · refine ⟨(fun i => match i.val with | 0 => true | 1 => false | 2 => true | _ => false),⟨0,rfl⟩,⟨1,rfl⟩,?_⟩
    intro i j hij
    have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
    have hj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
    have hsij := hs i j
    clear hs
    rcases hi with rfl|rfl|rfl|rfl <;> rcases hj with rfl|rfl|rfl|rfl <;>
      simp_all <;> omega
  · refine ⟨(fun i => match i.val with | 0 => true | 1 => false | 2 => false | _ => true),⟨0,rfl⟩,⟨1,rfl⟩,?_⟩
    intro i j hij
    have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
    have hj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
    have hsij := hs i j
    clear hs
    rcases hi with rfl|rfl|rfl|rfl <;> rcases hj with rfl|rfl|rfl|rfl <;>
      simp_all <;> omega

/-- The 28 saved disconnected representatives; this list is not an assertion of
exhaustiveness of the bounded isomorphism census. -/
def disconnectedBaseline (i : Fin 28) : Matrix 4 :=
  match i.val with
  | 0 => ofSix (-2) (-2) (0) (-2) (0) (0)
  | 1 => ofSix (-2) (-2) (0) (-1) (0) (0)
  | 2 => ofSix (-2) (-2) (0) (0) (0) (0)
  | 3 => ofSix (-2) (-1) (0) (-2) (0) (0)
  | 4 => ofSix (-2) (-1) (0) (-1) (0) (0)
  | 5 => ofSix (-2) (-1) (0) (0) (0) (0)
  | 6 => ofSix (-2) (-1) (0) (1) (0) (0)
  | 7 => ofSix (-2) (-1) (0) (2) (0) (0)
  | 8 => ofSix (-2) (0) (0) (-2) (0) (0)
  | 9 => ofSix (-2) (0) (0) (-1) (0) (0)
  | 10 => ofSix (-2) (0) (0) (0) (0) (-2)
  | 11 => ofSix (-2) (0) (0) (0) (0) (-1)
  | 12 => ofSix (-2) (0) (0) (0) (0) (0)
  | 13 => ofSix (-2) (0) (0) (0) (1) (0)
  | 14 => ofSix (-2) (0) (0) (0) (2) (0)
  | 15 => ofSix (-2) (0) (1) (0) (-2) (0)
  | 16 => ofSix (-2) (0) (1) (0) (-1) (0)
  | 17 => ofSix (-2) (0) (1) (0) (0) (0)
  | 18 => ofSix (-2) (0) (1) (0) (1) (0)
  | 19 => ofSix (-2) (0) (2) (0) (-2) (0)
  | 20 => ofSix (-1) (-1) (0) (-1) (0) (0)
  | 21 => ofSix (-1) (-1) (0) (0) (0) (0)
  | 22 => ofSix (-1) (0) (0) (-1) (0) (0)
  | 23 => ofSix (-1) (0) (0) (0) (0) (-1)
  | 24 => ofSix (-1) (0) (0) (0) (0) (0)
  | 25 => ofSix (-1) (0) (0) (0) (1) (0)
  | 26 => ofSix (-1) (0) (1) (0) (-1) (0)
  | _ => ofSix (0) (0) (0) (0) (0) (0)

theorem disconnectedBaseline_skew (i : Fin 28) : SkewSymmetric (disconnectedBaseline i) := by
  have h : ∀ i, SkewSymmetric (disconnectedBaseline i) := by unfold SkewSymmetric; decide
  exact h i

theorem disconnectedBaseline_support (i : Fin 28) : DisconnectedSupport (disconnectedBaseline i) := by
  apply disconnected_cut_support _ (disconnectedBaseline_skew i)
  have h : ∀ i, DisconnectedCut (disconnectedBaseline i) := by unfold DisconnectedCut; decide
  exact h i

theorem disconnectedBaseline_decision :
    ∀ i : Fin 28, disconnectedMA (disconnectedBaseline i) = decide (i ≠ 19) := by decide

/-- All 28 recorded disconnected representatives now have complete Lean decisions. -/
theorem disconnectedBaseline_classification (i : Fin 28) :
    MutationAcyclic (disconnectedBaseline i) ↔ i ≠ 19 := by
  rw [← disconnectedMA_true_iff _ (disconnectedBaseline_skew i) (disconnectedBaseline_support i),
    disconnectedBaseline_decision]
  simp

def disconnectedBaselineWord (i : Fin 28) : List (Fin 4) :=
  match i.val with
  | 15 => [0]
  | 16 => [3]
  | 26 => [0]
  | _ => []

def disconnectedBaselineRank (i : Fin 28) (j : Fin 4) : Nat :=
  match i.val with
  | 0 => match j.val with | 0 => 3 | 1 => 2 | 2 => 0 | _ => 1
  | 1 => match j.val with | 0 => 3 | 1 => 2 | 2 => 0 | _ => 1
  | 2 => match j.val with | 0 => 3 | 1 => 0 | 2 => 1 | _ => 2
  | 3 => match j.val with | 0 => 3 | 1 => 2 | 2 => 0 | _ => 1
  | 4 => match j.val with | 0 => 3 | 1 => 2 | 2 => 0 | _ => 1
  | 5 => match j.val with | 0 => 3 | 1 => 0 | 2 => 1 | _ => 2
  | 6 => match j.val with | 0 => 3 | 1 => 0 | 2 => 2 | _ => 1
  | 7 => match j.val with | 0 => 3 | 1 => 0 | 2 => 2 | _ => 1
  | 8 => match j.val with | 0 => 3 | 1 => 2 | 2 => 0 | _ => 1
  | 9 => match j.val with | 0 => 3 | 1 => 2 | 2 => 0 | _ => 1
  | 10 => match j.val with | 0 => 2 | 1 => 0 | 2 => 3 | _ => 1
  | 11 => match j.val with | 0 => 2 | 1 => 0 | 2 => 3 | _ => 1
  | 12 => match j.val with | 0 => 3 | 1 => 0 | 2 => 1 | _ => 2
  | 13 => match j.val with | 0 => 2 | 1 => 0 | 2 => 1 | _ => 3
  | 14 => match j.val with | 0 => 2 | 1 => 0 | 2 => 1 | _ => 3
  | 15 => match j.val with | 0 => 2 | 1 => 3 | 2 => 0 | _ => 1
  | 16 => match j.val with | 0 => 3 | 1 => 0 | 2 => 1 | _ => 2
  | 17 => match j.val with | 0 => 2 | 1 => 0 | 2 => 1 | _ => 3
  | 18 => match j.val with | 0 => 2 | 1 => 0 | 2 => 1 | _ => 3
  | 19 => match j.val with | 0 => 0 | 1 => 1 | 2 => 2 | _ => 3
  | 20 => match j.val with | 0 => 3 | 1 => 2 | 2 => 0 | _ => 1
  | 21 => match j.val with | 0 => 3 | 1 => 0 | 2 => 1 | _ => 2
  | 22 => match j.val with | 0 => 3 | 1 => 2 | 2 => 0 | _ => 1
  | 23 => match j.val with | 0 => 2 | 1 => 0 | 2 => 3 | _ => 1
  | 24 => match j.val with | 0 => 3 | 1 => 0 | 2 => 1 | _ => 2
  | 25 => match j.val with | 0 => 2 | 1 => 0 | 2 => 1 | _ => 3
  | 26 => match j.val with | 0 => 2 | 1 => 3 | 2 => 0 | _ => 1
  | _ => match j.val with | 0 => 0 | 1 => 1 | 2 => 2 | _ => 3

theorem disconnectedBaselineWord_length (i : Fin 28) : (disconnectedBaselineWord i).length ≤ 1 := by
  have h : ∀ i, (disconnectedBaselineWord i).length ≤ 1 := by decide
  exact h i

/-- Every MA entry has an explicit word of at most one mutation, checked by reduction. -/
theorem disconnectedBaselineWord_correct (i : Fin 28) (hi : i ≠ 19) :
    Acyclic (applyWord (disconnectedBaseline i) (disconnectedBaselineWord i)) := by
  refine ⟨disconnectedBaselineRank i,?_⟩
  have h : ∀ i : Fin 28, i ≠ 19 → ∀ j k : Fin 4,
      0 < applyWord (disconnectedBaseline i) (disconnectedBaselineWord i) j k →
      disconnectedBaselineRank i j < disconnectedBaselineRank i k := by decide
  exact h i hi

end QuiverProofs
