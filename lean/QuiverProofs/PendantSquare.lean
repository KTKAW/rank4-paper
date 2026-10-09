import QuiverProofs.Pendant

/-! Universal pendant-square transition calculations over the exact integer
cone from “All four transitions of a pendant square”. The graph-theoretic normalization and the two-parent recursive language
are proved separately in PendantNormalization and PendantLanguage. -/
namespace QuiverProofs.PendantSquare
open TriangleRegions Regions Pendant

/-- Leaf 0, junction 3, return 1, remaining vertex 2. -/
def state (c d x y ε : Int) : Matrix 4 := ofSix 0 0 (ε*c) d (-x) y

def Domain (c d x y : Int) : Prop :=
  2 ≤ c ∧ 2 ≤ d ∧ 2 ≤ x ∧ d < y ∧ x < y

def Sign (ε : Int) : Prop := ε=1 ∨ ε= -1

private theorem fin4 (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega

def swap12 : Relabeling 4 :=
  ⟨fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i,
   fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i, by decide, by decide⟩

def plusFrame : Relabeling 4 :=
  ⟨fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 0 | _ => 2,
   fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 3 | _ => 0, by decide, by decide⟩

def minusFrame : Relabeling 4 :=
  ⟨fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | _ => 1,
   fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | _ => 0, by decide, by decide⟩

theorem compound_bounds (c d x y : Int) (h : Domain c d x y) :
    x < x*y-d ∧ y < x*y-d ∧ d < d*y-x ∧ y < d*y-x := by
  obtain ⟨_,hd,hx,hdy,hxy⟩ := h
  exact ⟨(Forks.product_sub_dominates x y d hx hxy hdy).1,
    (Forks.product_sub_dominates x y d hx hxy hdy).2,
    (Forks.product_sub_dominates d y x hd hdy hxy).1,
    (Forks.product_sub_dominates d y x hd hdy hxy).2⟩

theorem leaf (c d x y ε : Int) :
    mutate (state c d x y ε) 0 = state c d x y (-ε) := by
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;>
    rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [state,mutate,ofSix,correction] <;> grind

theorem parent (c d x y ε : Int) (h : Domain c d x y) :
    mutate (state c d x y ε) 1 = ofSix 0 0 (ε*c) (-d) x (y-d*x) := by
  obtain ⟨hc,hd,hx,hdy,hxy⟩ := h
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;>
    rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [state,mutate,ofSix,correction] <;> grind

theorem child (c d x y ε : Int) (h : Domain c d x y) :
    mutate (state c d x y ε) 2 = ofSix 0 0 (ε*c) (-d) (d*y-x) (-y) := by
  obtain ⟨hc,hd,hx,hdy,hxy⟩ := h
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;>
    rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [state,mutate,ofSix,correction] <;> grind

theorem junction_plus (c d x y : Int) (h : Domain c d x y) :
    mutate (state c d x y 1) 3 = ofSix (c*x) 0 (-c) (-(x*y-d)) x (-y) := by
  obtain ⟨hc,hd,hx,hdy,hxy⟩ := h
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;>
    rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [state,mutate,ofSix,correction] <;> grind

theorem junction_minus (c d x y : Int) (h : Domain c d x y) :
    mutate (state c d x y (-1)) 3 = ofSix 0 (-c*y) c (-(x*y-d)) x (-y) := by
  obtain ⟨hc,hd,hx,hdy,hxy⟩ := h
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;>
    rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [state,mutate,ofSix,correction] <;> grind

theorem child_domain (c d x y : Int) (h : Domain c d x y) :
    Domain c d y (d*y-x) := by
  have := compound_bounds c d x y h
  unfold Domain at *
  omega

theorem child_frame (c d x y ε : Int) (h : Domain c d x y) :
    relabel (mutate (state c d x y ε) 2) swap12 = state c d y (d*y-x) ε := by
  rw [child c d x y ε h]
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;>
    rcases fin4 j with rfl|rfl|rfl|rfl <;> simp [relabel,swap12,state,ofSix]

theorem junction_isRoot (c d x y ε : Int) (h : Domain c d x y) (hε : Sign ε) :
    IsRoot (mutate (state c d x y ε) 3) 3 := by
  have hh := compound_bounds c d x y h
  obtain ⟨hc,hd,hx,hdy,hxy⟩ := h
  have hcx := Forks.product_add_dominates c x 0 hc hx (by decide)
  have hcy := Forks.product_add_dominates c y 0 hc (by omega) (by decide)
  rcases hε with rfl|rfl
  · have heq : relabel (reverse (mutate (state c d x y 1) 3)) plusFrame =
        root x (c*x) (x*y-d) c y 0 := by
      rw [junction_plus c d x y ⟨hc,hd,hx,hdy,hxy⟩]
      funext i j
      rcases fin4 i with rfl|rfl|rfl|rfl <;>
        rcases fin4 j with rfl|rfl|rfl|rfl <;> simp [root,relabel,reverse,plusFrame,ofSix]
    have hr : IsRoot (relabel (reverse (mutate (state c d x y 1) 3)) plusFrame) 0 := by
      rw [heq]
      exact IsRoot.basic _ _ _ _ _ _ (by unfold Regions.Domain; omega) (Or.inl rfl)
    exact root_of_reverse (root_of_relabel plusFrame hr)
  · have heq : relabel (mutate (state c d x y (-1)) 3) minusFrame =
        root y (c*y) (x*y-d) c x 0 := by
      rw [junction_minus c d x y ⟨hc,hd,hx,hdy,hxy⟩]
      funext i j
      rcases fin4 i with rfl|rfl|rfl|rfl <;>
        rcases fin4 j with rfl|rfl|rfl|rfl <;> simp [root,relabel,minusFrame,ofSix] <;> grind
    have hr : IsRoot (relabel (mutate (state c d x y (-1)) 3) minusFrame) 0 := by
      rw [heq]
      exact IsRoot.basic _ _ _ _ _ _ (by unfold Regions.Domain; omega) (Or.inl rfl)
    exact root_of_relabel minusFrame hr

theorem pendant_at (c d x y ε : Int) (h : Domain c d x y) (hε : Sign ε) :
    At (state c d x y ε) 0 3 := by
  obtain ⟨hc,hd,hx,hdy,hxy⟩ := h
  refine ⟨by decide,?_,?_⟩
  · rcases hε with rfl|rfl <;> simp [state,ofSix] <;> omega
  · intro j hj
    rcases fin4 j with rfl|rfl|rfl|rfl <;> simp_all [state,ofSix]

theorem cyclic (c d x y ε : Int) (h : Domain c d x y) : ¬ Acyclic (state c d x y ε) := by
  obtain ⟨hc,hd,hx,hdy,hxy⟩ := h
  rintro ⟨rank,hr⟩
  have h12 := hr 1 2 (by simp [state,ofSix]; omega)
  have h23 := hr 2 3 (by simp [state,ofSix]; omega)
  have h31 := hr 3 1 (by simp [state,ofSix]; omega)
  omega

theorem triangles_containing_leaf_acyclic (c d x y ε : Int)
    (h : Domain c d x y) (hε : Sign ε) (e : Fin 3 → Fin 4)
    (he : Function.Injective e) (k : Fin 3) (hk : e k=0) :
    Acyclic (restrict (state c d x y ε) e) :=
  containing_leaf_acyclic _ (ofSix_skew _ _ _ _ _ _) 0 3
    (pendant_at c d x y ε h hε) e he k hk

/-- The second parent is exactly the leaf mutation of the first parent. -/
theorem parent_leaf_compatibility (c d x y ε : Int) (h : Domain c d x y) :
    mutate (mutate (state c d x y ε) 1) 0 = mutate (state c d x y (-ε)) 1 := by
  rw [parent c d x y ε h,parent c d x y (-ε) h]
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;>
    rcases fin4 j with rfl|rfl|rfl|rfl <;> simp [mutate,ofSix,correction] <;> grind

/-- Both child orientations belong to exactly the same normalized cell. -/
theorem child_leaf_compatibility (c d x y ε : Int) (h : Domain c d x y) :
    mutate (mutate (state c d x y ε) 2) 0 = mutate (state c d x y (-ε)) 2 := by
  rw [child c d x y ε h,child c d x y (-ε) h]
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;>
    rcases fin4 j with rfl|rfl|rfl|rfl <;> simp [mutate,ofSix,correction] <;> grind

/-- Deleting the inward return leaves only the two-edge path through the junction. -/
theorem return_deletion_acyclic (c d x y ε : Int)
    (h : Domain c d x y) (hε : Sign ε) : DeletionAcyclic (state c d x y ε) 1 := by
  obtain ⟨hc,hd,hx,hdy,hxy⟩ := h
  rcases hε with rfl|rfl
  · refine ⟨fun i => if i=3 then 1 else 0,?_⟩
    intro i j hi hj hij
    rcases fin4 i with rfl|rfl|rfl|rfl <;>
      rcases fin4 j with rfl|rfl|rfl|rfl <;> simp_all [state,ofSix] <;> omega
  · refine ⟨fun i => if i=0 then 2 else if i=3 then 1 else 0,?_⟩
    intro i j hi hj hij
    rcases fin4 i with rfl|rfl|rfl|rfl <;>
      rcases fin4 j with rfl|rfl|rfl|rfl <;> simp_all [state,ofSix] <;> omega

theorem triangle_transfer (c d x y ε : Int) (h : Domain c d x y) (hε : Sign ε)
    (hp : AllTrianglesMA (mutate (state c d x y ε) 1)) :
    AllTrianglesMA (state c d x y ε) :=
  deletion_triangle_transfer _ 1 (return_deletion_acyclic c d x y ε h hε) hp

end QuiverProofs.PendantSquare
