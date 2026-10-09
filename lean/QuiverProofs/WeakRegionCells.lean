import QuiverProofs.WeakRegionSemantics

namespace QuiverProofs.WeakRegionCells
open WeakRegions WeakRegionSemantics

/-- The four actual labeled corners of the zero-edge diamond. -/
def diamondState (A B C D E : Int) (i : Fin 4) : Matrix 4 :=
  match i.val with
  | 0 => root A B C D E 0
  | 1 => diamondW2 A B C D E
  | 2 => diamondW3 A B C D E
  | _ => diamondT A B C D E

/-- The ten actual labeled corners, retaining both special-swap copies. -/
def unitState (A B C D E : Int) (i : Fin 10) : Matrix 4 :=
  match i.val with
  | 0 => root A B C D E 1
  | 1 => unitW A B C D E
  | 2 => unitT A B C D E
  | 3 => unitTP A B C D E
  | 4 => unitWP A B C D E
  | 5 => relabel (root A B C D E 1) frame0132
  | 6 => relabel (unitW A B C D E) frame0132
  | 7 => relabel (unitT A B C D E) frame0132
  | 8 => relabel (unitTP A B C D E) frame0132
  | _ => relabel (unitWP A B C D E) frame0132

private theorem fin4 (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
private theorem fin10 (i : Fin 10) :
    i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 := by omega

theorem diamond_skew (A B C D E : Int) (i : Fin 4) :
    SkewSymmetric (diamondState A B C D E i) := by
  rcases fin4 i with rfl | rfl | rfl | rfl <;>
    exact ofSix_skew _ _ _ _ _ _

theorem unit_skew (A B C D E : Int) (i : Fin 10) :
    SkewSymmetric (unitState A B C D E i) := by
  rcases fin10 i with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ofSix_skew _ _ _ _ _ _ | exact relabel_skew _ _ (ofSix_skew _ _ _ _ _ _)

theorem diamond_cyclic (A B C D E : Int) (h : Domain A B C D E) (i : Fin 4) :
    ¬ Acyclic (diamondState A B C D E i) := by
  rcases fin4 i with rfl | rfl | rfl | rfl
  · exact root_cyclic A B C D E 0 h
  · exact diamond_w2_cyclic A B C D E h
  · exact diamond_w3_cyclic A B C D E h
  · exact diamond_t_cyclic A B C D E h

theorem unit_cyclic (A B C D E : Int) (h : Domain A B C D E) (i : Fin 10) :
    ¬ Acyclic (unitState A B C D E i) := by
  rcases fin10 i with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact root_cyclic A B C D E 1 h
  · exact unit_w_cyclic A B C D E h
  · exact unit_t_cyclic A B C D E h
  · exact unit_tp_cyclic A B C D E h
  · exact unit_wp_cyclic A B C D E h
  · exact fun ha => root_cyclic A B C D E 1 h ((acyclic_relabel_iff _ _).mp ha)
  · exact fun ha => unit_w_cyclic A B C D E h ((acyclic_relabel_iff _ _).mp ha)
  · exact fun ha => unit_t_cyclic A B C D E h ((acyclic_relabel_iff _ _).mp ha)
  · exact fun ha => unit_tp_cyclic A B C D E h ((acyclic_relabel_iff _ _).mp ha)
  · exact fun ha => unit_wp_cyclic A B C D E h ((acyclic_relabel_iff _ _).mp ha)

theorem special_swap_twice (Q : Matrix 4) : relabel (relabel Q frame0132) frame0132 = Q := by
  funext i j
  rcases fin4 i with rfl | rfl | rfl | rfl <;>
    rcases fin4 j with rfl | rfl | rfl | rfl <;> rfl

def diamondCell (A B C D E : Int) (h : Domain A B C D E) : Cell where
  size := 4
  rootIndex := 0
  state := diamondState A B C D E
  returnVertex := 0
  skew := diamond_skew A B C D E
  cyclic := diamond_cyclic A B C D E h
  edges := by
    intro i k
    rcases fin4 i with rfl | rfl | rfl | rfl <;>
      rcases fin4 k with rfl | rfl | rfl | rfl
    · right; left; exact ⟨Relabeling.identity 4, rfl⟩
    · right; right; right; exact root_one_root A B C D E 0 h (by decide)
    · left; exact ⟨1, diamond_root_two A B C D E h⟩
    · left; exact ⟨2, diamond_root_three A B C D E h⟩
    · right; right; left; exact diamond_w2_zero_fork A B C D E h
    · right; right; left; exact diamond_w2_one_fork A B C D E h
    · left; exact ⟨0, diamond_w2_two A B C D E h⟩
    · left; exact ⟨3, diamond_w2_three A B C D E h⟩
    · right; right; left; exact diamond_w3_zero_fork A B C D E h
    · right; right; left; exact diamond_w3_one_fork A B C D E h
    · left; exact ⟨3, diamond_w3_two A B C D E h⟩
    · left; exact ⟨0, diamond_w3_three A B C D E h⟩
    · right; right; right; exact diamond_t_zero_root A B C D E h
    · right; right; right; exact diamond_t_one_root A B C D E h
    · left; exact ⟨2, diamond_t_two A B C D E h⟩
    · left; exact ⟨1, diamond_t_three A B C D E h⟩

def unitCell (A B C D E : Int) (h : Domain A B C D E) : Cell where
  size := 10
  rootIndex := 0
  state := unitState A B C D E
  returnVertex := 0
  skew := unit_skew A B C D E
  cyclic := unit_cyclic A B C D E h
  edges := by
    intro i k
    rcases fin10 i with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases fin4 k with rfl | rfl | rfl | rfl
    · right; left; exact ⟨Relabeling.identity 4, rfl⟩
    · right; right; right; exact root_one_root A B C D E 1 h (by decide)
    · left; exact ⟨1, unit_root_two A B C D E h⟩
    · left; exact ⟨9, unit_root_three A B C D E h⟩
    · right; right; left; exact unit_w_zero_fork A B C D E h
    · right; right; left; exact unit_w_one_fork A B C D E h
    · left; exact ⟨0, unit_w_two A B C D E h⟩
    · left; exact ⟨2, unit_w_three A B C D E h⟩
    · right; right; right; exact unit_t_zero_root A B C D E h
    · right; right; left; exact unit_t_one_fork A B C D E h
    · left; exact ⟨3, unit_t_two A B C D E h⟩
    · left; exact ⟨1, unit_t_three A B C D E h⟩
    · right; right; left; exact unit_tp_zero_fork A B C D E h
    · right; right; right; exact unit_tp_one_root A B C D E h
    · left; exact ⟨2, unit_tp_two A B C D E h⟩
    · left; exact ⟨4, unit_tp_three A B C D E h⟩
    · right; right; left; exact unit_wp_zero_fork A B C D E h
    · right; right; left; exact unit_wp_one_fork A B C D E h
    · left; refine ⟨5,?_⟩
      change mutate (unitWP A B C D E) 2 = relabel (root A B C D E 1) frame0132
      rw [unit_wp_two A B C D E h,root_special_swap]
    · left; exact ⟨3, unit_wp_three A B C D E h⟩
    · right; left; exact ⟨frame0132,mutate_relabel (root A B C D E 1) frame0132 0⟩
    · right; right; right
      have hh := IsRoot.relabelled (root_one_root A B C D E 1 h (by decide)) frame0132
      change IsRoot (mutate (relabel (root A B C D E 1) frame0132) 1) 1
      rw [mutate_relabel]
      exact hh
    · left; refine ⟨4,?_⟩
      change mutate (relabel (root A B C D E 1) frame0132) 2 = _
      rw [mutate_relabel]
      change relabel (mutate (root A B C D E 1) 3) frame0132 = _
      rw [unit_root_three A B C D E h,special_swap_twice]
      rfl
    · left; refine ⟨6,?_⟩
      change mutate (relabel (root A B C D E 1) frame0132) 3 = _
      rw [mutate_relabel]
      change relabel (mutate (root A B C D E 1) 2) frame0132 = _
      rw [unit_root_two A B C D E h]
      rfl
    · right; right; left
      have hh := WeakForks.IsWeakFork.relabelled (unit_w_zero_fork A B C D E h) frame0132
      change WeakForks.IsWeakFork (mutate (relabel (unitW A B C D E) frame0132) 0) 0
      rw [mutate_relabel]
      exact hh
    · right; right; left
      have hh := WeakForks.IsWeakFork.relabelled (unit_w_one_fork A B C D E h) frame0132
      change WeakForks.IsWeakFork (mutate (relabel (unitW A B C D E) frame0132) 1) 1
      rw [mutate_relabel]
      exact hh
    · left; refine ⟨7,?_⟩
      change mutate (relabel (unitW A B C D E) frame0132) 2 = _
      rw [mutate_relabel]
      change relabel (mutate (unitW A B C D E) 3) frame0132 = _
      rw [unit_w_three A B C D E h]
      rfl
    · left; refine ⟨5,?_⟩
      change mutate (relabel (unitW A B C D E) frame0132) 3 = _
      rw [mutate_relabel]
      change relabel (mutate (unitW A B C D E) 2) frame0132 = _
      rw [unit_w_two A B C D E h]
      rfl
    · right; right; right
      have hh := IsRoot.relabelled (unit_t_zero_root A B C D E h) frame0132
      change IsRoot (mutate (relabel (unitT A B C D E) frame0132) 0) 0
      rw [mutate_relabel]
      exact hh
    · right; right; left
      have hh := WeakForks.IsWeakFork.relabelled (unit_t_one_fork A B C D E h) frame0132
      change WeakForks.IsWeakFork (mutate (relabel (unitT A B C D E) frame0132) 1) 1
      rw [mutate_relabel]
      exact hh
    · left; refine ⟨6,?_⟩
      change mutate (relabel (unitT A B C D E) frame0132) 2 = _
      rw [mutate_relabel]
      change relabel (mutate (unitT A B C D E) 3) frame0132 = _
      rw [unit_t_three A B C D E h]
      rfl
    · left; refine ⟨8,?_⟩
      change mutate (relabel (unitT A B C D E) frame0132) 3 = _
      rw [mutate_relabel]
      change relabel (mutate (unitT A B C D E) 2) frame0132 = _
      rw [unit_t_two A B C D E h]
      rfl
    · right; right; left
      have hh := WeakForks.IsWeakFork.relabelled (unit_tp_zero_fork A B C D E h) frame0132
      change WeakForks.IsWeakFork (mutate (relabel (unitTP A B C D E) frame0132) 0) 0
      rw [mutate_relabel]
      exact hh
    · right; right; right
      have hh := IsRoot.relabelled (unit_tp_one_root A B C D E h) frame0132
      change IsRoot (mutate (relabel (unitTP A B C D E) frame0132) 1) 1
      rw [mutate_relabel]
      exact hh
    · left; refine ⟨9,?_⟩
      change mutate (relabel (unitTP A B C D E) frame0132) 2 = _
      rw [mutate_relabel]
      change relabel (mutate (unitTP A B C D E) 3) frame0132 = _
      rw [unit_tp_three A B C D E h]
      rfl
    · left; refine ⟨7,?_⟩
      change mutate (relabel (unitTP A B C D E) frame0132) 3 = _
      rw [mutate_relabel]
      change relabel (mutate (unitTP A B C D E) 2) frame0132 = _
      rw [unit_tp_two A B C D E h]
      rfl
    · right; right; left
      have hh := WeakForks.IsWeakFork.relabelled (unit_wp_zero_fork A B C D E h) frame0132
      change WeakForks.IsWeakFork (mutate (relabel (unitWP A B C D E) frame0132) 0) 0
      rw [mutate_relabel]
      exact hh
    · right; right; left
      have hh := WeakForks.IsWeakFork.relabelled (unit_wp_one_fork A B C D E h) frame0132
      change WeakForks.IsWeakFork (mutate (relabel (unitWP A B C D E) frame0132) 1) 1
      rw [mutate_relabel]
      exact hh
    · left; refine ⟨8,?_⟩
      change mutate (relabel (unitWP A B C D E) frame0132) 2 = _
      rw [mutate_relabel]
      change relabel (mutate (unitWP A B C D E) 3) frame0132 = _
      rw [unit_wp_three A B C D E h]
      rfl
    · left; refine ⟨0,?_⟩
      change mutate (relabel (unitWP A B C D E) frame0132) 3 = _
      rw [mutate_relabel]
      change relabel (mutate (unitWP A B C D E) 2) frame0132 = _
      rw [unit_wp_two A B C D E h,←root_special_swap,special_swap_twice]
      rfl

/-- Relabeling transports the entire checked cell, including its return frame. -/
def cellRelabel (c : Cell) (p : Relabeling 4) : Cell where
  size := c.size
  rootIndex := c.rootIndex
  state i := relabel (c.state i) p
  returnVertex := p.invFun c.returnVertex
  skew i := relabel_skew _ p (c.skew i)
  cyclic i := fun h => c.cyclic i ((acyclic_relabel_iff _ p).mp h)
  edges := by
    intro i k
    rcases c.edges i (p.toFun k) with ⟨j,hj⟩ | ⟨q,hq⟩ | hf | hr
    · left; refine ⟨j,?_⟩
      rw [mutate_relabel,hj]
    · right; left
      refine ⟨p.symm.trans (q.trans p),?_⟩
      rw [mutate_relabel,hq,mutate_relabel,p.right_inv]
      funext i j
      simp [relabel,Relabeling.trans,Relabeling.symm,p.right_inv]
    · right; right; left
      have hf' := WeakForks.IsWeakFork.relabelled hf p
      simpa only [p.left_inv,mutate_relabel] using hf'
    · right; right; right
      have hr' := IsRoot.relabelled hr p
      simpa only [p.left_inv,mutate_relabel] using hr'

/-- Simultaneous arrow reversal transports all cell transitions. -/
def cellReverse (c : Cell) : Cell where
  size := c.size
  rootIndex := c.rootIndex
  state i := reverse (c.state i)
  returnVertex := c.returnVertex
  skew i := reverse_skew _ (c.skew i)
  cyclic i := fun h => c.cyclic i ((acyclic_reverse_iff _ (c.skew i)).mp h)
  edges := by
    intro i k
    rcases c.edges i k with ⟨j,hj⟩ | ⟨p,hp⟩ | hf | hr
    · left; refine ⟨j,?_⟩
      rw [mutate_reverse,hj]
    · right; left; refine ⟨p,?_⟩
      rw [mutate_reverse,hp,mutate_reverse]
      rfl
    · right; right; left
      simpa only [mutate_reverse] using WeakForks.IsWeakFork.reversed hf
    · right; right; right
      simpa only [mutate_reverse] using IsRoot.reversed hr

/-- Every admitted pre-fork root has a finite cell with all four mutations
checked at every corner, including the special-swapped unit return. -/
theorem root_cells_exist : RootCellsExist := by
  intro Q r h
  induction h with
  | basic A B C D E ε h hε =>
    rcases hε with rfl | rfl
    · exact ⟨diamondCell A B C D E h,rfl,rfl⟩
    · exact ⟨unitCell A B C D E h,rfl,rfl⟩
  | @relabelled Q r h p ih =>
    obtain ⟨c,heq,hret⟩ := ih
    refine ⟨cellRelabel c p,?_,?_⟩
    · change relabel (c.state c.rootIndex) p = relabel Q p
      rw [heq]
    · change p.invFun c.returnVertex = p.invFun r
      rw [hret]
  | @reversed Q r h ih =>
    obtain ⟨c,heq,hret⟩ := ih
    refine ⟨cellReverse c,?_,hret⟩
    change reverse (c.state c.rootIndex) = reverse Q
    rw [heq]

end QuiverProofs.WeakRegionCells
