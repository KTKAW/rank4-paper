import QuiverProofs.RegionSemantics
import QuiverProofs.RegionCells

namespace QuiverProofs.Box
open Forks Regions RegionSemantics

def box (a b : Int) : Matrix 4 := ofSix a 0 (-b) b 0 a
def middle (a b : Int) : Matrix 4 := ofSix (-a) 0 b b (-a*b) a
def node (a b : Int) (i : Fin 2) : Matrix 4 := if i=0 then box a b else middle a b

private theorem fin4 (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega

def p3210 : Relabeling 4 :=
  ⟨fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | _ => 0,
   fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | _ => 0, by decide,by decide⟩
def p2301 : Relabeling 4 :=
  ⟨fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | _ => 1,
   fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | _ => 1, by decide,by decide⟩
def p1032 : Relabeling 4 :=
  ⟨fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | _ => 2,
   fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | _ => 2, by decide,by decide⟩
def p1302 : Relabeling 4 :=
  ⟨fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 0 | _ => 2,
   fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 3 | _ => 1, by decide,by decide⟩

theorem boundary_domain (a b : Int) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    Regions.Domain (a*b) (b*(a^2-1)) (a*(b^2-1)) a b := by
  have hp := product_add_dominates a b 0 ha hb (by decide)
  have ha' := product_sub_dominates a (a*b) b ha (by omega) (by omega)
  have hb' := product_sub_dominates b (a*b) a hb (by omega) (by omega)
  unfold Regions.Domain
  grind

theorem box_zero (a b : Int) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    mutate (box a b) 0 = middle a b := by
  funext i j
  rcases fin4 i with rfl | rfl | rfl | rfl <;>
    rcases fin4 j with rfl | rfl | rfl | rfl <;>
    simp [box,middle,mutate,ofSix,correction] <;> grind

theorem box_one (a b : Int) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    mutate (box a b) 1 = relabel (middle a b) p3210 := by
  funext i j
  rcases fin4 i with rfl | rfl | rfl | rfl <;>
    rcases fin4 j with rfl | rfl | rfl | rfl <;>
    simp [box,middle,relabel,p3210,mutate,ofSix,correction] <;> grind

theorem box_two (a b : Int) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    mutate (box a b) 2 = relabel (middle a b) p2301 := by
  funext i j
  rcases fin4 i with rfl | rfl | rfl | rfl <;>
    rcases fin4 j with rfl | rfl | rfl | rfl <;>
    simp [box,middle,relabel,p2301,mutate,ofSix,correction] <;> grind

theorem box_three (a b : Int) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    mutate (box a b) 3 = relabel (middle a b) p1032 := by
  funext i j
  rcases fin4 i with rfl | rfl | rfl | rfl <;>
    rcases fin4 j with rfl | rfl | rfl | rfl <;>
    simp [box,middle,relabel,p1032,mutate,ofSix,correction] <;> grind

theorem middle_two (a b : Int) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    mutate (middle a b) 2 = relabel (box a b) p1032 := by
  have hp := Int.mul_pos (show 0<a by omega) (show 0<b by omega)
  funext i j
  rcases fin4 i with rfl | rfl | rfl | rfl <;>
    rcases fin4 j with rfl | rfl | rfl | rfl <;>
    simp [box,middle,relabel,p1032,mutate,ofSix,correction] <;> grind

theorem middle_one_root (a b : Int) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    IsRoot (mutate (middle a b) 1) 1 := by
  have hp := Int.mul_pos (show 0<a by omega) (show 0<b by omega)
  have heq : relabel (mutate (middle a b) 1) p1302 =
      root (a*b) (b*(a^2-1)) (a*(b^2-1)) a b 0 := by
    funext i j
    rcases fin4 i with rfl | rfl | rfl | rfl <;>
      rcases fin4 j with rfl | rfl | rfl | rfl <;>
      simp [middle,relabel,p1302,root,mutate,ofSix,correction] <;> grind
  have hr : IsRoot (relabel (mutate (middle a b) 1) p1302) 0 := by
    rw [heq]
    exact IsRoot.basic _ _ _ _ _ _ (boundary_domain a b ha hb) (by decide)
  exact root_of_relabel p1302 hr

theorem middle_three_root (a b : Int) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    IsRoot (mutate (middle a b) 3) 3 := by
  have hp := Int.mul_pos (show 0<a by omega) (show 0<b by omega)
  have heq : relabel (reverse (mutate (middle a b) 3)) Forks.rotate3102 =
      root (b*a) (a*(b^2-1)) (b*(a^2-1)) b a 0 := by
    funext i j
    rcases fin4 i with rfl | rfl | rfl | rfl <;>
      rcases fin4 j with rfl | rfl | rfl | rfl <;>
      simp [middle,relabel,reverse,Forks.rotate3102,root,mutate,ofSix,correction] <;> grind
  have hr : IsRoot (relabel (reverse (mutate (middle a b) 3)) Forks.rotate3102) 0 := by
    rw [heq]
    exact IsRoot.basic _ _ _ _ _ _ (boundary_domain b a hb ha) (by decide)
  exact root_of_reverse (root_of_relabel Forks.rotate3102 hr)

theorem core_cyclic (a b : Int) (ha : 2 ≤ a) (hb : 2 ≤ b) (i : Fin 2) :
    ¬ Acyclic (node a b i) := by
  have hp := Int.mul_pos (show 0<a by omega) (show 0<b by omega)
  have hi : i=0 ∨ i=1 := by omega
  rcases hi with rfl | rfl
  · rintro ⟨rank,hr⟩
    have h01 := hr 0 1 (by simp [node,box,ofSix]; omega)
    have h12 := hr 1 2 (by simp [node,box,ofSix]; omega)
    have h23 := hr 2 3 (by simp [node,box,ofSix]; omega)
    have h30 := hr 3 0 (by simp [node,box,ofSix]; omega)
    omega
  · rintro ⟨rank,hr⟩
    have h10 := hr 1 0 (by simp [node,middle,ofSix]; omega)
    have h03 := hr 0 3 (by simp [node,middle,ofSix]; omega)
    have h31 := hr 3 1 (by simp [node,middle,ofSix]; grind)
    omega

theorem core_edges (a b : Int) (ha : 2 ≤ a) (hb : 2 ≤ b) (i : Fin 2) (k : Fin 4) :
    FramedCore (node a b) (mutate (node a b i) k) ∨
      IsFork (mutate (node a b i) k) k ∨ IsRoot (mutate (node a b i) k) k := by
  have hi : i=0 ∨ i=1 := by omega
  rcases hi with rfl | rfl <;> rcases fin4 k with rfl | rfl | rfl | rfl
  · left; exact ⟨1,.identity 4,box_zero a b ha hb⟩
  · left; exact ⟨1,p3210,box_one a b ha hb⟩
  · left; exact ⟨1,p2301,box_two a b ha hb⟩
  · left; exact ⟨1,p1032,box_three a b ha hb⟩
  · left; refine ⟨0,.identity 4,?_⟩
    change mutate (middle a b) 0 = box a b
    rw [← box_zero a b ha hb, mutation_involutive]
  · exact Or.inr (Or.inr (middle_one_root a b ha hb))
  · left; exact ⟨0,p1032,middle_two a b ha hb⟩
  · exact Or.inr (Or.inr (middle_three_root a b ha hb))

theorem box_NMA_from_cells (hCells : RootCellsExist) (a b : Int)
    (ha : 2 ≤ a) (hb : 2 ≤ b) : ¬ MutationAcyclic (box a b) := by
  apply framed_region_NMA hCells (node a b) ?_ (core_cyclic a b ha hb) (core_edges a b ha hb) 0
  intro i
  have hi : i=0 ∨ i=1 := by omega
  rcases hi with rfl | rfl <;> simp only [node,↓reduceIte]
  · exact ofSix_skew _ _ _ _ _ _
  · exact ofSix_skew _ _ _ _ _ _

/-- All alternating boxes are NMA, with no imported classification theorem. -/
theorem box_NMA (a b : Int) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    ¬ MutationAcyclic (box a b) :=
  box_NMA_from_cells RegionCells.root_cells_exist a b ha hb

end QuiverProofs.Box
