import QuiverProofs.GlobalFamilies
import QuiverProofs.Pendant

/-! The complete ten-phase unit-zero strip. Parameters are arbitrary integers
in the source cone. This module proves symbolic identities and local boundary
obligations; its two unswapped parents remain explicit interfaces. -/
namespace QuiverProofs.UnitZeroStrip
open TriangleRegions Regions Forks
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

private theorem fin4 (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
private theorem fin10 (i : Fin 10) :
    i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 := by omega

def Domain (x u v w : Int) : Prop := 2≤x ∧ 2≤u ∧ x<v ∧ v<w
def sum (u w : Int) : Int := u+w
def gap (x v w : Int) : Int := x*w-v
def nextU (_x _u _v w : Int) : Int := w
def nextV (x u v w : Int) : Int := x*(u+w)-v
def nextW (x u v w : Int) : Int := (x*x-1)*(u+w)-x*v

theorem bounds (x u v w : Int) (h : Domain x u v w) :
    2≤x ∧ 2≤u ∧ 3≤v ∧ 4≤w ∧ x<v ∧ v<w ∧
    w<gap x v w ∧ gap x v w<nextV x u v w ∧
    v<sum u w ∧ sum u w<nextV x u v w ∧
    nextV x u v w<nextW x u v w ∧
    u<nextW x u v w ∧ w<nextW x u v w := by
  obtain ⟨hx,hu,hv,hw⟩ := h
  have hxw := Int.mul_le_mul_of_nonneg_right hx (show 0≤w by omega)
  have hxu := Int.mul_pos (show 0<x by omega) (show 0<u by omega)
  have hxs := Int.mul_le_mul_of_nonneg_right hx (show 0≤u+w by omega)
  have hvp : u+w<nextV x u v w := by unfold nextV; omega
  have hxV := Int.mul_le_mul_of_nonneg_right hx (show 0≤nextV x u v w by omega)
  have he : nextW x u v w = x*nextV x u v w-(u+w) := by
    unfold nextV nextW; grind
  have hdist : x*(u+w)=x*u+x*w := by grind
  unfold gap nextV sum at *
  omega

theorem preserves_domain (x u v w : Int) (h : Domain x u v w) :
    Domain x (nextU x u v w) (nextV x u v w) (nextW x u v w) := by
  have := bounds x u v w h
  unfold Domain nextU
  omega

theorem inverse (x u v w : Int) :
    x*nextV x u v w-nextU x u v w-nextW x u v w=u ∧
    (x*x-1)*nextV x u v w-x*nextW x u v w=v ∧
    nextU x u v w=w := by
  simp only [nextU,nextV,nextW]
  constructor
  · grind
  constructor <;> grind

def sigma : Relabeling 4 :=
  ⟨fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | _ => 0,
   fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | _ => 0,by decide,by decide⟩

def node (x u v w : Int) (i : Fin 10) : Matrix 4 := match i.val with
  | 0 => ofSix (0) (-u) (1) (v) (-x) (w)
  | 1 => ofSix (0) (u) (-1) (v) (-x) (u+w)
  | 2 => ofSix (0) (-w) (1) (v-x*(u+w)) (x) (-u-w)
  | 3 => ofSix (0) (w) (-1) (v-x*(u+w)) (x) (-u)
  | 4 => ofSix (-x) (w) (1) (v-x*w) (-x) (u)
  | 5 => ofSix (-(-x)) (-(w)) (-(1)) (v) (-(0)) (-(-u))
  | 6 => ofSix (-(-x)) (-(u+w)) (-(-1)) (v) (-(0)) (-(u))
  | 7 => ofSix (-(x)) (-(-u-w)) (-(1)) (v-x*(u+w)) (-(0)) (-(-w))
  | 8 => ofSix (-(x)) (-(-u)) (-(-1)) (v-x*(u+w)) (-(0)) (-(w))
  | _ => ofSix (-(-x)) (-(u)) (-(1)) (v-x*w) (-(-x)) (-(w))

def swapPhase (i : Fin 10) : Fin 10 := ⟨(i.val+5)%10, by omega⟩

theorem swapped (x u v w : Int) (i : Fin 10) :
    node x u v w (swapPhase i) = relabel (node x u v w i) sigma := by
  rcases fin10 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    funext a b <;> rcases fin4 a with rfl|rfl|rfl|rfl <;>
    rcases fin4 b with rfl|rfl|rfl|rfl <;>
    simp [node,swapPhase,relabel,sigma,ofSix]

theorem node_skew (x u v w : Int) (i : Fin 10) : SkewSymmetric (node x u v w i) := by
  rcases fin10 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    exact ofSix_skew _ _ _ _ _ _

def nextPhase (i : Fin 10) : Fin 10 := ⟨(i.val+1)%10,by omega⟩
def forwardVertex (i : Fin 10) : Fin 4 := if i.val%2=0 then 0 else 3

theorem special_0 (x u v w : Int) (h : Domain x u v w) :
    mutate (node x u v w 0) 0 = node x u v w 1 := by
  have hb := bounds x u v w h
  simp only [gap,nextV,sum] at hb
  funext a b
  rcases fin4 a with rfl|rfl|rfl|rfl <;> rcases fin4 b with rfl|rfl|rfl|rfl <;>
    simp [node,mutate,correction,ofSix] <;> grind

theorem special_1 (x u v w : Int) (h : Domain x u v w) :
    mutate (node x u v w 1) 3 = node x u v w 2 := by
  have hb := bounds x u v w h
  simp only [gap,nextV,sum] at hb
  funext a b
  rcases fin4 a with rfl|rfl|rfl|rfl <;> rcases fin4 b with rfl|rfl|rfl|rfl <;>
    simp [node,mutate,correction,ofSix] <;> grind

theorem special_2 (x u v w : Int) (h : Domain x u v w) :
    mutate (node x u v w 2) 0 = node x u v w 3 := by
  have hb := bounds x u v w h
  simp only [gap,nextV,sum] at hb
  funext a b
  rcases fin4 a with rfl|rfl|rfl|rfl <;> rcases fin4 b with rfl|rfl|rfl|rfl <;>
    simp [node,mutate,correction,ofSix] <;> grind

theorem special_3 (x u v w : Int) (h : Domain x u v w) :
    mutate (node x u v w 3) 3 = node x u v w 4 := by
  have hb := bounds x u v w h
  simp only [gap,nextV,sum] at hb
  funext a b
  rcases fin4 a with rfl|rfl|rfl|rfl <;> rcases fin4 b with rfl|rfl|rfl|rfl <;>
    simp [node,mutate,correction,ofSix] <;> grind

theorem special_4 (x u v w : Int) (h : Domain x u v w) :
    mutate (node x u v w 4) 0 = node x u v w 5 := by
  have hb := bounds x u v w h
  simp only [gap,nextV,sum] at hb
  funext a b
  rcases fin4 a with rfl|rfl|rfl|rfl <;> rcases fin4 b with rfl|rfl|rfl|rfl <;>
    simp [node,mutate,correction,ofSix] <;> grind

theorem special_5 (x u v w : Int) (h : Domain x u v w) :
    mutate (node x u v w 5) 3 = node x u v w 6 := by
  have hb := bounds x u v w h
  simp only [gap,nextV,sum] at hb
  funext a b
  rcases fin4 a with rfl|rfl|rfl|rfl <;> rcases fin4 b with rfl|rfl|rfl|rfl <;>
    simp [node,mutate,correction,ofSix] <;> grind

theorem special_6 (x u v w : Int) (h : Domain x u v w) :
    mutate (node x u v w 6) 0 = node x u v w 7 := by
  have hb := bounds x u v w h
  simp only [gap,nextV,sum] at hb
  funext a b
  rcases fin4 a with rfl|rfl|rfl|rfl <;> rcases fin4 b with rfl|rfl|rfl|rfl <;>
    simp [node,mutate,correction,ofSix] <;> grind

theorem special_7 (x u v w : Int) (h : Domain x u v w) :
    mutate (node x u v w 7) 3 = node x u v w 8 := by
  have hb := bounds x u v w h
  simp only [gap,nextV,sum] at hb
  funext a b
  rcases fin4 a with rfl|rfl|rfl|rfl <;> rcases fin4 b with rfl|rfl|rfl|rfl <;>
    simp [node,mutate,correction,ofSix] <;> grind

theorem special_8 (x u v w : Int) (h : Domain x u v w) :
    mutate (node x u v w 8) 0 = node x u v w 9 := by
  have hb := bounds x u v w h
  simp only [gap,nextV,sum] at hb
  funext a b
  rcases fin4 a with rfl|rfl|rfl|rfl <;> rcases fin4 b with rfl|rfl|rfl|rfl <;>
    simp [node,mutate,correction,ofSix] <;> grind

theorem special_9 (x u v w : Int) (h : Domain x u v w) :
    mutate (node x u v w 9) 3 = node x u v w 0 := by
  have hb := bounds x u v w h
  simp only [gap,nextV,sum] at hb
  funext a b
  rcases fin4 a with rfl|rfl|rfl|rfl <;> rcases fin4 b with rfl|rfl|rfl|rfl <;>
    simp [node,mutate,correction,ofSix] <;> grind

theorem forward_step (x u v w : Int) (h : Domain x u v w) (i : Fin 10) :
    mutate (node x u v w i) (forwardVertex i) = node x u v w (nextPhase i) := by
  rcases fin10 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact special_0 x u v w h
  · exact special_1 x u v w h
  · exact special_2 x u v w h
  · exact special_3 x u v w h
  · exact special_4 x u v w h
  · exact special_5 x u v w h
  · exact special_6 x u v w h
  · exact special_7 x u v w h
  · exact special_8 x u v w h
  · exact special_9 x u v w h

theorem backward_0 (x u v w : Int) (h : Domain x u v w) :
    mutate (node x u v w 1) 0=node x u v w 0 := by
  rw [←special_0 x u v w h,mutation_involutive]

theorem backward_1 (x u v w : Int) (h : Domain x u v w) :
    mutate (node x u v w 2) 3=node x u v w 1 := by
  rw [←special_1 x u v w h,mutation_involutive]

theorem backward_2 (x u v w : Int) (h : Domain x u v w) :
    mutate (node x u v w 3) 0=node x u v w 2 := by
  rw [←special_2 x u v w h,mutation_involutive]

theorem backward_3 (x u v w : Int) (h : Domain x u v w) :
    mutate (node x u v w 4) 3=node x u v w 3 := by
  rw [←special_3 x u v w h,mutation_involutive]

theorem backward_4 (x u v w : Int) (h : Domain x u v w) :
    mutate (node x u v w 5) 0=node x u v w 4 := by
  rw [←special_4 x u v w h,mutation_involutive]

theorem backward_5 (x u v w : Int) (h : Domain x u v w) :
    mutate (node x u v w 6) 3=node x u v w 5 := by
  rw [←special_5 x u v w h,mutation_involutive]

theorem backward_6 (x u v w : Int) (h : Domain x u v w) :
    mutate (node x u v w 7) 0=node x u v w 6 := by
  rw [←special_6 x u v w h,mutation_involutive]

theorem backward_7 (x u v w : Int) (h : Domain x u v w) :
    mutate (node x u v w 8) 3=node x u v w 7 := by
  rw [←special_7 x u v w h,mutation_involutive]

theorem backward_8 (x u v w : Int) (h : Domain x u v w) :
    mutate (node x u v w 9) 0=node x u v w 8 := by
  rw [←special_8 x u v w h,mutation_involutive]

theorem backward_9 (x u v w : Int) (h : Domain x u v w) :
    mutate (node x u v w 0) 3=node x u v w 9 := by
  rw [←special_9 x u v w h,mutation_involutive]

theorem node2_one (x u v w : Int) (h : Domain x u v w) :
    mutate (node x u v w 2) 1 = node x (nextU x u v w) (nextV x u v w) (nextW x u v w) 0 := by
  have hb := bounds x u v w h
  simp only [gap,nextV,sum] at hb
  funext a b
  rcases fin4 a with rfl|rfl|rfl|rfl <;> rcases fin4 b with rfl|rfl|rfl|rfl <;>
    simp [node,nextU,nextV,nextW,mutate,correction,ofSix] <;> grind

theorem node3_one (x u v w : Int) (h : Domain x u v w) :
    mutate (node x u v w 3) 1 = node x (nextU x u v w) (nextV x u v w) (nextW x u v w) 1 := by
  have hb := bounds x u v w h
  simp only [gap,nextV,sum] at hb
  funext a b
  rcases fin4 a with rfl|rfl|rfl|rfl <;> rcases fin4 b with rfl|rfl|rfl|rfl <;>
    simp [node,nextU,nextV,nextW,mutate,correction,ofSix] <;> grind

theorem next_node0_one (x u v w : Int) (h : Domain x u v w) :
    mutate (node x (nextU x u v w) (nextV x u v w) (nextW x u v w) 0) 1 = node x u v w 2 := by
  rw [←node2_one x u v w h,mutation_involutive]

theorem next_node1_one (x u v w : Int) (h : Domain x u v w) :
    mutate (node x (nextU x u v w) (nextV x u v w) (nextW x u v w) 1) 1 = node x u v w 3 := by
  rw [←node3_one x u v w h,mutation_involutive]

theorem parent_commutation (x u v w : Int) (h : Domain x u v w) :
    mutate (node x u v w 1) 1 = mutate (mutate (node x u v w 0) 1) 0 := by
  have hb := bounds x u v w h
  simp only [gap,nextV,sum] at hb
  funext a b
  rcases fin4 a with rfl|rfl|rfl|rfl <;> rcases fin4 b with rfl|rfl|rfl|rfl <;>
    simp [node,mutate,correction,ofSix] <;> grind


theorem cyclic_0 (x u v w : Int) (h : Domain x u v w) : ¬ Acyclic (node x u v w 0) := by
  have hb := bounds x u v w h
  simp only [gap,nextV,sum] at hb
  rintro ⟨rank,hr⟩
  have h0 := hr 1 2 (by simp [node,ofSix] <;> omega)
  have h1 := hr 2 3 (by simp [node,ofSix] <;> omega)
  have h2 := hr 3 1 (by simp [node,ofSix] <;> omega)
  omega

theorem cyclic_1 (x u v w : Int) (h : Domain x u v w) : ¬ Acyclic (node x u v w 1) := by
  have hb := bounds x u v w h
  simp only [gap,nextV,sum] at hb
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (by simp [node,ofSix] <;> omega)
  have h1 := hr 2 3 (by simp [node,ofSix] <;> omega)
  have h2 := hr 3 0 (by simp [node,ofSix] <;> omega)
  omega

theorem cyclic_2 (x u v w : Int) (h : Domain x u v w) : ¬ Acyclic (node x u v w 2) := by
  have hb := bounds x u v w h
  simp only [gap,nextV,sum] at hb
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by simp [node,ofSix] <;> omega)
  have h1 := hr 3 2 (by simp [node,ofSix] <;> omega)
  have h2 := hr 2 0 (by simp [node,ofSix] <;> omega)
  omega

theorem cyclic_3 (x u v w : Int) (h : Domain x u v w) : ¬ Acyclic (node x u v w 3) := by
  have hb := bounds x u v w h
  simp only [gap,nextV,sum] at hb
  rintro ⟨rank,hr⟩
  have h0 := hr 1 3 (by simp [node,ofSix] <;> omega)
  have h1 := hr 3 2 (by simp [node,ofSix] <;> omega)
  have h2 := hr 2 1 (by simp [node,ofSix] <;> omega)
  omega

theorem cyclic_4 (x u v w : Int) (h : Domain x u v w) : ¬ Acyclic (node x u v w 4) := by
  have hb := bounds x u v w h
  simp only [gap,nextV,sum] at hb
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (by simp [node,ofSix] <;> omega)
  have h1 := hr 2 1 (by simp [node,ofSix] <;> omega)
  have h2 := hr 1 0 (by simp [node,ofSix] <;> omega)
  omega

theorem cyclic_5 (x u v w : Int) (h : Domain x u v w) : ¬ Acyclic (node x u v w 5) := by
  have hb := bounds x u v w h
  simp only [gap,nextV,sum] at hb
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (by simp [node,ofSix] <;> omega)
  have h1 := hr 1 2 (by simp [node,ofSix] <;> omega)
  have h2 := hr 2 0 (by simp [node,ofSix] <;> omega)
  omega

theorem cyclic_6 (x u v w : Int) (h : Domain x u v w) : ¬ Acyclic (node x u v w 6) := by
  have hb := bounds x u v w h
  simp only [gap,nextV,sum] at hb
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (by simp [node,ofSix] <;> omega)
  have h1 := hr 1 2 (by simp [node,ofSix] <;> omega)
  have h2 := hr 2 0 (by simp [node,ofSix] <;> omega)
  omega

theorem cyclic_7 (x u v w : Int) (h : Domain x u v w) : ¬ Acyclic (node x u v w 7) := by
  have hb := bounds x u v w h
  simp only [gap,nextV,sum] at hb
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (by simp [node,ofSix] <;> omega)
  have h1 := hr 2 1 (by simp [node,ofSix] <;> omega)
  have h2 := hr 1 0 (by simp [node,ofSix] <;> omega)
  omega

theorem cyclic_8 (x u v w : Int) (h : Domain x u v w) : ¬ Acyclic (node x u v w 8) := by
  have hb := bounds x u v w h
  simp only [gap,nextV,sum] at hb
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (by simp [node,ofSix] <;> omega)
  have h1 := hr 2 1 (by simp [node,ofSix] <;> omega)
  have h2 := hr 1 0 (by simp [node,ofSix] <;> omega)
  omega

theorem cyclic_9 (x u v w : Int) (h : Domain x u v w) : ¬ Acyclic (node x u v w 9) := by
  have hb := bounds x u v w h
  simp only [gap,nextV,sum] at hb
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (by simp [node,ofSix] <;> omega)
  have h1 := hr 1 3 (by simp [node,ofSix] <;> omega)
  have h2 := hr 3 0 (by simp [node,ofSix] <;> omega)
  omega

theorem node_cyclic (x u v w : Int) (h : Domain x u v w) (i : Fin 10) :
    ¬ Acyclic (node x u v w i) := by
  rcases fin10 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact cyclic_0 x u v w h
  · exact cyclic_1 x u v w h
  · exact cyclic_2 x u v w h
  · exact cyclic_3 x u v w h
  · exact cyclic_4 x u v w h
  · exact cyclic_5 x u v w h
  · exact cyclic_6 x u v w h
  · exact cyclic_7 x u v w h
  · exact cyclic_8 x u v w h
  · exact cyclic_9 x u v w h


private theorem boundary_bounds (x u v w : Int) (h : Domain x u v w) :
    u<u*v ∧ v<u*v ∧ v<v*w-x ∧ w<v*w-x ∧
    u<u*(u+w)-1 ∧ u+w<u*(u+w)-1 ∧
    v<v*(u+w)-x ∧ u+w<v*(u+w)-x ∧
    w<w*(u+w)-1 ∧ u+w<w*(u+w)-1 ∧
    nextV x u v w<nextV x u v w*(u+w)-x ∧
    u+w<nextV x u v w*(u+w)-x ∧
    w<w*nextV x u v w ∧ nextV x u v w<w*nextV x u v w ∧
    u<nextV x u v w*u-x ∧ nextV x u v w<nextV x u v w*u-x ∧
    x<x*gap x v w-w ∧ gap x v w<x*gap x v w-w ∧
    x<x*x-1 ∧ w<w*gap x v w-x ∧ gap x v w<w*gap x v w-x ∧
    u<1+w*u ∧ w<1+w*u := by
  have hb := bounds x u v w h
  unfold sum at hb
  have h0 := Forks.product_add_dominates u v 0 (by omega) (by omega) (by omega)
  have h1 := Forks.product_sub_dominates v w x (by omega) (by omega) (by omega)
  have h2 := Forks.product_sub_dominates u (u+w) 1 (by omega) (by omega) (by omega)
  have h3 := Forks.product_sub_dominates v (u+w) x (by omega) (by omega) (by omega)
  have h4 := Forks.product_sub_dominates w (u+w) 1 (by omega) (by omega) (by omega)
  have h5 := Forks.product_sub_dominates (u+w) (nextV x u v w) x (by omega) (by omega) (by omega)
  have h6 := Forks.product_add_dominates w (nextV x u v w) 0 (by omega) (by omega) (by omega)
  have h7 := Forks.product_sub_dominates u (nextV x u v w) x (by omega) (by omega) (by omega)
  have h8 := Forks.product_sub_dominates x (gap x v w) w (by omega) (by omega) (by omega)
  have h9 := Int.mul_le_mul_of_nonneg_right hb.1 (show 0≤x by omega)
  have h10 := Forks.product_sub_dominates w (gap x v w) x (by omega) (by omega) (by omega)
  have h11 := Forks.product_add_dominates w u 1 (by omega) (by omega) (by omega)
  simp only [Int.mul_comm (nextV x u v w) (u+w),Int.mul_comm (nextV x u v w) u]
  omega

private def frame2103 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | _ => 3),(fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | _ => 3),by decide,by decide⟩

theorem node0_2_root (x u v w : Int) (h : Domain x u v w) :
    Regions.IsRoot (mutate (node x u v w 0) 2) 2 := by
  have hb := bounds x u v w h
  have hh := boundary_bounds x u v w h
  simp only [gap,nextV,sum] at hb hh
  have heq : relabel (mutate (node x u v w 0) 2) frame2103 = Regions.root (-(-v)) (-(-u*v)) (v*w-x) (-(-(u))) (-(-w)) (1) := by
    funext a b
    rcases fin4 a with rfl|rfl|rfl|rfl <;> rcases fin4 b with rfl|rfl|rfl|rfl <;>
      simp [node,Regions.root,relabel,reverse,frame2103,mutate,correction,ofSix,gap,nextV] <;> grind
  have hf : Regions.IsRoot (relabel (mutate (node x u v w 0) 2) frame2103) 0 := by
    rw [heq]
    apply Regions.IsRoot.basic
    · simp only [Regions.Domain,gap,nextV]; grind
    · decide
  exact Regions.root_of_relabel frame2103 hf

private def frame2301 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | _ => 1),(fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | _ => 1),by decide,by decide⟩

theorem node1_2_root (x u v w : Int) (h : Domain x u v w) :
    Regions.IsRoot (mutate (node x u v w 1) 2) 2 := by
  have hb := bounds x u v w h
  have hh := boundary_bounds x u v w h
  simp only [gap,nextV,sum] at hb hh
  have heq : relabel (reverse (mutate (node x u v w 1) 2)) frame2301 = Regions.root (-(-u-w)) (-(-(u*(u+w)-1))) (-(-(v*(u+w)-x))) (-(-(-(-u)))) (-(-(-(-v)))) (-(0)) := by
    funext a b
    rcases fin4 a with rfl|rfl|rfl|rfl <;> rcases fin4 b with rfl|rfl|rfl|rfl <;>
      simp [node,Regions.root,relabel,reverse,frame2301,mutate,correction,ofSix,gap,nextV] <;> grind
  have hf : Regions.IsRoot (relabel (reverse (mutate (node x u v w 1) 2)) frame2301) 0 := by
    rw [heq]
    apply Regions.IsRoot.basic
    · simp only [Regions.Domain,gap,nextV]; grind
    · decide
  exact Regions.root_of_reverse (Regions.root_of_relabel frame2301 hf)

theorem node2_2_root (x u v w : Int) (h : Domain x u v w) :
    Regions.IsRoot (mutate (node x u v w 2) 2) 2 := by
  have hb := bounds x u v w h
  have hh := boundary_bounds x u v w h
  simp only [gap,nextV,sum] at hb hh
  have heq : relabel (mutate (node x u v w 2) 2) frame2301 = Regions.root (u+w) (-(1-w*(u+w))) (-(x-(nextV x u v w)*(u+w))) (-(-(w))) (-(-(nextV x u v w))) (0) := by
    funext a b
    rcases fin4 a with rfl|rfl|rfl|rfl <;> rcases fin4 b with rfl|rfl|rfl|rfl <;>
      simp [node,Regions.root,relabel,reverse,frame2301,mutate,correction,ofSix,gap,nextV] <;> grind
  have hf : Regions.IsRoot (relabel (mutate (node x u v w 2) 2) frame2301) 0 := by
    rw [heq]
    apply Regions.IsRoot.basic
    · simp only [Regions.Domain,gap,nextV]; grind
    · decide
  exact Regions.root_of_relabel frame2301 hf

theorem node3_2_root (x u v w : Int) (h : Domain x u v w) :
    Regions.IsRoot (mutate (node x u v w 3) 2) 2 := by
  have hb := bounds x u v w h
  have hh := boundary_bounds x u v w h
  simp only [gap,nextV,sum] at hb hh
  have heq : relabel (reverse (mutate (node x u v w 3) 2)) frame2103 = Regions.root (-(-(nextV x u v w))) (-(-(w*(nextV x u v w)))) (-(x-(nextV x u v w)*u)) (-(-(-(-w)))) (-(-(u))) (-(-1)) := by
    funext a b
    rcases fin4 a with rfl|rfl|rfl|rfl <;> rcases fin4 b with rfl|rfl|rfl|rfl <;>
      simp [node,Regions.root,relabel,reverse,frame2103,mutate,correction,ofSix,gap,nextV] <;> grind
  have hf : Regions.IsRoot (relabel (reverse (mutate (node x u v w 3) 2)) frame2103) 0 := by
    rw [heq]
    apply Regions.IsRoot.basic
    · simp only [Regions.Domain,gap,nextV]; grind
    · decide
  exact Regions.root_of_reverse (Regions.root_of_relabel frame2103 hf)

private def frame1023 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | _ => 3),(fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | _ => 3),by decide,by decide⟩

theorem node4_1_fork (x u v w : Int) (h : Domain x u v w) :
    Forks.IsFork (mutate (node x u v w 4) 1) 1 := by
  have hb := bounds x u v w h
  have hh := boundary_bounds x u v w h
  simp only [gap,nextV,sum] at hb hh
  have heq : relabel (mutate (node x u v w 4) 1) frame1023 = Forks.template (-(-(x))) (gap x v w) (x) (-(w-x*(gap x v w))) (-(1-x*x)) (u) := by
    funext a b
    rcases fin4 a with rfl|rfl|rfl|rfl <;> rcases fin4 b with rfl|rfl|rfl|rfl <;>
      simp [node,Forks.template,relabel,reverse,frame1023,mutate,correction,ofSix,gap,nextV] <;> grind
  have hf : Forks.IsFork (relabel (mutate (node x u v w 4) 1) frame1023) 0 := by
    rw [heq]
    apply Forks.IsFork.basic
    simp only [Forks.Domain,gap,nextV]
    grind
  exact Forks.fork_of_relabel frame1023 hf

private def frame2013 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 1 | _ => 3),(fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 0 | _ => 3),by decide,by decide⟩

theorem node4_2_fork (x u v w : Int) (h : Domain x u v w) :
    Forks.IsFork (mutate (node x u v w 4) 2) 2 := by
  have hb := bounds x u v w h
  have hh := boundary_bounds x u v w h
  simp only [gap,nextV,sum] at hb hh
  have heq : relabel (reverse (mutate (node x u v w 4) 2)) frame2013 = Forks.template (-(-(-(-w)))) (-(-(gap x v w))) (-(-u)) (-(-(w*(gap x v w)-x))) (-(-(1+w*u))) (-(-x)) := by
    funext a b
    rcases fin4 a with rfl|rfl|rfl|rfl <;> rcases fin4 b with rfl|rfl|rfl|rfl <;>
      simp [node,Forks.template,relabel,reverse,frame2013,mutate,correction,ofSix,gap,nextV] <;> grind
  have hf : Forks.IsFork (relabel (reverse (mutate (node x u v w 4) 2)) frame2013) 0 := by
    rw [heq]
    apply Forks.IsFork.basic
    simp only [Forks.Domain,gap,nextV]
    grind
  exact Forks.fork_of_reverse (Forks.fork_of_relabel frame2013 hf)


/-- Selected retained mutation and printed phase level for triangle descent. -/
def inward (i : Fin 10) : Fin 4 := match i.val with
  | 0 => 1 | 1 => 1 | 2 => 3 | 3 => 3 | 4 => 0
  | 5 => 1 | 6 => 1 | 7 => 0 | 8 => 0 | _ => 3

def level (i : Fin 10) : Nat := match i.val with
  | 2 => 1 | 3 => 2 | 4 => 1 | 7 => 1 | 8 => 2 | 9 => 1 | _ => 0

private theorem triangle_reconstruct (Q : Matrix 3) (hQ : SkewSymmetric Q) :
    Q=cycleThree (Q 0 1) (Q 1 2) (Q 2 0) := by
  funext i j
  have hi : i=0 ∨ i=1 ∨ i=2 := by omega
  have hj : j=0 ∨ j=1 ∨ j=2 := by omega
  rcases hi with rfl|rfl|rfl <;> rcases hj with rfl|rfl|rfl <;>
    simp [cycleThree] <;>
    have := hQ 0 0 <;> have := hQ 1 1 <;> have := hQ 2 2 <;>
    have := hQ 1 0 <;> have := hQ 2 1 <;> have := hQ 0 2 <;> omega

private theorem node4_deletion (x u v w : Int) (h : Domain x u v w) :
    DeletionAcyclic (node x u v w 4) 0 := by
  have hb := bounds x u v w h
  obtain ⟨hx,hu,hv,hw⟩ := h
  simp only [gap,nextV,sum] at hb
  refine ⟨fun i => match i.val with | 1 => 2 | 3 => 1 | _ => 0,?_⟩
  intro i j hi hj hij
  rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp_all [node,ofSix] <;> omega

private theorem node9_deletion (x u v w : Int) (h : Domain x u v w) :
    DeletionAcyclic (node x u v w 9) 3 := by
  have hh := deletion_relabel (node x u v w 4) 0 sigma (node4_deletion x u v w h)
  rw [←swapped x u v w 4] at hh
  exact hh

/-- The deleted triangle is MA, including the unit-edge cyclic cases.
This is the separate retained-triangle premise, not a cyclicity inference. -/
theorem deletionMA (x u v w : Int) (h : Domain x u v w) (i : Fin 10) :
    Pendant.DeletionMA (node x u v w i) (inward i) := by
  intro e he hav
  by_cases h4 : i=4
  · subst i
    obtain ⟨rank,hr⟩ := node4_deletion x u v w h
    exact acyclic_is_mutationAcyclic _ ⟨rank ∘ e,fun a b hab => hr _ _ (hav a) (hav b) hab⟩
  by_cases h9 : i=9
  · subst i
    obtain ⟨rank,hr⟩ := node9_deletion x u v w h
    exact acyclic_is_mutationAcyclic _ ⟨rank ∘ e,fun a b hab => hr _ _ (hav a) (hav b) hab⟩
  rw [triangle_reconstruct _ (restrict_skew _ _ (node_skew x u v w i))]
  apply GlobalFamilies.weak_triangle_MA
  have h0 := hav 0
  have h1 := hav 1
  have h2 := hav 2
  have he01 : e 0≠e 1 := fun hh => (by have := he hh; omega)
  have he02 : e 0≠e 2 := fun hh => (by have := he hh; omega)
  have he12 : e 1≠e 2 := fun hh => (by have := he hh; omega)
  rcases fin10 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    rcases fin4 (e 0) with h0e|h0e|h0e|h0e <;>
    rcases fin4 (e 1) with h1e|h1e|h1e|h1e <;>
    rcases fin4 (e 2) with h2e|h2e|h2e|h2e <;>
    simp_all [node,ofSix,inward,restrict] <;> omega

/-- The general transfer used by both new local regions. -/
theorem triangles_from_deletionMA (Q : Matrix 4) (r : Fin 4)
    (hd : Pendant.DeletionMA Q r) (hp : AllTrianglesMA (mutate Q r)) :
    AllTrianglesMA Q := by
  intro e he
  by_cases hret : ∃ k, e k=r
  · obtain ⟨k,hk⟩ := hret
    exact retained_triangle_transfer Q r hp e he k hk
  · exact hd e he (by grind)

structure Parameters where
  u : Int
  v : Int
  w : Int

def step (x : Int) (p : Parameters) : Parameters :=
  ⟨nextU x p.u p.v p.w,nextV x p.u p.v p.w,nextW x p.u p.v p.w⟩

def orbit (x : Int) (p : Parameters) : Nat → Parameters
  | 0 => p
  | n+1 => step x (orbit x p n)

theorem orbit_domain (x : Int) (p : Parameters) (h : Domain x p.u p.v p.w) (n : Nat) :
    Domain x (orbit x p n).u (orbit x p n).v (orbit x p n).w := by
  induction n with
  | zero => exact h
  | succ n ih => exact preserves_domain _ _ _ _ ih

def strip (x : Int) (p : Parameters) (n : Nat) (i : Fin 10) : Matrix 4 :=
  node x (orbit x p n).u (orbit x p n).v (orbit x p n).w i

def parent (x : Int) (p : Parameters) (j : Fin 2) : Matrix 4 :=
  mutate (strip x p 0 (if j=0 then 0 else 1)) 1

def descentRank (n : Nat) (i : Fin 10) : Nat := 3*n+level i


def FramedStrip (x : Int) (p : Parameters) (Q : Matrix 4) : Prop :=
  ∃ n i, ∃ f : Relabeling 4, Q=relabel (strip x p n i) f

def FramedParent (x : Int) (p : Parameters) (Q : Matrix 4) : Prop :=
  ∃ j, ∃ f : Relabeling 4, Q=relabel (parent x p j) f

def Exit (x : Int) (p : Parameters) (Q : Matrix 4) (k : Fin 4) : Prop :=
  FramedStrip x p (mutate Q k) ∨ FramedParent x p (mutate Q k) ∨
  Forks.IsFork (mutate Q k) k ∨ Regions.IsRoot (mutate Q k) k

theorem exit_relabel (x : Int) (p : Parameters) (Q : Matrix 4) (f : Relabeling 4)
    (k : Fin 4) (h : Exit x p Q (f.toFun k)) : Exit x p (relabel Q f) k := by
  unfold Exit
  rw [mutate_relabel]
  rcases h with ⟨n,i,g,hg⟩|⟨j,g,hg⟩|hf|hr
  · left; exact ⟨n,i,g.trans f,by rw [hg]; rfl⟩
  · right; left; exact ⟨j,g.trans f,by rw [hg]; rfl⟩
  · right; right; left
    simpa only [f.left_inv] using Forks.IsFork.relabelled hf f
  · right; right; right
    simpa only [f.left_inv] using Regions.IsRoot.relabelled hr f

theorem node0_edges (x : Int) (p : Parameters) (h : Domain x p.u p.v p.w)
    (n : Nat) (k : Fin 4) : Exit x p (strip x p n 0) k := by
  have hd := orbit_domain x p h n
  rcases fin4 k with rfl|rfl|rfl|rfl
  · left; exact ⟨n,1,.identity 4,special_0 _ _ _ _ hd⟩
  · cases n with
    | zero => right; left; exact ⟨0,.identity 4,rfl⟩
    | succ n => left; exact ⟨n,2,.identity 4,next_node0_one _ _ _ _ (orbit_domain x p h n)⟩
  · right; right; right; exact node0_2_root _ _ _ _ hd
  · left; exact ⟨n,9,.identity 4,backward_9 _ _ _ _ hd⟩

theorem node1_edges (x : Int) (p : Parameters) (h : Domain x p.u p.v p.w)
    (n : Nat) (k : Fin 4) : Exit x p (strip x p n 1) k := by
  have hd := orbit_domain x p h n
  rcases fin4 k with rfl|rfl|rfl|rfl
  · left; exact ⟨n,0,.identity 4,backward_0 _ _ _ _ hd⟩
  · cases n with
    | zero => right; left; exact ⟨1,.identity 4,rfl⟩
    | succ n => left; exact ⟨n,3,.identity 4,next_node1_one _ _ _ _ (orbit_domain x p h n)⟩
  · right; right; right; exact node1_2_root _ _ _ _ hd
  · left; exact ⟨n,2,.identity 4,special_1 _ _ _ _ hd⟩

theorem node2_edges (x : Int) (p : Parameters) (h : Domain x p.u p.v p.w)
    (n : Nat) (k : Fin 4) : Exit x p (strip x p n 2) k := by
  have hd := orbit_domain x p h n
  rcases fin4 k with rfl|rfl|rfl|rfl
  · left; exact ⟨n,3,.identity 4,special_2 _ _ _ _ hd⟩
  · left; exact ⟨n+1,0,.identity 4,node2_one _ _ _ _ hd⟩
  · right; right; right; exact node2_2_root _ _ _ _ hd
  · left; exact ⟨n,1,.identity 4,backward_1 _ _ _ _ hd⟩

theorem node3_edges (x : Int) (p : Parameters) (h : Domain x p.u p.v p.w)
    (n : Nat) (k : Fin 4) : Exit x p (strip x p n 3) k := by
  have hd := orbit_domain x p h n
  rcases fin4 k with rfl|rfl|rfl|rfl
  · left; exact ⟨n,2,.identity 4,backward_2 _ _ _ _ hd⟩
  · left; exact ⟨n+1,1,.identity 4,node3_one _ _ _ _ hd⟩
  · right; right; right; exact node3_2_root _ _ _ _ hd
  · left; exact ⟨n,4,.identity 4,special_3 _ _ _ _ hd⟩

theorem node4_edges (x : Int) (p : Parameters) (h : Domain x p.u p.v p.w)
    (n : Nat) (k : Fin 4) : Exit x p (strip x p n 4) k := by
  have hd := orbit_domain x p h n
  rcases fin4 k with rfl|rfl|rfl|rfl
  · left; exact ⟨n,5,.identity 4,special_4 _ _ _ _ hd⟩
  · right; right; left; exact node4_1_fork _ _ _ _ hd
  · right; right; left; exact node4_2_fork _ _ _ _ hd
  · left; exact ⟨n,3,.identity 4,backward_3 _ _ _ _ hd⟩

theorem all_edges (x : Int) (p : Parameters) (h : Domain x p.u p.v p.w)
    (n : Nat) (i : Fin 10) (k : Fin 4) : Exit x p (strip x p n i) k := by
  rcases fin10 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact node0_edges x p h n k
  · exact node1_edges x p h n k
  · exact node2_edges x p h n k
  · exact node3_edges x p h n k
  · exact node4_edges x p h n k
  · have he : strip x p n 5=relabel (strip x p n 0) sigma := swapped _ _ _ _ 0
    rw [he]
    exact exit_relabel x p (strip x p n 0) sigma k (node0_edges x p h n (sigma.toFun k))
  · have he : strip x p n 6=relabel (strip x p n 1) sigma := swapped _ _ _ _ 1
    rw [he]
    exact exit_relabel x p (strip x p n 1) sigma k (node1_edges x p h n (sigma.toFun k))
  · have he : strip x p n 7=relabel (strip x p n 2) sigma := swapped _ _ _ _ 2
    rw [he]
    exact exit_relabel x p (strip x p n 2) sigma k (node2_edges x p h n (sigma.toFun k))
  · have he : strip x p n 8=relabel (strip x p n 3) sigma := swapped _ _ _ _ 3
    rw [he]
    exact exit_relabel x p (strip x p n 3) sigma k (node3_edges x p h n (sigma.toFun k))
  · have he : strip x p n 9=relabel (strip x p n 4) sigma := swapped _ _ _ _ 4
    rw [he]
    exact exit_relabel x p (strip x p n 4) sigma k (node4_edges x p h n (sigma.toFun k))

/-- Retained inward steps land at a strictly smaller strip address, or at
one of the two explicit parents (with the fixed special swap permitted). -/
theorem inward_descent (x : Int) (p : Parameters) (h : Domain x p.u p.v p.w)
    (n : Nat) (i : Fin 10) :
    (∃ n' i', descentRank n' i' < descentRank n i ∧
      mutate (strip x p n i) (inward i)=strip x p n' i') ∨
    FramedParent x p (mutate (strip x p n i) (inward i)) := by
  have hd := orbit_domain x p h n
  rcases fin10 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · cases n with
    | zero => right; exact ⟨0,.identity 4,rfl⟩
    | succ n => left; exact ⟨n,2,by simp [descentRank,level];omega,next_node0_one _ _ _ _ (orbit_domain x p h n)⟩
  · cases n with
    | zero => right; exact ⟨1,.identity 4,rfl⟩
    | succ n => left; exact ⟨n,3,by simp [descentRank,level];omega,next_node1_one _ _ _ _ (orbit_domain x p h n)⟩
  · left; exact ⟨n,1,by simp [descentRank,level],backward_1 _ _ _ _ hd⟩
  · left; exact ⟨n,4,by simp [descentRank,level],special_3 _ _ _ _ hd⟩
  · left; exact ⟨n,5,by simp [descentRank,level],special_4 _ _ _ _ hd⟩
  · cases n with
    | zero =>
      right; refine ⟨0,sigma,?_⟩
      change mutate (node x p.u p.v p.w 5) 1 = relabel (mutate (node x p.u p.v p.w 0) 1) sigma
      rw [show node x p.u p.v p.w 5=relabel (node x p.u p.v p.w 0) sigma from swapped _ _ _ _ 0,mutate_relabel]
      rfl
    | succ n =>
      left; refine ⟨n,7,by simp [descentRank,level];omega,?_⟩
      have he : strip x p (n+1) 5=relabel (strip x p (n+1) 0) sigma := swapped _ _ _ _ 0
      change mutate (strip x p (n+1) 5) 1 = strip x p n 7
      rw [he,mutate_relabel]
      change relabel (mutate (strip x p (n+1) 0) 1) sigma = strip x p n 7
      have hh : mutate (strip x p (n+1) 0) 1=strip x p n 2 := next_node0_one _ _ _ _ (orbit_domain x p h n)
      rw [hh]
      exact (swapped _ _ _ _ 2).symm
  · cases n with
    | zero =>
      right; refine ⟨1,sigma,?_⟩
      change mutate (node x p.u p.v p.w 6) 1 = relabel (mutate (node x p.u p.v p.w 1) 1) sigma
      rw [show node x p.u p.v p.w 6=relabel (node x p.u p.v p.w 1) sigma from swapped _ _ _ _ 1,mutate_relabel]
      rfl
    | succ n =>
      left; refine ⟨n,8,by simp [descentRank,level];omega,?_⟩
      have he : strip x p (n+1) 6=relabel (strip x p (n+1) 1) sigma := swapped _ _ _ _ 1
      change mutate (strip x p (n+1) 6) 1 = strip x p n 8
      rw [he,mutate_relabel]
      change relabel (mutate (strip x p (n+1) 1) 1) sigma = strip x p n 8
      have hh : mutate (strip x p (n+1) 1) 1=strip x p n 3 := next_node1_one _ _ _ _ (orbit_domain x p h n)
      rw [hh]
      exact (swapped _ _ _ _ 3).symm
  · left; exact ⟨n,6,by simp [descentRank,level],backward_6 _ _ _ _ hd⟩
  · left; exact ⟨n,9,by simp [descentRank,level],special_8 _ _ _ _ hd⟩
  · left; exact ⟨n,0,by simp [descentRank,level],special_9 _ _ _ _ hd⟩
theorem strip_skew (x : Int) (p : Parameters) (n : Nat) (i : Fin 10) :
    SkewSymmetric (strip x p n i) := node_skew _ _ _ _ i

theorem parent_skew (x : Int) (p : Parameters) (j : Fin 2) :
    SkewSymmetric (parent x p j) :=
  mutation_preserves_skew _ 1 (strip_skew x p 0 (if j=0 then 0 else 1))

theorem strip_cyclic (x : Int) (p : Parameters) (h : Domain x p.u p.v p.w)
    (n : Nat) (i : Fin 10) : ¬ Acyclic (strip x p n i) :=
  node_cyclic _ _ _ _ (orbit_domain x p h n) i

end QuiverProofs.UnitZeroStrip
