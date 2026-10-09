import QuiverProofs.RegionCells

/- Generated candidate formulas are proved for all a,b,c ≥ 2 by Lean. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace QuiverProofs.ResidualFamily
open Forks Regions RegionSemantics

def perm0 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | _ => 3), (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | _ => 3), by decide, by decide⟩

def perm1 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | _ => 2), (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | _ => 2), by decide, by decide⟩

def perm2 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | _ => 3), (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | _ => 3), by decide, by decide⟩

def perm3 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | _ => 1), (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | _ => 2), by decide, by decide⟩

def perm4 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | _ => 2), (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | _ => 1), by decide, by decide⟩

def perm5 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | _ => 1), (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | _ => 1), by decide, by decide⟩

def perm6 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | _ => 3), (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | _ => 3), by decide, by decide⟩

def perm7 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | _ => 2), (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | _ => 2), by decide, by decide⟩

def perm8 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 0 | _ => 3), (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 1 | _ => 3), by decide, by decide⟩

def perm9 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | _ => 0), (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | _ => 2), by decide, by decide⟩

def perm10 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 0 | _ => 2), (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 3 | _ => 1), by decide, by decide⟩

def perm11 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | _ => 0), (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | _ => 1), by decide, by decide⟩

def perm12 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 1 | _ => 3), (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 0 | _ => 3), by decide, by decide⟩

def perm13 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 3 | _ => 1), (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 0 | _ => 2), by decide, by decide⟩

def perm14 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | _ => 3), (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | _ => 3), by decide, by decide⟩

def perm15 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 3 | _ => 0), (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 0 | _ => 2), by decide, by decide⟩

def perm16 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | _ => 1), (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | _ => 1), by decide, by decide⟩

def perm17 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | _ => 0), (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | _ => 1), by decide, by decide⟩

def perm18 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | _ => 2), (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | _ => 0), by decide, by decide⟩

def perm19 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | _ => 1), (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | _ => 0), by decide, by decide⟩

def perm20 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 0 | _ => 2), (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 3 | _ => 0), by decide, by decide⟩

def perm21 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | _ => 0), (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | _ => 0), by decide, by decide⟩

def perm22 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | _ => 1), (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | _ => 0), by decide, by decide⟩

def perm23 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | _ => 0), (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | _ => 0), by decide, by decide⟩

private theorem fin4 (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega

theorem product_minus_one (x y : Int) (hx : 2 ≤ x) (hy : 2 ≤ y) :
    x < x*y-1 ∧ y < x*y-1 := by
  have h₁ := Int.mul_le_mul_of_nonneg_left hy (show 0 ≤ x by omega)
  have h₂ := Int.mul_le_mul_of_nonneg_right hx (show 0 ≤ y by omega)
  constructor <;> omega

def node (a b c : Int) (i : Fin 14) : Matrix 4 := match i.val with
  | 0 => (ofSix ((-1)*c) ((-1)*b) ((-1)*a) (1) ((-1)) (1))
  | 1 => (ofSix ((-1)*c) ((-1)) (1) (a) (b) ((-1)))
  | 2 => (ofSix ((-1)*c + (-1)*a) ((-1)*b) (c) (0) ((-1)) (1))
  | 3 => (ofSix ((-1)*c + (-1)*b) ((-1)*a) (b) (0) ((-1)) (1))
  | 4 => (ofSix ((-1)*c) ((-1)*b + (-1)*a) (a) (0) (1) ((-1)))
  | 5 => (ofSix ((-1)*c + (-1)*b) (0) (1) (a) ((-1)*c) ((-1)))
  | 6 => (ofSix ((-1)*c + (-1)*a) (0) (1) (b) ((-1)*a) ((-1)))
  | 7 => (ofSix ((-1)*c) ((-1)) (0) ((-1)*b) (b + a) ((-1)))
  | 8 => (ofSix ((-1)*c + (-1)*a) (0) (1) ((-1)*b) ((-1)*a) (1))
  | 9 => (ofSix ((-1)*c + (-1)*a) (b) (c) (0) ((-1)) ((-1)))
  | 10 => (ofSix ((-1)*c + (-1)*b) (0) (1) ((-1)*a) ((-1)*c) (1))
  | 11 => (ofSix ((-1)*c + (-1)*b) (a) (b) (0) ((-1)) ((-1)))
  | 12 => (ofSix ((-1)*c) ((-1)) (0) (a) ((-1)*b + (-1)*a) (1))
  | _ => (ofSix ((-1)*c) ((-1)*b) (b + a) (1) (0) ((-1)))

theorem cyclic0 (a b c : Int) (_ha : 2≤a) (_hb : 2≤b) (_hc : 2≤c) : ¬ Acyclic (node a b c 0) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 1 2 (by simp [node,ofSix] <;> omega)
  have h1 := hr 2 3 (by simp [node,ofSix] <;> omega)
  have h2 := hr 3 1 (by simp [node,ofSix] <;> omega)
  omega

theorem edge0_0 (a b c : Int) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) :
    FramedCore (node a b c) (mutate (node a b c 0) 0) ∨
      IsFork (mutate (node a b c 0) 0) 0 ∨ IsRoot (mutate (node a b c 0) 0) 0 := by
  left; refine ⟨1,perm7,?_⟩
  funext u v
  rcases fin4 u with rfl | rfl | rfl | rfl <;>
    rcases fin4 v with rfl | rfl | rfl | rfl <;>
    simp [node,relabel,perm7,mutate,ofSix,correction] <;> grind

theorem edge0_1 (a b c : Int) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) :
    FramedCore (node a b c) (mutate (node a b c 0) 1) ∨
      IsFork (mutate (node a b c 0) 1) 1 ∨ IsRoot (mutate (node a b c 0) 1) 1 := by
  left; refine ⟨2,perm5,?_⟩
  funext u v
  rcases fin4 u with rfl | rfl | rfl | rfl <;>
    rcases fin4 v with rfl | rfl | rfl | rfl <;>
    simp [node,relabel,perm5,mutate,ofSix,correction] <;> grind

theorem edge0_2 (a b c : Int) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) :
    FramedCore (node a b c) (mutate (node a b c 0) 2) ∨
      IsFork (mutate (node a b c 0) 2) 2 ∨ IsRoot (mutate (node a b c 0) 2) 2 := by
  left; refine ⟨3,perm1,?_⟩
  funext u v
  rcases fin4 u with rfl | rfl | rfl | rfl <;>
    rcases fin4 v with rfl | rfl | rfl | rfl <;>
    simp [node,relabel,perm1,mutate,ofSix,correction] <;> grind

theorem edge0_3 (a b c : Int) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) :
    FramedCore (node a b c) (mutate (node a b c 0) 3) ∨
      IsFork (mutate (node a b c 0) 3) 3 ∨ IsRoot (mutate (node a b c 0) 3) 3 := by
  left; refine ⟨4,perm0,?_⟩
  funext u v
  rcases fin4 u with rfl | rfl | rfl | rfl <;>
    rcases fin4 v with rfl | rfl | rfl | rfl <;>
    simp [node,relabel,perm0,mutate,ofSix,correction] <;> grind

theorem cyclic1 (a b c : Int) (_ha : 2≤a) (_hb : 2≤b) (_hc : 2≤c) : ¬ Acyclic (node a b c 1) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by simp [node,ofSix] <;> omega)
  have h1 := hr 3 2 (by simp [node,ofSix] <;> omega)
  have h2 := hr 2 0 (by simp [node,ofSix] <;> omega)
  omega

theorem edge1_0 (a b c : Int) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) :
    FramedCore (node a b c) (mutate (node a b c 1) 0) ∨
      IsFork (mutate (node a b c 1) 0) 0 ∨ IsRoot (mutate (node a b c 1) 0) 0 := by
  left; refine ⟨5,perm21,?_⟩
  funext u v
  rcases fin4 u with rfl | rfl | rfl | rfl <;>
    rcases fin4 v with rfl | rfl | rfl | rfl <;>
    simp [node,relabel,perm21,mutate,ofSix,correction] <;> grind

theorem edge1_1 (a b c : Int) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) :
    FramedCore (node a b c) (mutate (node a b c 1) 1) ∨
      IsFork (mutate (node a b c 1) 1) 1 ∨ IsRoot (mutate (node a b c 1) 1) 1 := by
  left; refine ⟨0,perm7,?_⟩
  funext u v
  rcases fin4 u with rfl | rfl | rfl | rfl <;>
    rcases fin4 v with rfl | rfl | rfl | rfl <;>
    simp [node,relabel,perm7,mutate,ofSix,correction] <;> grind

theorem edge1_2 (a b c : Int) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) :
    FramedCore (node a b c) (mutate (node a b c 1) 2) ∨
      IsFork (mutate (node a b c 1) 2) 2 ∨ IsRoot (mutate (node a b c 1) 2) 2 := by
  left; refine ⟨6,perm1,?_⟩
  funext u v
  rcases fin4 u with rfl | rfl | rfl | rfl <;>
    rcases fin4 v with rfl | rfl | rfl | rfl <;>
    simp [node,relabel,perm1,mutate,ofSix,correction] <;> grind

theorem edge1_3 (a b c : Int) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) :
    FramedCore (node a b c) (mutate (node a b c 1) 3) ∨
      IsFork (mutate (node a b c 1) 3) 3 ∨ IsRoot (mutate (node a b c 1) 3) 3 := by
  left; refine ⟨7,perm1,?_⟩
  funext u v
  rcases fin4 u with rfl | rfl | rfl | rfl <;>
    rcases fin4 v with rfl | rfl | rfl | rfl <;>
    simp [node,relabel,perm1,mutate,ofSix,correction] <;> grind

theorem cyclic2 (a b c : Int) (_ha : 2≤a) (_hb : 2≤b) (_hc : 2≤c) : ¬ Acyclic (node a b c 2) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by simp [node,ofSix] <;> omega)
  have h1 := hr 3 1 (by simp [node,ofSix] <;> omega)
  have h2 := hr 1 0 (by simp [node,ofSix] <;> omega)
  omega

theorem edge2_0 (a b c : Int) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) :
    FramedCore (node a b c) (mutate (node a b c 2) 0) ∨
      IsFork (mutate (node a b c 2) 0) 0 ∨ IsRoot (mutate (node a b c 2) 0) 0 := by
  right; right
  have hd : Regions.Domain (c) ((-1) + c^2 + a*c) (1 + b*c) (c + a) (b) := by
    have hsa0 := product_minus_one a a (by omega) (by omega)
    have hpa0 := Forks.product_add_dominates a a 0 (by omega) (by omega) (by decide)
    have hsa1 := product_minus_one a b (by omega) (by omega)
    have hpa1 := Forks.product_add_dominates a b 0 (by omega) (by omega) (by decide)
    have hsa2 := product_minus_one a c (by omega) (by omega)
    have hpa2 := Forks.product_add_dominates a c 0 (by omega) (by omega) (by decide)
    have hsa3 := product_minus_one a (a+b) (by omega) (by omega)
    have hpa3 := Forks.product_add_dominates a (a+b) 0 (by omega) (by omega) (by decide)
    have hsa4 := product_minus_one a (b+c) (by omega) (by omega)
    have hpa4 := Forks.product_add_dominates a (b+c) 0 (by omega) (by omega) (by decide)
    have hsa5 := product_minus_one a (c+a) (by omega) (by omega)
    have hpa5 := Forks.product_add_dominates a (c+a) 0 (by omega) (by omega) (by decide)
    have hsb0 := product_minus_one b a (by omega) (by omega)
    have hpb0 := Forks.product_add_dominates b a 0 (by omega) (by omega) (by decide)
    have hsb1 := product_minus_one b b (by omega) (by omega)
    have hpb1 := Forks.product_add_dominates b b 0 (by omega) (by omega) (by decide)
    have hsb2 := product_minus_one b c (by omega) (by omega)
    have hpb2 := Forks.product_add_dominates b c 0 (by omega) (by omega) (by decide)
    have hsb3 := product_minus_one b (a+b) (by omega) (by omega)
    have hpb3 := Forks.product_add_dominates b (a+b) 0 (by omega) (by omega) (by decide)
    have hsb4 := product_minus_one b (b+c) (by omega) (by omega)
    have hpb4 := Forks.product_add_dominates b (b+c) 0 (by omega) (by omega) (by decide)
    have hsb5 := product_minus_one b (c+a) (by omega) (by omega)
    have hpb5 := Forks.product_add_dominates b (c+a) 0 (by omega) (by omega) (by decide)
    have hsc0 := product_minus_one c a (by omega) (by omega)
    have hpc0 := Forks.product_add_dominates c a 0 (by omega) (by omega) (by decide)
    have hsc1 := product_minus_one c b (by omega) (by omega)
    have hpc1 := Forks.product_add_dominates c b 0 (by omega) (by omega) (by decide)
    have hsc2 := product_minus_one c c (by omega) (by omega)
    have hpc2 := Forks.product_add_dominates c c 0 (by omega) (by omega) (by decide)
    have hsc3 := product_minus_one c (a+b) (by omega) (by omega)
    have hpc3 := Forks.product_add_dominates c (a+b) 0 (by omega) (by omega) (by decide)
    have hsc4 := product_minus_one c (b+c) (by omega) (by omega)
    have hpc4 := Forks.product_add_dominates c (b+c) 0 (by omega) (by omega) (by decide)
    have hsc5 := product_minus_one c (c+a) (by omega) (by omega)
    have hpc5 := Forks.product_add_dominates c (c+a) 0 (by omega) (by omega) (by decide)
    unfold Regions.Domain
    grind
  have he : relabel (reverse (mutate (node a b c 2) 0)) perm4 = root (c) ((-1) + c^2 + a*c) (1 + b*c) (c + a) (b) (0) := by
    funext u v
    rcases fin4 u with rfl | rfl | rfl | rfl <;>
      rcases fin4 v with rfl | rfl | rfl | rfl <;>
      simp [node,relabel,perm4,reverse,root,mutate,ofSix,correction] <;> grind
  have hr : IsRoot (relabel (reverse (mutate (node a b c 2) 0)) perm4) 0 := by
    rw [he]; exact IsRoot.basic _ _ _ _ _ _ hd (by decide)
  exact root_of_reverse (root_of_relabel perm4 hr)

theorem edge2_1 (a b c : Int) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) :
    FramedCore (node a b c) (mutate (node a b c 2) 1) ∨
      IsFork (mutate (node a b c 2) 1) 1 ∨ IsRoot (mutate (node a b c 2) 1) 1 := by
  left; refine ⟨8,perm6,?_⟩
  funext u v
  rcases fin4 u with rfl | rfl | rfl | rfl <;>
    rcases fin4 v with rfl | rfl | rfl | rfl <;>
    simp [node,relabel,perm6,mutate,ofSix,correction] <;> grind

theorem edge2_2 (a b c : Int) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) :
    FramedCore (node a b c) (mutate (node a b c 2) 2) ∨
      IsFork (mutate (node a b c 2) 2) 2 ∨ IsRoot (mutate (node a b c 2) 2) 2 := by
  left; refine ⟨9,perm0,?_⟩
  funext u v
  rcases fin4 u with rfl | rfl | rfl | rfl <;>
    rcases fin4 v with rfl | rfl | rfl | rfl <;>
    simp [node,relabel,perm0,mutate,ofSix,correction] <;> grind

theorem edge2_3 (a b c : Int) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) :
    FramedCore (node a b c) (mutate (node a b c 2) 3) ∨
      IsFork (mutate (node a b c 2) 3) 3 ∨ IsRoot (mutate (node a b c 2) 3) 3 := by
  left; refine ⟨0,perm5,?_⟩
  funext u v
  rcases fin4 u with rfl | rfl | rfl | rfl <;>
    rcases fin4 v with rfl | rfl | rfl | rfl <;>
    simp [node,relabel,perm5,mutate,ofSix,correction] <;> grind

theorem cyclic3 (a b c : Int) (_ha : 2≤a) (_hb : 2≤b) (_hc : 2≤c) : ¬ Acyclic (node a b c 3) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by simp [node,ofSix] <;> omega)
  have h1 := hr 3 1 (by simp [node,ofSix] <;> omega)
  have h2 := hr 1 0 (by simp [node,ofSix] <;> omega)
  omega

theorem edge3_0 (a b c : Int) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) :
    FramedCore (node a b c) (mutate (node a b c 3) 0) ∨
      IsFork (mutate (node a b c 3) 0) 0 ∨ IsRoot (mutate (node a b c 3) 0) 0 := by
  right; right
  have hd : Regions.Domain (b) ((-1) + b*c + b^2) (1 + a*b) (c + b) (a) := by
    have hsa0 := product_minus_one a a (by omega) (by omega)
    have hpa0 := Forks.product_add_dominates a a 0 (by omega) (by omega) (by decide)
    have hsa1 := product_minus_one a b (by omega) (by omega)
    have hpa1 := Forks.product_add_dominates a b 0 (by omega) (by omega) (by decide)
    have hsa2 := product_minus_one a c (by omega) (by omega)
    have hpa2 := Forks.product_add_dominates a c 0 (by omega) (by omega) (by decide)
    have hsa3 := product_minus_one a (a+b) (by omega) (by omega)
    have hpa3 := Forks.product_add_dominates a (a+b) 0 (by omega) (by omega) (by decide)
    have hsa4 := product_minus_one a (b+c) (by omega) (by omega)
    have hpa4 := Forks.product_add_dominates a (b+c) 0 (by omega) (by omega) (by decide)
    have hsa5 := product_minus_one a (c+a) (by omega) (by omega)
    have hpa5 := Forks.product_add_dominates a (c+a) 0 (by omega) (by omega) (by decide)
    have hsb0 := product_minus_one b a (by omega) (by omega)
    have hpb0 := Forks.product_add_dominates b a 0 (by omega) (by omega) (by decide)
    have hsb1 := product_minus_one b b (by omega) (by omega)
    have hpb1 := Forks.product_add_dominates b b 0 (by omega) (by omega) (by decide)
    have hsb2 := product_minus_one b c (by omega) (by omega)
    have hpb2 := Forks.product_add_dominates b c 0 (by omega) (by omega) (by decide)
    have hsb3 := product_minus_one b (a+b) (by omega) (by omega)
    have hpb3 := Forks.product_add_dominates b (a+b) 0 (by omega) (by omega) (by decide)
    have hsb4 := product_minus_one b (b+c) (by omega) (by omega)
    have hpb4 := Forks.product_add_dominates b (b+c) 0 (by omega) (by omega) (by decide)
    have hsb5 := product_minus_one b (c+a) (by omega) (by omega)
    have hpb5 := Forks.product_add_dominates b (c+a) 0 (by omega) (by omega) (by decide)
    have hsc0 := product_minus_one c a (by omega) (by omega)
    have hpc0 := Forks.product_add_dominates c a 0 (by omega) (by omega) (by decide)
    have hsc1 := product_minus_one c b (by omega) (by omega)
    have hpc1 := Forks.product_add_dominates c b 0 (by omega) (by omega) (by decide)
    have hsc2 := product_minus_one c c (by omega) (by omega)
    have hpc2 := Forks.product_add_dominates c c 0 (by omega) (by omega) (by decide)
    have hsc3 := product_minus_one c (a+b) (by omega) (by omega)
    have hpc3 := Forks.product_add_dominates c (a+b) 0 (by omega) (by omega) (by decide)
    have hsc4 := product_minus_one c (b+c) (by omega) (by omega)
    have hpc4 := Forks.product_add_dominates c (b+c) 0 (by omega) (by omega) (by decide)
    have hsc5 := product_minus_one c (c+a) (by omega) (by omega)
    have hpc5 := Forks.product_add_dominates c (c+a) 0 (by omega) (by omega) (by decide)
    unfold Regions.Domain
    grind
  have he : relabel (reverse (mutate (node a b c 3) 0)) perm4 = root (b) ((-1) + b*c + b^2) (1 + a*b) (c + b) (a) (0) := by
    funext u v
    rcases fin4 u with rfl | rfl | rfl | rfl <;>
      rcases fin4 v with rfl | rfl | rfl | rfl <;>
      simp [node,relabel,perm4,reverse,root,mutate,ofSix,correction] <;> grind
  have hr : IsRoot (relabel (reverse (mutate (node a b c 3) 0)) perm4) 0 := by
    rw [he]; exact IsRoot.basic _ _ _ _ _ _ hd (by decide)
  exact root_of_reverse (root_of_relabel perm4 hr)

theorem edge3_1 (a b c : Int) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) :
    FramedCore (node a b c) (mutate (node a b c 3) 1) ∨
      IsFork (mutate (node a b c 3) 1) 1 ∨ IsRoot (mutate (node a b c 3) 1) 1 := by
  left; refine ⟨10,perm6,?_⟩
  funext u v
  rcases fin4 u with rfl | rfl | rfl | rfl <;>
    rcases fin4 v with rfl | rfl | rfl | rfl <;>
    simp [node,relabel,perm6,mutate,ofSix,correction] <;> grind

theorem edge3_2 (a b c : Int) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) :
    FramedCore (node a b c) (mutate (node a b c 3) 2) ∨
      IsFork (mutate (node a b c 3) 2) 2 ∨ IsRoot (mutate (node a b c 3) 2) 2 := by
  left; refine ⟨11,perm0,?_⟩
  funext u v
  rcases fin4 u with rfl | rfl | rfl | rfl <;>
    rcases fin4 v with rfl | rfl | rfl | rfl <;>
    simp [node,relabel,perm0,mutate,ofSix,correction] <;> grind

theorem edge3_3 (a b c : Int) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) :
    FramedCore (node a b c) (mutate (node a b c 3) 3) ∨
      IsFork (mutate (node a b c 3) 3) 3 ∨ IsRoot (mutate (node a b c 3) 3) 3 := by
  left; refine ⟨0,perm1,?_⟩
  funext u v
  rcases fin4 u with rfl | rfl | rfl | rfl <;>
    rcases fin4 v with rfl | rfl | rfl | rfl <;>
    simp [node,relabel,perm1,mutate,ofSix,correction] <;> grind

theorem cyclic4 (a b c : Int) (_ha : 2≤a) (_hb : 2≤b) (_hc : 2≤c) : ¬ Acyclic (node a b c 4) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by simp [node,ofSix] <;> omega)
  have h1 := hr 3 2 (by simp [node,ofSix] <;> omega)
  have h2 := hr 2 0 (by simp [node,ofSix] <;> omega)
  omega

theorem edge4_0 (a b c : Int) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) :
    FramedCore (node a b c) (mutate (node a b c 4) 0) ∨
      IsFork (mutate (node a b c 4) 0) 0 ∨ IsRoot (mutate (node a b c 4) 0) 0 := by
  right; right
  have hd : Regions.Domain (a) (1 + a*c) ((-1) + a*b + a^2) (c) (b + a) := by
    have hsa0 := product_minus_one a a (by omega) (by omega)
    have hpa0 := Forks.product_add_dominates a a 0 (by omega) (by omega) (by decide)
    have hsa1 := product_minus_one a b (by omega) (by omega)
    have hpa1 := Forks.product_add_dominates a b 0 (by omega) (by omega) (by decide)
    have hsa2 := product_minus_one a c (by omega) (by omega)
    have hpa2 := Forks.product_add_dominates a c 0 (by omega) (by omega) (by decide)
    have hsa3 := product_minus_one a (a+b) (by omega) (by omega)
    have hpa3 := Forks.product_add_dominates a (a+b) 0 (by omega) (by omega) (by decide)
    have hsa4 := product_minus_one a (b+c) (by omega) (by omega)
    have hpa4 := Forks.product_add_dominates a (b+c) 0 (by omega) (by omega) (by decide)
    have hsa5 := product_minus_one a (c+a) (by omega) (by omega)
    have hpa5 := Forks.product_add_dominates a (c+a) 0 (by omega) (by omega) (by decide)
    have hsb0 := product_minus_one b a (by omega) (by omega)
    have hpb0 := Forks.product_add_dominates b a 0 (by omega) (by omega) (by decide)
    have hsb1 := product_minus_one b b (by omega) (by omega)
    have hpb1 := Forks.product_add_dominates b b 0 (by omega) (by omega) (by decide)
    have hsb2 := product_minus_one b c (by omega) (by omega)
    have hpb2 := Forks.product_add_dominates b c 0 (by omega) (by omega) (by decide)
    have hsb3 := product_minus_one b (a+b) (by omega) (by omega)
    have hpb3 := Forks.product_add_dominates b (a+b) 0 (by omega) (by omega) (by decide)
    have hsb4 := product_minus_one b (b+c) (by omega) (by omega)
    have hpb4 := Forks.product_add_dominates b (b+c) 0 (by omega) (by omega) (by decide)
    have hsb5 := product_minus_one b (c+a) (by omega) (by omega)
    have hpb5 := Forks.product_add_dominates b (c+a) 0 (by omega) (by omega) (by decide)
    have hsc0 := product_minus_one c a (by omega) (by omega)
    have hpc0 := Forks.product_add_dominates c a 0 (by omega) (by omega) (by decide)
    have hsc1 := product_minus_one c b (by omega) (by omega)
    have hpc1 := Forks.product_add_dominates c b 0 (by omega) (by omega) (by decide)
    have hsc2 := product_minus_one c c (by omega) (by omega)
    have hpc2 := Forks.product_add_dominates c c 0 (by omega) (by omega) (by decide)
    have hsc3 := product_minus_one c (a+b) (by omega) (by omega)
    have hpc3 := Forks.product_add_dominates c (a+b) 0 (by omega) (by omega) (by decide)
    have hsc4 := product_minus_one c (b+c) (by omega) (by omega)
    have hpc4 := Forks.product_add_dominates c (b+c) 0 (by omega) (by omega) (by decide)
    have hsc5 := product_minus_one c (c+a) (by omega) (by omega)
    have hpc5 := Forks.product_add_dominates c (c+a) 0 (by omega) (by omega) (by decide)
    unfold Regions.Domain
    grind
  have he : relabel (reverse (mutate (node a b c 4) 0)) perm4 = root (a) (1 + a*c) ((-1) + a*b + a^2) (c) (b + a) (0) := by
    funext u v
    rcases fin4 u with rfl | rfl | rfl | rfl <;>
      rcases fin4 v with rfl | rfl | rfl | rfl <;>
      simp [node,relabel,perm4,reverse,root,mutate,ofSix,correction] <;> grind
  have hr : IsRoot (relabel (reverse (mutate (node a b c 4) 0)) perm4) 0 := by
    rw [he]; exact IsRoot.basic _ _ _ _ _ _ hd (by decide)
  exact root_of_reverse (root_of_relabel perm4 hr)

theorem edge4_1 (a b c : Int) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) :
    FramedCore (node a b c) (mutate (node a b c 4) 1) ∨
      IsFork (mutate (node a b c 4) 1) 1 ∨ IsRoot (mutate (node a b c 4) 1) 1 := by
  left; refine ⟨12,perm7,?_⟩
  funext u v
  rcases fin4 u with rfl | rfl | rfl | rfl <;>
    rcases fin4 v with rfl | rfl | rfl | rfl <;>
    simp [node,relabel,perm7,mutate,ofSix,correction] <;> grind

theorem edge4_2 (a b c : Int) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) :
    FramedCore (node a b c) (mutate (node a b c 4) 2) ∨
      IsFork (mutate (node a b c 4) 2) 2 ∨ IsRoot (mutate (node a b c 4) 2) 2 := by
  left; refine ⟨13,perm1,?_⟩
  funext u v
  rcases fin4 u with rfl | rfl | rfl | rfl <;>
    rcases fin4 v with rfl | rfl | rfl | rfl <;>
    simp [node,relabel,perm1,mutate,ofSix,correction] <;> grind

theorem edge4_3 (a b c : Int) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) :
    FramedCore (node a b c) (mutate (node a b c 4) 3) ∨
      IsFork (mutate (node a b c 4) 3) 3 ∨ IsRoot (mutate (node a b c 4) 3) 3 := by
  left; refine ⟨0,perm0,?_⟩
  funext u v
  rcases fin4 u with rfl | rfl | rfl | rfl <;>
    rcases fin4 v with rfl | rfl | rfl | rfl <;>
    simp [node,relabel,perm0,mutate,ofSix,correction] <;> grind

theorem cyclic5 (a b c : Int) (_ha : 2≤a) (_hb : 2≤b) (_hc : 2≤c) : ¬ Acyclic (node a b c 5) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by simp [node,ofSix] <;> omega)
  have h1 := hr 3 1 (by simp [node,ofSix] <;> omega)
  have h2 := hr 1 0 (by simp [node,ofSix] <;> omega)
  omega

theorem edge5_0 (a b c : Int) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) :
    FramedCore (node a b c) (mutate (node a b c 5) 0) ∨
      IsFork (mutate (node a b c 5) 0) 0 ∨ IsRoot (mutate (node a b c 5) 0) 0 := by
  left; refine ⟨11,perm6,?_⟩
  funext u v
  rcases fin4 u with rfl | rfl | rfl | rfl <;>
    rcases fin4 v with rfl | rfl | rfl | rfl <;>
    simp [node,relabel,perm6,mutate,ofSix,correction] <;> grind

theorem edge5_1 (a b c : Int) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) :
    FramedCore (node a b c) (mutate (node a b c 5) 1) ∨
      IsFork (mutate (node a b c 5) 1) 1 ∨ IsRoot (mutate (node a b c 5) 1) 1 := by
  right; right
  have hd : Regions.Domain (c) ((-1) + c^2 + b*c) (1 + a*c) (c + b) (a) := by
    have hsa0 := product_minus_one a a (by omega) (by omega)
    have hpa0 := Forks.product_add_dominates a a 0 (by omega) (by omega) (by decide)
    have hsa1 := product_minus_one a b (by omega) (by omega)
    have hpa1 := Forks.product_add_dominates a b 0 (by omega) (by omega) (by decide)
    have hsa2 := product_minus_one a c (by omega) (by omega)
    have hpa2 := Forks.product_add_dominates a c 0 (by omega) (by omega) (by decide)
    have hsa3 := product_minus_one a (a+b) (by omega) (by omega)
    have hpa3 := Forks.product_add_dominates a (a+b) 0 (by omega) (by omega) (by decide)
    have hsa4 := product_minus_one a (b+c) (by omega) (by omega)
    have hpa4 := Forks.product_add_dominates a (b+c) 0 (by omega) (by omega) (by decide)
    have hsa5 := product_minus_one a (c+a) (by omega) (by omega)
    have hpa5 := Forks.product_add_dominates a (c+a) 0 (by omega) (by omega) (by decide)
    have hsb0 := product_minus_one b a (by omega) (by omega)
    have hpb0 := Forks.product_add_dominates b a 0 (by omega) (by omega) (by decide)
    have hsb1 := product_minus_one b b (by omega) (by omega)
    have hpb1 := Forks.product_add_dominates b b 0 (by omega) (by omega) (by decide)
    have hsb2 := product_minus_one b c (by omega) (by omega)
    have hpb2 := Forks.product_add_dominates b c 0 (by omega) (by omega) (by decide)
    have hsb3 := product_minus_one b (a+b) (by omega) (by omega)
    have hpb3 := Forks.product_add_dominates b (a+b) 0 (by omega) (by omega) (by decide)
    have hsb4 := product_minus_one b (b+c) (by omega) (by omega)
    have hpb4 := Forks.product_add_dominates b (b+c) 0 (by omega) (by omega) (by decide)
    have hsb5 := product_minus_one b (c+a) (by omega) (by omega)
    have hpb5 := Forks.product_add_dominates b (c+a) 0 (by omega) (by omega) (by decide)
    have hsc0 := product_minus_one c a (by omega) (by omega)
    have hpc0 := Forks.product_add_dominates c a 0 (by omega) (by omega) (by decide)
    have hsc1 := product_minus_one c b (by omega) (by omega)
    have hpc1 := Forks.product_add_dominates c b 0 (by omega) (by omega) (by decide)
    have hsc2 := product_minus_one c c (by omega) (by omega)
    have hpc2 := Forks.product_add_dominates c c 0 (by omega) (by omega) (by decide)
    have hsc3 := product_minus_one c (a+b) (by omega) (by omega)
    have hpc3 := Forks.product_add_dominates c (a+b) 0 (by omega) (by omega) (by decide)
    have hsc4 := product_minus_one c (b+c) (by omega) (by omega)
    have hpc4 := Forks.product_add_dominates c (b+c) 0 (by omega) (by omega) (by decide)
    have hsc5 := product_minus_one c (c+a) (by omega) (by omega)
    have hpc5 := Forks.product_add_dominates c (c+a) 0 (by omega) (by omega) (by decide)
    unfold Regions.Domain
    grind
  have he : relabel (mutate (node a b c 5) 1) perm10 = root (c) ((-1) + c^2 + b*c) (1 + a*c) (c + b) (a) (0) := by
    funext u v
    rcases fin4 u with rfl | rfl | rfl | rfl <;>
      rcases fin4 v with rfl | rfl | rfl | rfl <;>
      simp [node,relabel,perm10,root,mutate,ofSix,correction] <;> grind
  have hr : IsRoot (relabel (mutate (node a b c 5) 1) perm10) 0 := by
    rw [he]; exact IsRoot.basic _ _ _ _ _ _ hd (by decide)
  exact root_of_relabel perm10 hr

theorem edge5_2 (a b c : Int) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) :
    FramedCore (node a b c) (mutate (node a b c 5) 2) ∨
      IsFork (mutate (node a b c 5) 2) 2 ∨ IsRoot (mutate (node a b c 5) 2) 2 := by
  left; refine ⟨10,perm0,?_⟩
  funext u v
  rcases fin4 u with rfl | rfl | rfl | rfl <;>
    rcases fin4 v with rfl | rfl | rfl | rfl <;>
    simp [node,relabel,perm0,mutate,ofSix,correction] <;> grind

theorem edge5_3 (a b c : Int) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) :
    FramedCore (node a b c) (mutate (node a b c 5) 3) ∨
      IsFork (mutate (node a b c 5) 3) 3 ∨ IsRoot (mutate (node a b c 5) 3) 3 := by
  left; refine ⟨1,perm21,?_⟩
  funext u v
  rcases fin4 u with rfl | rfl | rfl | rfl <;>
    rcases fin4 v with rfl | rfl | rfl | rfl <;>
    simp [node,relabel,perm21,mutate,ofSix,correction] <;> grind

theorem cyclic6 (a b c : Int) (_ha : 2≤a) (_hb : 2≤b) (_hc : 2≤c) : ¬ Acyclic (node a b c 6) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by simp [node,ofSix] <;> omega)
  have h1 := hr 3 1 (by simp [node,ofSix] <;> omega)
  have h2 := hr 1 0 (by simp [node,ofSix] <;> omega)
  omega

theorem edge6_0 (a b c : Int) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) :
    FramedCore (node a b c) (mutate (node a b c 6) 0) ∨
      IsFork (mutate (node a b c 6) 0) 0 ∨ IsRoot (mutate (node a b c 6) 0) 0 := by
  left; refine ⟨9,perm6,?_⟩
  funext u v
  rcases fin4 u with rfl | rfl | rfl | rfl <;>
    rcases fin4 v with rfl | rfl | rfl | rfl <;>
    simp [node,relabel,perm6,mutate,ofSix,correction] <;> grind

theorem edge6_1 (a b c : Int) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) :
    FramedCore (node a b c) (mutate (node a b c 6) 1) ∨
      IsFork (mutate (node a b c 6) 1) 1 ∨ IsRoot (mutate (node a b c 6) 1) 1 := by
  right; right
  have hd : Regions.Domain (a) ((-1) + a*c + a^2) (1 + a*b) (c + a) (b) := by
    have hsa0 := product_minus_one a a (by omega) (by omega)
    have hpa0 := Forks.product_add_dominates a a 0 (by omega) (by omega) (by decide)
    have hsa1 := product_minus_one a b (by omega) (by omega)
    have hpa1 := Forks.product_add_dominates a b 0 (by omega) (by omega) (by decide)
    have hsa2 := product_minus_one a c (by omega) (by omega)
    have hpa2 := Forks.product_add_dominates a c 0 (by omega) (by omega) (by decide)
    have hsa3 := product_minus_one a (a+b) (by omega) (by omega)
    have hpa3 := Forks.product_add_dominates a (a+b) 0 (by omega) (by omega) (by decide)
    have hsa4 := product_minus_one a (b+c) (by omega) (by omega)
    have hpa4 := Forks.product_add_dominates a (b+c) 0 (by omega) (by omega) (by decide)
    have hsa5 := product_minus_one a (c+a) (by omega) (by omega)
    have hpa5 := Forks.product_add_dominates a (c+a) 0 (by omega) (by omega) (by decide)
    have hsb0 := product_minus_one b a (by omega) (by omega)
    have hpb0 := Forks.product_add_dominates b a 0 (by omega) (by omega) (by decide)
    have hsb1 := product_minus_one b b (by omega) (by omega)
    have hpb1 := Forks.product_add_dominates b b 0 (by omega) (by omega) (by decide)
    have hsb2 := product_minus_one b c (by omega) (by omega)
    have hpb2 := Forks.product_add_dominates b c 0 (by omega) (by omega) (by decide)
    have hsb3 := product_minus_one b (a+b) (by omega) (by omega)
    have hpb3 := Forks.product_add_dominates b (a+b) 0 (by omega) (by omega) (by decide)
    have hsb4 := product_minus_one b (b+c) (by omega) (by omega)
    have hpb4 := Forks.product_add_dominates b (b+c) 0 (by omega) (by omega) (by decide)
    have hsb5 := product_minus_one b (c+a) (by omega) (by omega)
    have hpb5 := Forks.product_add_dominates b (c+a) 0 (by omega) (by omega) (by decide)
    have hsc0 := product_minus_one c a (by omega) (by omega)
    have hpc0 := Forks.product_add_dominates c a 0 (by omega) (by omega) (by decide)
    have hsc1 := product_minus_one c b (by omega) (by omega)
    have hpc1 := Forks.product_add_dominates c b 0 (by omega) (by omega) (by decide)
    have hsc2 := product_minus_one c c (by omega) (by omega)
    have hpc2 := Forks.product_add_dominates c c 0 (by omega) (by omega) (by decide)
    have hsc3 := product_minus_one c (a+b) (by omega) (by omega)
    have hpc3 := Forks.product_add_dominates c (a+b) 0 (by omega) (by omega) (by decide)
    have hsc4 := product_minus_one c (b+c) (by omega) (by omega)
    have hpc4 := Forks.product_add_dominates c (b+c) 0 (by omega) (by omega) (by decide)
    have hsc5 := product_minus_one c (c+a) (by omega) (by omega)
    have hpc5 := Forks.product_add_dominates c (c+a) 0 (by omega) (by omega) (by decide)
    unfold Regions.Domain
    grind
  have he : relabel (mutate (node a b c 6) 1) perm10 = root (a) ((-1) + a*c + a^2) (1 + a*b) (c + a) (b) (0) := by
    funext u v
    rcases fin4 u with rfl | rfl | rfl | rfl <;>
      rcases fin4 v with rfl | rfl | rfl | rfl <;>
      simp [node,relabel,perm10,root,mutate,ofSix,correction] <;> grind
  have hr : IsRoot (relabel (mutate (node a b c 6) 1) perm10) 0 := by
    rw [he]; exact IsRoot.basic _ _ _ _ _ _ hd (by decide)
  exact root_of_relabel perm10 hr

theorem edge6_2 (a b c : Int) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) :
    FramedCore (node a b c) (mutate (node a b c 6) 2) ∨
      IsFork (mutate (node a b c 6) 2) 2 ∨ IsRoot (mutate (node a b c 6) 2) 2 := by
  left; refine ⟨8,perm0,?_⟩
  funext u v
  rcases fin4 u with rfl | rfl | rfl | rfl <;>
    rcases fin4 v with rfl | rfl | rfl | rfl <;>
    simp [node,relabel,perm0,mutate,ofSix,correction] <;> grind

theorem edge6_3 (a b c : Int) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) :
    FramedCore (node a b c) (mutate (node a b c 6) 3) ∨
      IsFork (mutate (node a b c 6) 3) 3 ∨ IsRoot (mutate (node a b c 6) 3) 3 := by
  left; refine ⟨1,perm1,?_⟩
  funext u v
  rcases fin4 u with rfl | rfl | rfl | rfl <;>
    rcases fin4 v with rfl | rfl | rfl | rfl <;>
    simp [node,relabel,perm1,mutate,ofSix,correction] <;> grind

theorem cyclic7 (a b c : Int) (_ha : 2≤a) (_hb : 2≤b) (_hc : 2≤c) : ¬ Acyclic (node a b c 7) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 1 3 (by simp [node,ofSix] <;> omega)
  have h1 := hr 3 2 (by simp [node,ofSix] <;> omega)
  have h2 := hr 2 1 (by simp [node,ofSix] <;> omega)
  omega

theorem edge7_0 (a b c : Int) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) :
    FramedCore (node a b c) (mutate (node a b c 7) 0) ∨
      IsFork (mutate (node a b c 7) 0) 0 ∨ IsRoot (mutate (node a b c 7) 0) 0 := by
  left; refine ⟨13,perm6,?_⟩
  funext u v
  rcases fin4 u with rfl | rfl | rfl | rfl <;>
    rcases fin4 v with rfl | rfl | rfl | rfl <;>
    simp [node,relabel,perm6,mutate,ofSix,correction] <;> grind

theorem edge7_1 (a b c : Int) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) :
    FramedCore (node a b c) (mutate (node a b c 7) 1) ∨
      IsFork (mutate (node a b c 7) 1) 1 ∨ IsRoot (mutate (node a b c 7) 1) 1 := by
  right; right
  have hd : Regions.Domain (b) (1 + b*c) ((-1) + b^2 + a*b) (c) (b + a) := by
    have hsa0 := product_minus_one a a (by omega) (by omega)
    have hpa0 := Forks.product_add_dominates a a 0 (by omega) (by omega) (by decide)
    have hsa1 := product_minus_one a b (by omega) (by omega)
    have hpa1 := Forks.product_add_dominates a b 0 (by omega) (by omega) (by decide)
    have hsa2 := product_minus_one a c (by omega) (by omega)
    have hpa2 := Forks.product_add_dominates a c 0 (by omega) (by omega) (by decide)
    have hsa3 := product_minus_one a (a+b) (by omega) (by omega)
    have hpa3 := Forks.product_add_dominates a (a+b) 0 (by omega) (by omega) (by decide)
    have hsa4 := product_minus_one a (b+c) (by omega) (by omega)
    have hpa4 := Forks.product_add_dominates a (b+c) 0 (by omega) (by omega) (by decide)
    have hsa5 := product_minus_one a (c+a) (by omega) (by omega)
    have hpa5 := Forks.product_add_dominates a (c+a) 0 (by omega) (by omega) (by decide)
    have hsb0 := product_minus_one b a (by omega) (by omega)
    have hpb0 := Forks.product_add_dominates b a 0 (by omega) (by omega) (by decide)
    have hsb1 := product_minus_one b b (by omega) (by omega)
    have hpb1 := Forks.product_add_dominates b b 0 (by omega) (by omega) (by decide)
    have hsb2 := product_minus_one b c (by omega) (by omega)
    have hpb2 := Forks.product_add_dominates b c 0 (by omega) (by omega) (by decide)
    have hsb3 := product_minus_one b (a+b) (by omega) (by omega)
    have hpb3 := Forks.product_add_dominates b (a+b) 0 (by omega) (by omega) (by decide)
    have hsb4 := product_minus_one b (b+c) (by omega) (by omega)
    have hpb4 := Forks.product_add_dominates b (b+c) 0 (by omega) (by omega) (by decide)
    have hsb5 := product_minus_one b (c+a) (by omega) (by omega)
    have hpb5 := Forks.product_add_dominates b (c+a) 0 (by omega) (by omega) (by decide)
    have hsc0 := product_minus_one c a (by omega) (by omega)
    have hpc0 := Forks.product_add_dominates c a 0 (by omega) (by omega) (by decide)
    have hsc1 := product_minus_one c b (by omega) (by omega)
    have hpc1 := Forks.product_add_dominates c b 0 (by omega) (by omega) (by decide)
    have hsc2 := product_minus_one c c (by omega) (by omega)
    have hpc2 := Forks.product_add_dominates c c 0 (by omega) (by omega) (by decide)
    have hsc3 := product_minus_one c (a+b) (by omega) (by omega)
    have hpc3 := Forks.product_add_dominates c (a+b) 0 (by omega) (by omega) (by decide)
    have hsc4 := product_minus_one c (b+c) (by omega) (by omega)
    have hpc4 := Forks.product_add_dominates c (b+c) 0 (by omega) (by omega) (by decide)
    have hsc5 := product_minus_one c (c+a) (by omega) (by omega)
    have hpc5 := Forks.product_add_dominates c (c+a) 0 (by omega) (by omega) (by decide)
    unfold Regions.Domain
    grind
  have he : relabel (mutate (node a b c 7) 1) perm8 = root (b) (1 + b*c) ((-1) + b^2 + a*b) (c) (b + a) (0) := by
    funext u v
    rcases fin4 u with rfl | rfl | rfl | rfl <;>
      rcases fin4 v with rfl | rfl | rfl | rfl <;>
      simp [node,relabel,perm8,root,mutate,ofSix,correction] <;> grind
  have hr : IsRoot (relabel (mutate (node a b c 7) 1) perm8) 0 := by
    rw [he]; exact IsRoot.basic _ _ _ _ _ _ hd (by decide)
  exact root_of_relabel perm8 hr

theorem edge7_2 (a b c : Int) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) :
    FramedCore (node a b c) (mutate (node a b c 7) 2) ∨
      IsFork (mutate (node a b c 7) 2) 2 ∨ IsRoot (mutate (node a b c 7) 2) 2 := by
  left; refine ⟨1,perm1,?_⟩
  funext u v
  rcases fin4 u with rfl | rfl | rfl | rfl <;>
    rcases fin4 v with rfl | rfl | rfl | rfl <;>
    simp [node,relabel,perm1,mutate,ofSix,correction] <;> grind

theorem edge7_3 (a b c : Int) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) :
    FramedCore (node a b c) (mutate (node a b c 7) 3) ∨
      IsFork (mutate (node a b c 7) 3) 3 ∨ IsRoot (mutate (node a b c 7) 3) 3 := by
  left; refine ⟨12,perm0,?_⟩
  funext u v
  rcases fin4 u with rfl | rfl | rfl | rfl <;>
    rcases fin4 v with rfl | rfl | rfl | rfl <;>
    simp [node,relabel,perm0,mutate,ofSix,correction] <;> grind

theorem cyclic8 (a b c : Int) (_ha : 2≤a) (_hb : 2≤b) (_hc : 2≤c) : ¬ Acyclic (node a b c 8) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by simp [node,ofSix] <;> omega)
  have h1 := hr 3 1 (by simp [node,ofSix] <;> omega)
  have h2 := hr 1 0 (by simp [node,ofSix] <;> omega)
  omega

theorem edge8_0 (a b c : Int) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) :
    FramedCore (node a b c) (mutate (node a b c 8) 0) ∨
      IsFork (mutate (node a b c 8) 0) 0 ∨ IsRoot (mutate (node a b c 8) 0) 0 := by
  left; refine ⟨2,perm6,?_⟩
  funext u v
  rcases fin4 u with rfl | rfl | rfl | rfl <;>
    rcases fin4 v with rfl | rfl | rfl | rfl <;>
    simp [node,relabel,perm6,mutate,ofSix,correction] <;> grind

theorem edge8_1 (a b c : Int) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) :
    FramedCore (node a b c) (mutate (node a b c 8) 1) ∨
      IsFork (mutate (node a b c 8) 1) 1 ∨ IsRoot (mutate (node a b c 8) 1) 1 := by
  right; right
  have hd : Regions.Domain (c + a) ((-1) + a*c + a^2) (b*c + a*b) (a) (b) := by
    have hsa0 := product_minus_one a a (by omega) (by omega)
    have hpa0 := Forks.product_add_dominates a a 0 (by omega) (by omega) (by decide)
    have hsa1 := product_minus_one a b (by omega) (by omega)
    have hpa1 := Forks.product_add_dominates a b 0 (by omega) (by omega) (by decide)
    have hsa2 := product_minus_one a c (by omega) (by omega)
    have hpa2 := Forks.product_add_dominates a c 0 (by omega) (by omega) (by decide)
    have hsa3 := product_minus_one a (a+b) (by omega) (by omega)
    have hpa3 := Forks.product_add_dominates a (a+b) 0 (by omega) (by omega) (by decide)
    have hsa4 := product_minus_one a (b+c) (by omega) (by omega)
    have hpa4 := Forks.product_add_dominates a (b+c) 0 (by omega) (by omega) (by decide)
    have hsa5 := product_minus_one a (c+a) (by omega) (by omega)
    have hpa5 := Forks.product_add_dominates a (c+a) 0 (by omega) (by omega) (by decide)
    have hsb0 := product_minus_one b a (by omega) (by omega)
    have hpb0 := Forks.product_add_dominates b a 0 (by omega) (by omega) (by decide)
    have hsb1 := product_minus_one b b (by omega) (by omega)
    have hpb1 := Forks.product_add_dominates b b 0 (by omega) (by omega) (by decide)
    have hsb2 := product_minus_one b c (by omega) (by omega)
    have hpb2 := Forks.product_add_dominates b c 0 (by omega) (by omega) (by decide)
    have hsb3 := product_minus_one b (a+b) (by omega) (by omega)
    have hpb3 := Forks.product_add_dominates b (a+b) 0 (by omega) (by omega) (by decide)
    have hsb4 := product_minus_one b (b+c) (by omega) (by omega)
    have hpb4 := Forks.product_add_dominates b (b+c) 0 (by omega) (by omega) (by decide)
    have hsb5 := product_minus_one b (c+a) (by omega) (by omega)
    have hpb5 := Forks.product_add_dominates b (c+a) 0 (by omega) (by omega) (by decide)
    have hsc0 := product_minus_one c a (by omega) (by omega)
    have hpc0 := Forks.product_add_dominates c a 0 (by omega) (by omega) (by decide)
    have hsc1 := product_minus_one c b (by omega) (by omega)
    have hpc1 := Forks.product_add_dominates c b 0 (by omega) (by omega) (by decide)
    have hsc2 := product_minus_one c c (by omega) (by omega)
    have hpc2 := Forks.product_add_dominates c c 0 (by omega) (by omega) (by decide)
    have hsc3 := product_minus_one c (a+b) (by omega) (by omega)
    have hpc3 := Forks.product_add_dominates c (a+b) 0 (by omega) (by omega) (by decide)
    have hsc4 := product_minus_one c (b+c) (by omega) (by omega)
    have hpc4 := Forks.product_add_dominates c (b+c) 0 (by omega) (by omega) (by decide)
    have hsc5 := product_minus_one c (c+a) (by omega) (by omega)
    have hpc5 := Forks.product_add_dominates c (c+a) 0 (by omega) (by omega) (by decide)
    unfold Regions.Domain
    grind
  have he : relabel (reverse (mutate (node a b c 8) 1)) perm7 = root (c + a) ((-1) + a*c + a^2) (b*c + a*b) (a) (b) (1) := by
    funext u v
    rcases fin4 u with rfl | rfl | rfl | rfl <;>
      rcases fin4 v with rfl | rfl | rfl | rfl <;>
      simp [node,relabel,perm7,reverse,root,mutate,ofSix,correction] <;> grind
  have hr : IsRoot (relabel (reverse (mutate (node a b c 8) 1)) perm7) 0 := by
    rw [he]; exact IsRoot.basic _ _ _ _ _ _ hd (by decide)
  exact root_of_reverse (root_of_relabel perm7 hr)

theorem edge8_2 (a b c : Int) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) :
    FramedCore (node a b c) (mutate (node a b c 8) 2) ∨
      IsFork (mutate (node a b c 8) 2) 2 ∨ IsRoot (mutate (node a b c 8) 2) 2 := by
  left; refine ⟨6,perm0,?_⟩
  funext u v
  rcases fin4 u with rfl | rfl | rfl | rfl <;>
    rcases fin4 v with rfl | rfl | rfl | rfl <;>
    simp [node,relabel,perm0,mutate,ofSix,correction] <;> grind

theorem edge8_3 (a b c : Int) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) :
    FramedCore (node a b c) (mutate (node a b c 8) 3) ∨
      IsFork (mutate (node a b c 8) 3) 3 ∨ IsRoot (mutate (node a b c 8) 3) 3 := by
  left; refine ⟨12,perm1,?_⟩
  funext u v
  rcases fin4 u with rfl | rfl | rfl | rfl <;>
    rcases fin4 v with rfl | rfl | rfl | rfl <;>
    simp [node,relabel,perm1,mutate,ofSix,correction] <;> grind

theorem cyclic9 (a b c : Int) (_ha : 2≤a) (_hb : 2≤b) (_hc : 2≤c) : ¬ Acyclic (node a b c 9) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by simp [node,ofSix] <;> omega)
  have h1 := hr 3 1 (by simp [node,ofSix] <;> omega)
  have h2 := hr 1 0 (by simp [node,ofSix] <;> omega)
  omega

theorem edge9_0 (a b c : Int) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) :
    FramedCore (node a b c) (mutate (node a b c 9) 0) ∨
      IsFork (mutate (node a b c 9) 0) 0 ∨ IsRoot (mutate (node a b c 9) 0) 0 := by
  right; right
  have hd : Regions.Domain (c + a) ((-1) + c^2 + a*c) (b*c + a*b) (c) (b) := by
    have hsa0 := product_minus_one a a (by omega) (by omega)
    have hpa0 := Forks.product_add_dominates a a 0 (by omega) (by omega) (by decide)
    have hsa1 := product_minus_one a b (by omega) (by omega)
    have hpa1 := Forks.product_add_dominates a b 0 (by omega) (by omega) (by decide)
    have hsa2 := product_minus_one a c (by omega) (by omega)
    have hpa2 := Forks.product_add_dominates a c 0 (by omega) (by omega) (by decide)
    have hsa3 := product_minus_one a (a+b) (by omega) (by omega)
    have hpa3 := Forks.product_add_dominates a (a+b) 0 (by omega) (by omega) (by decide)
    have hsa4 := product_minus_one a (b+c) (by omega) (by omega)
    have hpa4 := Forks.product_add_dominates a (b+c) 0 (by omega) (by omega) (by decide)
    have hsa5 := product_minus_one a (c+a) (by omega) (by omega)
    have hpa5 := Forks.product_add_dominates a (c+a) 0 (by omega) (by omega) (by decide)
    have hsb0 := product_minus_one b a (by omega) (by omega)
    have hpb0 := Forks.product_add_dominates b a 0 (by omega) (by omega) (by decide)
    have hsb1 := product_minus_one b b (by omega) (by omega)
    have hpb1 := Forks.product_add_dominates b b 0 (by omega) (by omega) (by decide)
    have hsb2 := product_minus_one b c (by omega) (by omega)
    have hpb2 := Forks.product_add_dominates b c 0 (by omega) (by omega) (by decide)
    have hsb3 := product_minus_one b (a+b) (by omega) (by omega)
    have hpb3 := Forks.product_add_dominates b (a+b) 0 (by omega) (by omega) (by decide)
    have hsb4 := product_minus_one b (b+c) (by omega) (by omega)
    have hpb4 := Forks.product_add_dominates b (b+c) 0 (by omega) (by omega) (by decide)
    have hsb5 := product_minus_one b (c+a) (by omega) (by omega)
    have hpb5 := Forks.product_add_dominates b (c+a) 0 (by omega) (by omega) (by decide)
    have hsc0 := product_minus_one c a (by omega) (by omega)
    have hpc0 := Forks.product_add_dominates c a 0 (by omega) (by omega) (by decide)
    have hsc1 := product_minus_one c b (by omega) (by omega)
    have hpc1 := Forks.product_add_dominates c b 0 (by omega) (by omega) (by decide)
    have hsc2 := product_minus_one c c (by omega) (by omega)
    have hpc2 := Forks.product_add_dominates c c 0 (by omega) (by omega) (by decide)
    have hsc3 := product_minus_one c (a+b) (by omega) (by omega)
    have hpc3 := Forks.product_add_dominates c (a+b) 0 (by omega) (by omega) (by decide)
    have hsc4 := product_minus_one c (b+c) (by omega) (by omega)
    have hpc4 := Forks.product_add_dominates c (b+c) 0 (by omega) (by omega) (by decide)
    have hsc5 := product_minus_one c (c+a) (by omega) (by omega)
    have hpc5 := Forks.product_add_dominates c (c+a) 0 (by omega) (by omega) (by decide)
    unfold Regions.Domain
    grind
  have he : relabel (mutate (node a b c 9) 0) perm1 = root (c + a) ((-1) + c^2 + a*c) (b*c + a*b) (c) (b) (1) := by
    funext u v
    rcases fin4 u with rfl | rfl | rfl | rfl <;>
      rcases fin4 v with rfl | rfl | rfl | rfl <;>
      simp [node,relabel,perm1,root,mutate,ofSix,correction] <;> grind
  have hr : IsRoot (relabel (mutate (node a b c 9) 0) perm1) 0 := by
    rw [he]; exact IsRoot.basic _ _ _ _ _ _ hd (by decide)
  exact root_of_relabel perm1 hr

theorem edge9_1 (a b c : Int) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) :
    FramedCore (node a b c) (mutate (node a b c 9) 1) ∨
      IsFork (mutate (node a b c 9) 1) 1 ∨ IsRoot (mutate (node a b c 9) 1) 1 := by
  left; refine ⟨6,perm6,?_⟩
  funext u v
  rcases fin4 u with rfl | rfl | rfl | rfl <;>
    rcases fin4 v with rfl | rfl | rfl | rfl <;>
    simp [node,relabel,perm6,mutate,ofSix,correction] <;> grind

theorem edge9_2 (a b c : Int) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) :
    FramedCore (node a b c) (mutate (node a b c 9) 2) ∨
      IsFork (mutate (node a b c 9) 2) 2 ∨ IsRoot (mutate (node a b c 9) 2) 2 := by
  left; refine ⟨2,perm0,?_⟩
  funext u v
  rcases fin4 u with rfl | rfl | rfl | rfl <;>
    rcases fin4 v with rfl | rfl | rfl | rfl <;>
    simp [node,relabel,perm0,mutate,ofSix,correction] <;> grind

theorem edge9_3 (a b c : Int) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) :
    FramedCore (node a b c) (mutate (node a b c 9) 3) ∨
      IsFork (mutate (node a b c 9) 3) 3 ∨ IsRoot (mutate (node a b c 9) 3) 3 := by
  left; refine ⟨10,perm8,?_⟩
  funext u v
  rcases fin4 u with rfl | rfl | rfl | rfl <;>
    rcases fin4 v with rfl | rfl | rfl | rfl <;>
    simp [node,relabel,perm8,mutate,ofSix,correction] <;> grind

theorem cyclic10 (a b c : Int) (_ha : 2≤a) (_hb : 2≤b) (_hc : 2≤c) : ¬ Acyclic (node a b c 10) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by simp [node,ofSix] <;> omega)
  have h1 := hr 3 1 (by simp [node,ofSix] <;> omega)
  have h2 := hr 1 0 (by simp [node,ofSix] <;> omega)
  omega

theorem edge10_0 (a b c : Int) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) :
    FramedCore (node a b c) (mutate (node a b c 10) 0) ∨
      IsFork (mutate (node a b c 10) 0) 0 ∨ IsRoot (mutate (node a b c 10) 0) 0 := by
  left; refine ⟨3,perm6,?_⟩
  funext u v
  rcases fin4 u with rfl | rfl | rfl | rfl <;>
    rcases fin4 v with rfl | rfl | rfl | rfl <;>
    simp [node,relabel,perm6,mutate,ofSix,correction] <;> grind

theorem edge10_1 (a b c : Int) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) :
    FramedCore (node a b c) (mutate (node a b c 10) 1) ∨
      IsFork (mutate (node a b c 10) 1) 1 ∨ IsRoot (mutate (node a b c 10) 1) 1 := by
  right; right
  have hd : Regions.Domain (c + b) ((-1) + c^2 + b*c) (a*c + a*b) (c) (a) := by
    have hsa0 := product_minus_one a a (by omega) (by omega)
    have hpa0 := Forks.product_add_dominates a a 0 (by omega) (by omega) (by decide)
    have hsa1 := product_minus_one a b (by omega) (by omega)
    have hpa1 := Forks.product_add_dominates a b 0 (by omega) (by omega) (by decide)
    have hsa2 := product_minus_one a c (by omega) (by omega)
    have hpa2 := Forks.product_add_dominates a c 0 (by omega) (by omega) (by decide)
    have hsa3 := product_minus_one a (a+b) (by omega) (by omega)
    have hpa3 := Forks.product_add_dominates a (a+b) 0 (by omega) (by omega) (by decide)
    have hsa4 := product_minus_one a (b+c) (by omega) (by omega)
    have hpa4 := Forks.product_add_dominates a (b+c) 0 (by omega) (by omega) (by decide)
    have hsa5 := product_minus_one a (c+a) (by omega) (by omega)
    have hpa5 := Forks.product_add_dominates a (c+a) 0 (by omega) (by omega) (by decide)
    have hsb0 := product_minus_one b a (by omega) (by omega)
    have hpb0 := Forks.product_add_dominates b a 0 (by omega) (by omega) (by decide)
    have hsb1 := product_minus_one b b (by omega) (by omega)
    have hpb1 := Forks.product_add_dominates b b 0 (by omega) (by omega) (by decide)
    have hsb2 := product_minus_one b c (by omega) (by omega)
    have hpb2 := Forks.product_add_dominates b c 0 (by omega) (by omega) (by decide)
    have hsb3 := product_minus_one b (a+b) (by omega) (by omega)
    have hpb3 := Forks.product_add_dominates b (a+b) 0 (by omega) (by omega) (by decide)
    have hsb4 := product_minus_one b (b+c) (by omega) (by omega)
    have hpb4 := Forks.product_add_dominates b (b+c) 0 (by omega) (by omega) (by decide)
    have hsb5 := product_minus_one b (c+a) (by omega) (by omega)
    have hpb5 := Forks.product_add_dominates b (c+a) 0 (by omega) (by omega) (by decide)
    have hsc0 := product_minus_one c a (by omega) (by omega)
    have hpc0 := Forks.product_add_dominates c a 0 (by omega) (by omega) (by decide)
    have hsc1 := product_minus_one c b (by omega) (by omega)
    have hpc1 := Forks.product_add_dominates c b 0 (by omega) (by omega) (by decide)
    have hsc2 := product_minus_one c c (by omega) (by omega)
    have hpc2 := Forks.product_add_dominates c c 0 (by omega) (by omega) (by decide)
    have hsc3 := product_minus_one c (a+b) (by omega) (by omega)
    have hpc3 := Forks.product_add_dominates c (a+b) 0 (by omega) (by omega) (by decide)
    have hsc4 := product_minus_one c (b+c) (by omega) (by omega)
    have hpc4 := Forks.product_add_dominates c (b+c) 0 (by omega) (by omega) (by decide)
    have hsc5 := product_minus_one c (c+a) (by omega) (by omega)
    have hpc5 := Forks.product_add_dominates c (c+a) 0 (by omega) (by omega) (by decide)
    unfold Regions.Domain
    grind
  have he : relabel (reverse (mutate (node a b c 10) 1)) perm7 = root (c + b) ((-1) + c^2 + b*c) (a*c + a*b) (c) (a) (1) := by
    funext u v
    rcases fin4 u with rfl | rfl | rfl | rfl <;>
      rcases fin4 v with rfl | rfl | rfl | rfl <;>
      simp [node,relabel,perm7,reverse,root,mutate,ofSix,correction] <;> grind
  have hr : IsRoot (relabel (reverse (mutate (node a b c 10) 1)) perm7) 0 := by
    rw [he]; exact IsRoot.basic _ _ _ _ _ _ hd (by decide)
  exact root_of_reverse (root_of_relabel perm7 hr)

theorem edge10_2 (a b c : Int) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) :
    FramedCore (node a b c) (mutate (node a b c 10) 2) ∨
      IsFork (mutate (node a b c 10) 2) 2 ∨ IsRoot (mutate (node a b c 10) 2) 2 := by
  left; refine ⟨5,perm0,?_⟩
  funext u v
  rcases fin4 u with rfl | rfl | rfl | rfl <;>
    rcases fin4 v with rfl | rfl | rfl | rfl <;>
    simp [node,relabel,perm0,mutate,ofSix,correction] <;> grind

theorem edge10_3 (a b c : Int) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) :
    FramedCore (node a b c) (mutate (node a b c 10) 3) ∨
      IsFork (mutate (node a b c 10) 3) 3 ∨ IsRoot (mutate (node a b c 10) 3) 3 := by
  left; refine ⟨9,perm12,?_⟩
  funext u v
  rcases fin4 u with rfl | rfl | rfl | rfl <;>
    rcases fin4 v with rfl | rfl | rfl | rfl <;>
    simp [node,relabel,perm12,mutate,ofSix,correction] <;> grind

theorem cyclic11 (a b c : Int) (_ha : 2≤a) (_hb : 2≤b) (_hc : 2≤c) : ¬ Acyclic (node a b c 11) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by simp [node,ofSix] <;> omega)
  have h1 := hr 3 1 (by simp [node,ofSix] <;> omega)
  have h2 := hr 1 0 (by simp [node,ofSix] <;> omega)
  omega

theorem edge11_0 (a b c : Int) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) :
    FramedCore (node a b c) (mutate (node a b c 11) 0) ∨
      IsFork (mutate (node a b c 11) 0) 0 ∨ IsRoot (mutate (node a b c 11) 0) 0 := by
  right; right
  have hd : Regions.Domain (c + b) ((-1) + b*c + b^2) (a*c + a*b) (b) (a) := by
    have hsa0 := product_minus_one a a (by omega) (by omega)
    have hpa0 := Forks.product_add_dominates a a 0 (by omega) (by omega) (by decide)
    have hsa1 := product_minus_one a b (by omega) (by omega)
    have hpa1 := Forks.product_add_dominates a b 0 (by omega) (by omega) (by decide)
    have hsa2 := product_minus_one a c (by omega) (by omega)
    have hpa2 := Forks.product_add_dominates a c 0 (by omega) (by omega) (by decide)
    have hsa3 := product_minus_one a (a+b) (by omega) (by omega)
    have hpa3 := Forks.product_add_dominates a (a+b) 0 (by omega) (by omega) (by decide)
    have hsa4 := product_minus_one a (b+c) (by omega) (by omega)
    have hpa4 := Forks.product_add_dominates a (b+c) 0 (by omega) (by omega) (by decide)
    have hsa5 := product_minus_one a (c+a) (by omega) (by omega)
    have hpa5 := Forks.product_add_dominates a (c+a) 0 (by omega) (by omega) (by decide)
    have hsb0 := product_minus_one b a (by omega) (by omega)
    have hpb0 := Forks.product_add_dominates b a 0 (by omega) (by omega) (by decide)
    have hsb1 := product_minus_one b b (by omega) (by omega)
    have hpb1 := Forks.product_add_dominates b b 0 (by omega) (by omega) (by decide)
    have hsb2 := product_minus_one b c (by omega) (by omega)
    have hpb2 := Forks.product_add_dominates b c 0 (by omega) (by omega) (by decide)
    have hsb3 := product_minus_one b (a+b) (by omega) (by omega)
    have hpb3 := Forks.product_add_dominates b (a+b) 0 (by omega) (by omega) (by decide)
    have hsb4 := product_minus_one b (b+c) (by omega) (by omega)
    have hpb4 := Forks.product_add_dominates b (b+c) 0 (by omega) (by omega) (by decide)
    have hsb5 := product_minus_one b (c+a) (by omega) (by omega)
    have hpb5 := Forks.product_add_dominates b (c+a) 0 (by omega) (by omega) (by decide)
    have hsc0 := product_minus_one c a (by omega) (by omega)
    have hpc0 := Forks.product_add_dominates c a 0 (by omega) (by omega) (by decide)
    have hsc1 := product_minus_one c b (by omega) (by omega)
    have hpc1 := Forks.product_add_dominates c b 0 (by omega) (by omega) (by decide)
    have hsc2 := product_minus_one c c (by omega) (by omega)
    have hpc2 := Forks.product_add_dominates c c 0 (by omega) (by omega) (by decide)
    have hsc3 := product_minus_one c (a+b) (by omega) (by omega)
    have hpc3 := Forks.product_add_dominates c (a+b) 0 (by omega) (by omega) (by decide)
    have hsc4 := product_minus_one c (b+c) (by omega) (by omega)
    have hpc4 := Forks.product_add_dominates c (b+c) 0 (by omega) (by omega) (by decide)
    have hsc5 := product_minus_one c (c+a) (by omega) (by omega)
    have hpc5 := Forks.product_add_dominates c (c+a) 0 (by omega) (by omega) (by decide)
    unfold Regions.Domain
    grind
  have he : relabel (mutate (node a b c 11) 0) perm1 = root (c + b) ((-1) + b*c + b^2) (a*c + a*b) (b) (a) (1) := by
    funext u v
    rcases fin4 u with rfl | rfl | rfl | rfl <;>
      rcases fin4 v with rfl | rfl | rfl | rfl <;>
      simp [node,relabel,perm1,root,mutate,ofSix,correction] <;> grind
  have hr : IsRoot (relabel (mutate (node a b c 11) 0) perm1) 0 := by
    rw [he]; exact IsRoot.basic _ _ _ _ _ _ hd (by decide)
  exact root_of_relabel perm1 hr

theorem edge11_1 (a b c : Int) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) :
    FramedCore (node a b c) (mutate (node a b c 11) 1) ∨
      IsFork (mutate (node a b c 11) 1) 1 ∨ IsRoot (mutate (node a b c 11) 1) 1 := by
  left; refine ⟨5,perm6,?_⟩
  funext u v
  rcases fin4 u with rfl | rfl | rfl | rfl <;>
    rcases fin4 v with rfl | rfl | rfl | rfl <;>
    simp [node,relabel,perm6,mutate,ofSix,correction] <;> grind

theorem edge11_2 (a b c : Int) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) :
    FramedCore (node a b c) (mutate (node a b c 11) 2) ∨
      IsFork (mutate (node a b c 11) 2) 2 ∨ IsRoot (mutate (node a b c 11) 2) 2 := by
  left; refine ⟨3,perm0,?_⟩
  funext u v
  rcases fin4 u with rfl | rfl | rfl | rfl <;>
    rcases fin4 v with rfl | rfl | rfl | rfl <;>
    simp [node,relabel,perm0,mutate,ofSix,correction] <;> grind

theorem edge11_3 (a b c : Int) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) :
    FramedCore (node a b c) (mutate (node a b c 11) 3) ∨
      IsFork (mutate (node a b c 11) 3) 3 ∨ IsRoot (mutate (node a b c 11) 3) 3 := by
  left; refine ⟨13,perm1,?_⟩
  funext u v
  rcases fin4 u with rfl | rfl | rfl | rfl <;>
    rcases fin4 v with rfl | rfl | rfl | rfl <;>
    simp [node,relabel,perm1,mutate,ofSix,correction] <;> grind

theorem cyclic12 (a b c : Int) (_ha : 2≤a) (_hb : 2≤b) (_hc : 2≤c) : ¬ Acyclic (node a b c 12) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 1 2 (by simp [node,ofSix] <;> omega)
  have h1 := hr 2 3 (by simp [node,ofSix] <;> omega)
  have h2 := hr 3 1 (by simp [node,ofSix] <;> omega)
  omega

theorem edge12_0 (a b c : Int) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) :
    FramedCore (node a b c) (mutate (node a b c 12) 0) ∨
      IsFork (mutate (node a b c 12) 0) 0 ∨ IsRoot (mutate (node a b c 12) 0) 0 := by
  left; refine ⟨4,perm7,?_⟩
  funext u v
  rcases fin4 u with rfl | rfl | rfl | rfl <;>
    rcases fin4 v with rfl | rfl | rfl | rfl <;>
    simp [node,relabel,perm7,mutate,ofSix,correction] <;> grind

theorem edge12_1 (a b c : Int) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) :
    FramedCore (node a b c) (mutate (node a b c 12) 1) ∨
      IsFork (mutate (node a b c 12) 1) 1 ∨ IsRoot (mutate (node a b c 12) 1) 1 := by
  right; right
  have hd : Regions.Domain (b + a) ((-1) + a*b + a^2) (b*c + a*c) (a) (c) := by
    have hsa0 := product_minus_one a a (by omega) (by omega)
    have hpa0 := Forks.product_add_dominates a a 0 (by omega) (by omega) (by decide)
    have hsa1 := product_minus_one a b (by omega) (by omega)
    have hpa1 := Forks.product_add_dominates a b 0 (by omega) (by omega) (by decide)
    have hsa2 := product_minus_one a c (by omega) (by omega)
    have hpa2 := Forks.product_add_dominates a c 0 (by omega) (by omega) (by decide)
    have hsa3 := product_minus_one a (a+b) (by omega) (by omega)
    have hpa3 := Forks.product_add_dominates a (a+b) 0 (by omega) (by omega) (by decide)
    have hsa4 := product_minus_one a (b+c) (by omega) (by omega)
    have hpa4 := Forks.product_add_dominates a (b+c) 0 (by omega) (by omega) (by decide)
    have hsa5 := product_minus_one a (c+a) (by omega) (by omega)
    have hpa5 := Forks.product_add_dominates a (c+a) 0 (by omega) (by omega) (by decide)
    have hsb0 := product_minus_one b a (by omega) (by omega)
    have hpb0 := Forks.product_add_dominates b a 0 (by omega) (by omega) (by decide)
    have hsb1 := product_minus_one b b (by omega) (by omega)
    have hpb1 := Forks.product_add_dominates b b 0 (by omega) (by omega) (by decide)
    have hsb2 := product_minus_one b c (by omega) (by omega)
    have hpb2 := Forks.product_add_dominates b c 0 (by omega) (by omega) (by decide)
    have hsb3 := product_minus_one b (a+b) (by omega) (by omega)
    have hpb3 := Forks.product_add_dominates b (a+b) 0 (by omega) (by omega) (by decide)
    have hsb4 := product_minus_one b (b+c) (by omega) (by omega)
    have hpb4 := Forks.product_add_dominates b (b+c) 0 (by omega) (by omega) (by decide)
    have hsb5 := product_minus_one b (c+a) (by omega) (by omega)
    have hpb5 := Forks.product_add_dominates b (c+a) 0 (by omega) (by omega) (by decide)
    have hsc0 := product_minus_one c a (by omega) (by omega)
    have hpc0 := Forks.product_add_dominates c a 0 (by omega) (by omega) (by decide)
    have hsc1 := product_minus_one c b (by omega) (by omega)
    have hpc1 := Forks.product_add_dominates c b 0 (by omega) (by omega) (by decide)
    have hsc2 := product_minus_one c c (by omega) (by omega)
    have hpc2 := Forks.product_add_dominates c c 0 (by omega) (by omega) (by decide)
    have hsc3 := product_minus_one c (a+b) (by omega) (by omega)
    have hpc3 := Forks.product_add_dominates c (a+b) 0 (by omega) (by omega) (by decide)
    have hsc4 := product_minus_one c (b+c) (by omega) (by omega)
    have hpc4 := Forks.product_add_dominates c (b+c) 0 (by omega) (by omega) (by decide)
    have hsc5 := product_minus_one c (c+a) (by omega) (by omega)
    have hpc5 := Forks.product_add_dominates c (c+a) 0 (by omega) (by omega) (by decide)
    unfold Regions.Domain
    grind
  have he : relabel (mutate (node a b c 12) 1) perm11 = root (b + a) ((-1) + a*b + a^2) (b*c + a*c) (a) (c) (1) := by
    funext u v
    rcases fin4 u with rfl | rfl | rfl | rfl <;>
      rcases fin4 v with rfl | rfl | rfl | rfl <;>
      simp [node,relabel,perm11,root,mutate,ofSix,correction] <;> grind
  have hr : IsRoot (relabel (mutate (node a b c 12) 1) perm11) 0 := by
    rw [he]; exact IsRoot.basic _ _ _ _ _ _ hd (by decide)
  exact root_of_relabel perm11 hr

theorem edge12_2 (a b c : Int) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) :
    FramedCore (node a b c) (mutate (node a b c 12) 2) ∨
      IsFork (mutate (node a b c 12) 2) 2 ∨ IsRoot (mutate (node a b c 12) 2) 2 := by
  left; refine ⟨8,perm1,?_⟩
  funext u v
  rcases fin4 u with rfl | rfl | rfl | rfl <;>
    rcases fin4 v with rfl | rfl | rfl | rfl <;>
    simp [node,relabel,perm1,mutate,ofSix,correction] <;> grind

theorem edge12_3 (a b c : Int) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) :
    FramedCore (node a b c) (mutate (node a b c 12) 3) ∨
      IsFork (mutate (node a b c 12) 3) 3 ∨ IsRoot (mutate (node a b c 12) 3) 3 := by
  left; refine ⟨7,perm0,?_⟩
  funext u v
  rcases fin4 u with rfl | rfl | rfl | rfl <;>
    rcases fin4 v with rfl | rfl | rfl | rfl <;>
    simp [node,relabel,perm0,mutate,ofSix,correction] <;> grind

theorem cyclic13 (a b c : Int) (_ha : 2≤a) (_hb : 2≤b) (_hc : 2≤c) : ¬ Acyclic (node a b c 13) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by simp [node,ofSix] <;> omega)
  have h1 := hr 3 2 (by simp [node,ofSix] <;> omega)
  have h2 := hr 2 0 (by simp [node,ofSix] <;> omega)
  omega

theorem edge13_0 (a b c : Int) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) :
    FramedCore (node a b c) (mutate (node a b c 13) 0) ∨
      IsFork (mutate (node a b c 13) 0) 0 ∨ IsRoot (mutate (node a b c 13) 0) 0 := by
  right; right
  have hd : Regions.Domain (b + a) ((-1) + b^2 + a*b) (b*c + a*c) (b) (c) := by
    have hsa0 := product_minus_one a a (by omega) (by omega)
    have hpa0 := Forks.product_add_dominates a a 0 (by omega) (by omega) (by decide)
    have hsa1 := product_minus_one a b (by omega) (by omega)
    have hpa1 := Forks.product_add_dominates a b 0 (by omega) (by omega) (by decide)
    have hsa2 := product_minus_one a c (by omega) (by omega)
    have hpa2 := Forks.product_add_dominates a c 0 (by omega) (by omega) (by decide)
    have hsa3 := product_minus_one a (a+b) (by omega) (by omega)
    have hpa3 := Forks.product_add_dominates a (a+b) 0 (by omega) (by omega) (by decide)
    have hsa4 := product_minus_one a (b+c) (by omega) (by omega)
    have hpa4 := Forks.product_add_dominates a (b+c) 0 (by omega) (by omega) (by decide)
    have hsa5 := product_minus_one a (c+a) (by omega) (by omega)
    have hpa5 := Forks.product_add_dominates a (c+a) 0 (by omega) (by omega) (by decide)
    have hsb0 := product_minus_one b a (by omega) (by omega)
    have hpb0 := Forks.product_add_dominates b a 0 (by omega) (by omega) (by decide)
    have hsb1 := product_minus_one b b (by omega) (by omega)
    have hpb1 := Forks.product_add_dominates b b 0 (by omega) (by omega) (by decide)
    have hsb2 := product_minus_one b c (by omega) (by omega)
    have hpb2 := Forks.product_add_dominates b c 0 (by omega) (by omega) (by decide)
    have hsb3 := product_minus_one b (a+b) (by omega) (by omega)
    have hpb3 := Forks.product_add_dominates b (a+b) 0 (by omega) (by omega) (by decide)
    have hsb4 := product_minus_one b (b+c) (by omega) (by omega)
    have hpb4 := Forks.product_add_dominates b (b+c) 0 (by omega) (by omega) (by decide)
    have hsb5 := product_minus_one b (c+a) (by omega) (by omega)
    have hpb5 := Forks.product_add_dominates b (c+a) 0 (by omega) (by omega) (by decide)
    have hsc0 := product_minus_one c a (by omega) (by omega)
    have hpc0 := Forks.product_add_dominates c a 0 (by omega) (by omega) (by decide)
    have hsc1 := product_minus_one c b (by omega) (by omega)
    have hpc1 := Forks.product_add_dominates c b 0 (by omega) (by omega) (by decide)
    have hsc2 := product_minus_one c c (by omega) (by omega)
    have hpc2 := Forks.product_add_dominates c c 0 (by omega) (by omega) (by decide)
    have hsc3 := product_minus_one c (a+b) (by omega) (by omega)
    have hpc3 := Forks.product_add_dominates c (a+b) 0 (by omega) (by omega) (by decide)
    have hsc4 := product_minus_one c (b+c) (by omega) (by omega)
    have hpc4 := Forks.product_add_dominates c (b+c) 0 (by omega) (by omega) (by decide)
    have hsc5 := product_minus_one c (c+a) (by omega) (by omega)
    have hpc5 := Forks.product_add_dominates c (c+a) 0 (by omega) (by omega) (by decide)
    unfold Regions.Domain
    grind
  have he : relabel (reverse (mutate (node a b c 13) 0)) perm5 = root (b + a) ((-1) + b^2 + a*b) (b*c + a*c) (b) (c) (1) := by
    funext u v
    rcases fin4 u with rfl | rfl | rfl | rfl <;>
      rcases fin4 v with rfl | rfl | rfl | rfl <;>
      simp [node,relabel,perm5,reverse,root,mutate,ofSix,correction] <;> grind
  have hr : IsRoot (relabel (reverse (mutate (node a b c 13) 0)) perm5) 0 := by
    rw [he]; exact IsRoot.basic _ _ _ _ _ _ hd (by decide)
  exact root_of_reverse (root_of_relabel perm5 hr)

theorem edge13_1 (a b c : Int) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) :
    FramedCore (node a b c) (mutate (node a b c 13) 1) ∨
      IsFork (mutate (node a b c 13) 1) 1 ∨ IsRoot (mutate (node a b c 13) 1) 1 := by
  left; refine ⟨7,perm6,?_⟩
  funext u v
  rcases fin4 u with rfl | rfl | rfl | rfl <;>
    rcases fin4 v with rfl | rfl | rfl | rfl <;>
    simp [node,relabel,perm6,mutate,ofSix,correction] <;> grind

theorem edge13_2 (a b c : Int) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) :
    FramedCore (node a b c) (mutate (node a b c 13) 2) ∨
      IsFork (mutate (node a b c 13) 2) 2 ∨ IsRoot (mutate (node a b c 13) 2) 2 := by
  left; refine ⟨11,perm1,?_⟩
  funext u v
  rcases fin4 u with rfl | rfl | rfl | rfl <;>
    rcases fin4 v with rfl | rfl | rfl | rfl <;>
    simp [node,relabel,perm1,mutate,ofSix,correction] <;> grind

theorem edge13_3 (a b c : Int) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) :
    FramedCore (node a b c) (mutate (node a b c 13) 3) ∨
      IsFork (mutate (node a b c 13) 3) 3 ∨ IsRoot (mutate (node a b c 13) 3) 3 := by
  left; refine ⟨4,perm1,?_⟩
  funext u v
  rcases fin4 u with rfl | rfl | rfl | rfl <;>
    rcases fin4 v with rfl | rfl | rfl | rfl <;>
    simp [node,relabel,perm1,mutate,ofSix,correction] <;> grind

theorem all_cyclic (a b c : Int) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) : ∀ i, ¬ Acyclic (node a b c i) := by
  intro i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 := by omega
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact cyclic0 a b c ha hb hc
  · exact cyclic1 a b c ha hb hc
  · exact cyclic2 a b c ha hb hc
  · exact cyclic3 a b c ha hb hc
  · exact cyclic4 a b c ha hb hc
  · exact cyclic5 a b c ha hb hc
  · exact cyclic6 a b c ha hb hc
  · exact cyclic7 a b c ha hb hc
  · exact cyclic8 a b c ha hb hc
  · exact cyclic9 a b c ha hb hc
  · exact cyclic10 a b c ha hb hc
  · exact cyclic11 a b c ha hb hc
  · exact cyclic12 a b c ha hb hc
  · exact cyclic13 a b c ha hb hc

theorem all_skew (a b c : Int) : ∀ i, SkewSymmetric (node a b c i) := by
  intro i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 := by omega
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ofSix_skew _ _ _ _ _ _

theorem all_edges (a b c : Int) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) : ∀ i k,
    FramedCore (node a b c) (mutate (node a b c i) k) ∨ IsFork (mutate (node a b c i) k) k ∨ IsRoot (mutate (node a b c i) k) k := by
  intro i k
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 := by omega
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases fin4 k with rfl | rfl | rfl | rfl
  · exact edge0_0 a b c ha hb hc
  · exact edge0_1 a b c ha hb hc
  · exact edge0_2 a b c ha hb hc
  · exact edge0_3 a b c ha hb hc
  · exact edge1_0 a b c ha hb hc
  · exact edge1_1 a b c ha hb hc
  · exact edge1_2 a b c ha hb hc
  · exact edge1_3 a b c ha hb hc
  · exact edge2_0 a b c ha hb hc
  · exact edge2_1 a b c ha hb hc
  · exact edge2_2 a b c ha hb hc
  · exact edge2_3 a b c ha hb hc
  · exact edge3_0 a b c ha hb hc
  · exact edge3_1 a b c ha hb hc
  · exact edge3_2 a b c ha hb hc
  · exact edge3_3 a b c ha hb hc
  · exact edge4_0 a b c ha hb hc
  · exact edge4_1 a b c ha hb hc
  · exact edge4_2 a b c ha hb hc
  · exact edge4_3 a b c ha hb hc
  · exact edge5_0 a b c ha hb hc
  · exact edge5_1 a b c ha hb hc
  · exact edge5_2 a b c ha hb hc
  · exact edge5_3 a b c ha hb hc
  · exact edge6_0 a b c ha hb hc
  · exact edge6_1 a b c ha hb hc
  · exact edge6_2 a b c ha hb hc
  · exact edge6_3 a b c ha hb hc
  · exact edge7_0 a b c ha hb hc
  · exact edge7_1 a b c ha hb hc
  · exact edge7_2 a b c ha hb hc
  · exact edge7_3 a b c ha hb hc
  · exact edge8_0 a b c ha hb hc
  · exact edge8_1 a b c ha hb hc
  · exact edge8_2 a b c ha hb hc
  · exact edge8_3 a b c ha hb hc
  · exact edge9_0 a b c ha hb hc
  · exact edge9_1 a b c ha hb hc
  · exact edge9_2 a b c ha hb hc
  · exact edge9_3 a b c ha hb hc
  · exact edge10_0 a b c ha hb hc
  · exact edge10_1 a b c ha hb hc
  · exact edge10_2 a b c ha hb hc
  · exact edge10_3 a b c ha hb hc
  · exact edge11_0 a b c ha hb hc
  · exact edge11_1 a b c ha hb hc
  · exact edge11_2 a b c ha hb hc
  · exact edge11_3 a b c ha hb hc
  · exact edge12_0 a b c ha hb hc
  · exact edge12_1 a b c ha hb hc
  · exact edge12_2 a b c ha hb hc
  · exact edge12_3 a b c ha hb hc
  · exact edge13_0 a b c ha hb hc
  · exact edge13_1 a b c ha hb hc
  · exact edge13_2 a b c ha hb hc
  · exact edge13_3 a b c ha hb hc

theorem residual_three_parameter_NMA (a b c : Int) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) :
    ¬ MutationAcyclic (ofSix (-a) (-b) (-c) (-1) 1 (-1)) := by
  have hn := framed_region_NMA RegionCells.root_cells_exist (node a b c) (all_skew a b c)
    (all_cyclic a b c ha hb hc) (all_edges a b c ha hb hc) 0
  have he : relabel (ofSix (-a) (-b) (-c) (-1) 1 (-1)) perm5 = node a b c 0 := by
    funext i j; rcases fin4 i with rfl | rfl | rfl | rfl <;>
      rcases fin4 j with rfl | rfl | rfl | rfl <;> simp [node,relabel,perm5,ofSix]
  intro hm
  apply hn; rw [← he]; exact (MA_relabel_iff _ perm5).mpr hm

theorem residual_diagonal_NMA (t : Int) (ht : 2≤t) :
    ¬ MutationAcyclic (ofSix (-t) (-t) (-t) (-1) 1 (-1)) :=
  residual_three_parameter_NMA t t t ht ht ht

end QuiverProofs.ResidualFamily
