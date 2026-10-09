import QuiverProofs.QFamilyPolynomialInterfaces
/-! The q041/q160 mutation component: fourteen finite states, ten polynomial corridor phases, two parameterized generic strips and one fixed generic strip. Polynomial coefficient certificates cover every nonnegative integer parameter, and all three parent interfaces of each strip are checked. -/
namespace QuiverProofs.Q041Corridor
open PolynomialCertificate QFamilyPolynomialInterfaces RecursiveRegions Forks Regions ForkCertificates
set_option maxHeartbeats 12000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

private theorem baseFin (i : Fin 14) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 := by omega
def baseP (i : Fin 14) : PMatrix := match i.val with
  | 0 => (six [-2] [-2] [-1] [-2] [1] [-1])
  | 1 => (six [-5] [-2] [3] [1] [-1] [-1])
  | 2 => (six [-5] [-1] [1] [-2] [-2] [-2])
  | 3 => (six [-3] [-2] [2] [1] [-1] [2])
  | 4 => (six [-3] [-2] [1] [-1] [-1] [1])
  | 5 => (six [-3] [-1] [1] [-2] [-1] [1])
  | 6 => (six [-3] [-2] [1] [1] [-2] [-3])
  | 7 => (six [-7] [-2] [3] [1] [-2] [-1])
  | 8 => (six [-5] [-5] [2] [-2] [-1] [-3])
  | 9 => (six [-11] [-3] [2] [2] [-7] [-1])
  | 10 => (six [-9] [1] [2] [-2] [-1] [-1])
  | 11 => (six [-15] [-3] [5] [-3] [-2] [-1])
  | 12 => (six [-17] [-1] [3] [-7] [-2] [-1])
  | _ => (six [-49] [-2] [3] [-7] [-17] [-1])
def baseNode (i : Fin 14) : Matrix 4 := matrix (baseP i) 0

private theorem tailFin (i : Fin 10) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 := by omega
def tailP (i : Fin 10) : PMatrix := match i.val with
  | 0 => (six [-7,-4] [1] [1] [-6,-4] [-5] [-1])
  | 1 => (six [-7,-4] [1] [1] [-2,-4] [-1] [-1])
  | 2 => (six [-6,-4] [-1] [2] [-5] [-2,-4] [-1])
  | 3 => (six [-13,-36,-16] [-1] [3,4] [-6,-4] [-1] [-1])
  | 4 => (six [-38,-160,-192,-64] [-2,-4] [3,4] [-6,-4] [-13,-36,-16] [-1])
  | 5 => (six [-6,-4] [-1] [2] [1] [-2,-4] [-1])
  | 6 => (six [-79,-268,-240,-64] [-1] [7,4] [-10,-32,-16] [-3,-4] [-1])
  | 7 => (six [-550,-2188,-2752,-1408,-256] [-6,-4] [7,4] [-10,-32,-16] [-79,-268,-240,-64] [-1])
  | 8 => (six [-10,-32,-16] [-3,-4] [2,4] [1] [-6,-4] [-1])
  | _ => (six [-58,-228,-224,-64] [-7,-4] [6,4] [3,4] [-10,-32,-16] [-1])
def tailNode (t : Int) (i : Fin 10) : Matrix 4 := matrix (tailP i) t


def Core (B : Matrix 4) : Prop :=
  (∃ i, B=baseNode i) ∨ ∃ t : Int, 0≤t ∧ ∃ i, B=tailNode t i
abbrev SafeCore := Safe data Core

theorem base_safe (i : Fin 14) : SafeCore (baseNode i) := Safe.central (Or.inl ⟨i,rfl⟩)
theorem tail_safe (t : Int) (ht : 0≤t) (i : Fin 10) : SafeCore (tailNode t i) :=
  Safe.central (Or.inr ⟨t,ht,i,rfl⟩)

def compose : P → P → P
  | [], _ => []
  | a::p, q => add [a] (mul q (compose p q))
theorem eval_compose (p q : P) (t : Int) : eval (compose p q) t=eval p (eval q t) := by
  induction p with
  | nil => rfl
  | cons a p ih => simp [compose,eval_add,eval_mul,eval,ih]
def shiftP (B : PMatrix) (d : Int) : PMatrix := fun i j => compose (B i j) [d,1]
theorem matrix_shift (B : PMatrix) (d t : Int) : matrix (shiftP B d) t=matrix B (t+d) := by
  funext i j
  simp only [matrix,shiftP,eval_compose,eval]
  congr 1
  omega

theorem tail_shift_safe (t : Int) (i : Fin 10) (d : Int) (ht : 0≤t+d) :
    SafeCore (matrix (shiftP (tailP i) d) t) := by
  rw [matrix_shift]
  exact tail_safe (t+d) ht i

theorem tail_point_safe_0_0 : SafeCore (matrix (six [-7] [1] [1] [-6] [-5] [-1]) 0) := by
  have he : matrix (six [-7] [1] [1] [-6] [-5] [-1]) 0=tailNode 0 0 := by funext u v; revert u v; decide
  rw [he]; exact tail_safe 0 (by decide) 0

theorem tail_point_safe_0_1 : SafeCore (matrix (six [-7] [1] [1] [-2] [-1] [-1]) 0) := by
  have he : matrix (six [-7] [1] [1] [-2] [-1] [-1]) 0=tailNode 0 1 := by funext u v; revert u v; decide
  rw [he]; exact tail_safe 0 (by decide) 1

theorem tail_point_safe_0_2 : SafeCore (matrix (six [-6] [-1] [2] [-5] [-2] [-1]) 0) := by
  have he : matrix (six [-6] [-1] [2] [-5] [-2] [-1]) 0=tailNode 0 2 := by funext u v; revert u v; decide
  rw [he]; exact tail_safe 0 (by decide) 2

theorem tail_point_safe_0_3 : SafeCore (matrix (six [-13] [-1] [3] [-6] [-1] [-1]) 0) := by
  have he : matrix (six [-13] [-1] [3] [-6] [-1] [-1]) 0=tailNode 0 3 := by funext u v; revert u v; decide
  rw [he]; exact tail_safe 0 (by decide) 3

theorem tail_point_safe_0_4 : SafeCore (matrix (six [-38] [-2] [3] [-6] [-13] [-1]) 0) := by
  have he : matrix (six [-38] [-2] [3] [-6] [-13] [-1]) 0=tailNode 0 4 := by funext u v; revert u v; decide
  rw [he]; exact tail_safe 0 (by decide) 4

theorem tail_point_safe_0_5 : SafeCore (matrix (six [-6] [-1] [2] [1] [-2] [-1]) 0) := by
  have he : matrix (six [-6] [-1] [2] [1] [-2] [-1]) 0=tailNode 0 5 := by funext u v; revert u v; decide
  rw [he]; exact tail_safe 0 (by decide) 5

theorem tail_point_safe_0_6 : SafeCore (matrix (six [-79] [-1] [7] [-10] [-3] [-1]) 0) := by
  have he : matrix (six [-79] [-1] [7] [-10] [-3] [-1]) 0=tailNode 0 6 := by funext u v; revert u v; decide
  rw [he]; exact tail_safe 0 (by decide) 6

theorem tail_point_safe_0_7 : SafeCore (matrix (six [-550] [-6] [7] [-10] [-79] [-1]) 0) := by
  have he : matrix (six [-550] [-6] [7] [-10] [-79] [-1]) 0=tailNode 0 7 := by funext u v; revert u v; decide
  rw [he]; exact tail_safe 0 (by decide) 7

theorem tail_point_safe_0_8 : SafeCore (matrix (six [-10] [-3] [2] [1] [-6] [-1]) 0) := by
  have he : matrix (six [-10] [-3] [2] [1] [-6] [-1]) 0=tailNode 0 8 := by funext u v; revert u v; decide
  rw [he]; exact tail_safe 0 (by decide) 8

theorem tail_point_safe_0_9 : SafeCore (matrix (six [-58] [-7] [6] [3] [-10] [-1]) 0) := by
  have he : matrix (six [-58] [-7] [6] [3] [-10] [-1]) 0=tailNode 0 9 := by funext u v; revert u v; decide
  rw [he]; exact tail_safe 0 (by decide) 9

theorem tail_point_safe_1_0 : SafeCore (matrix (six [-11] [1] [1] [-10] [-5] [-1]) 0) := by
  have he : matrix (six [-11] [1] [1] [-10] [-5] [-1]) 0=tailNode 1 0 := by funext u v; revert u v; decide
  rw [he]; exact tail_safe 1 (by decide) 0

theorem tail_point_safe_1_1 : SafeCore (matrix (six [-11] [1] [1] [-6] [-1] [-1]) 0) := by
  have he : matrix (six [-11] [1] [1] [-6] [-1] [-1]) 0=tailNode 1 1 := by funext u v; revert u v; decide
  rw [he]; exact tail_safe 1 (by decide) 1

theorem tail_point_safe_1_2 : SafeCore (matrix (six [-10] [-1] [2] [-5] [-6] [-1]) 0) := by
  have he : matrix (six [-10] [-1] [2] [-5] [-6] [-1]) 0=tailNode 1 2 := by funext u v; revert u v; decide
  rw [he]; exact tail_safe 1 (by decide) 2

theorem tail_point_safe_1_3 : SafeCore (matrix (six [-65] [-1] [7] [-10] [-1] [-1]) 0) := by
  have he : matrix (six [-65] [-1] [7] [-10] [-1] [-1]) 0=tailNode 1 3 := by funext u v; revert u v; decide
  rw [he]; exact tail_safe 1 (by decide) 3

theorem tail_point_safe_1_4 : SafeCore (matrix (six [-454] [-6] [7] [-10] [-65] [-1]) 0) := by
  have he : matrix (six [-454] [-6] [7] [-10] [-65] [-1]) 0=tailNode 1 4 := by funext u v; revert u v; decide
  rw [he]; exact tail_safe 1 (by decide) 4

theorem tail_point_safe_1_5 : SafeCore (matrix (six [-10] [-1] [2] [1] [-6] [-1]) 0) := by
  have he : matrix (six [-10] [-1] [2] [1] [-6] [-1]) 0=tailNode 1 5 := by funext u v; revert u v; decide
  rw [he]; exact tail_safe 1 (by decide) 5

theorem tail_point_safe_1_6 : SafeCore (matrix (six [-651] [-1] [11] [-58] [-7] [-1]) 0) := by
  have he : matrix (six [-651] [-1] [11] [-58] [-7] [-1]) 0=tailNode 1 6 := by funext u v; revert u v; decide
  rw [he]; exact tail_safe 1 (by decide) 6

theorem tail_point_safe_1_7 : SafeCore (matrix (six [-7154] [-10] [11] [-58] [-651] [-1]) 0) := by
  have he : matrix (six [-7154] [-10] [11] [-58] [-651] [-1]) 0=tailNode 1 7 := by funext u v; revert u v; decide
  rw [he]; exact tail_safe 1 (by decide) 7

theorem tail_point_safe_1_8 : SafeCore (matrix (six [-58] [-7] [6] [1] [-10] [-1]) 0) := by
  have he : matrix (six [-58] [-7] [6] [1] [-10] [-1]) 0=tailNode 1 8 := by funext u v; revert u v; decide
  rw [he]; exact tail_safe 1 (by decide) 8

theorem tail_point_safe_1_9 : SafeCore (matrix (six [-574] [-11] [10] [7] [-58] [-1]) 0) := by
  have he : matrix (six [-574] [-11] [10] [7] [-58] [-1]) 0=tailNode 1 9 := by funext u v; revert u v; decide
  rw [he]; exact tail_safe 1 (by decide) 9

theorem tail_point_safe_2_0 : SafeCore (matrix (six [-15] [1] [1] [-14] [-5] [-1]) 0) := by
  have he : matrix (six [-15] [1] [1] [-14] [-5] [-1]) 0=tailNode 2 0 := by funext u v; revert u v; decide
  rw [he]; exact tail_safe 2 (by decide) 0

theorem tail_point_safe_2_1 : SafeCore (matrix (six [-15] [1] [1] [-10] [-1] [-1]) 0) := by
  have he : matrix (six [-15] [1] [1] [-10] [-1] [-1]) 0=tailNode 2 1 := by funext u v; revert u v; decide
  rw [he]; exact tail_safe 2 (by decide) 1

theorem tail_point_safe_2_2 : SafeCore (matrix (six [-14] [-1] [2] [-5] [-10] [-1]) 0) := by
  have he : matrix (six [-14] [-1] [2] [-5] [-10] [-1]) 0=tailNode 2 2 := by funext u v; revert u v; decide
  rw [he]; exact tail_safe 2 (by decide) 2

theorem tail_point_safe_2_3 : SafeCore (matrix (six [-149] [-1] [11] [-14] [-1] [-1]) 0) := by
  have he : matrix (six [-149] [-1] [11] [-14] [-1] [-1]) 0=tailNode 2 3 := by funext u v; revert u v; decide
  rw [he]; exact tail_safe 2 (by decide) 3

theorem tail_point_safe_2_4 : SafeCore (matrix (six [-1638] [-10] [11] [-14] [-149] [-1]) 0) := by
  have he : matrix (six [-1638] [-10] [11] [-14] [-149] [-1]) 0=tailNode 2 4 := by funext u v; revert u v; decide
  rw [he]; exact tail_safe 2 (by decide) 4

theorem tail_point_safe_2_5 : SafeCore (matrix (six [-14] [-1] [2] [1] [-10] [-1]) 0) := by
  have he : matrix (six [-14] [-1] [2] [1] [-10] [-1]) 0=tailNode 2 5 := by funext u v; revert u v; decide
  rw [he]; exact tail_safe 2 (by decide) 5

theorem tail_point_safe_2_6 : SafeCore (matrix (six [-2087] [-1] [15] [-138] [-11] [-1]) 0) := by
  have he : matrix (six [-2087] [-1] [15] [-138] [-11] [-1]) 0=tailNode 2 6 := by funext u v; revert u v; decide
  rw [he]; exact tail_safe 2 (by decide) 6

theorem tail_point_safe_2_7 : SafeCore (matrix (six [-31294] [-14] [15] [-138] [-2087] [-1]) 0) := by
  have he : matrix (six [-31294] [-14] [15] [-138] [-2087] [-1]) 0=tailNode 2 7 := by funext u v; revert u v; decide
  rw [he]; exact tail_safe 2 (by decide) 7

theorem tail_point_safe_2_8 : SafeCore (matrix (six [-138] [-11] [10] [1] [-14] [-1]) 0) := by
  have he : matrix (six [-138] [-11] [10] [1] [-14] [-1]) 0=tailNode 2 8 := by funext u v; revert u v; decide
  rw [he]; exact tail_safe 2 (by decide) 8

theorem tail_point_safe_2_9 : SafeCore (matrix (six [-1922] [-15] [14] [11] [-138] [-1]) 0) := by
  have he : matrix (six [-1922] [-15] [14] [11] [-138] [-1]) 0=tailNode 2 9 := by funext u v; revert u v; decide
  rw [he]; exact tail_safe 2 (by decide) 9

def tailParam0_0 : P := [2,4]
def tailParam0_1 : P := [13,36,16]
def tailParam0_2 : P := [6,4]
def tailParam0_3 : P := [7,4]
theorem tailDomain0 (t : Int) (ht : 0≤t) : GenericStrip.Domain (eval tailParam0_0 t) (eval tailParam0_1 t) (eval tailParam0_2 t) (eval tailParam0_3 t) :=
  generic_domain tailParam0_0 tailParam0_1 tailParam0_2 tailParam0_3 t ht (by decide)
def tailRegion0 (t : Int) (ht : 0≤t) : Region := .inl (.inl ⟨eval tailParam0_0 t,⟨eval tailParam0_1 t,eval tailParam0_2 t,eval tailParam0_3 t⟩,tailDomain0 t ht⟩)
theorem tailParent0_0 (t : Int) (ht : 0≤t) : data.parent (tailRegion0 t ht) (0 : Fin 3)=(reverse (relabel (matrix (shiftP (tailP 3) (0)) t) perm3)) := by
  have he := mutation_equal (generic tailParam0_0 tailParam0_1 tailParam0_2 tailParam0_3 0) (preverse (prelabel (shiftP (tailP 3) (0)) perm3)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem tailParent0_1 (t : Int) (ht : 0≤t) : data.parent (tailRegion0 t ht) (1 : Fin 3)=(relabel (matrix (shiftP (tailP 1) (0)) t) perm17) := by
  have he := mutation_equal (generic tailParam0_0 tailParam0_1 tailParam0_2 tailParam0_3 0) (prelabel (shiftP (tailP 1) (0)) perm17) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem tailParent0_2 (t : Int) (ht : 0≤t) : data.parent (tailRegion0 t ht) (2 : Fin 3)=(reverse (relabel (matrix (shiftP (tailP 4) (0)) t) perm16)) := by
  have he := mutation_equal (generic tailParam0_0 tailParam0_1 tailParam0_2 tailParam0_3 2) (preverse (prelabel (shiftP (tailP 4) (0)) perm16)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem tailParents0_safe (t : Int) (ht : 0≤t) (p : Fin 3) : SafeCore (data.parent (tailRegion0 t ht) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by omega
  rcases hp with rfl|rfl|rfl
  · rw [tailParent0_0 t ht]
    exact Safe.reversed (Safe.framed (tail_shift_safe t 3 (0) (by omega)) perm3)
  · rw [tailParent0_1 t ht]
    exact Safe.framed (tail_shift_safe t 1 (0) (by omega)) perm17
  · rw [tailParent0_2 t ht]
    exact Safe.reversed (Safe.framed (tail_shift_safe t 4 (0) (by omega)) perm16)
theorem tailRegion0_safe (t : Int) (ht : 0≤t) (i : Fin 3) : SafeCore (matrix (generic tailParam0_0 tailParam0_1 tailParam0_2 tailParam0_3 i) t) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core) (tailRegion0 t ht) (tailParents0_safe t ht) (0,Fin.castLE (by decide) i)

def tailParam1_0 : P := [6,4]
def tailParam1_1 : P := [79,268,240,64]
def tailParam1_2 : P := [10,32,16]
def tailParam1_3 : P := [13,36,16]
theorem tailDomain1 (t : Int) (ht : 0≤t) : GenericStrip.Domain (eval tailParam1_0 t) (eval tailParam1_1 t) (eval tailParam1_2 t) (eval tailParam1_3 t) :=
  generic_domain tailParam1_0 tailParam1_1 tailParam1_2 tailParam1_3 t ht (by decide)
def tailRegion1 (t : Int) (ht : 0≤t) : Region := .inl (.inl ⟨eval tailParam1_0 t,⟨eval tailParam1_1 t,eval tailParam1_2 t,eval tailParam1_3 t⟩,tailDomain1 t ht⟩)
theorem tailParent1_0 (t : Int) (ht : 0≤t) : data.parent (tailRegion1 t ht) (0 : Fin 3)=(reverse (relabel (matrix (shiftP (tailP 6) (0)) t) perm3)) := by
  have he := mutation_equal (generic tailParam1_0 tailParam1_1 tailParam1_2 tailParam1_3 0) (preverse (prelabel (shiftP (tailP 6) (0)) perm3)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem tailParent1_1 (t : Int) (ht : 0≤t) : data.parent (tailRegion1 t ht) (1 : Fin 3)=(relabel (matrix (shiftP (tailP 3) (0)) t) perm17) := by
  have he := mutation_equal (generic tailParam1_0 tailParam1_1 tailParam1_2 tailParam1_3 0) (prelabel (shiftP (tailP 3) (0)) perm17) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem tailParent1_2 (t : Int) (ht : 0≤t) : data.parent (tailRegion1 t ht) (2 : Fin 3)=(reverse (relabel (matrix (shiftP (tailP 7) (0)) t) perm16)) := by
  have he := mutation_equal (generic tailParam1_0 tailParam1_1 tailParam1_2 tailParam1_3 2) (preverse (prelabel (shiftP (tailP 7) (0)) perm16)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem tailParents1_safe (t : Int) (ht : 0≤t) (p : Fin 3) : SafeCore (data.parent (tailRegion1 t ht) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by omega
  rcases hp with rfl|rfl|rfl
  · rw [tailParent1_0 t ht]
    exact Safe.reversed (Safe.framed (tail_shift_safe t 6 (0) (by omega)) perm3)
  · rw [tailParent1_1 t ht]
    exact Safe.framed (tail_shift_safe t 3 (0) (by omega)) perm17
  · rw [tailParent1_2 t ht]
    exact Safe.reversed (Safe.framed (tail_shift_safe t 7 (0) (by omega)) perm16)
theorem tailRegion1_safe (t : Int) (ht : 0≤t) (i : Fin 3) : SafeCore (matrix (generic tailParam1_0 tailParam1_1 tailParam1_2 tailParam1_3 i) t) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core) (tailRegion1 t ht) (tailParents1_safe t ht) (0,Fin.castLE (by decide) i)

def extraParam0_0 : P := [2]
def extraParam0_1 : P := [17]
def extraParam0_2 : P := [7]
def extraParam0_3 : P := [9]
theorem extraDomain0 : GenericStrip.Domain (eval extraParam0_0 0) (eval extraParam0_1 0) (eval extraParam0_2 0) (eval extraParam0_3 0) :=
  generic_domain extraParam0_0 extraParam0_1 extraParam0_2 extraParam0_3 0 (by decide) (by decide)
def extraRegion0 : Region := .inl (.inl ⟨eval extraParam0_0 0,⟨eval extraParam0_1 0,eval extraParam0_2 0,eval extraParam0_3 0⟩,extraDomain0⟩)
theorem extraParent0_0 : data.parent (extraRegion0) (0 : Fin 3)=(reverse (relabel (matrix (baseP 12) 0) perm3)) := by
  have he := mutation_equal (generic extraParam0_0 extraParam0_1 extraParam0_2 extraParam0_3 0) (preverse (prelabel (baseP 12) perm3)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem extraParent0_1 : data.parent (extraRegion0) (1 : Fin 3)=(relabel (matrix (baseP 10) 0) perm17) := by
  have he := mutation_equal (generic extraParam0_0 extraParam0_1 extraParam0_2 extraParam0_3 0) (prelabel (baseP 10) perm17) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem extraParent0_2 : data.parent (extraRegion0) (2 : Fin 3)=(reverse (relabel (matrix (baseP 13) 0) perm16)) := by
  have he := mutation_equal (generic extraParam0_0 extraParam0_1 extraParam0_2 extraParam0_3 2) (preverse (prelabel (baseP 13) perm16)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem extraParents0_safe (p : Fin 3) : SafeCore (data.parent (extraRegion0) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by omega
  rcases hp with rfl|rfl|rfl
  · rw [extraParent0_0]
    exact Safe.reversed (Safe.framed (base_safe 12) perm3)
  · rw [extraParent0_1]
    exact Safe.framed (base_safe 10) perm17
  · rw [extraParent0_2]
    exact Safe.reversed (Safe.framed (base_safe 13) perm16)
theorem extraRegion0_safe (i : Fin 3) : SafeCore (matrix (generic extraParam0_0 extraParam0_1 extraParam0_2 extraParam0_3 i) 0) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core) (extraRegion0) (extraParents0_safe) (0,Fin.castLE (by decide) i)

theorem baseCyclic0 : ¬ Acyclic (baseNode 0) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 1 3 (pos (baseP 0 1 3) 0 (by decide) (by decide))
  have h1 := hr 3 2 (pos (baseP 0 3 2) 0 (by decide) (by decide))
  have h2 := hr 2 1 (pos (baseP 0 2 1) 0 (by decide) (by decide))
  omega

theorem baseEdge0_0 : SafeCore (mutate (baseNode 0) 0) := by
  have he := mutation_equal (baseP 0) (preverse (prelabel (baseP 0) perm2)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (baseP 0) 0) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (base_safe 0) perm2)

theorem baseEdge0_1 : SafeCore (mutate (baseNode 0) 1) := by
  have he := mutation_equal (baseP 0) (preverse (prelabel ((six [-6] [-1] [2] [1] [-2] [-1])) perm10)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (baseP 0) 0) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (tail_point_safe_0_5) perm10)

theorem baseEdge0_2 : SafeCore (mutate (baseNode 0) 2) := by
  have he := mutation_equal (baseP 0) (prelabel (baseP 3) perm3) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (baseP 0) 0) 2)
  rw [he]
  exact Safe.framed (base_safe 3) perm3

theorem baseEdge0_3 : SafeCore (mutate (baseNode 0) 3) := by
  have he := mutation_equal (baseP 0) (prelabel (baseP 4) perm0) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (baseP 0) 0) 3)
  rw [he]
  exact Safe.framed (base_safe 4) perm0

theorem baseCyclic1 : ¬ Acyclic (baseNode 1) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (baseP 1 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (baseP 1 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (baseP 1 1 0) 0 (by decide) (by decide))
  omega

theorem baseEdge1_0 : SafeCore (mutate (baseNode 1) 0) := by
  have he := mutation_equal (baseP 1) (preverse (prelabel (root [3] [5] [14] [2] [5] [1]) perm5)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (base_safe 1) 0
  rw [show mutate (baseNode 1) 0=(reverse (relabel (matrix (root [3] [5] [14] [2] [5] [1]) 0) perm5)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [3] [5] [14] [2] [5] [1] 0 (by decide) (by decide)) perm5)

theorem baseEdge1_1 : SafeCore (mutate (baseNode 1) 1) := by
  have he := mutation_equal (baseP 1) (prelabel (baseP 2) perm6) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (baseP 1) 0) 1)
  rw [he]
  exact Safe.framed (base_safe 2) perm6

theorem baseEdge1_2 : SafeCore (mutate (baseNode 1) 2) := by
  have he := mutation_equal (baseP 1) (preverse (prelabel ((six [-7] [1] [1] [-2] [-1] [-1])) perm6)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (baseP 1) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (tail_point_safe_0_1) perm6)

theorem baseEdge1_3 : SafeCore (mutate (baseNode 1) 3) := by
  have he := mutation_equal (baseP 1) (prelabel (baseP 4) perm3) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (baseP 1) 0) 3)
  rw [he]
  exact Safe.framed (base_safe 4) perm3

theorem baseCyclic2 : ¬ Acyclic (baseNode 2) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (baseP 2 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (baseP 2 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (baseP 2 1 0) 0 (by decide) (by decide))
  omega

theorem baseEdge2_0 : SafeCore (mutate (baseNode 2) 0) := by
  have he := mutation_equal (baseP 2) (prelabel (baseP 1) perm6) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (baseP 2) 0) 0)
  rw [he]
  exact Safe.framed (base_safe 1) perm6

theorem baseEdge2_1 : SafeCore (mutate (baseNode 2) 1) := by
  have he := mutation_equal (baseP 2) (prelabel (fork [5] [2] [2] [9] [11] [2]) perm7) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (base_safe 2)
  rw [show mutate (baseNode 2) 1=(relabel (matrix (fork [5] [2] [2] [9] [11] [2]) 0) perm7) from he]
  exact IsFork.relabelled (fork_sound [5] [2] [2] [9] [11] [2] 0 (by decide) (by decide)) perm7

theorem baseEdge2_2 : SafeCore (mutate (baseNode 2) 2) := by
  have he := mutation_equal (baseP 2) (preverse (prelabel ((six [-6] [-1] [2] [-5] [-2] [-1])) perm15)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (baseP 2) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (tail_point_safe_0_2) perm15)

theorem baseEdge2_3 : SafeCore (mutate (baseNode 2) 3) := by
  have he := mutation_equal (baseP 2) (preverse (prelabel (baseP 3) perm7)) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (baseP 2) 0) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (base_safe 3) perm7)

theorem baseCyclic3 : ¬ Acyclic (baseNode 3) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (baseP 3 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (baseP 3 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (baseP 3 1 0) 0 (by decide) (by decide))
  omega

theorem baseEdge3_0 : SafeCore (mutate (baseNode 3) 0) := by
  have he := mutation_equal (baseP 3) (preverse (prelabel (root [2] [6] [5] [2] [3] [1]) perm5)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (base_safe 3) 0
  rw [show mutate (baseNode 3) 0=(reverse (relabel (matrix (root [2] [6] [5] [2] [3] [1]) 0) perm5)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [2] [6] [5] [2] [3] [1] 0 (by decide) (by decide)) perm5)

theorem baseEdge3_1 : SafeCore (mutate (baseNode 3) 1) := by
  have he := mutation_equal (baseP 3) (prelabel (baseP 5) perm6) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (baseP 3) 0) 1)
  rw [he]
  exact Safe.framed (base_safe 5) perm6

theorem baseEdge3_2 : SafeCore (mutate (baseNode 3) 2) := by
  have he := mutation_equal (baseP 3) (preverse (prelabel (baseP 2) perm7)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (baseP 3) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (base_safe 2) perm7)

theorem baseEdge3_3 : SafeCore (mutate (baseNode 3) 3) := by
  have he := mutation_equal (baseP 3) (prelabel (baseP 0) perm4) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (baseP 3) 0) 3)
  rw [he]
  exact Safe.framed (base_safe 0) perm4

theorem baseCyclic4 : ¬ Acyclic (baseNode 4) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (baseP 4 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (baseP 4 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (baseP 4 1 0) 0 (by decide) (by decide))
  omega

theorem baseEdge4_0 : SafeCore (mutate (baseNode 4) 0) := by
  have he := mutation_equal (baseP 4) (prelabel (baseP 6) perm23) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (baseP 4) 0) 0)
  rw [he]
  exact Safe.framed (base_safe 6) perm23

theorem baseEdge4_1 : SafeCore (mutate (baseNode 4) 1) := by
  have he := mutation_equal (baseP 4) (prelabel (baseP 1) perm4) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (baseP 4) 0) 1)
  rw [he]
  exact Safe.framed (base_safe 1) perm4

theorem baseEdge4_2 : SafeCore (mutate (baseNode 4) 2) := by
  have he := mutation_equal (baseP 4) (preverse (prelabel (baseP 5) perm6)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (baseP 4) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (base_safe 5) perm6)

theorem baseEdge4_3 : SafeCore (mutate (baseNode 4) 3) := by
  have he := mutation_equal (baseP 4) (prelabel (baseP 0) perm0) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (baseP 4) 0) 3)
  rw [he]
  exact Safe.framed (base_safe 0) perm0

theorem baseCyclic5 : ¬ Acyclic (baseNode 5) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (baseP 5 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (baseP 5 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (baseP 5 1 0) 0 (by decide) (by decide))
  omega

theorem baseEdge5_0 : SafeCore (mutate (baseNode 5) 0) := by
  have he := mutation_equal (baseP 5) (prelabel (baseP 3) perm6) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (baseP 5) 0) 0)
  rw [he]
  exact Safe.framed (base_safe 3) perm6

theorem baseEdge5_1 : SafeCore (mutate (baseNode 5) 1) := by
  have he := mutation_equal (baseP 5) (prelabel (baseP 7) perm4) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (baseP 5) 0) 1)
  rw [he]
  exact Safe.framed (base_safe 7) perm4

theorem baseEdge5_2 : SafeCore (mutate (baseNode 5) 2) := by
  have he := mutation_equal (baseP 5) (preverse (prelabel (baseP 4) perm6)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (baseP 5) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (base_safe 4) perm6)

theorem baseEdge5_3 : SafeCore (mutate (baseNode 5) 3) := by
  have he := mutation_equal (baseP 5) (preverse (prelabel (baseP 5) perm14)) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (baseP 5) 0) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (base_safe 5) perm14)

theorem baseCyclic6 : ¬ Acyclic (baseNode 6) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (baseP 6 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (baseP 6 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (baseP 6 1 0) 0 (by decide) (by decide))
  omega

theorem baseEdge6_0 : SafeCore (mutate (baseNode 6) 0) := by
  have he := mutation_equal (baseP 6) (preverse (prelabel (baseP 4) perm0)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (baseP 6) 0) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (base_safe 4) perm0)

theorem baseEdge6_1 : SafeCore (mutate (baseNode 6) 1) := by
  have he := mutation_equal (baseP 6) (preverse (prelabel (baseP 8) perm17)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (baseP 6) 0) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (base_safe 8) perm17)

theorem baseEdge6_2 : SafeCore (mutate (baseNode 6) 2) := by
  have he := mutation_equal (baseP 6) (prelabel (baseP 8) perm1) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (baseP 6) 0) 2)
  rw [he]
  exact Safe.framed (base_safe 8) perm1

theorem baseEdge6_3 : SafeCore (mutate (baseNode 6) 3) := by
  have he := mutation_equal (baseP 6) (prelabel (baseP 4) perm23) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (baseP 6) 0) 3)
  rw [he]
  exact Safe.framed (base_safe 4) perm23

theorem baseCyclic7 : ¬ Acyclic (baseNode 7) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (baseP 7 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (baseP 7 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (baseP 7 1 0) 0 (by decide) (by decide))
  omega

theorem baseEdge7_0 : SafeCore (mutate (baseNode 7) 0) := by
  have he := mutation_equal (baseP 7) (preverse (prelabel (root [3] [5] [19] [2] [7] [1]) perm5)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (base_safe 7) 0
  rw [show mutate (baseNode 7) 0=(reverse (relabel (matrix (root [3] [5] [19] [2] [7] [1]) 0) perm5)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [3] [5] [19] [2] [7] [1] 0 (by decide) (by decide)) perm5)

theorem baseEdge7_1 : SafeCore (mutate (baseNode 7) 1) := by
  have he := mutation_equal (baseP 7) (preverse (prelabel (baseP 9) perm11)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (baseP 7) 0) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (base_safe 9) perm11)

theorem baseEdge7_2 : SafeCore (mutate (baseNode 7) 2) := by
  have he := mutation_equal (baseP 7) (prelabel (baseP 10) perm1) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (baseP 7) 0) 2)
  rw [he]
  exact Safe.framed (base_safe 10) perm1

theorem baseEdge7_3 : SafeCore (mutate (baseNode 7) 3) := by
  have he := mutation_equal (baseP 7) (prelabel (baseP 5) perm3) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (baseP 7) 0) 3)
  rw [he]
  exact Safe.framed (base_safe 5) perm3

theorem baseCyclic8 : ¬ Acyclic (baseNode 8) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (baseP 8 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (baseP 8 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (baseP 8 1 0) 0 (by decide) (by decide))
  omega

theorem baseEdge8_0 : SafeCore (mutate (baseNode 8) 0) := by
  have he := mutation_equal (baseP 8) (prelabel (fork [2] [5] [5] [7] [9] [2]) perm5) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (base_safe 8)
  rw [show mutate (baseNode 8) 0=(relabel (matrix (fork [2] [5] [5] [7] [9] [2]) 0) perm5) from he]
  exact IsFork.relabelled (fork_sound [2] [5] [5] [7] [9] [2] 0 (by decide) (by decide)) perm5

theorem baseEdge8_1 : SafeCore (mutate (baseNode 8) 1) := by
  have he := mutation_equal (baseP 8) (prelabel (baseP 11) perm4) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (baseP 8) 0) 1)
  rw [he]
  exact Safe.framed (base_safe 11) perm4

theorem baseEdge8_2 : SafeCore (mutate (baseNode 8) 2) := by
  have he := mutation_equal (baseP 8) (preverse (prelabel (fork [3] [5] [2] [13] [7] [5]) perm16)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 2 (base_safe 8)
  rw [show mutate (baseNode 8) 2=(reverse (relabel (matrix (fork [3] [5] [2] [13] [7] [5]) 0) perm16)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [3] [5] [2] [13] [7] [5] 0 (by decide) (by decide)) perm16)

theorem baseEdge8_3 : SafeCore (mutate (baseNode 8) 3) := by
  have he := mutation_equal (baseP 8) (prelabel (baseP 6) perm1) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (baseP 8) 0) 3)
  rw [he]
  exact Safe.framed (base_safe 6) perm1

theorem baseCyclic9 : ¬ Acyclic (baseNode 9) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (baseP 9 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (baseP 9 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (baseP 9 1 0) 0 (by decide) (by decide))
  omega

theorem baseEdge9_0 : SafeCore (mutate (baseNode 9) 0) := by
  have he := mutation_equal (baseP 9) (prelabel (fork [2] [11] [3] [15] [5] [2]) perm3) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (base_safe 9)
  rw [show mutate (baseNode 9) 0=(relabel (matrix (fork [2] [11] [3] [15] [5] [2]) 0) perm3) from he]
  exact IsFork.relabelled (fork_sound [2] [11] [3] [15] [5] [2] 0 (by decide) (by decide)) perm3

theorem baseEdge9_1 : SafeCore (mutate (baseNode 9) 1) := by
  have he := mutation_equal (baseP 9) (preverse (prelabel (fork [7] [11] [2] [75] [15] [3]) perm13)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (base_safe 9)
  rw [show mutate (baseNode 9) 1=(reverse (relabel (matrix (fork [7] [11] [2] [75] [15] [3]) 0) perm13)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [7] [11] [2] [75] [15] [3] 0 (by decide) (by decide)) perm13)

theorem baseEdge9_2 : SafeCore (mutate (baseNode 9) 2) := by
  have he := mutation_equal (baseP 9) (prelabel (baseP 12) perm1) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (baseP 9) 0) 2)
  rw [he]
  exact Safe.framed (base_safe 12) perm1

theorem baseEdge9_3 : SafeCore (mutate (baseNode 9) 3) := by
  have he := mutation_equal (baseP 9) (preverse (prelabel (baseP 7) perm19)) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (baseP 9) 0) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (base_safe 7) perm19)

theorem baseCyclic10 : ¬ Acyclic (baseNode 10) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (baseP 10 0 2) 0 (by decide) (by decide))
  have h1 := hr 2 1 (pos (baseP 10 2 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (baseP 10 1 0) 0 (by decide) (by decide))
  omega

theorem baseEdge10_0 : SafeCore (mutate (baseNode 10) 0) := by
  have he := mutation_equal (baseP 10) (preverse (prelabel (generic extraParam0_0 extraParam0_1 extraParam0_2 extraParam0_3 0) perm17)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (baseP 10) 0) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (extraRegion0_safe 0) perm17)

theorem baseEdge10_1 : SafeCore (mutate (baseNode 10) 1) := by
  have he := mutation_equal (baseP 10) (prelabel (generic extraParam0_0 extraParam0_1 extraParam0_2 extraParam0_3 0) perm22) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (baseP 10) 0) 1)
  rw [he]
  exact Safe.framed (extraRegion0_safe 0) perm22

theorem baseEdge10_2 : SafeCore (mutate (baseNode 10) 2) := by
  have he := mutation_equal (baseP 10) (preverse (prelabel (baseP 7) perm6)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (baseP 10) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (base_safe 7) perm6)

theorem baseEdge10_3 : SafeCore (mutate (baseNode 10) 3) := by
  have he := mutation_equal (baseP 10) (prelabel (baseP 7) perm1) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (baseP 10) 0) 3)
  rw [he]
  exact Safe.framed (base_safe 7) perm1

theorem baseCyclic11 : ¬ Acyclic (baseNode 11) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (baseP 11 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (baseP 11 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (baseP 11 1 0) 0 (by decide) (by decide))
  omega

theorem baseEdge11_0 : SafeCore (mutate (baseNode 11) 0) := by
  have he := mutation_equal (baseP 11) (prelabel (fork [5] [3] [15] [14] [73] [3]) perm5) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (base_safe 11)
  rw [show mutate (baseNode 11) 0=(relabel (matrix (fork [5] [3] [15] [14] [73] [3]) 0) perm5) from he]
  exact IsFork.relabelled (fork_sound [5] [3] [15] [14] [73] [3] 0 (by decide) (by decide)) perm5

theorem baseEdge11_1 : SafeCore (mutate (baseNode 11) 1) := by
  have he := mutation_equal (baseP 11) (preverse (prelabel (root [15] [48] [25] [3] [2] [1]) perm6)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (base_safe 11) 1
  rw [show mutate (baseNode 11) 1=(reverse (relabel (matrix (root [15] [48] [25] [3] [2] [1]) 0) perm6)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [15] [48] [25] [3] [2] [1] 0 (by decide) (by decide)) perm6)

theorem baseEdge11_2 : SafeCore (mutate (baseNode 11) 2) := by
  have he := mutation_equal (baseP 11) (preverse (prelabel (baseP 11) perm6)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (baseP 11) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (base_safe 11) perm6)

theorem baseEdge11_3 : SafeCore (mutate (baseNode 11) 3) := by
  have he := mutation_equal (baseP 11) (prelabel (baseP 8) perm3) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (baseP 11) 0) 3)
  rw [he]
  exact Safe.framed (base_safe 8) perm3

theorem baseCyclic12 : ¬ Acyclic (baseNode 12) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (baseP 12 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (baseP 12 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (baseP 12 1 0) 0 (by decide) (by decide))
  omega

theorem baseEdge12_0 : SafeCore (mutate (baseNode 12) 0) := by
  have he := mutation_equal (baseP 12) (prelabel (baseP 13) perm21) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (baseP 12) 0) 0)
  rw [he]
  exact Safe.framed (base_safe 13) perm21

theorem baseEdge12_1 : SafeCore (mutate (baseNode 12) 1) := by
  have he := mutation_equal (baseP 12) (preverse (prelabel (root [17] [120] [31] [7] [2] [1]) perm6)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (base_safe 12) 1
  rw [show mutate (baseNode 12) 1=(reverse (relabel (matrix (root [17] [120] [31] [7] [2] [1]) 0) perm6)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [17] [120] [31] [7] [2] [1] 0 (by decide) (by decide)) perm6)

theorem baseEdge12_2 : SafeCore (mutate (baseNode 12) 2) := by
  have he := mutation_equal (baseP 12) (preverse (prelabel (generic extraParam0_0 extraParam0_1 extraParam0_2 extraParam0_3 0) perm4)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (baseP 12) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (extraRegion0_safe 0) perm4)

theorem baseEdge12_3 : SafeCore (mutate (baseNode 12) 3) := by
  have he := mutation_equal (baseP 12) (prelabel (baseP 9) perm1) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (baseP 12) 0) 3)
  rw [he]
  exact Safe.framed (base_safe 9) perm1

theorem baseCyclic13 : ¬ Acyclic (baseNode 13) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (baseP 13 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (baseP 13 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (baseP 13 1 0) 0 (by decide) (by decide))
  omega

theorem baseEdge13_0 : SafeCore (mutate (baseNode 13) 0) := by
  have he := mutation_equal (baseP 13) (prelabel (fork [3] [2] [49] [5] [130] [7]) perm5) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (base_safe 13)
  rw [show mutate (baseNode 13) 0=(relabel (matrix (fork [3] [2] [49] [5] [130] [7]) 0) perm5) from he]
  exact IsFork.relabelled (fork_sound [3] [2] [49] [5] [130] [7] 0 (by decide) (by decide)) perm5

theorem baseEdge13_1 : SafeCore (mutate (baseNode 13) 1) := by
  have he := mutation_equal (baseP 13) (preverse (prelabel (root [49] [345] [830] [7] [17] [1]) perm6)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (base_safe 13) 1
  rw [show mutate (baseNode 13) 1=(reverse (relabel (matrix (root [49] [345] [830] [7] [17] [1]) 0) perm6)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [49] [345] [830] [7] [17] [1] 0 (by decide) (by decide)) perm6)

theorem baseEdge13_2 : SafeCore (mutate (baseNode 13) 2) := by
  have he := mutation_equal (baseP 13) (preverse (prelabel (generic extraParam0_0 extraParam0_1 extraParam0_2 extraParam0_3 2) perm16)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (baseP 13) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (extraRegion0_safe 2) perm16)

theorem baseEdge13_3 : SafeCore (mutate (baseNode 13) 3) := by
  have he := mutation_equal (baseP 13) (prelabel (baseP 12) perm21) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (baseP 13) 0) 3)
  rw [he]
  exact Safe.framed (base_safe 12) perm21

theorem base_skew (i : Fin 14) : SkewSymmetric (baseNode i) := by
  rcases baseFin i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp only [baseNode,baseP,matrix_six] <;> exact ofSix_skew _ _ _ _ _ _

theorem base_cyclic (i : Fin 14) : ¬ Acyclic (baseNode i) := by
  rcases baseFin i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact baseCyclic0
  · exact baseCyclic1
  · exact baseCyclic2
  · exact baseCyclic3
  · exact baseCyclic4
  · exact baseCyclic5
  · exact baseCyclic6
  · exact baseCyclic7
  · exact baseCyclic8
  · exact baseCyclic9
  · exact baseCyclic10
  · exact baseCyclic11
  · exact baseCyclic12
  · exact baseCyclic13

theorem base_edges (i : Fin 14) (k : Fin 4) : SafeCore (mutate (baseNode i) k) := by
  have hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
  rcases baseFin i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rcases hk with rfl|rfl|rfl|rfl
  · exact baseEdge0_0
  · exact baseEdge0_1
  · exact baseEdge0_2
  · exact baseEdge0_3
  · exact baseEdge1_0
  · exact baseEdge1_1
  · exact baseEdge1_2
  · exact baseEdge1_3
  · exact baseEdge2_0
  · exact baseEdge2_1
  · exact baseEdge2_2
  · exact baseEdge2_3
  · exact baseEdge3_0
  · exact baseEdge3_1
  · exact baseEdge3_2
  · exact baseEdge3_3
  · exact baseEdge4_0
  · exact baseEdge4_1
  · exact baseEdge4_2
  · exact baseEdge4_3
  · exact baseEdge5_0
  · exact baseEdge5_1
  · exact baseEdge5_2
  · exact baseEdge5_3
  · exact baseEdge6_0
  · exact baseEdge6_1
  · exact baseEdge6_2
  · exact baseEdge6_3
  · exact baseEdge7_0
  · exact baseEdge7_1
  · exact baseEdge7_2
  · exact baseEdge7_3
  · exact baseEdge8_0
  · exact baseEdge8_1
  · exact baseEdge8_2
  · exact baseEdge8_3
  · exact baseEdge9_0
  · exact baseEdge9_1
  · exact baseEdge9_2
  · exact baseEdge9_3
  · exact baseEdge10_0
  · exact baseEdge10_1
  · exact baseEdge10_2
  · exact baseEdge10_3
  · exact baseEdge11_0
  · exact baseEdge11_1
  · exact baseEdge11_2
  · exact baseEdge11_3
  · exact baseEdge12_0
  · exact baseEdge12_1
  · exact baseEdge12_2
  · exact baseEdge12_3
  · exact baseEdge13_0
  · exact baseEdge13_1
  · exact baseEdge13_2
  · exact baseEdge13_3

theorem tailCyclic0 (t : Int) (ht : 0≤t) : ¬ Acyclic (tailNode t 0) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (tailP 0 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (tailP 0 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (tailP 0 1 0) t ht (by decide))
  omega

theorem tailEdge0_0 (t : Int) (ht : 0≤t) : SafeCore (mutate (tailNode t 0) 0) := by
  have he := mutation_equal (tailP 0) (preverse (prelabel (shiftP (tailP 1) (0)) perm1)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (tailP 0) t) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (tail_shift_safe t 1 (0) (by omega)) perm1)

theorem tailEdge0_1 (t : Int) (ht : 0≤t) : SafeCore (mutate (tailNode t 0) 1) := by
  have he := mutation_equal (tailP 0) (preverse (prelabel (root [7,4] [41,52,16] [34,20] [6,4] [5] [1]) perm6)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (tail_safe t ht 0) 1
  rw [show mutate (tailNode t 0) 1=(reverse (relabel (matrix (root [7,4] [41,52,16] [34,20] [6,4] [5] [1]) t) perm6)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [7,4] [41,52,16] [34,20] [6,4] [5] [1] t ht (by decide)) perm6)

theorem tailEdge0_2 (t : Int) (ht : 0≤t) : SafeCore (mutate (tailNode t 0) 2) := by
  have he := mutation_equal (tailP 0) (preverse (prelabel (shiftP (tailP 1) (1)) perm21)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (tailP 0) t) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (tail_shift_safe t 1 (1) (by omega)) perm21)

theorem tailEdge0_3 (t : Int) (ht : 0≤t) : SafeCore (mutate (tailNode t 0) 3) := by
  have he := mutation_equal (tailP 0) (preverse (prelabel (shiftP (tailP 2) (0)) perm20)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (tailP 0) t) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (tail_shift_safe t 2 (0) (by omega)) perm20)

theorem tailCyclic1 (t : Int) (ht : 0≤t) : ¬ Acyclic (tailNode t 1) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (tailP 1 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (tailP 1 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (tailP 1 1 0) t ht (by decide))
  omega

theorem tailEdge1_0 (t : Int) (ht : 0≤t) : SafeCore (mutate (tailNode t 1) 0) := by
  have he := mutation_equal (tailP 1) (preverse (prelabel (shiftP (tailP 0) (0)) perm1)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (tailP 1) t) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (tail_shift_safe t 0 (0) (by omega)) perm1)

theorem tailEdge1_1 (t : Int) (ht : 0≤t) : SafeCore (mutate (tailNode t 1) 1) := by
  have he := mutation_equal (tailP 1) (prelabel (generic tailParam0_0 tailParam0_1 tailParam0_2 tailParam0_3 0) perm22) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (tailP 1) t) 1)
  rw [he]
  exact Safe.framed (tailRegion0_safe t ht 0) perm22

theorem tailEdge1_2_zero : SafeCore (mutate (tailNode 0 1) 2) := by
  have he : mutate (tailNode 0 1) 2=(reverse (relabel (matrix (baseP 1) 0) perm6)) := by funext u v; revert u v; decide
  rw [he]
  exact Safe.reversed (Safe.framed (base_safe 1) perm6)

theorem tailEdge1_2_pos (t : Int) (ht : 0≤t) (hpos : 1≤t) : SafeCore (mutate (tailNode t 1) 2) := by
  have he := mutation_equal (tailP 1) (preverse (prelabel (shiftP (tailP 0) (-1)) perm21)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (tailP 1) t) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (tail_shift_safe t 0 (-1) (by omega)) perm21)

theorem tailEdge1_2 (t : Int) (ht : 0≤t) : SafeCore (mutate (tailNode t 1) 2) := by
  by_cases hz : t=0
  · subst t; exact tailEdge1_2_zero
  · exact tailEdge1_2_pos t ht (by omega)

theorem tailEdge1_3 (t : Int) (ht : 0≤t) : SafeCore (mutate (tailNode t 1) 3) := by
  have he := mutation_equal (tailP 1) (prelabel (shiftP (tailP 5) (0)) perm1) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (tailP 1) t) 3)
  rw [he]
  exact Safe.framed (tail_shift_safe t 5 (0) (by omega)) perm1

theorem tailCyclic2 (t : Int) (ht : 0≤t) : ¬ Acyclic (tailNode t 2) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (tailP 2 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (tailP 2 3 1) t ht (by decide))
  have h2 := hr 1 0 (pos (tailP 2 1 0) t ht (by decide))
  omega

theorem tailEdge2_0 (t : Int) (ht : 0≤t) : SafeCore (mutate (tailNode t 2) 0) := by
  have he := mutation_equal (tailP 2) (prelabel (shiftP (tailP 2) (1)) perm21) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (tailP 2) t) 0)
  rw [he]
  exact Safe.framed (tail_shift_safe t 2 (1) (by omega)) perm21

theorem tailEdge2_1 (t : Int) (ht : 0≤t) : SafeCore (mutate (tailNode t 2) 1) := by
  have he := mutation_equal (tailP 2) (preverse (prelabel (root [6,4] [31,20] [10,32,16] [5] [2,4] [1]) perm6)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (tail_safe t ht 2) 1
  rw [show mutate (tailNode t 2) 1=(reverse (relabel (matrix (root [6,4] [31,20] [10,32,16] [5] [2,4] [1]) t) perm6)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [6,4] [31,20] [10,32,16] [5] [2,4] [1] t ht (by decide)) perm6)

theorem tailEdge2_2 (t : Int) (ht : 0≤t) : SafeCore (mutate (tailNode t 2) 2) := by
  have he := mutation_equal (tailP 2) (preverse (prelabel (shiftP (tailP 0) (0)) perm15)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (tailP 2) t) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (tail_shift_safe t 0 (0) (by omega)) perm15)

theorem tailEdge2_3_zero : SafeCore (mutate (tailNode 0 2) 3) := by
  have he : mutate (tailNode 0 2) 3=(reverse (relabel (matrix (baseP 2) 0) perm20)) := by funext u v; revert u v; decide
  rw [he]
  exact Safe.reversed (Safe.framed (base_safe 2) perm20)

theorem tailEdge2_3_pos (t : Int) (ht : 0≤t) (hpos : 1≤t) : SafeCore (mutate (tailNode t 2) 3) := by
  have he := mutation_equal (tailP 2) (prelabel (shiftP (tailP 2) (-1)) perm21) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (tailP 2) t) 3)
  rw [he]
  exact Safe.framed (tail_shift_safe t 2 (-1) (by omega)) perm21

theorem tailEdge2_3 (t : Int) (ht : 0≤t) : SafeCore (mutate (tailNode t 2) 3) := by
  by_cases hz : t=0
  · subst t; exact tailEdge2_3_zero
  · exact tailEdge2_3_pos t ht (by omega)

theorem tailCyclic3 (t : Int) (ht : 0≤t) : ¬ Acyclic (tailNode t 3) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (tailP 3 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (tailP 3 3 1) t ht (by decide))
  have h2 := hr 1 0 (pos (tailP 3 1 0) t ht (by decide))
  omega

theorem tailEdge3_0 (t : Int) (ht : 0≤t) : SafeCore (mutate (tailNode t 3) 0) := by
  have he := mutation_equal (tailP 3) (prelabel (shiftP (tailP 4) (0)) perm21) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (tailP 3) t) 0)
  rw [he]
  exact Safe.framed (tail_shift_safe t 4 (0) (by omega)) perm21

theorem tailEdge3_1 (t : Int) (ht : 0≤t) : SafeCore (mutate (tailNode t 3) 1) := by
  have he := mutation_equal (tailP 3) (prelabel (generic tailParam1_0 tailParam1_1 tailParam1_2 tailParam1_3 0) perm22) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (tailP 3) t) 1)
  rw [he]
  exact Safe.framed (tailRegion1_safe t ht 0) perm22

theorem tailEdge3_2 (t : Int) (ht : 0≤t) : SafeCore (mutate (tailNode t 3) 2) := by
  have he := mutation_equal (tailP 3) (preverse (prelabel (generic tailParam0_0 tailParam0_1 tailParam0_2 tailParam0_3 0) perm4)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (tailP 3) t) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (tailRegion0_safe t ht 0) perm4)

theorem tailEdge3_3 (t : Int) (ht : 0≤t) : SafeCore (mutate (tailNode t 3) 3) := by
  have he := mutation_equal (tailP 3) (prelabel (shiftP (tailP 8) (0)) perm1) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (tailP 3) t) 3)
  rw [he]
  exact Safe.framed (tail_shift_safe t 8 (0) (by omega)) perm1

theorem tailCyclic4 (t : Int) (ht : 0≤t) : ¬ Acyclic (tailNode t 4) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (tailP 4 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (tailP 4 3 1) t ht (by decide))
  have h2 := hr 1 0 (pos (tailP 4 1 0) t ht (by decide))
  omega

theorem tailEdge4_0 (t : Int) (ht : 0≤t) : SafeCore (mutate (tailNode t 4) 0) := by
  have he := mutation_equal (tailP 4) (prelabel (fork [3,4] [2,4] [38,160,192,64] [5,20,16] [101,596,1200,960,256] [6,4]) perm5) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (tail_safe t ht 4)
  rw [show mutate (tailNode t 4) 0=(relabel (matrix (fork [3,4] [2,4] [38,160,192,64] [5,20,16] [101,596,1200,960,256] [6,4]) t) perm5) from he]
  exact IsFork.relabelled (fork_sound [3,4] [2,4] [38,160,192,64] [5,20,16] [101,596,1200,960,256] [6,4] t ht (by decide)) perm5

theorem tailEdge4_1 (t : Int) (ht : 0≤t) : SafeCore (mutate (tailNode t 4) 1) := by
  have he := mutation_equal (tailP 4) (preverse (prelabel (root [38,160,192,64] [230,1116,1792,1152,256] [491,3444,8864,10304,5376,1024] [6,4] [13,36,16] [1]) perm6)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (tail_safe t ht 4) 1
  rw [show mutate (tailNode t 4) 1=(reverse (relabel (matrix (root [38,160,192,64] [230,1116,1792,1152,256] [491,3444,8864,10304,5376,1024] [6,4] [13,36,16] [1]) t) perm6)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [38,160,192,64] [230,1116,1792,1152,256] [491,3444,8864,10304,5376,1024] [6,4] [13,36,16] [1] t ht (by decide)) perm6)

theorem tailEdge4_2 (t : Int) (ht : 0≤t) : SafeCore (mutate (tailNode t 4) 2) := by
  have he := mutation_equal (tailP 4) (preverse (prelabel (generic tailParam0_0 tailParam0_1 tailParam0_2 tailParam0_3 2) perm16)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (tailP 4) t) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (tailRegion0_safe t ht 2) perm16)

theorem tailEdge4_3 (t : Int) (ht : 0≤t) : SafeCore (mutate (tailNode t 4) 3) := by
  have he := mutation_equal (tailP 4) (prelabel (shiftP (tailP 3) (0)) perm21) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (tailP 4) t) 3)
  rw [he]
  exact Safe.framed (tail_shift_safe t 3 (0) (by omega)) perm21

theorem tailCyclic5 (t : Int) (ht : 0≤t) : ¬ Acyclic (tailNode t 5) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (tailP 5 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (tailP 5 3 1) t ht (by decide))
  have h2 := hr 1 0 (pos (tailP 5 1 0) t ht (by decide))
  omega

theorem tailEdge5_0 (t : Int) (ht : 0≤t) : SafeCore (mutate (tailNode t 5) 0) := by
  have he := mutation_equal (tailP 5) (prelabel (shiftP (tailP 5) (1)) perm21) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (tailP 5) t) 0)
  rw [he]
  exact Safe.framed (tail_shift_safe t 5 (1) (by omega)) perm21

theorem tailEdge5_1 (t : Int) (ht : 0≤t) : SafeCore (mutate (tailNode t 5) 1) := by
  have he := mutation_equal (tailP 5) (preverse (prelabel (shiftP (tailP 8) (0)) perm11)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (tailP 5) t) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (tail_shift_safe t 8 (0) (by omega)) perm11)

theorem tailEdge5_2 (t : Int) (ht : 0≤t) : SafeCore (mutate (tailNode t 5) 2) := by
  have he := mutation_equal (tailP 5) (prelabel (shiftP (tailP 1) (0)) perm1) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (tailP 5) t) 2)
  rw [he]
  exact Safe.framed (tail_shift_safe t 1 (0) (by omega)) perm1

theorem tailEdge5_3_zero : SafeCore (mutate (tailNode 0 5) 3) := by
  have he : mutate (tailNode 0 5) 3=(reverse (relabel (matrix (baseP 0) 0) perm13)) := by funext u v; revert u v; decide
  rw [he]
  exact Safe.reversed (Safe.framed (base_safe 0) perm13)

theorem tailEdge5_3_pos (t : Int) (ht : 0≤t) (hpos : 1≤t) : SafeCore (mutate (tailNode t 5) 3) := by
  have he := mutation_equal (tailP 5) (prelabel (shiftP (tailP 5) (-1)) perm21) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (tailP 5) t) 3)
  rw [he]
  exact Safe.framed (tail_shift_safe t 5 (-1) (by omega)) perm21

theorem tailEdge5_3 (t : Int) (ht : 0≤t) : SafeCore (mutate (tailNode t 5) 3) := by
  by_cases hz : t=0
  · subst t; exact tailEdge5_3_zero
  · exact tailEdge5_3_pos t ht (by omega)

theorem tailCyclic6 (t : Int) (ht : 0≤t) : ¬ Acyclic (tailNode t 6) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (tailP 6 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (tailP 6 3 1) t ht (by decide))
  have h2 := hr 1 0 (pos (tailP 6 1 0) t ht (by decide))
  omega

theorem tailEdge6_0 (t : Int) (ht : 0≤t) : SafeCore (mutate (tailNode t 6) 0) := by
  have he := mutation_equal (tailP 6) (prelabel (shiftP (tailP 7) (0)) perm21) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (tailP 6) t) 0)
  rw [he]
  exact Safe.framed (tail_shift_safe t 7 (0) (by omega)) perm21

theorem tailEdge6_1 (t : Int) (ht : 0≤t) : SafeCore (mutate (tailNode t 6) 1) := by
  have he := mutation_equal (tailP 6) (preverse (prelabel (root [79,268,240,64] [791,5208,12240,12608,5888,1024] [230,1116,1792,1152,256] [10,32,16] [3,4] [1]) perm6)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (tail_safe t ht 6) 1
  rw [show mutate (tailNode t 6) 1=(reverse (relabel (matrix (root [79,268,240,64] [791,5208,12240,12608,5888,1024] [230,1116,1792,1152,256] [10,32,16] [3,4] [1]) t) perm6)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [79,268,240,64] [791,5208,12240,12608,5888,1024] [230,1116,1792,1152,256] [10,32,16] [3,4] [1] t ht (by decide)) perm6)

theorem tailEdge6_2 (t : Int) (ht : 0≤t) : SafeCore (mutate (tailNode t 6) 2) := by
  have he := mutation_equal (tailP 6) (preverse (prelabel (generic tailParam1_0 tailParam1_1 tailParam1_2 tailParam1_3 0) perm4)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (tailP 6) t) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (tailRegion1_safe t ht 0) perm4)

theorem tailEdge6_3 (t : Int) (ht : 0≤t) : SafeCore (mutate (tailNode t 6) 3) := by
  have he := mutation_equal (tailP 6) (prelabel (shiftP (tailP 9) (0)) perm1) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (tailP 6) t) 3)
  rw [he]
  exact Safe.framed (tail_shift_safe t 9 (0) (by omega)) perm1

theorem tailCyclic7 (t : Int) (ht : 0≤t) : ¬ Acyclic (tailNode t 7) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (tailP 7 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (tailP 7 3 1) t ht (by decide))
  have h2 := hr 1 0 (pos (tailP 7 1 0) t ht (by decide))
  omega

theorem tailEdge7_0 (t : Int) (ht : 0≤t) : SafeCore (mutate (tailNode t 7) 0) := by
  have he := mutation_equal (tailP 7) (prelabel (fork [7,4] [6,4] [550,2188,2752,1408,256] [41,52,16] [3771,17248,27776,20800,7424,1024] [10,32,16]) perm5) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (tail_safe t ht 7)
  rw [show mutate (tailNode t 7) 0=(relabel (matrix (fork [7,4] [6,4] [550,2188,2752,1408,256] [41,52,16] [3771,17248,27776,20800,7424,1024] [10,32,16]) t) perm5) from he]
  exact IsFork.relabelled (fork_sound [7,4] [6,4] [550,2188,2752,1408,256] [41,52,16] [3771,17248,27776,20800,7424,1024] [10,32,16] t ht (by decide)) perm5

theorem tailEdge7_1 (t : Int) (ht : 0≤t) : SafeCore (mutate (tailNode t 7) 1) := by
  have he := mutation_equal (tailP 7) (preverse (prelabel (root [550,2188,2752,1408,256] [5506,39484,106336,137152,91648,30720,4096] [43443,320248,935792,1409088,1198080,582656,151552,16384] [10,32,16] [79,268,240,64] [1]) perm6)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (tail_safe t ht 7) 1
  rw [show mutate (tailNode t 7) 1=(reverse (relabel (matrix (root [550,2188,2752,1408,256] [5506,39484,106336,137152,91648,30720,4096] [43443,320248,935792,1409088,1198080,582656,151552,16384] [10,32,16] [79,268,240,64] [1]) t) perm6)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [550,2188,2752,1408,256] [5506,39484,106336,137152,91648,30720,4096] [43443,320248,935792,1409088,1198080,582656,151552,16384] [10,32,16] [79,268,240,64] [1] t ht (by decide)) perm6)

theorem tailEdge7_2 (t : Int) (ht : 0≤t) : SafeCore (mutate (tailNode t 7) 2) := by
  have he := mutation_equal (tailP 7) (preverse (prelabel (generic tailParam1_0 tailParam1_1 tailParam1_2 tailParam1_3 2) perm16)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (tailP 7) t) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (tailRegion1_safe t ht 2) perm16)

theorem tailEdge7_3 (t : Int) (ht : 0≤t) : SafeCore (mutate (tailNode t 7) 3) := by
  have he := mutation_equal (tailP 7) (prelabel (shiftP (tailP 6) (0)) perm21) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (tailP 7) t) 3)
  rw [he]
  exact Safe.framed (tail_shift_safe t 6 (0) (by omega)) perm21

theorem tailCyclic8 (t : Int) (ht : 0≤t) : ¬ Acyclic (tailNode t 8) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (tailP 8 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (tailP 8 3 1) t ht (by decide))
  have h2 := hr 1 0 (pos (tailP 8 1 0) t ht (by decide))
  omega

theorem tailEdge8_0 (t : Int) (ht : 0≤t) : SafeCore (mutate (tailNode t 8) 0) := by
  have he := mutation_equal (tailP 8) (preverse (prelabel (root [2,4] [5,20,16] [14,100,160,64] [3,4] [10,32,16] [1]) perm5)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (tail_safe t ht 8) 0
  rw [show mutate (tailNode t 8) 0=(reverse (relabel (matrix (root [2,4] [5,20,16] [14,100,160,64] [3,4] [10,32,16] [1]) t) perm5)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [2,4] [5,20,16] [14,100,160,64] [3,4] [10,32,16] [1] t ht (by decide)) perm5)

theorem tailEdge8_1 (t : Int) (ht : 0≤t) : SafeCore (mutate (tailNode t 8) 1) := by
  have he := mutation_equal (tailP 8) (preverse (prelabel (shiftP (tailP 9) (0)) perm11)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (tailP 8) t) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (tail_shift_safe t 9 (0) (by omega)) perm11)

theorem tailEdge8_2 (t : Int) (ht : 0≤t) : SafeCore (mutate (tailNode t 8) 2) := by
  have he := mutation_equal (tailP 8) (prelabel (shiftP (tailP 3) (0)) perm1) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (tailP 8) t) 2)
  rw [he]
  exact Safe.framed (tail_shift_safe t 3 (0) (by omega)) perm1

theorem tailEdge8_3 (t : Int) (ht : 0≤t) : SafeCore (mutate (tailNode t 8) 3) := by
  have he := mutation_equal (tailP 8) (preverse (prelabel (shiftP (tailP 5) (0)) perm19)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (tailP 8) t) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (tail_shift_safe t 5 (0) (by omega)) perm19)

theorem tailCyclic9 (t : Int) (ht : 0≤t) : ¬ Acyclic (tailNode t 9) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (tailP 9 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (tailP 9 3 1) t ht (by decide))
  have h2 := hr 1 0 (pos (tailP 9 1 0) t ht (by decide))
  omega

theorem tailEdge9_0 (t : Int) (ht : 0≤t) : SafeCore (mutate (tailNode t 9) 0) := by
  have he := mutation_equal (tailP 9) (prelabel (fork [6,4] [58,228,224,64] [7,4] [338,1568,2240,1280,256] [41,52,16] [3,4]) perm3) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (tail_safe t ht 9)
  rw [show mutate (tailNode t 9) 0=(relabel (matrix (fork [6,4] [58,228,224,64] [7,4] [338,1568,2240,1280,256] [41,52,16] [3,4]) t) perm3) from he]
  exact IsFork.relabelled (fork_sound [6,4] [58,228,224,64] [7,4] [338,1568,2240,1280,256] [41,52,16] [3,4] t ht (by decide)) perm3

theorem tailEdge9_1 (t : Int) (ht : 0≤t) : SafeCore (mutate (tailNode t 9) 1) := by
  have he := mutation_equal (tailP 9) (preverse (prelabel (fork [10,32,16] [58,228,224,64] [3,4] [574,4132,10464,11456,5632,1024] [31,136,176,64] [7,4]) perm13)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (tail_safe t ht 9)
  rw [show mutate (tailNode t 9) 1=(reverse (relabel (matrix (fork [10,32,16] [58,228,224,64] [3,4] [574,4132,10464,11456,5632,1024] [31,136,176,64] [7,4]) t) perm13)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [10,32,16] [58,228,224,64] [3,4] [574,4132,10464,11456,5632,1024] [31,136,176,64] [7,4] t ht (by decide)) perm13)

theorem tailEdge9_2 (t : Int) (ht : 0≤t) : SafeCore (mutate (tailNode t 9) 2) := by
  have he := mutation_equal (tailP 9) (prelabel (shiftP (tailP 6) (0)) perm1) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (tailP 9) t) 2)
  rw [he]
  exact Safe.framed (tail_shift_safe t 6 (0) (by omega)) perm1

theorem tailEdge9_3 (t : Int) (ht : 0≤t) : SafeCore (mutate (tailNode t 9) 3) := by
  have he := mutation_equal (tailP 9) (preverse (prelabel (shiftP (tailP 8) (0)) perm19)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (tailP 9) t) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (tail_shift_safe t 8 (0) (by omega)) perm19)

theorem tail_skew (t : Int) (i : Fin 10) : SkewSymmetric (tailNode t i) := by
  rcases tailFin i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp only [tailNode,tailP,matrix_six] <;> exact ofSix_skew _ _ _ _ _ _

theorem tail_cyclic (t : Int) (ht : 0≤t) (i : Fin 10) : ¬ Acyclic (tailNode t i) := by
  rcases tailFin i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact tailCyclic0 t ht
  · exact tailCyclic1 t ht
  · exact tailCyclic2 t ht
  · exact tailCyclic3 t ht
  · exact tailCyclic4 t ht
  · exact tailCyclic5 t ht
  · exact tailCyclic6 t ht
  · exact tailCyclic7 t ht
  · exact tailCyclic8 t ht
  · exact tailCyclic9 t ht

theorem tail_edges (t : Int) (ht : 0≤t) (i : Fin 10) (k : Fin 4) : SafeCore (mutate (tailNode t i) k) := by
  have hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
  rcases tailFin i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rcases hk with rfl|rfl|rfl|rfl
  · exact tailEdge0_0 t ht
  · exact tailEdge0_1 t ht
  · exact tailEdge0_2 t ht
  · exact tailEdge0_3 t ht
  · exact tailEdge1_0 t ht
  · exact tailEdge1_1 t ht
  · exact tailEdge1_2 t ht
  · exact tailEdge1_3 t ht
  · exact tailEdge2_0 t ht
  · exact tailEdge2_1 t ht
  · exact tailEdge2_2 t ht
  · exact tailEdge2_3 t ht
  · exact tailEdge3_0 t ht
  · exact tailEdge3_1 t ht
  · exact tailEdge3_2 t ht
  · exact tailEdge3_3 t ht
  · exact tailEdge4_0 t ht
  · exact tailEdge4_1 t ht
  · exact tailEdge4_2 t ht
  · exact tailEdge4_3 t ht
  · exact tailEdge5_0 t ht
  · exact tailEdge5_1 t ht
  · exact tailEdge5_2 t ht
  · exact tailEdge5_3 t ht
  · exact tailEdge6_0 t ht
  · exact tailEdge6_1 t ht
  · exact tailEdge6_2 t ht
  · exact tailEdge6_3 t ht
  · exact tailEdge7_0 t ht
  · exact tailEdge7_1 t ht
  · exact tailEdge7_2 t ht
  · exact tailEdge7_3 t ht
  · exact tailEdge8_0 t ht
  · exact tailEdge8_1 t ht
  · exact tailEdge8_2 t ht
  · exact tailEdge8_3 t ht
  · exact tailEdge9_0 t ht
  · exact tailEdge9_1 t ht
  · exact tailEdge9_2 t ht
  · exact tailEdge9_3 t ht

theorem core_skew (B : Matrix 4) (h : Core B) : SkewSymmetric B := by
  rcases h with ⟨i,rfl⟩|⟨t,ht,i,rfl⟩
  · exact base_skew i
  · exact tail_skew t i
theorem core_cyclic (B : Matrix 4) (h : Core B) : ¬ Acyclic B := by
  rcases h with ⟨i,rfl⟩|⟨t,ht,i,rfl⟩
  · exact base_cyclic i
  · exact tail_cyclic t ht i
theorem core_edges (B : Matrix 4) (h : Core B) (k : Fin 4) : SafeCore (mutate B k) := by
  rcases h with ⟨i,rfl⟩|⟨t,ht,i,rfl⟩
  · exact base_edges i k
  · exact tail_edges t ht i k
theorem safe_nma (B : Matrix 4) (h : SafeCore B) : ¬ MutationAcyclic B :=
  safe_NMA data rules Core core_skew core_cyclic core_edges h
theorem nma_q041 : ¬ MutationAcyclic (ofSix (-2) (-2) (-1) (-2) 1 (-1)) := by
  simpa [baseNode,baseP,matrix_six,eval] using safe_nma _ (base_safe 0)
theorem frame_q160 : ofSix (-2) (-2) 1 (-2) (-1) 1 = reverse (relabel (baseNode 0) perm14) := by
  funext i j
  revert i j
  decide
theorem nma_q160 : ¬ MutationAcyclic (ofSix (-2) (-2) 1 (-2) (-1) 1) := by
  rw [frame_q160]
  exact safe_nma _ (Safe.reversed (Safe.framed (base_safe 0) perm14))
end QuiverProofs.Q041Corridor
