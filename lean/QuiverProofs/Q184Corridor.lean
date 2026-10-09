import QuiverProofs.QFamilyPolynomialInterfaces

namespace QuiverProofs.Q184Corridor
open PolynomialCertificate QFamilyPolynomialInterfaces RecursiveRegions Forks Regions ForkCertificates
set_option maxHeartbeats 12000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

private theorem fin4 (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega

def pnode (i : Fin 16) : PMatrix := match i.val with
  | 0 => six [-6,-1] [1] [1] [-2,-1] [-1] [-1]
  | 1 => six [-6,-1] [-1] [2] [1] [-3,-1] [-1]
  | 2 => six [-6,-1] [-1] [2] [-4] [-3,-1] [-1]
  | 3 => six [-6,-1] [1] [1] [-5,-1] [-4] [-1]
  | 4 => six [-11,-8,-1] [-1] [3,1] [-5,-1] [-1] [-1]
  | 5 => six [-32,-35,-11,-1] [-2,-1] [3,1] [-5,-1] [-11,-8,-1] [-1]
  | 6 => six [-16,-9,-1] [-4,-1] [3,1] [1] [-6,-1] [-1]
  | 7 => six [-56,-51,-13,-1] [-1] [6,1] [-8,-7,-1] [-3,-1] [-1]
  | 8 => six [-333,-361,-129,-19,-1] [-5,-1] [6,1] [-8,-7,-1] [-56,-51,-13,-1] [-1]
  | 9 => six [-8,-7,-1] [-3,-1] [2,1] [1] [-5,-1] [-1]
  | 10 => six [-93,-69,-15,-1] [-7,-1] [6,1] [4,1] [-16,-9,-1] [-1]
  | 11 => six [-20,-10,-1] [-1] [4,1] [-6,-1] [-1] [-1]
  | 12 => six [-38,-42,-12,-1] [-6,-1] [5,1] [3,1] [-8,-7,-1] [-1]
  | 13 => six [-121,-80,-16,-1] [-1] [7,1] [-16,-9,-1] [-4,-1] [-1]
  | 14 => six [-79,-60,-14,-1] [-3,-1] [4,1] [-6,-1] [-20,-10,-1] [-1]
  | _ => six [-843,-680,-192,-23,-1] [-6,-1] [7,1] [-16,-9,-1] [-121,-80,-16,-1] [-1]

def bnode (i : Fin 59) : PMatrix := match i.val with
  | 0 => six [-2] [-2] [1] [-1] [-1] [1]
  | 1 => six [-3] [-1] [1] [-1] [-1] [1]
  | 2 => six [] [-3] [-1] [2] [-1] [1]
  | 3 => six [] [-4] [3] [1] [-2] [1]
  | 4 => six [-4] [-2] [3] [1] [-1] [-1]
  | 5 => six [] [-4] [1] [1] [1] [-1]
  | 6 => six [-4] [-1] [1] [1] [-2] [1]
  | 7 => six [-4] [-1] [1] [-4] [1] [-2]
  | 8 => six [-4] [-3] [4] [1] [-1] [-1]
  | 9 => six [-5] [1] [1] [-1] [-1] [-1]
  | 10 => six [-5] [-1] [2] [1] [-2] [-1]
  | 11 => six [-5] [-1] [2] [-4] [-2] [-1]
  | 12 => six [-5] [1] [1] [-4] [-4] [-1]
  | 13 => six [-3] [-1] [1] [1] [-2] [-2]
  | 14 => six [-2] [-1] [-1] [-2] [1] [-1]
  | 15 => six [] [-3] [-1] [-2] [1] [-1]
  | 16 => six [] [-4] [3] [-1] [2] [-13]
  | 17 => six [] [-4] [3] [-1] [2] [-1]
  | 18 => six [-4] [-1] [1] [-2] [-1] [-2]
  | 19 => six [] [-4] [1] [-1] [-1] [-3]
  | 20 => six [] [-4] [1] [-1] [-1] [-1]
  | 21 => six [-4] [-1] [1] [-1] [-2] [-2]
  | 22 => six [-17] [-2] [4] [-1] [-4] [-1]
  | 23 => six [-8] [-3] [2] [1] [-5] [-1]
  | 24 => six [-5] [-4] [2] [1] [-3] [-1]
  | 25 => six [-2] [-2] [1] [-1] [2] [-1]
  | 26 => six [-3] [-1] [-1] [-1] [1] [-1]
  | 27 => six [] [-4] [3] [1] [-2] [-11]
  | 28 => six [] [-49] [4] [-11] [1] [-13]
  | 29 => six [-9] [-3] [4] [-2] [-2] [-1]
  | 30 => six [] [-4] [1] [1] [1] [-3]
  | 31 => six [] [-11] [4] [-4] [1] [-3]
  | 32 => six [-7] [-5] [4] [2] [-2] [-1]
  | 33 => six [-64] [-19] [17] [1] [-4] [-1]
  | 34 => six [-17] [-1] [5] [-2] [-2] [-1]
  | 35 => six [-38] [-6] [5] [3] [-8] [-1]
  | 36 => six [-11] [-1] [3] [-5] [-1] [-1]
  | 37 => six [-13] [-4] [3] [4] [-5] [-1]
  | 38 => six [-9] [-2] [4] [-3] [-1] [-1]
  | 39 => six [-41] [-4] [4] [2] [-11] [-1]
  | 40 => six [] [-49] [4] [11] [-1] [-2]
  | 41 => six [-11] [-4] [4] [-1] [-3] [-1]
  | 42 => six [] [-11] [4] [4] [-1] [1]
  | 43 => six [-239] [-19] [64] [5] [-4] [1]
  | 44 => six [-83] [-2] [19] [-4] [-1] [-1]
  | 45 => six [-83] [-4] [5] [-2] [-17] [-1]
  | 46 => six [-56] [-1] [6] [-8] [-3] [-1]
  | 47 => six [-32] [-2] [3] [-5] [-11] [-1]
  | 48 => six [-333] [-5] [6] [-8] [-56] [-1]
  | 49 => six [-29] [-1] [4] [-5] [-4] [-1]
  | 50 => six [-112] [-3] [4] [-5] [-29] [-1]
  | 51 => six [-29] [-15] [11] [1] [-3] [-1]
  | 52 => six [-44] [-3] [4] [-4] [-11] [-1]
  | 53 => six [-334] [-1] [5] [-64] [-19] [-1]
  | 54 => six [-1651] [-4] [5] [-64] [-334] [-1]
  | 55 => six [-76] [-15] [29] [4] [-3] [1]
  | 56 => six [-44] [-4] [15] [-3] [-1] [-1]
  | 57 => six [-136] [-1] [4] [-29] [-15] [-1]
  | _ => six [-529] [-3] [4] [-29] [-136] [-1]

def node (t : Int) (i : Fin 16) : Matrix 4 := matrix (pnode i) t
def base (i : Fin 59) : Matrix 4 := matrix (bnode i) 0

def tail (n : Int) (i : Fin 4) : Matrix 4 := match i.val with
  | 0 => ofSix (-n) 1 1 (4-n) (-1) (-1)
  | 1 => ofSix (-n) (-1) 2 1 (3-n) (-1)
  | 2 => ofSix (-n) (-1) 2 (-4) (3-n) (-1)
  | _ => ofSix (-n) 1 1 (1-n) (-4) (-1)

def ptail (n : P) (i : Fin 4) : PMatrix := match i.val with
  | 0 => six (neg n) [1] [1] (sub [4] n) [-1] [-1]
  | 1 => six (neg n) [-1] [2] [1] (sub [3] n) [-1]
  | 2 => six (neg n) [-1] [2] [-4] (sub [3] n) [-1]
  | _ => six (neg n) [1] [1] (sub [1] n) [-4] [-1]

theorem ptail_eval (n : P) (i : Fin 4) (t : Int) : matrix (ptail n i) t=tail (eval n t) i := by
  rcases fin4 i with rfl|rfl|rfl|rfl <;> simp [ptail,tail,matrix_six,eval_neg,eval_sub,eval]

inductive Core : Matrix 4 → Prop
  | node (t : Int) (ht : 0≤t) (i : Fin 16) : Core (node t i)
  | base (i : Fin 59) : Core (base i)

abbrev SafeCore := Safe data Core
theorem node_safe (t : Int) (ht : 0≤t) (i) : SafeCore (node t i) := Safe.central (.node t ht i)
theorem base_safe (i) : SafeCore (base i) := Safe.central (.base i)

theorem tail_safe (n : Int) (hn : 3≤n) (i : Fin 4) : SafeCore (tail n i) := by
  by_cases hi : 6≤n
  · have he : tail n i = node (n-6) (Fin.castLE (by decide +kernel) i) := by
      rcases fin4 i with rfl|rfl|rfl|rfl <;> simp [tail,node,pnode,matrix_six,eval] <;> grind
    rw [he]; exact node_safe (n-6) (by omega) _
  · have hh : n=3 ∨ n=4 ∨ n=5 := by omega
    rcases hh with rfl|rfl|rfl <;> rcases fin4 i with rfl|rfl|rfl|rfl
    · have he : tail 3 0 = (reverse (relabel (base 1) perm6.symm)) := by funext a b; revert a b; decide
      rw [he]; exact Safe.reversed (Safe.framed (base_safe 1) perm6.symm)
    · have he : tail 3 1 = (reverse (relabel (base 2) perm10.symm)) := by funext a b; revert a b; decide
      rw [he]; exact Safe.reversed (Safe.framed (base_safe 2) perm10.symm)
    · have he : tail 3 2 = (relabel (base 3) perm11.symm) := by funext a b; revert a b; decide
      rw [he]; exact Safe.framed (base_safe 3) perm11.symm
    · have he : tail 3 3 = (relabel (base 4) perm11.symm) := by funext a b; revert a b; decide
      rw [he]; exact Safe.framed (base_safe 4) perm11.symm
    · have he : tail 4 0 = (reverse (relabel (base 5) perm8.symm)) := by funext a b; revert a b; decide
      rw [he]; exact Safe.reversed (Safe.framed (base_safe 5) perm8.symm)
    · have he : tail 4 1 = (reverse (relabel (base 6) perm6.symm)) := by funext a b; revert a b; decide
      rw [he]; exact Safe.reversed (Safe.framed (base_safe 6) perm6.symm)
    · have he : tail 4 2 = (reverse (relabel (base 7) perm14.symm)) := by funext a b; revert a b; decide
      rw [he]; exact Safe.reversed (Safe.framed (base_safe 7) perm14.symm)
    · have he : tail 4 3 = (relabel (base 8) perm11.symm) := by funext a b; revert a b; decide
      rw [he]; exact Safe.framed (base_safe 8) perm11.symm
    · have he : tail 5 0 = (relabel (base 9) perm0.symm) := by funext a b; revert a b; decide
      rw [he]; exact Safe.framed (base_safe 9) perm0.symm
    · have he : tail 5 1 = (relabel (base 10) perm0.symm) := by funext a b; revert a b; decide
      rw [he]; exact Safe.framed (base_safe 10) perm0.symm
    · have he : tail 5 2 = (relabel (base 11) perm0.symm) := by funext a b; revert a b; decide
      rw [he]; exact Safe.framed (base_safe 11) perm0.symm
    · have he : tail 5 3 = (relabel (base 12) perm0.symm) := by funext a b; revert a b; decide
      rw [he]; exact Safe.framed (base_safe 12) perm0.symm

def param0_0 : P := [2,1]
def param0_1 : P := [11,8,1]
def param0_2 : P := [5,1]
def param0_3 : P := [6,1]
theorem domain0 (t : Int) (ht : 0≤t) : GenericStrip.Domain (eval param0_0 t) (eval param0_1 t) (eval param0_2 t) (eval param0_3 t) := generic_domain param0_0 param0_1 param0_2 param0_3 t ht (by decide +kernel)
def region0 (t : Int) (ht : 0≤t) : Region := .inl (.inl ⟨eval param0_0 t,⟨eval param0_1 t,eval param0_2 t,eval param0_3 t⟩,domain0 t ht⟩)
theorem parent0_0 (t : Int) (ht : 0≤t) : SafeCore (data.parent (region0 t ht) (0 : Fin 3)) := by
  have he := mutation_equal (generic param0_0 param0_1 param0_2 param0_3 0) (preverse (prelabel (pnode 4) perm4.symm)) 1 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  rw [show data.parent (region0 t ht) (0 : Fin 3) = _ from he]
  exact Safe.reversed (Safe.framed (node_safe t ht 4) perm4.symm)
theorem parent0_1 (t : Int) (ht : 0≤t) : SafeCore (data.parent (region0 t ht) (1 : Fin 3)) := by
  have he := mutation_equal (generic param0_0 param0_1 param0_2 param0_3 0) (prelabel (pnode 0) perm22.symm) 2 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  rw [show data.parent (region0 t ht) (1 : Fin 3) = _ from he]
  exact Safe.framed (node_safe t ht 0) perm22.symm
theorem parent0_2 (t : Int) (ht : 0≤t) : SafeCore (data.parent (region0 t ht) (2 : Fin 3)) := by
  have he := mutation_equal (generic param0_0 param0_1 param0_2 param0_3 2) (preverse (prelabel (pnode 5) perm16.symm)) 0 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  rw [show data.parent (region0 t ht) (2 : Fin 3) = _ from he]
  exact Safe.reversed (Safe.framed (node_safe t ht 5) perm16.symm)
theorem parents0_safe (t : Int) (ht : 0≤t) (p : Fin 3) : SafeCore (data.parent (region0 t ht) p) := by
  have hh : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hh with rfl|rfl|rfl
  · exact parent0_0 t ht
  · exact parent0_1 t ht
  · exact parent0_2 t ht
theorem region0_safe (t : Int) (ht : 0≤t) (i : Fin 3) : SafeCore (matrix (generic param0_0 param0_1 param0_2 param0_3 i) t) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core) (region0 t ht) (parents0_safe t ht) (0,Fin.castLE (by decide +kernel) i)

def param1_0 : P := [5,1]
def param1_1 : P := [56,51,13,1]
def param1_2 : P := [8,7,1]
def param1_3 : P := [11,8,1]
theorem domain1 (t : Int) (ht : 0≤t) : GenericStrip.Domain (eval param1_0 t) (eval param1_1 t) (eval param1_2 t) (eval param1_3 t) := generic_domain param1_0 param1_1 param1_2 param1_3 t ht (by decide +kernel)
def region1 (t : Int) (ht : 0≤t) : Region := .inl (.inl ⟨eval param1_0 t,⟨eval param1_1 t,eval param1_2 t,eval param1_3 t⟩,domain1 t ht⟩)
theorem parent1_0 (t : Int) (ht : 0≤t) : SafeCore (data.parent (region1 t ht) (0 : Fin 3)) := by
  have he := mutation_equal (generic param1_0 param1_1 param1_2 param1_3 0) (preverse (prelabel (pnode 7) perm4.symm)) 1 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  rw [show data.parent (region1 t ht) (0 : Fin 3) = _ from he]
  exact Safe.reversed (Safe.framed (node_safe t ht 7) perm4.symm)
theorem parent1_1 (t : Int) (ht : 0≤t) : SafeCore (data.parent (region1 t ht) (1 : Fin 3)) := by
  have he := mutation_equal (generic param1_0 param1_1 param1_2 param1_3 0) (prelabel (pnode 4) perm22.symm) 2 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  rw [show data.parent (region1 t ht) (1 : Fin 3) = _ from he]
  exact Safe.framed (node_safe t ht 4) perm22.symm
theorem parent1_2 (t : Int) (ht : 0≤t) : SafeCore (data.parent (region1 t ht) (2 : Fin 3)) := by
  have he := mutation_equal (generic param1_0 param1_1 param1_2 param1_3 2) (preverse (prelabel (pnode 8) perm16.symm)) 0 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  rw [show data.parent (region1 t ht) (2 : Fin 3) = _ from he]
  exact Safe.reversed (Safe.framed (node_safe t ht 8) perm16.symm)
theorem parents1_safe (t : Int) (ht : 0≤t) (p : Fin 3) : SafeCore (data.parent (region1 t ht) p) := by
  have hh : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hh with rfl|rfl|rfl
  · exact parent1_0 t ht
  · exact parent1_1 t ht
  · exact parent1_2 t ht
theorem region1_safe (t : Int) (ht : 0≤t) (i : Fin 3) : SafeCore (matrix (generic param1_0 param1_1 param1_2 param1_3 i) t) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core) (region1 t ht) (parents1_safe t ht) (0,Fin.castLE (by decide +kernel) i)

def param2_0 : P := [6,1]
def param2_1 : P := [121,80,16,1]
def param2_2 : P := [16,9,1]
def param2_3 : P := [20,10,1]
theorem domain2 (t : Int) (ht : 0≤t) : GenericStrip.Domain (eval param2_0 t) (eval param2_1 t) (eval param2_2 t) (eval param2_3 t) := generic_domain param2_0 param2_1 param2_2 param2_3 t ht (by decide +kernel)
def region2 (t : Int) (ht : 0≤t) : Region := .inl (.inl ⟨eval param2_0 t,⟨eval param2_1 t,eval param2_2 t,eval param2_3 t⟩,domain2 t ht⟩)
theorem parent2_0 (t : Int) (ht : 0≤t) : SafeCore (data.parent (region2 t ht) (0 : Fin 3)) := by
  have he := mutation_equal (generic param2_0 param2_1 param2_2 param2_3 0) (preverse (prelabel (pnode 13) perm4.symm)) 1 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  rw [show data.parent (region2 t ht) (0 : Fin 3) = _ from he]
  exact Safe.reversed (Safe.framed (node_safe t ht 13) perm4.symm)
theorem parent2_1 (t : Int) (ht : 0≤t) : SafeCore (data.parent (region2 t ht) (1 : Fin 3)) := by
  have he := mutation_equal (generic param2_0 param2_1 param2_2 param2_3 0) (prelabel (pnode 11) perm22.symm) 2 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  rw [show data.parent (region2 t ht) (1 : Fin 3) = _ from he]
  exact Safe.framed (node_safe t ht 11) perm22.symm
theorem parent2_2 (t : Int) (ht : 0≤t) : SafeCore (data.parent (region2 t ht) (2 : Fin 3)) := by
  have he := mutation_equal (generic param2_0 param2_1 param2_2 param2_3 2) (preverse (prelabel (pnode 15) perm16.symm)) 0 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  rw [show data.parent (region2 t ht) (2 : Fin 3) = _ from he]
  exact Safe.reversed (Safe.framed (node_safe t ht 15) perm16.symm)
theorem parents2_safe (t : Int) (ht : 0≤t) (p : Fin 3) : SafeCore (data.parent (region2 t ht) p) := by
  have hh : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hh with rfl|rfl|rfl
  · exact parent2_0 t ht
  · exact parent2_1 t ht
  · exact parent2_2 t ht
theorem region2_safe (t : Int) (ht : 0≤t) (i : Fin 3) : SafeCore (matrix (generic param2_0 param2_1 param2_2 param2_3 i) t) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core) (region2 t ht) (parents2_safe t ht) (0,Fin.castLE (by decide +kernel) i)

def param3_0 : P := [3,1]
def param3_1 : P := [20,10,1]
def param3_2 : P := [6,1]
def param3_3 : P := [7,1]
theorem domain3 (t : Int) (ht : 0≤t) : GenericStrip.Domain (eval param3_0 t) (eval param3_1 t) (eval param3_2 t) (eval param3_3 t) := generic_domain param3_0 param3_1 param3_2 param3_3 t ht (by decide +kernel)
def region3 (t : Int) (ht : 0≤t) : Region := .inl (.inl ⟨eval param3_0 t,⟨eval param3_1 t,eval param3_2 t,eval param3_3 t⟩,domain3 t ht⟩)
theorem parent3_0 (t : Int) (ht : 0≤t) : SafeCore (data.parent (region3 t ht) (0 : Fin 3)) := by
  have he := mutation_equal (generic param3_0 param3_1 param3_2 param3_3 0) (preverse (prelabel (pnode 11) perm4.symm)) 1 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  rw [show data.parent (region3 t ht) (0 : Fin 3) = _ from he]
  exact Safe.reversed (Safe.framed (node_safe t ht 11) perm4.symm)
theorem parent3_1 (t : Int) (ht : 0≤t) : SafeCore (data.parent (region3 t ht) (1 : Fin 3)) := by
  have he := mutation_equal (generic param3_0 param3_1 param3_2 param3_3 0) (prelabel (ptail [7,1] 0) perm22.symm) 2 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse,generic_eval,ptail_eval] at he
  rw [show data.parent (region3 t ht) (1 : Fin 3) = _ from he]
  exact Safe.framed (tail_safe (eval [7,1] t) (by simpa [eval] using le [3] [7,1] t ht (by decide +kernel)) 0) perm22.symm
theorem parent3_2 (t : Int) (ht : 0≤t) : SafeCore (data.parent (region3 t ht) (2 : Fin 3)) := by
  have he := mutation_equal (generic param3_0 param3_1 param3_2 param3_3 2) (preverse (prelabel (pnode 14) perm16.symm)) 0 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  rw [show data.parent (region3 t ht) (2 : Fin 3) = _ from he]
  exact Safe.reversed (Safe.framed (node_safe t ht 14) perm16.symm)
theorem parents3_safe (t : Int) (ht : 0≤t) (p : Fin 3) : SafeCore (data.parent (region3 t ht) p) := by
  have hh : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hh with rfl|rfl|rfl
  · exact parent3_0 t ht
  · exact parent3_1 t ht
  · exact parent3_2 t ht
theorem region3_safe (t : Int) (ht : 0≤t) (i : Fin 3) : SafeCore (matrix (generic param3_0 param3_1 param3_2 param3_3 i) t) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core) (region3 t ht) (parents3_safe t ht) (0,Fin.castLE (by decide +kernel) i)

def param4_0 : P := [4]
def param4_1 : P := [11]
def param4_2 : P := [49]
def param4_3 : P := [183]
theorem domain4 (t : Int) (ht : 0≤t) : UnitZeroStrip.Domain (eval param4_0 t) (eval param4_1 t) (eval param4_2 t) (eval param4_3 t) := zero_domain param4_0 param4_1 param4_2 param4_3 t ht (by decide +kernel)
def region4 (t : Int) (ht : 0≤t) : Region := .inl (.inr (.n (eval param4_0 t) ⟨eval param4_1 t,eval param4_2 t,eval param4_3 t⟩ (domain4 t ht)))
theorem parent4_0 : SafeCore (data.parent (region4 0 (by decide +kernel)) (0 : Fin 2)) := by
  have he := mutation_equal (zero param4_0 param4_1 param4_2 param4_3 0) (prelabel (bnode 28) perm6.symm) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse,zero_eval] at he
  rw [show data.parent (region4 0 (by decide +kernel)) (0 : Fin 2) = _ from he]
  exact Safe.framed (base_safe 28) perm6.symm
theorem parent4_1 : SafeCore (data.parent (region4 0 (by decide +kernel)) (1 : Fin 2)) := by
  have he := mutation_equal (zero param4_0 param4_1 param4_2 param4_3 1) (prelabel (bnode 40) perm6.symm) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse,zero_eval] at he
  rw [show data.parent (region4 0 (by decide +kernel)) (1 : Fin 2) = _ from he]
  exact Safe.framed (base_safe 40) perm6.symm
theorem parents4_safe (p : Fin 2) : SafeCore (data.parent (region4 0 (by decide +kernel)) p) := by
  have hh : p=0 ∨ p=1 := by change p=(0 : Fin 2) ∨ p=(1 : Fin 2); omega
  rcases hh with rfl|rfl
  · exact parent4_0
  · exact parent4_1
theorem region4_safe (i : Fin 2) : SafeCore (matrix (zero param4_0 param4_1 param4_2 param4_3 i) 0) := by
  rw [zero_eval]
  exact Safe.region (D:=data) (core:=Core) (region4 0 (by decide +kernel)) (parents4_safe) (0,Fin.castLE (by decide +kernel) i)

def param5_0 : P := [4]
def param5_1 : P := [4]
def param5_2 : P := [11]
def param5_3 : P := [41]
theorem domain5 (t : Int) (ht : 0≤t) : UnitZeroStrip.Domain (eval param5_0 t) (eval param5_1 t) (eval param5_2 t) (eval param5_3 t) := zero_domain param5_0 param5_1 param5_2 param5_3 t ht (by decide +kernel)
def region5 (t : Int) (ht : 0≤t) : Region := .inl (.inr (.n (eval param5_0 t) ⟨eval param5_1 t,eval param5_2 t,eval param5_3 t⟩ (domain5 t ht)))
theorem parent5_0 : SafeCore (data.parent (region5 0 (by decide +kernel)) (0 : Fin 2)) := by
  have he := mutation_equal (zero param5_0 param5_1 param5_2 param5_3 0) (prelabel (bnode 31) perm6.symm) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse,zero_eval] at he
  rw [show data.parent (region5 0 (by decide +kernel)) (0 : Fin 2) = _ from he]
  exact Safe.framed (base_safe 31) perm6.symm
theorem parent5_1 : SafeCore (data.parent (region5 0 (by decide +kernel)) (1 : Fin 2)) := by
  have he := mutation_equal (zero param5_0 param5_1 param5_2 param5_3 1) (prelabel (bnode 42) perm6.symm) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse,zero_eval] at he
  rw [show data.parent (region5 0 (by decide +kernel)) (1 : Fin 2) = _ from he]
  exact Safe.framed (base_safe 42) perm6.symm
theorem parents5_safe (p : Fin 2) : SafeCore (data.parent (region5 0 (by decide +kernel)) p) := by
  have hh : p=0 ∨ p=1 := by change p=(0 : Fin 2) ∨ p=(1 : Fin 2); omega
  rcases hh with rfl|rfl
  · exact parent5_0
  · exact parent5_1
theorem region5_safe (i : Fin 2) : SafeCore (matrix (zero param5_0 param5_1 param5_2 param5_3 i) 0) := by
  rw [zero_eval]
  exact Safe.region (D:=data) (core:=Core) (region5 0 (by decide +kernel)) (parents5_safe) (0,Fin.castLE (by decide +kernel) i)

def param6_0 : P := [5]
def param6_1 : P := [56]
def param6_2 : P := [8]
def param6_3 : P := [11]
theorem domain6 (t : Int) (ht : 0≤t) : GenericStrip.Domain (eval param6_0 t) (eval param6_1 t) (eval param6_2 t) (eval param6_3 t) := generic_domain param6_0 param6_1 param6_2 param6_3 t ht (by decide +kernel)
def region6 (t : Int) (ht : 0≤t) : Region := .inl (.inl ⟨eval param6_0 t,⟨eval param6_1 t,eval param6_2 t,eval param6_3 t⟩,domain6 t ht⟩)
theorem parent6_0 : SafeCore (data.parent (region6 0 (by decide +kernel)) (0 : Fin 3)) := by
  have he := mutation_equal (generic param6_0 param6_1 param6_2 param6_3 0) (preverse (prelabel (bnode 46) perm4.symm)) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  rw [show data.parent (region6 0 (by decide +kernel)) (0 : Fin 3) = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 46) perm4.symm)
theorem parent6_1 : SafeCore (data.parent (region6 0 (by decide +kernel)) (1 : Fin 3)) := by
  have he := mutation_equal (generic param6_0 param6_1 param6_2 param6_3 0) (prelabel (bnode 36) perm22.symm) 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  rw [show data.parent (region6 0 (by decide +kernel)) (1 : Fin 3) = _ from he]
  exact Safe.framed (base_safe 36) perm22.symm
theorem parent6_2 : SafeCore (data.parent (region6 0 (by decide +kernel)) (2 : Fin 3)) := by
  have he := mutation_equal (generic param6_0 param6_1 param6_2 param6_3 2) (preverse (prelabel (bnode 48) perm16.symm)) 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  rw [show data.parent (region6 0 (by decide +kernel)) (2 : Fin 3) = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 48) perm16.symm)
theorem parents6_safe (p : Fin 3) : SafeCore (data.parent (region6 0 (by decide +kernel)) p) := by
  have hh : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hh with rfl|rfl|rfl
  · exact parent6_0
  · exact parent6_1
  · exact parent6_2
theorem region6_safe (i : Fin 3) : SafeCore (matrix (generic param6_0 param6_1 param6_2 param6_3 i) 0) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core) (region6 0 (by decide +kernel)) (parents6_safe) (0,Fin.castLE (by decide +kernel) i)

def param7_0 : P := [2]
def param7_1 : P := [11]
def param7_2 : P := [5]
def param7_3 : P := [6]
theorem domain7 (t : Int) (ht : 0≤t) : GenericStrip.Domain (eval param7_0 t) (eval param7_1 t) (eval param7_2 t) (eval param7_3 t) := generic_domain param7_0 param7_1 param7_2 param7_3 t ht (by decide +kernel)
def region7 (t : Int) (ht : 0≤t) : Region := .inl (.inl ⟨eval param7_0 t,⟨eval param7_1 t,eval param7_2 t,eval param7_3 t⟩,domain7 t ht⟩)
theorem parent7_0 : SafeCore (data.parent (region7 0 (by decide +kernel)) (0 : Fin 3)) := by
  have he := mutation_equal (generic param7_0 param7_1 param7_2 param7_3 0) (preverse (prelabel (bnode 36) perm4.symm)) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  rw [show data.parent (region7 0 (by decide +kernel)) (0 : Fin 3) = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 36) perm4.symm)
theorem parent7_1 : SafeCore (data.parent (region7 0 (by decide +kernel)) (1 : Fin 3)) := by
  have he := mutation_equal (generic param7_0 param7_1 param7_2 param7_3 0) (prelabel (ptail [6] 0) perm22.symm) 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse,generic_eval,ptail_eval] at he
  rw [show data.parent (region7 0 (by decide +kernel)) (1 : Fin 3) = _ from he]
  exact Safe.framed (tail_safe (eval [6] 0) (by simpa [eval] using le [3] [6] 0 (by decide +kernel) (by decide +kernel)) 0) perm22.symm
theorem parent7_2 : SafeCore (data.parent (region7 0 (by decide +kernel)) (2 : Fin 3)) := by
  have he := mutation_equal (generic param7_0 param7_1 param7_2 param7_3 2) (preverse (prelabel (bnode 47) perm16.symm)) 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  rw [show data.parent (region7 0 (by decide +kernel)) (2 : Fin 3) = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 47) perm16.symm)
theorem parents7_safe (p : Fin 3) : SafeCore (data.parent (region7 0 (by decide +kernel)) p) := by
  have hh : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hh with rfl|rfl|rfl
  · exact parent7_0
  · exact parent7_1
  · exact parent7_2
theorem region7_safe (i : Fin 3) : SafeCore (matrix (generic param7_0 param7_1 param7_2 param7_3 i) 0) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core) (region7 0 (by decide +kernel)) (parents7_safe) (0,Fin.castLE (by decide +kernel) i)

def param8_0 : P := [3]
def param8_1 : P := [29]
def param8_2 : P := [5]
def param8_3 : P := [9]
theorem domain8 (t : Int) (ht : 0≤t) : GenericStrip.Domain (eval param8_0 t) (eval param8_1 t) (eval param8_2 t) (eval param8_3 t) := generic_domain param8_0 param8_1 param8_2 param8_3 t ht (by decide +kernel)
def region8 (t : Int) (ht : 0≤t) : Region := .inl (.inl ⟨eval param8_0 t,⟨eval param8_1 t,eval param8_2 t,eval param8_3 t⟩,domain8 t ht⟩)
theorem parent8_0 : SafeCore (data.parent (region8 0 (by decide +kernel)) (0 : Fin 3)) := by
  have he := mutation_equal (generic param8_0 param8_1 param8_2 param8_3 0) (preverse (prelabel (bnode 49) perm4.symm)) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  rw [show data.parent (region8 0 (by decide +kernel)) (0 : Fin 3) = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 49) perm4.symm)
theorem parent8_1 : SafeCore (data.parent (region8 0 (by decide +kernel)) (1 : Fin 3)) := by
  have he := mutation_equal (generic param8_0 param8_1 param8_2 param8_3 0) (prelabel (bnode 38) perm22.symm) 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  rw [show data.parent (region8 0 (by decide +kernel)) (1 : Fin 3) = _ from he]
  exact Safe.framed (base_safe 38) perm22.symm
theorem parent8_2 : SafeCore (data.parent (region8 0 (by decide +kernel)) (2 : Fin 3)) := by
  have he := mutation_equal (generic param8_0 param8_1 param8_2 param8_3 2) (preverse (prelabel (bnode 50) perm16.symm)) 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  rw [show data.parent (region8 0 (by decide +kernel)) (2 : Fin 3) = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 50) perm16.symm)
theorem parents8_safe (p : Fin 3) : SafeCore (data.parent (region8 0 (by decide +kernel)) p) := by
  have hh : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hh with rfl|rfl|rfl
  · exact parent8_0
  · exact parent8_1
  · exact parent8_2
theorem region8_safe (i : Fin 3) : SafeCore (matrix (generic param8_0 param8_1 param8_2 param8_3 i) 0) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core) (region8 0 (by decide +kernel)) (parents8_safe) (0,Fin.castLE (by decide +kernel) i)

def param9_0 : P := [4]
def param9_1 : P := [334]
def param9_2 : P := [64]
def param9_3 : P := [83]
theorem domain9 (t : Int) (ht : 0≤t) : GenericStrip.Domain (eval param9_0 t) (eval param9_1 t) (eval param9_2 t) (eval param9_3 t) := generic_domain param9_0 param9_1 param9_2 param9_3 t ht (by decide +kernel)
def region9 (t : Int) (ht : 0≤t) : Region := .inl (.inl ⟨eval param9_0 t,⟨eval param9_1 t,eval param9_2 t,eval param9_3 t⟩,domain9 t ht⟩)
theorem parent9_0 : SafeCore (data.parent (region9 0 (by decide +kernel)) (0 : Fin 3)) := by
  have he := mutation_equal (generic param9_0 param9_1 param9_2 param9_3 0) (preverse (prelabel (bnode 53) perm4.symm)) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  rw [show data.parent (region9 0 (by decide +kernel)) (0 : Fin 3) = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 53) perm4.symm)
theorem parent9_1 : SafeCore (data.parent (region9 0 (by decide +kernel)) (1 : Fin 3)) := by
  have he := mutation_equal (generic param9_0 param9_1 param9_2 param9_3 0) (prelabel (bnode 44) perm22.symm) 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  rw [show data.parent (region9 0 (by decide +kernel)) (1 : Fin 3) = _ from he]
  exact Safe.framed (base_safe 44) perm22.symm
theorem parent9_2 : SafeCore (data.parent (region9 0 (by decide +kernel)) (2 : Fin 3)) := by
  have he := mutation_equal (generic param9_0 param9_1 param9_2 param9_3 2) (preverse (prelabel (bnode 54) perm16.symm)) 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  rw [show data.parent (region9 0 (by decide +kernel)) (2 : Fin 3) = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 54) perm16.symm)
theorem parents9_safe (p : Fin 3) : SafeCore (data.parent (region9 0 (by decide +kernel)) p) := by
  have hh : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hh with rfl|rfl|rfl
  · exact parent9_0
  · exact parent9_1
  · exact parent9_2
theorem region9_safe (i : Fin 3) : SafeCore (matrix (generic param9_0 param9_1 param9_2 param9_3 i) 0) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core) (region9 0 (by decide +kernel)) (parents9_safe) (0,Fin.castLE (by decide +kernel) i)

def param10_0 : P := [3]
def param10_1 : P := [136]
def param10_2 : P := [29]
def param10_3 : P := [44]
theorem domain10 (t : Int) (ht : 0≤t) : GenericStrip.Domain (eval param10_0 t) (eval param10_1 t) (eval param10_2 t) (eval param10_3 t) := generic_domain param10_0 param10_1 param10_2 param10_3 t ht (by decide +kernel)
def region10 (t : Int) (ht : 0≤t) : Region := .inl (.inl ⟨eval param10_0 t,⟨eval param10_1 t,eval param10_2 t,eval param10_3 t⟩,domain10 t ht⟩)
theorem parent10_0 : SafeCore (data.parent (region10 0 (by decide +kernel)) (0 : Fin 3)) := by
  have he := mutation_equal (generic param10_0 param10_1 param10_2 param10_3 0) (preverse (prelabel (bnode 57) perm4.symm)) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  rw [show data.parent (region10 0 (by decide +kernel)) (0 : Fin 3) = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 57) perm4.symm)
theorem parent10_1 : SafeCore (data.parent (region10 0 (by decide +kernel)) (1 : Fin 3)) := by
  have he := mutation_equal (generic param10_0 param10_1 param10_2 param10_3 0) (prelabel (bnode 56) perm22.symm) 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  rw [show data.parent (region10 0 (by decide +kernel)) (1 : Fin 3) = _ from he]
  exact Safe.framed (base_safe 56) perm22.symm
theorem parent10_2 : SafeCore (data.parent (region10 0 (by decide +kernel)) (2 : Fin 3)) := by
  have he := mutation_equal (generic param10_0 param10_1 param10_2 param10_3 2) (preverse (prelabel (bnode 58) perm16.symm)) 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  rw [show data.parent (region10 0 (by decide +kernel)) (2 : Fin 3) = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 58) perm16.symm)
theorem parents10_safe (p : Fin 3) : SafeCore (data.parent (region10 0 (by decide +kernel)) p) := by
  have hh : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hh with rfl|rfl|rfl
  · exact parent10_0
  · exact parent10_1
  · exact parent10_2
theorem region10_safe (i : Fin 3) : SafeCore (matrix (generic param10_0 param10_1 param10_2 param10_3 i) 0) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core) (region10 0 (by decide +kernel)) (parents10_safe) (0,Fin.castLE (by decide +kernel) i)

theorem base_cyclic0 : ¬Acyclic (base 0) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (bnode 0 0 3) 0 (by decide +kernel) (by decide +kernel))
  have h1 := hr 3 1 (pos (bnode 0 3 1) 0 (by decide +kernel) (by decide +kernel))
  have h2 := hr 1 0 (pos (bnode 0 1 0) 0 (by decide +kernel) (by decide +kernel))
  omega

theorem base_edge0_0 : SafeCore (mutate (base 0) 0) := by
  have he := mutation_equal (bnode 0) (prelabel (bnode 13) perm23.symm) 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 0) 0 = _ from he]
  exact Safe.framed (base_safe 13) perm23.symm

theorem base_edge0_1 : SafeCore (mutate (base 0) 1) := by
  have he := mutation_equal (bnode 0) (preverse (prelabel (bnode 6) perm13.symm)) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 0) 1 = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 6) perm13.symm)

theorem base_edge0_2 : SafeCore (mutate (base 0) 2) := by
  have he := mutation_equal (bnode 0) (prelabel (bnode 14) perm12.symm) 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 0) 2 = _ from he]
  exact Safe.framed (base_safe 14) perm12.symm

theorem base_edge0_3 : SafeCore (mutate (base 0) 3) := by
  have he := mutation_equal (bnode 0) (preverse (prelabel (bnode 0) perm14.symm)) 3 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 0) 3 = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 0) perm14.symm)

theorem base_cyclic1 : ¬Acyclic (base 1) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (bnode 1 0 3) 0 (by decide +kernel) (by decide +kernel))
  have h1 := hr 3 1 (pos (bnode 1 3 1) 0 (by decide +kernel) (by decide +kernel))
  have h2 := hr 1 0 (pos (bnode 1 1 0) 0 (by decide +kernel) (by decide +kernel))
  omega

theorem base_edge1_0 : SafeCore (mutate (base 1) 0) := by
  have he := mutation_equal (bnode 1) (preverse (prelabel (bnode 13) perm0.symm)) 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 1) 0 = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 13) perm0.symm)

theorem base_edge1_1 : SafeCore (mutate (base 1) 1) := by
  have he := mutation_equal (bnode 1) (prelabel (bnode 4) perm3.symm) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 1) 1 = _ from he]
  exact Safe.framed (base_safe 4) perm3.symm

theorem base_edge1_2 : SafeCore (mutate (base 1) 2) := by
  have he := mutation_equal (bnode 1) (preverse (prelabel (bnode 1) perm6.symm)) 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 1) 2 = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 1) perm6.symm)

theorem base_edge1_3 : SafeCore (mutate (base 1) 3) := by
  have he := mutation_equal (bnode 1) (prelabel (bnode 14) perm0.symm) 3 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 1) 3 = _ from he]
  exact Safe.framed (base_safe 14) perm0.symm

theorem base_cyclic2 : ¬Acyclic (base 2) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 1 2 (pos (bnode 2 1 2) 0 (by decide +kernel) (by decide +kernel))
  have h1 := hr 2 3 (pos (bnode 2 2 3) 0 (by decide +kernel) (by decide +kernel))
  have h2 := hr 3 1 (pos (bnode 2 3 1) 0 (by decide +kernel) (by decide +kernel))
  omega

theorem base_edge2_0 : SafeCore (mutate (base 2) 0) := by
  have he := mutation_equal (bnode 2) (preverse (prelabel (bnode 15) perm0.symm)) 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 2) 0 = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 15) perm0.symm)

theorem base_edge2_1 : SafeCore (mutate (base 2) 1) := by
  have he := mutation_equal (bnode 2) (prelabel (bnode 15) perm0.symm) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 2) 1 = _ from he]
  exact Safe.framed (base_safe 15) perm0.symm

theorem base_edge2_2 : SafeCore (mutate (base 2) 2) := by
  have he := mutation_equal (bnode 2) (preverse (prelabel (ptail [6] 1) perm7.symm)) 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse,ptail_eval] at he
  rw [show mutate (base 2) 2 = _ from he]
  exact Safe.reversed (Safe.framed (tail_safe (eval [6] 0) (by simpa [eval] using le [3] [6] 0 (by decide +kernel) (by decide +kernel)) 1) perm7.symm)

theorem base_edge2_3 : SafeCore (mutate (base 2) 3) := by
  have he := mutation_equal (bnode 2) (prelabel (bnode 5) perm0.symm) 3 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 2) 3 = _ from he]
  exact Safe.framed (base_safe 5) perm0.symm

theorem base_cyclic3 : ¬Acyclic (base 3) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 1 2 (pos (bnode 3 1 2) 0 (by decide +kernel) (by decide +kernel))
  have h1 := hr 2 3 (pos (bnode 3 2 3) 0 (by decide +kernel) (by decide +kernel))
  have h2 := hr 3 1 (pos (bnode 3 3 1) 0 (by decide +kernel) (by decide +kernel))
  omega

theorem base_edge3_0 : SafeCore (mutate (base 3) 0) := by
  have he := mutation_equal (bnode 3) (preverse (prelabel (bnode 16) perm0.symm)) 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 3) 0 = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 16) perm0.symm)

theorem base_edge3_1 : SafeCore (mutate (base 3) 1) := by
  have he := mutation_equal (bnode 3) (prelabel (bnode 17) perm0.symm) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 3) 1 = _ from he]
  exact Safe.framed (base_safe 17) perm0.symm

theorem base_edge3_2 : SafeCore (mutate (base 3) 2) := by
  have he := mutation_equal (bnode 3) (preverse (prelabel (bnode 8) perm3.symm)) 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 3) 2 = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 8) perm3.symm)

theorem base_edge3_3 : SafeCore (mutate (base 3) 3) := by
  have he := mutation_equal (bnode 3) (prelabel (ptail [6] 2) perm6.symm) 3 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse,ptail_eval] at he
  rw [show mutate (base 3) 3 = _ from he]
  exact Safe.framed (tail_safe (eval [6] 0) (by simpa [eval] using le [3] [6] 0 (by decide +kernel) (by decide +kernel)) 2) perm6.symm

theorem base_cyclic4 : ¬Acyclic (base 4) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (bnode 4 0 3) 0 (by decide +kernel) (by decide +kernel))
  have h1 := hr 3 1 (pos (bnode 4 3 1) 0 (by decide +kernel) (by decide +kernel))
  have h2 := hr 1 0 (pos (bnode 4 1 0) 0 (by decide +kernel) (by decide +kernel))
  omega

theorem base_edge4_0 : SafeCore (mutate (base 4) 0) := by
  have he := mutation_equal (bnode 4) (preverse (prelabel (root [3] [5] [11] [2] [4] [1]) perm5.symm)) 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (base_safe 4) 0
  rw [show mutate (base 4) 0 = _ from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [3] [5] [11] [2] [4] [1] 0 (by decide +kernel) (by decide +kernel)) perm5.symm)

theorem base_edge4_1 : SafeCore (mutate (base 4) 1) := by
  have he := mutation_equal (bnode 4) (prelabel (bnode 18) perm6.symm) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 4) 1 = _ from he]
  exact Safe.framed (base_safe 18) perm6.symm

theorem base_edge4_2 : SafeCore (mutate (base 4) 2) := by
  have he := mutation_equal (bnode 4) (preverse (prelabel (ptail [6] 0) perm6.symm)) 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse,ptail_eval] at he
  rw [show mutate (base 4) 2 = _ from he]
  exact Safe.reversed (Safe.framed (tail_safe (eval [6] 0) (by simpa [eval] using le [3] [6] 0 (by decide +kernel) (by decide +kernel)) 0) perm6.symm)

theorem base_edge4_3 : SafeCore (mutate (base 4) 3) := by
  have he := mutation_equal (bnode 4) (prelabel (bnode 1) perm4.symm) 3 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 4) 3 = _ from he]
  exact Safe.framed (base_safe 1) perm4.symm

theorem base_cyclic5 : ¬Acyclic (base 5) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (bnode 5 0 3) 0 (by decide +kernel) (by decide +kernel))
  have h1 := hr 3 2 (pos (bnode 5 3 2) 0 (by decide +kernel) (by decide +kernel))
  have h2 := hr 2 0 (pos (bnode 5 2 0) 0 (by decide +kernel) (by decide +kernel))
  omega

theorem base_edge5_0 : SafeCore (mutate (base 5) 0) := by
  have he := mutation_equal (bnode 5) (preverse (prelabel (bnode 19) perm0.symm)) 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 5) 0 = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 19) perm0.symm)

theorem base_edge5_1 : SafeCore (mutate (base 5) 1) := by
  have he := mutation_equal (bnode 5) (prelabel (bnode 20) perm0.symm) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 5) 1 = _ from he]
  exact Safe.framed (base_safe 20) perm0.symm

theorem base_edge5_2 : SafeCore (mutate (base 5) 2) := by
  have he := mutation_equal (bnode 5) (prelabel (bnode 8) perm1.symm) 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 5) 2 = _ from he]
  exact Safe.framed (base_safe 8) perm1.symm

theorem base_edge5_3 : SafeCore (mutate (base 5) 3) := by
  have he := mutation_equal (bnode 5) (prelabel (bnode 2) perm0.symm) 3 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 5) 3 = _ from he]
  exact Safe.framed (base_safe 2) perm0.symm

theorem base_cyclic6 : ¬Acyclic (base 6) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (bnode 6 0 3) 0 (by decide +kernel) (by decide +kernel))
  have h1 := hr 3 1 (pos (bnode 6 3 1) 0 (by decide +kernel) (by decide +kernel))
  have h2 := hr 1 0 (pos (bnode 6 1 0) 0 (by decide +kernel) (by decide +kernel))
  omega

theorem base_edge6_0 : SafeCore (mutate (base 6) 0) := by
  have he := mutation_equal (bnode 6) (preverse (prelabel (bnode 21) perm0.symm)) 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 6) 0 = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 21) perm0.symm)

theorem base_edge6_1 : SafeCore (mutate (base 6) 1) := by
  have he := mutation_equal (bnode 6) (preverse (prelabel (ptail [7] 1) perm19.symm)) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse,ptail_eval] at he
  rw [show mutate (base 6) 1 = _ from he]
  exact Safe.reversed (Safe.framed (tail_safe (eval [7] 0) (by simpa [eval] using le [3] [7] 0 (by decide +kernel) (by decide +kernel)) 1) perm19.symm)

theorem base_edge6_2 : SafeCore (mutate (base 6) 2) := by
  have he := mutation_equal (bnode 6) (prelabel (bnode 9) perm0.symm) 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 6) 2 = _ from he]
  exact Safe.framed (base_safe 9) perm0.symm

theorem base_edge6_3 : SafeCore (mutate (base 6) 3) := by
  have he := mutation_equal (bnode 6) (preverse (prelabel (bnode 0) perm10.symm)) 3 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 6) 3 = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 0) perm10.symm)

theorem base_cyclic7 : ¬Acyclic (base 7) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (bnode 7 0 3) 0 (by decide +kernel) (by decide +kernel))
  have h1 := hr 3 2 (pos (bnode 7 3 2) 0 (by decide +kernel) (by decide +kernel))
  have h2 := hr 2 0 (pos (bnode 7 2 0) 0 (by decide +kernel) (by decide +kernel))
  omega

theorem base_edge7_0 : SafeCore (mutate (base 7) 0) := by
  have he := mutation_equal (bnode 7) (prelabel (bnode 12) perm21.symm) 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 7) 0 = _ from he]
  exact Safe.framed (base_safe 12) perm21.symm

theorem base_edge7_1 : SafeCore (mutate (base 7) 1) := by
  have he := mutation_equal (bnode 7) (preverse (prelabel (bnode 22) perm13.symm)) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 7) 1 = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 22) perm13.symm)

theorem base_edge7_2 : SafeCore (mutate (base 7) 2) := by
  have he := mutation_equal (bnode 7) (preverse (prelabel (ptail [7] 2) perm20.symm)) 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse,ptail_eval] at he
  rw [show mutate (base 7) 2 = _ from he]
  exact Safe.reversed (Safe.framed (tail_safe (eval [7] 0) (by simpa [eval] using le [3] [7] 0 (by decide +kernel) (by decide +kernel)) 2) perm20.symm)

theorem base_edge7_3 : SafeCore (mutate (base 7) 3) := by
  have he := mutation_equal (bnode 7) (prelabel (bnode 21) perm1.symm) 3 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 7) 3 = _ from he]
  exact Safe.framed (base_safe 21) perm1.symm

theorem base_cyclic8 : ¬Acyclic (base 8) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (bnode 8 0 3) 0 (by decide +kernel) (by decide +kernel))
  have h1 := hr 3 1 (pos (bnode 8 3 1) 0 (by decide +kernel) (by decide +kernel))
  have h2 := hr 1 0 (pos (bnode 8 1 0) 0 (by decide +kernel) (by decide +kernel))
  omega

theorem base_edge8_0 : SafeCore (mutate (base 8) 0) := by
  have he := mutation_equal (bnode 8) (preverse (prelabel (root [4] [11] [15] [3] [4] [1]) perm5.symm)) 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (base_safe 8) 0
  rw [show mutate (base 8) 0 = _ from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [4] [11] [15] [3] [4] [1] 0 (by decide +kernel) (by decide +kernel)) perm5.symm)

theorem base_edge8_1 : SafeCore (mutate (base 8) 1) := by
  have he := mutation_equal (bnode 8) (preverse (prelabel (bnode 3) perm4.symm)) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 8) 1 = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 3) perm4.symm)

theorem base_edge8_2 : SafeCore (mutate (base 8) 2) := by
  have he := mutation_equal (bnode 8) (preverse (prelabel (ptail [7] 0) perm6.symm)) 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse,ptail_eval] at he
  rw [show mutate (base 8) 2 = _ from he]
  exact Safe.reversed (Safe.framed (tail_safe (eval [7] 0) (by simpa [eval] using le [3] [7] 0 (by decide +kernel) (by decide +kernel)) 0) perm6.symm)

theorem base_edge8_3 : SafeCore (mutate (base 8) 3) := by
  have he := mutation_equal (bnode 8) (prelabel (bnode 5) perm1.symm) 3 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 8) 3 = _ from he]
  exact Safe.framed (base_safe 5) perm1.symm

theorem base_cyclic9 : ¬Acyclic (base 9) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (bnode 9 0 2) 0 (by decide +kernel) (by decide +kernel))
  have h1 := hr 2 1 (pos (bnode 9 2 1) 0 (by decide +kernel) (by decide +kernel))
  have h2 := hr 1 0 (pos (bnode 9 1 0) 0 (by decide +kernel) (by decide +kernel))
  omega

theorem base_edge9_0 : SafeCore (mutate (base 9) 0) := by
  have he := mutation_equal (bnode 9) (preverse (prelabel (bnode 12) perm1.symm)) 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 9) 0 = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 12) perm1.symm)

theorem base_edge9_1 : SafeCore (mutate (base 9) 1) := by
  have he := mutation_equal (bnode 9) (prelabel (bnode 12) perm6.symm) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 9) 1 = _ from he]
  exact Safe.framed (base_safe 12) perm6.symm

theorem base_edge9_2 : SafeCore (mutate (base 9) 2) := by
  have he := mutation_equal (bnode 9) (prelabel (bnode 6) perm0.symm) 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 9) 2 = _ from he]
  exact Safe.framed (base_safe 6) perm0.symm

theorem base_edge9_3 : SafeCore (mutate (base 9) 3) := by
  have he := mutation_equal (bnode 9) (preverse (prelabel (bnode 6) perm7.symm)) 3 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 9) 3 = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 6) perm7.symm)

theorem base_cyclic10 : ¬Acyclic (base 10) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (bnode 10 0 3) 0 (by decide +kernel) (by decide +kernel))
  have h1 := hr 3 1 (pos (bnode 10 3 1) 0 (by decide +kernel) (by decide +kernel))
  have h2 := hr 1 0 (pos (bnode 10 1 0) 0 (by decide +kernel) (by decide +kernel))
  omega

theorem base_edge10_0 : SafeCore (mutate (base 10) 0) := by
  have he := mutation_equal (bnode 10) (prelabel (ptail [8] 1) perm21.symm) 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse,ptail_eval] at he
  rw [show mutate (base 10) 0 = _ from he]
  exact Safe.framed (tail_safe (eval [8] 0) (by simpa [eval] using le [3] [8] 0 (by decide +kernel) (by decide +kernel)) 1) perm21.symm

theorem base_edge10_1 : SafeCore (mutate (base 10) 1) := by
  have he := mutation_equal (bnode 10) (preverse (prelabel (bnode 23) perm19.symm)) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 10) 1 = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 23) perm19.symm)

theorem base_edge10_2 : SafeCore (mutate (base 10) 2) := by
  have he := mutation_equal (bnode 10) (prelabel (ptail [6] 0) perm1.symm) 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse,ptail_eval] at he
  rw [show mutate (base 10) 2 = _ from he]
  exact Safe.framed (tail_safe (eval [6] 0) (by simpa [eval] using le [3] [6] 0 (by decide +kernel) (by decide +kernel)) 0) perm1.symm

theorem base_edge10_3 : SafeCore (mutate (base 10) 3) := by
  have he := mutation_equal (bnode 10) (preverse (prelabel (bnode 14) perm10.symm)) 3 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 10) 3 = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 14) perm10.symm)

theorem base_cyclic11 : ¬Acyclic (base 11) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (bnode 11 0 3) 0 (by decide +kernel) (by decide +kernel))
  have h1 := hr 3 1 (pos (bnode 11 3 1) 0 (by decide +kernel) (by decide +kernel))
  have h2 := hr 1 0 (pos (bnode 11 1 0) 0 (by decide +kernel) (by decide +kernel))
  omega

theorem base_edge11_0 : SafeCore (mutate (base 11) 0) := by
  have he := mutation_equal (bnode 11) (prelabel (ptail [8] 2) perm21.symm) 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse,ptail_eval] at he
  rw [show mutate (base 11) 0 = _ from he]
  exact Safe.framed (tail_safe (eval [8] 0) (by simpa [eval] using le [3] [8] 0 (by decide +kernel) (by decide +kernel)) 2) perm21.symm

theorem base_edge11_1 : SafeCore (mutate (base 11) 1) := by
  have he := mutation_equal (bnode 11) (preverse (prelabel (root [5] [21] [8] [4] [2] [1]) perm6.symm)) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (base_safe 11) 1
  rw [show mutate (base 11) 1 = _ from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [5] [21] [8] [4] [2] [1] 0 (by decide +kernel) (by decide +kernel)) perm6.symm)

theorem base_edge11_2 : SafeCore (mutate (base 11) 2) := by
  have he := mutation_equal (bnode 11) (preverse (prelabel (ptail [6] 3) perm20.symm)) 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse,ptail_eval] at he
  rw [show mutate (base 11) 2 = _ from he]
  exact Safe.reversed (Safe.framed (tail_safe (eval [6] 0) (by simpa [eval] using le [3] [6] 0 (by decide +kernel) (by decide +kernel)) 3) perm20.symm)

theorem base_edge11_3 : SafeCore (mutate (base 11) 3) := by
  have he := mutation_equal (bnode 11) (preverse (prelabel (bnode 18) perm15.symm)) 3 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 11) 3 = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 18) perm15.symm)

theorem base_cyclic12 : ¬Acyclic (base 12) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (bnode 12 0 2) 0 (by decide +kernel) (by decide +kernel))
  have h1 := hr 2 1 (pos (bnode 12 2 1) 0 (by decide +kernel) (by decide +kernel))
  have h2 := hr 1 0 (pos (bnode 12 1 0) 0 (by decide +kernel) (by decide +kernel))
  omega

theorem base_edge12_0 : SafeCore (mutate (base 12) 0) := by
  have he := mutation_equal (bnode 12) (prelabel (bnode 9) perm6.symm) 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 12) 0 = _ from he]
  exact Safe.framed (base_safe 9) perm6.symm

theorem base_edge12_1 : SafeCore (mutate (base 12) 1) := by
  have he := mutation_equal (bnode 12) (preverse (prelabel (root [5] [19] [19] [4] [4] [1]) perm6.symm)) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (base_safe 12) 1
  rw [show mutate (base 12) 1 = _ from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [5] [19] [19] [4] [4] [1] 0 (by decide +kernel) (by decide +kernel)) perm6.symm)

theorem base_edge12_2 : SafeCore (mutate (base 12) 2) := by
  have he := mutation_equal (bnode 12) (preverse (prelabel (ptail [8] 0) perm21.symm)) 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse,ptail_eval] at he
  rw [show mutate (base 12) 2 = _ from he]
  exact Safe.reversed (Safe.framed (tail_safe (eval [8] 0) (by simpa [eval] using le [3] [8] 0 (by decide +kernel) (by decide +kernel)) 0) perm21.symm)

theorem base_edge12_3 : SafeCore (mutate (base 12) 3) := by
  have he := mutation_equal (bnode 12) (prelabel (bnode 7) perm21.symm) 3 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 12) 3 = _ from he]
  exact Safe.framed (base_safe 7) perm21.symm

theorem base_cyclic13 : ¬Acyclic (base 13) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (bnode 13 0 3) 0 (by decide +kernel) (by decide +kernel))
  have h1 := hr 3 1 (pos (bnode 13 3 1) 0 (by decide +kernel) (by decide +kernel))
  have h2 := hr 1 0 (pos (bnode 13 1 0) 0 (by decide +kernel) (by decide +kernel))
  omega

theorem base_edge13_0 : SafeCore (mutate (base 13) 0) := by
  have he := mutation_equal (bnode 13) (preverse (prelabel (bnode 1) perm0.symm)) 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 13) 0 = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 1) perm0.symm)

theorem base_edge13_1 : SafeCore (mutate (base 13) 1) := by
  have he := mutation_equal (bnode 13) (preverse (prelabel (bnode 24) perm19.symm)) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 13) 1 = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 24) perm19.symm)

theorem base_edge13_2 : SafeCore (mutate (base 13) 2) := by
  have he := mutation_equal (bnode 13) (prelabel (bnode 18) perm1.symm) 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 13) 2 = _ from he]
  exact Safe.framed (base_safe 18) perm1.symm

theorem base_edge13_3 : SafeCore (mutate (base 13) 3) := by
  have he := mutation_equal (bnode 13) (prelabel (bnode 0) perm23.symm) 3 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 13) 3 = _ from he]
  exact Safe.framed (base_safe 0) perm23.symm

theorem base_cyclic14 : ¬Acyclic (base 14) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 1 3 (pos (bnode 14 1 3) 0 (by decide +kernel) (by decide +kernel))
  have h1 := hr 3 2 (pos (bnode 14 3 2) 0 (by decide +kernel) (by decide +kernel))
  have h2 := hr 2 1 (pos (bnode 14 2 1) 0 (by decide +kernel) (by decide +kernel))
  omega

theorem base_edge14_0 : SafeCore (mutate (base 14) 0) := by
  have he := mutation_equal (bnode 14) (prelabel (bnode 0) perm8.symm) 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 14) 0 = _ from he]
  exact Safe.framed (base_safe 0) perm8.symm

theorem base_edge14_1 : SafeCore (mutate (base 14) 1) := by
  have he := mutation_equal (bnode 14) (preverse (prelabel (bnode 10) perm13.symm)) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 14) 1 = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 10) perm13.symm)

theorem base_edge14_2 : SafeCore (mutate (base 14) 2) := by
  have he := mutation_equal (bnode 14) (prelabel (bnode 25) perm1.symm) 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 14) 2 = _ from he]
  exact Safe.framed (base_safe 25) perm1.symm

theorem base_edge14_3 : SafeCore (mutate (base 14) 3) := by
  have he := mutation_equal (bnode 14) (prelabel (bnode 1) perm0.symm) 3 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 14) 3 = _ from he]
  exact Safe.framed (base_safe 1) perm0.symm

theorem base_cyclic15 : ¬Acyclic (base 15) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 1 3 (pos (bnode 15 1 3) 0 (by decide +kernel) (by decide +kernel))
  have h1 := hr 3 2 (pos (bnode 15 3 2) 0 (by decide +kernel) (by decide +kernel))
  have h2 := hr 2 1 (pos (bnode 15 2 1) 0 (by decide +kernel) (by decide +kernel))
  omega

theorem base_edge15_0 : SafeCore (mutate (base 15) 0) := by
  have he := mutation_equal (bnode 15) (preverse (prelabel (bnode 2) perm0.symm)) 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 15) 0 = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 2) perm0.symm)

theorem base_edge15_1 : SafeCore (mutate (base 15) 1) := by
  have he := mutation_equal (bnode 15) (prelabel (bnode 2) perm0.symm) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 15) 1 = _ from he]
  exact Safe.framed (base_safe 2) perm0.symm

theorem base_edge15_2 : SafeCore (mutate (base 15) 2) := by
  have he := mutation_equal (bnode 15) (prelabel (bnode 17) perm1.symm) 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 15) 2 = _ from he]
  exact Safe.framed (base_safe 17) perm1.symm

theorem base_edge15_3 : SafeCore (mutate (base 15) 3) := by
  have he := mutation_equal (bnode 15) (preverse (prelabel (bnode 26) perm13.symm)) 3 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 15) 3 = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 26) perm13.symm)

theorem base_cyclic16 : ¬Acyclic (base 16) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (bnode 16 0 3) 0 (by decide +kernel) (by decide +kernel))
  have h1 := hr 3 2 (pos (bnode 16 3 2) 0 (by decide +kernel) (by decide +kernel))
  have h2 := hr 2 0 (pos (bnode 16 2 0) 0 (by decide +kernel) (by decide +kernel))
  omega

theorem base_edge16_0 : SafeCore (mutate (base 16) 0) := by
  have he := mutation_equal (bnode 16) (preverse (prelabel (bnode 3) perm0.symm)) 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 16) 0 = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 3) perm0.symm)

theorem base_edge16_1 : SafeCore (mutate (base 16) 1) := by
  have he := mutation_equal (bnode 16) (prelabel (bnode 27) perm0.symm) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 16) 1 = _ from he]
  exact Safe.framed (base_safe 27) perm0.symm

theorem base_edge16_2 : SafeCore (mutate (base 16) 2) := by
  have he := mutation_equal (bnode 16) (prelabel (bnode 28) perm1.symm) 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 16) 2 = _ from he]
  exact Safe.framed (base_safe 28) perm1.symm

theorem base_edge16_3 : SafeCore (mutate (base 16) 3) := by
  have he := mutation_equal (bnode 16) (preverse (prelabel (root [13] [35] [25] [3] [2] []) perm22.symm)) 3 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (base_safe 16) 3
  rw [show mutate (base 16) 3 = _ from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [13] [35] [25] [3] [2] [] 0 (by decide +kernel) (by decide +kernel)) perm22.symm)

theorem base_cyclic17 : ¬Acyclic (base 17) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (bnode 17 0 3) 0 (by decide +kernel) (by decide +kernel))
  have h1 := hr 3 2 (pos (bnode 17 3 2) 0 (by decide +kernel) (by decide +kernel))
  have h2 := hr 2 0 (pos (bnode 17 2 0) 0 (by decide +kernel) (by decide +kernel))
  omega

theorem base_edge17_0 : SafeCore (mutate (base 17) 0) := by
  have he := mutation_equal (bnode 17) (preverse (prelabel (bnode 27) perm0.symm)) 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 17) 0 = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 27) perm0.symm)

theorem base_edge17_1 : SafeCore (mutate (base 17) 1) := by
  have he := mutation_equal (bnode 17) (prelabel (bnode 3) perm0.symm) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 17) 1 = _ from he]
  exact Safe.framed (base_safe 3) perm0.symm

theorem base_edge17_2 : SafeCore (mutate (base 17) 2) := by
  have he := mutation_equal (bnode 17) (preverse (prelabel (bnode 20) perm0.symm)) 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 17) 2 = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 20) perm0.symm)

theorem base_edge17_3 : SafeCore (mutate (base 17) 3) := by
  have he := mutation_equal (bnode 17) (prelabel (bnode 15) perm1.symm) 3 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 17) 3 = _ from he]
  exact Safe.framed (base_safe 15) perm1.symm

theorem base_cyclic18 : ¬Acyclic (base 18) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (bnode 18 0 3) 0 (by decide +kernel) (by decide +kernel))
  have h1 := hr 3 1 (pos (bnode 18 3 1) 0 (by decide +kernel) (by decide +kernel))
  have h2 := hr 1 0 (pos (bnode 18 1 0) 0 (by decide +kernel) (by decide +kernel))
  omega

theorem base_edge18_0 : SafeCore (mutate (base 18) 0) := by
  have he := mutation_equal (bnode 18) (prelabel (bnode 4) perm6.symm) 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 18) 0 = _ from he]
  exact Safe.framed (base_safe 4) perm6.symm

theorem base_edge18_1 : SafeCore (mutate (base 18) 1) := by
  have he := mutation_equal (bnode 18) (prelabel (bnode 29) perm3.symm) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 18) 1 = _ from he]
  exact Safe.framed (base_safe 29) perm3.symm

theorem base_edge18_2 : SafeCore (mutate (base 18) 2) := by
  have he := mutation_equal (bnode 18) (preverse (prelabel (bnode 11) perm20.symm)) 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 18) 2 = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 11) perm20.symm)

theorem base_edge18_3 : SafeCore (mutate (base 18) 3) := by
  have he := mutation_equal (bnode 18) (prelabel (bnode 13) perm1.symm) 3 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 18) 3 = _ from he]
  exact Safe.framed (base_safe 13) perm1.symm

theorem base_cyclic19 : ¬Acyclic (base 19) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (bnode 19 0 3) 0 (by decide +kernel) (by decide +kernel))
  have h1 := hr 3 2 (pos (bnode 19 3 2) 0 (by decide +kernel) (by decide +kernel))
  have h2 := hr 2 0 (pos (bnode 19 2 0) 0 (by decide +kernel) (by decide +kernel))
  omega

theorem base_edge19_0 : SafeCore (mutate (base 19) 0) := by
  have he := mutation_equal (bnode 19) (preverse (prelabel (bnode 5) perm0.symm)) 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 19) 0 = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 5) perm0.symm)

theorem base_edge19_1 : SafeCore (mutate (base 19) 1) := by
  have he := mutation_equal (bnode 19) (prelabel (bnode 30) perm0.symm) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 19) 1 = _ from he]
  exact Safe.framed (base_safe 30) perm0.symm

theorem base_edge19_2 : SafeCore (mutate (base 19) 2) := by
  have he := mutation_equal (bnode 19) (prelabel (bnode 31) perm1.symm) 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 19) 2 = _ from he]
  exact Safe.framed (base_safe 31) perm1.symm

theorem base_edge19_3 : SafeCore (mutate (base 19) 3) := by
  have he := mutation_equal (bnode 19) (preverse (prelabel (bnode 26) perm16.symm)) 3 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 19) 3 = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 26) perm16.symm)

theorem base_cyclic20 : ¬Acyclic (base 20) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (bnode 20 0 3) 0 (by decide +kernel) (by decide +kernel))
  have h1 := hr 3 2 (pos (bnode 20 3 2) 0 (by decide +kernel) (by decide +kernel))
  have h2 := hr 2 0 (pos (bnode 20 2 0) 0 (by decide +kernel) (by decide +kernel))
  omega

theorem base_edge20_0 : SafeCore (mutate (base 20) 0) := by
  have he := mutation_equal (bnode 20) (preverse (prelabel (bnode 30) perm0.symm)) 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 20) 0 = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 30) perm0.symm)

theorem base_edge20_1 : SafeCore (mutate (base 20) 1) := by
  have he := mutation_equal (bnode 20) (prelabel (bnode 5) perm0.symm) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 20) 1 = _ from he]
  exact Safe.framed (base_safe 5) perm0.symm

theorem base_edge20_2 : SafeCore (mutate (base 20) 2) := by
  have he := mutation_equal (bnode 20) (preverse (prelabel (bnode 17) perm0.symm)) 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 20) 2 = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 17) perm0.symm)

theorem base_edge20_3 : SafeCore (mutate (base 20) 3) := by
  have he := mutation_equal (bnode 20) (preverse (prelabel (bnode 26) perm12.symm)) 3 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 20) 3 = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 26) perm12.symm)

theorem base_cyclic21 : ¬Acyclic (base 21) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (bnode 21 0 3) 0 (by decide +kernel) (by decide +kernel))
  have h1 := hr 3 1 (pos (bnode 21 3 1) 0 (by decide +kernel) (by decide +kernel))
  have h2 := hr 1 0 (pos (bnode 21 1 0) 0 (by decide +kernel) (by decide +kernel))
  omega

theorem base_edge21_0 : SafeCore (mutate (base 21) 0) := by
  have he := mutation_equal (bnode 21) (preverse (prelabel (bnode 6) perm0.symm)) 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 21) 0 = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 6) perm0.symm)

theorem base_edge21_1 : SafeCore (mutate (base 21) 1) := by
  have he := mutation_equal (bnode 21) (prelabel (bnode 32) perm5.symm) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 21) 1 = _ from he]
  exact Safe.framed (base_safe 32) perm5.symm

theorem base_edge21_2 : SafeCore (mutate (base 21) 2) := by
  have he := mutation_equal (bnode 21) (prelabel (bnode 7) perm1.symm) 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 21) 2 = _ from he]
  exact Safe.framed (base_safe 7) perm1.symm

theorem base_edge21_3 : SafeCore (mutate (base 21) 3) := by
  have he := mutation_equal (bnode 21) (prelabel (bnode 25) perm21.symm) 3 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 21) 3 = _ from he]
  exact Safe.framed (base_safe 25) perm21.symm

theorem base_cyclic22 : ¬Acyclic (base 22) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (bnode 22 0 3) 0 (by decide +kernel) (by decide +kernel))
  have h1 := hr 3 1 (pos (bnode 22 3 1) 0 (by decide +kernel) (by decide +kernel))
  have h2 := hr 1 0 (pos (bnode 22 1 0) 0 (by decide +kernel) (by decide +kernel))
  omega

theorem base_edge22_0 : SafeCore (mutate (base 22) 0) := by
  have he := mutation_equal (bnode 22) (preverse (prelabel (root [4] [64] [7] [17] [2] [1]) perm4.symm)) 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (base_safe 22) 0
  rw [show mutate (base 22) 0 = _ from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [4] [64] [7] [17] [2] [1] 0 (by decide +kernel) (by decide +kernel)) perm4.symm)

theorem base_edge22_1 : SafeCore (mutate (base 22) 1) := by
  have he := mutation_equal (bnode 22) (prelabel (bnode 33) perm5.symm) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 22) 1 = _ from he]
  exact Safe.framed (base_safe 33) perm5.symm

theorem base_edge22_2 : SafeCore (mutate (base 22) 2) := by
  have he := mutation_equal (bnode 22) (preverse (prelabel (bnode 34) perm6.symm)) 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 22) 2 = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 34) perm6.symm)

theorem base_edge22_3 : SafeCore (mutate (base 22) 3) := by
  have he := mutation_equal (bnode 22) (preverse (prelabel (bnode 7) perm10.symm)) 3 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 22) 3 = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 7) perm10.symm)

theorem base_cyclic23 : ¬Acyclic (base 23) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (bnode 23 0 3) 0 (by decide +kernel) (by decide +kernel))
  have h1 := hr 3 1 (pos (bnode 23 3 1) 0 (by decide +kernel) (by decide +kernel))
  have h2 := hr 1 0 (pos (bnode 23 1 0) 0 (by decide +kernel) (by decide +kernel))
  omega

theorem base_edge23_0 : SafeCore (mutate (base 23) 0) := by
  have he := mutation_equal (bnode 23) (preverse (prelabel (root [2] [5] [11] [3] [8] [1]) perm5.symm)) 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (base_safe 23) 0
  rw [show mutate (base 23) 0 = _ from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [2] [5] [11] [3] [8] [1] 0 (by decide +kernel) (by decide +kernel)) perm5.symm)

theorem base_edge23_1 : SafeCore (mutate (base 23) 1) := by
  have he := mutation_equal (bnode 23) (preverse (prelabel (bnode 35) perm19.symm)) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 23) 1 = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 35) perm19.symm)

theorem base_edge23_2 : SafeCore (mutate (base 23) 2) := by
  have he := mutation_equal (bnode 23) (prelabel (bnode 36) perm1.symm) 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 23) 2 = _ from he]
  exact Safe.framed (base_safe 36) perm1.symm

theorem base_edge23_3 : SafeCore (mutate (base 23) 3) := by
  have he := mutation_equal (bnode 23) (preverse (prelabel (bnode 10) perm11.symm)) 3 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 23) 3 = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 10) perm11.symm)

theorem base_cyclic24 : ¬Acyclic (base 24) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (bnode 24 0 3) 0 (by decide +kernel) (by decide +kernel))
  have h1 := hr 3 1 (pos (bnode 24 3 1) 0 (by decide +kernel) (by decide +kernel))
  have h2 := hr 1 0 (pos (bnode 24 1 0) 0 (by decide +kernel) (by decide +kernel))
  omega

theorem base_edge24_0 : SafeCore (mutate (base 24) 0) := by
  have he := mutation_equal (bnode 24) (preverse (prelabel (root [2] [7] [7] [4] [5] [1]) perm5.symm)) 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (base_safe 24) 0
  rw [show mutate (base 24) 0 = _ from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [2] [7] [7] [4] [5] [1] 0 (by decide +kernel) (by decide +kernel)) perm5.symm)

theorem base_edge24_1 : SafeCore (mutate (base 24) 1) := by
  have he := mutation_equal (bnode 24) (preverse (prelabel (bnode 37) perm19.symm)) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 24) 1 = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 37) perm19.symm)

theorem base_edge24_2 : SafeCore (mutate (base 24) 2) := by
  have he := mutation_equal (bnode 24) (prelabel (bnode 38) perm1.symm) 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 24) 2 = _ from he]
  exact Safe.framed (base_safe 38) perm1.symm

theorem base_edge24_3 : SafeCore (mutate (base 24) 3) := by
  have he := mutation_equal (bnode 24) (preverse (prelabel (bnode 13) perm11.symm)) 3 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 24) 3 = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 13) perm11.symm)

theorem base_cyclic25 : ¬Acyclic (base 25) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (bnode 25 0 3) 0 (by decide +kernel) (by decide +kernel))
  have h1 := hr 3 2 (pos (bnode 25 3 2) 0 (by decide +kernel) (by decide +kernel))
  have h2 := hr 2 0 (pos (bnode 25 2 0) 0 (by decide +kernel) (by decide +kernel))
  omega

theorem base_edge25_0 : SafeCore (mutate (base 25) 0) := by
  have he := mutation_equal (bnode 25) (prelabel (bnode 21) perm21.symm) 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 25) 0 = _ from he]
  exact Safe.framed (base_safe 21) perm21.symm

theorem base_edge25_1 : SafeCore (mutate (base 25) 1) := by
  have he := mutation_equal (bnode 25) (preverse (prelabel (bnode 21) perm13.symm)) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 25) 1 = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 21) perm13.symm)

theorem base_edge25_2 : SafeCore (mutate (base 25) 2) := by
  have he := mutation_equal (bnode 25) (preverse (prelabel (bnode 14) perm6.symm)) 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 25) 2 = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 14) perm6.symm)

theorem base_edge25_3 : SafeCore (mutate (base 25) 3) := by
  have he := mutation_equal (bnode 25) (prelabel (bnode 14) perm1.symm) 3 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 25) 3 = _ from he]
  exact Safe.framed (base_safe 14) perm1.symm

theorem base_cyclic26 : ¬Acyclic (base 26) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 1 3 (pos (bnode 26 1 3) 0 (by decide +kernel) (by decide +kernel))
  have h1 := hr 3 2 (pos (bnode 26 3 2) 0 (by decide +kernel) (by decide +kernel))
  have h2 := hr 2 1 (pos (bnode 26 2 1) 0 (by decide +kernel) (by decide +kernel))
  omega

theorem base_edge26_0 : SafeCore (mutate (base 26) 0) := by
  have he := mutation_equal (bnode 26) (preverse (prelabel (bnode 26) perm1.symm)) 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 26) 0 = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 26) perm1.symm)

theorem base_edge26_1 : SafeCore (mutate (base 26) 1) := by
  have he := mutation_equal (bnode 26) (preverse (prelabel (bnode 19) perm16.symm)) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 26) 1 = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 19) perm16.symm)

theorem base_edge26_2 : SafeCore (mutate (base 26) 2) := by
  have he := mutation_equal (bnode 26) (preverse (prelabel (bnode 15) perm10.symm)) 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 26) 2 = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 15) perm10.symm)

theorem base_edge26_3 : SafeCore (mutate (base 26) 3) := by
  have he := mutation_equal (bnode 26) (preverse (prelabel (bnode 20) perm8.symm)) 3 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 26) 3 = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 20) perm8.symm)

theorem base_cyclic27 : ¬Acyclic (base 27) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (bnode 27 0 3) 0 (by decide +kernel) (by decide +kernel))
  have h1 := hr 3 2 (pos (bnode 27 3 2) 0 (by decide +kernel) (by decide +kernel))
  have h2 := hr 2 0 (pos (bnode 27 2 0) 0 (by decide +kernel) (by decide +kernel))
  omega

theorem base_edge27_0 : SafeCore (mutate (base 27) 0) := by
  have he := mutation_equal (bnode 27) (preverse (prelabel (bnode 17) perm0.symm)) 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 27) 0 = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 17) perm0.symm)

theorem base_edge27_1 : SafeCore (mutate (base 27) 1) := by
  have he := mutation_equal (bnode 27) (prelabel (bnode 16) perm0.symm) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 27) 1 = _ from he]
  exact Safe.framed (base_safe 16) perm0.symm

theorem base_edge27_2 : SafeCore (mutate (base 27) 2) := by
  have he := mutation_equal (bnode 27) (prelabel (bnode 39) perm4.symm) 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 27) 2 = _ from he]
  exact Safe.framed (base_safe 39) perm4.symm

theorem base_edge27_3 : SafeCore (mutate (base 27) 3) := by
  have he := mutation_equal (bnode 27) (prelabel (root [3] [6] [29] [2] [11] [1]) perm18.symm) 3 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (base_safe 27) 3
  rw [show mutate (base 27) 3 = _ from he]
  exact IsRoot.relabelled (root_sound [3] [6] [29] [2] [11] [1] 0 (by decide +kernel) (by decide +kernel)) perm18.symm

theorem base_cyclic28 : ¬Acyclic (base 28) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (bnode 28 0 3) 0 (by decide +kernel) (by decide +kernel))
  have h1 := hr 3 2 (pos (bnode 28 3 2) 0 (by decide +kernel) (by decide +kernel))
  have h2 := hr 2 0 (pos (bnode 28 2 0) 0 (by decide +kernel) (by decide +kernel))
  omega

theorem base_edge28_0 : SafeCore (mutate (base 28) 0) := by
  have he := mutation_equal (bnode 28) (prelabel (zero param4_0 param4_1 param4_2 param4_3 0) perm6.symm) 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 28) 0 = _ from he]
  exact Safe.framed (region4_safe 0) perm6.symm

theorem base_edge28_1 : SafeCore (mutate (base 28) 1) := by
  have he := mutation_equal (bnode 28) (prelabel (bnode 40) perm0.symm) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 28) 1 = _ from he]
  exact Safe.framed (base_safe 40) perm0.symm

theorem base_edge28_2 : SafeCore (mutate (base 28) 2) := by
  have he := mutation_equal (bnode 28) (prelabel (root [13] [633] [142] [49] [11] []) perm16.symm) 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (base_safe 28) 2
  rw [show mutate (base 28) 2 = _ from he]
  exact IsRoot.relabelled (root_sound [13] [633] [142] [49] [11] [] 0 (by decide +kernel) (by decide +kernel)) perm16.symm

theorem base_edge28_3 : SafeCore (mutate (base 28) 3) := by
  have he := mutation_equal (bnode 28) (prelabel (bnode 16) perm1.symm) 3 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 28) 3 = _ from he]
  exact Safe.framed (base_safe 16) perm1.symm

theorem base_cyclic29 : ¬Acyclic (base 29) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (bnode 29 0 3) 0 (by decide +kernel) (by decide +kernel))
  have h1 := hr 3 1 (pos (bnode 29 3 1) 0 (by decide +kernel) (by decide +kernel))
  have h2 := hr 1 0 (pos (bnode 29 1 0) 0 (by decide +kernel) (by decide +kernel))
  omega

theorem base_edge29_0 : SafeCore (mutate (base 29) 0) := by
  have he := mutation_equal (bnode 29) (prelabel (fork [4] [3] [9] [11] [34] [2]) perm5.symm) 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (base_safe 29)
  rw [show mutate (base 29) 0 = _ from he]
  exact IsFork.relabelled (fork_sound [4] [3] [9] [11] [34] [2] 0 (by decide +kernel) (by decide +kernel)) perm5.symm

theorem base_edge29_1 : SafeCore (mutate (base 29) 1) := by
  have he := mutation_equal (bnode 29) (preverse (prelabel (root [9] [21] [14] [2] [2] [1]) perm6.symm)) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (base_safe 29) 1
  rw [show mutate (base 29) 1 = _ from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [9] [21] [14] [2] [2] [1] 0 (by decide +kernel) (by decide +kernel)) perm6.symm)

theorem base_edge29_2 : SafeCore (mutate (base 29) 2) := by
  have he := mutation_equal (bnode 29) (preverse (prelabel (bnode 38) perm6.symm)) 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 29) 2 = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 38) perm6.symm)

theorem base_edge29_3 : SafeCore (mutate (base 29) 3) := by
  have he := mutation_equal (bnode 29) (prelabel (bnode 18) perm4.symm) 3 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 29) 3 = _ from he]
  exact Safe.framed (base_safe 18) perm4.symm

theorem base_cyclic30 : ¬Acyclic (base 30) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (bnode 30 0 3) 0 (by decide +kernel) (by decide +kernel))
  have h1 := hr 3 2 (pos (bnode 30 3 2) 0 (by decide +kernel) (by decide +kernel))
  have h2 := hr 2 0 (pos (bnode 30 2 0) 0 (by decide +kernel) (by decide +kernel))
  omega

theorem base_edge30_0 : SafeCore (mutate (base 30) 0) := by
  have he := mutation_equal (bnode 30) (preverse (prelabel (bnode 20) perm0.symm)) 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 30) 0 = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 20) perm0.symm)

theorem base_edge30_1 : SafeCore (mutate (base 30) 1) := by
  have he := mutation_equal (bnode 30) (prelabel (bnode 19) perm0.symm) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 30) 1 = _ from he]
  exact Safe.framed (base_safe 19) perm0.symm

theorem base_edge30_2 : SafeCore (mutate (base 30) 2) := by
  have he := mutation_equal (bnode 30) (prelabel (bnode 41) perm4.symm) 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 30) 2 = _ from he]
  exact Safe.framed (base_safe 41) perm4.symm

theorem base_edge30_3 : SafeCore (mutate (base 30) 3) := by
  have he := mutation_equal (bnode 30) (preverse (prelabel (bnode 30) perm6.symm)) 3 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 30) 3 = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 30) perm6.symm)

theorem base_cyclic31 : ¬Acyclic (base 31) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (bnode 31 0 3) 0 (by decide +kernel) (by decide +kernel))
  have h1 := hr 3 2 (pos (bnode 31 3 2) 0 (by decide +kernel) (by decide +kernel))
  have h2 := hr 2 0 (pos (bnode 31 2 0) 0 (by decide +kernel) (by decide +kernel))
  omega

theorem base_edge31_0 : SafeCore (mutate (base 31) 0) := by
  have he := mutation_equal (bnode 31) (prelabel (zero param5_0 param5_1 param5_2 param5_3 0) perm6.symm) 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 31) 0 = _ from he]
  exact Safe.framed (region5_safe 0) perm6.symm

theorem base_edge31_1 : SafeCore (mutate (base 31) 1) := by
  have he := mutation_equal (bnode 31) (prelabel (bnode 42) perm0.symm) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 31) 1 = _ from he]
  exact Safe.framed (base_safe 42) perm0.symm

theorem base_edge31_2 : SafeCore (mutate (base 31) 2) := by
  have he := mutation_equal (bnode 31) (prelabel (root [3] [29] [11] [11] [4] []) perm16.symm) 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (base_safe 31) 2
  rw [show mutate (base 31) 2 = _ from he]
  exact IsRoot.relabelled (root_sound [3] [29] [11] [11] [4] [] 0 (by decide +kernel) (by decide +kernel)) perm16.symm

theorem base_edge31_3 : SafeCore (mutate (base 31) 3) := by
  have he := mutation_equal (bnode 31) (prelabel (bnode 19) perm1.symm) 3 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 31) 3 = _ from he]
  exact Safe.framed (base_safe 19) perm1.symm

theorem base_cyclic32 : ¬Acyclic (base 32) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (bnode 32 0 3) 0 (by decide +kernel) (by decide +kernel))
  have h1 := hr 3 1 (pos (bnode 32 3 1) 0 (by decide +kernel) (by decide +kernel))
  have h2 := hr 1 0 (pos (bnode 32 1 0) 0 (by decide +kernel) (by decide +kernel))
  omega

theorem base_edge32_0 : SafeCore (mutate (base 32) 0) := by
  have he := mutation_equal (bnode 32) (prelabel (fork [4] [7] [5] [26] [19] [2]) perm4.symm) 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (base_safe 32)
  rw [show mutate (base 32) 0 = _ from he]
  exact IsFork.relabelled (fork_sound [4] [7] [5] [26] [19] [2] 0 (by decide +kernel) (by decide +kernel)) perm4.symm

theorem base_edge32_1 : SafeCore (mutate (base 32) 1) := by
  have he := mutation_equal (bnode 32) (preverse (prelabel (fork [2] [7] [2] [10] [5] [5]) perm10.symm)) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (base_safe 32)
  rw [show mutate (base 32) 1 = _ from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [2] [7] [2] [10] [5] [5] 0 (by decide +kernel) (by decide +kernel)) perm10.symm)

theorem base_edge32_2 : SafeCore (mutate (base 32) 2) := by
  have he := mutation_equal (bnode 32) (prelabel (bnode 34) perm1.symm) 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 32) 2 = _ from he]
  exact Safe.framed (base_safe 34) perm1.symm

theorem base_edge32_3 : SafeCore (mutate (base 32) 3) := by
  have he := mutation_equal (bnode 32) (prelabel (bnode 21) perm5.symm) 3 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 32) 3 = _ from he]
  exact Safe.framed (base_safe 21) perm5.symm

theorem base_cyclic33 : ¬Acyclic (base 33) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (bnode 33 0 3) 0 (by decide +kernel) (by decide +kernel))
  have h1 := hr 3 1 (pos (bnode 33 3 1) 0 (by decide +kernel) (by decide +kernel))
  have h2 := hr 1 0 (pos (bnode 33 1 0) 0 (by decide +kernel) (by decide +kernel))
  omega

theorem base_edge33_0 : SafeCore (mutate (base 33) 0) := by
  have he := mutation_equal (bnode 33) (preverse (prelabel (root [17] [322] [1084] [19] [64] [1]) perm5.symm)) 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (base_safe 33) 0
  rw [show mutate (base 33) 0 = _ from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [17] [322] [1084] [19] [64] [1] 0 (by decide +kernel) (by decide +kernel)) perm5.symm)

theorem base_edge33_1 : SafeCore (mutate (base 33) 1) := by
  have he := mutation_equal (bnode 33) (prelabel (bnode 43) perm5.symm) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 33) 1 = _ from he]
  exact Safe.framed (base_safe 43) perm5.symm

theorem base_edge33_2 : SafeCore (mutate (base 33) 2) := by
  have he := mutation_equal (bnode 33) (prelabel (bnode 44) perm1.symm) 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 33) 2 = _ from he]
  exact Safe.framed (base_safe 44) perm1.symm

theorem base_edge33_3 : SafeCore (mutate (base 33) 3) := by
  have he := mutation_equal (bnode 33) (prelabel (bnode 22) perm5.symm) 3 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 33) 3 = _ from he]
  exact Safe.framed (base_safe 22) perm5.symm

theorem base_cyclic34 : ¬Acyclic (base 34) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (bnode 34 0 3) 0 (by decide +kernel) (by decide +kernel))
  have h1 := hr 3 1 (pos (bnode 34 3 1) 0 (by decide +kernel) (by decide +kernel))
  have h2 := hr 1 0 (pos (bnode 34 1 0) 0 (by decide +kernel) (by decide +kernel))
  omega

theorem base_edge34_0 : SafeCore (mutate (base 34) 0) := by
  have he := mutation_equal (bnode 34) (prelabel (bnode 45) perm21.symm) 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 34) 0 = _ from he]
  exact Safe.framed (base_safe 45) perm21.symm

theorem base_edge34_1 : SafeCore (mutate (base 34) 1) := by
  have he := mutation_equal (bnode 34) (preverse (prelabel (root [17] [35] [29] [2] [2] [1]) perm6.symm)) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (base_safe 34) 1
  rw [show mutate (base 34) 1 = _ from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [17] [35] [29] [2] [2] [1] 0 (by decide +kernel) (by decide +kernel)) perm6.symm)

theorem base_edge34_2 : SafeCore (mutate (base 34) 2) := by
  have he := mutation_equal (bnode 34) (preverse (prelabel (bnode 22) perm6.symm)) 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 34) 2 = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 22) perm6.symm)

theorem base_edge34_3 : SafeCore (mutate (base 34) 3) := by
  have he := mutation_equal (bnode 34) (prelabel (bnode 32) perm1.symm) 3 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 34) 3 = _ from he]
  exact Safe.framed (base_safe 32) perm1.symm

theorem base_cyclic35 : ¬Acyclic (base 35) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (bnode 35 0 3) 0 (by decide +kernel) (by decide +kernel))
  have h1 := hr 3 1 (pos (bnode 35 3 1) 0 (by decide +kernel) (by decide +kernel))
  have h2 := hr 1 0 (pos (bnode 35 1 0) 0 (by decide +kernel) (by decide +kernel))
  omega

theorem base_edge35_0 : SafeCore (mutate (base 35) 0) := by
  have he := mutation_equal (bnode 35) (prelabel (fork [5] [38] [6] [182] [29] [3]) perm4.symm) 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (base_safe 35)
  rw [show mutate (base 35) 0 = _ from he]
  exact IsFork.relabelled (fork_sound [5] [38] [6] [182] [29] [3] 0 (by decide +kernel) (by decide +kernel)) perm4.symm

theorem base_edge35_1 : SafeCore (mutate (base 35) 1) := by
  have he := mutation_equal (bnode 35) (preverse (prelabel (fork [8] [38] [3] [299] [25] [6]) perm10.symm)) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (base_safe 35)
  rw [show mutate (base 35) 1 = _ from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [8] [38] [3] [299] [25] [6] 0 (by decide +kernel) (by decide +kernel)) perm10.symm)

theorem base_edge35_2 : SafeCore (mutate (base 35) 2) := by
  have he := mutation_equal (bnode 35) (prelabel (bnode 46) perm1.symm) 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 35) 2 = _ from he]
  exact Safe.framed (base_safe 46) perm1.symm

theorem base_edge35_3 : SafeCore (mutate (base 35) 3) := by
  have he := mutation_equal (bnode 35) (preverse (prelabel (bnode 23) perm11.symm)) 3 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 35) 3 = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 23) perm11.symm)

theorem base_cyclic36 : ¬Acyclic (base 36) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (bnode 36 0 3) 0 (by decide +kernel) (by decide +kernel))
  have h1 := hr 3 1 (pos (bnode 36 3 1) 0 (by decide +kernel) (by decide +kernel))
  have h2 := hr 1 0 (pos (bnode 36 1 0) 0 (by decide +kernel) (by decide +kernel))
  omega

theorem base_edge36_0 : SafeCore (mutate (base 36) 0) := by
  have he := mutation_equal (bnode 36) (prelabel (bnode 47) perm21.symm) 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 36) 0 = _ from he]
  exact Safe.framed (base_safe 47) perm21.symm

theorem base_edge36_1 : SafeCore (mutate (base 36) 1) := by
  have he := mutation_equal (bnode 36) (prelabel (generic param6_0 param6_1 param6_2 param6_3 0) perm17.symm) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 36) 1 = _ from he]
  exact Safe.framed (region6_safe 0) perm17.symm

theorem base_edge36_2 : SafeCore (mutate (base 36) 2) := by
  have he := mutation_equal (bnode 36) (preverse (prelabel (generic param7_0 param7_1 param7_2 param7_3 0) perm3.symm)) 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 36) 2 = _ from he]
  exact Safe.reversed (Safe.framed (region7_safe 0) perm3.symm)

theorem base_edge36_3 : SafeCore (mutate (base 36) 3) := by
  have he := mutation_equal (bnode 36) (prelabel (bnode 23) perm1.symm) 3 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 36) 3 = _ from he]
  exact Safe.framed (base_safe 23) perm1.symm

theorem base_cyclic37 : ¬Acyclic (base 37) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (bnode 37 0 3) 0 (by decide +kernel) (by decide +kernel))
  have h1 := hr 3 1 (pos (bnode 37 3 1) 0 (by decide +kernel) (by decide +kernel))
  have h2 := hr 1 0 (pos (bnode 37 1 0) 0 (by decide +kernel) (by decide +kernel))
  omega

theorem base_edge37_0 : SafeCore (mutate (base 37) 0) := by
  have he := mutation_equal (bnode 37) (prelabel (fork [3] [13] [4] [34] [11] [4]) perm4.symm) 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (base_safe 37)
  rw [show mutate (base 37) 0 = _ from he]
  exact IsFork.relabelled (fork_sound [3] [13] [4] [34] [11] [4] 0 (by decide +kernel) (by decide +kernel)) perm4.symm

theorem base_edge37_1 : SafeCore (mutate (base 37) 1) := by
  have he := mutation_equal (bnode 37) (preverse (prelabel (fork [5] [13] [4] [62] [21] [4]) perm10.symm)) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (base_safe 37)
  rw [show mutate (base 37) 1 = _ from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [5] [13] [4] [62] [21] [4] 0 (by decide +kernel) (by decide +kernel)) perm10.symm)

theorem base_edge37_2 : SafeCore (mutate (base 37) 2) := by
  have he := mutation_equal (bnode 37) (prelabel (bnode 49) perm1.symm) 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 37) 2 = _ from he]
  exact Safe.framed (base_safe 49) perm1.symm

theorem base_edge37_3 : SafeCore (mutate (base 37) 3) := by
  have he := mutation_equal (bnode 37) (preverse (prelabel (bnode 24) perm11.symm)) 3 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 37) 3 = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 24) perm11.symm)

theorem base_cyclic38 : ¬Acyclic (base 38) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (bnode 38 0 3) 0 (by decide +kernel) (by decide +kernel))
  have h1 := hr 3 1 (pos (bnode 38 3 1) 0 (by decide +kernel) (by decide +kernel))
  have h2 := hr 1 0 (pos (bnode 38 1 0) 0 (by decide +kernel) (by decide +kernel))
  omega

theorem base_edge38_0 : SafeCore (mutate (base 38) 0) := by
  have he := mutation_equal (bnode 38) (prelabel (fork [4] [2] [9] [7] [35] [3]) perm5.symm) 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (base_safe 38)
  rw [show mutate (base 38) 0 = _ from he]
  exact IsFork.relabelled (fork_sound [4] [2] [9] [7] [35] [3] 0 (by decide +kernel) (by decide +kernel)) perm5.symm

theorem base_edge38_1 : SafeCore (mutate (base 38) 1) := by
  have he := mutation_equal (bnode 38) (prelabel (generic param8_0 param8_1 param8_2 param8_3 0) perm17.symm) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 38) 1 = _ from he]
  exact Safe.framed (region8_safe 0) perm17.symm

theorem base_edge38_2 : SafeCore (mutate (base 38) 2) := by
  have he := mutation_equal (bnode 38) (preverse (prelabel (bnode 29) perm6.symm)) 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 38) 2 = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 29) perm6.symm)

theorem base_edge38_3 : SafeCore (mutate (base 38) 3) := by
  have he := mutation_equal (bnode 38) (prelabel (bnode 24) perm1.symm) 3 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 38) 3 = _ from he]
  exact Safe.framed (base_safe 24) perm1.symm

theorem base_cyclic39 : ¬Acyclic (base 39) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (bnode 39 0 3) 0 (by decide +kernel) (by decide +kernel))
  have h1 := hr 3 1 (pos (bnode 39 3 1) 0 (by decide +kernel) (by decide +kernel))
  have h2 := hr 1 0 (pos (bnode 39 1 0) 0 (by decide +kernel) (by decide +kernel))
  omega

theorem base_edge39_0 : SafeCore (mutate (base 39) 0) := by
  have he := mutation_equal (bnode 39) (prelabel (fork [4] [41] [4] [153] [15] [2]) perm4.symm) 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (base_safe 39)
  rw [show mutate (base 39) 0 = _ from he]
  exact IsFork.relabelled (fork_sound [4] [41] [4] [153] [15] [2] 0 (by decide +kernel) (by decide +kernel)) perm4.symm

theorem base_edge39_1 : SafeCore (mutate (base 39) 1) := by
  have he := mutation_equal (bnode 39) (preverse (prelabel (fork [11] [41] [2] [447] [23] [4]) perm10.symm)) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (base_safe 39)
  rw [show mutate (base 39) 1 = _ from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [11] [41] [2] [447] [23] [4] 0 (by decide +kernel) (by decide +kernel)) perm10.symm)

theorem base_edge39_2 : SafeCore (mutate (base 39) 2) := by
  have he := mutation_equal (bnode 39) (prelabel (bnode 40) perm4.symm) 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 39) 2 = _ from he]
  exact Safe.framed (base_safe 40) perm4.symm

theorem base_edge39_3 : SafeCore (mutate (base 39) 3) := by
  have he := mutation_equal (bnode 39) (prelabel (bnode 27) perm3.symm) 3 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 39) 3 = _ from he]
  exact Safe.framed (base_safe 27) perm3.symm

theorem base_cyclic40 : ¬Acyclic (base 40) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (bnode 40 0 3) 0 (by decide +kernel) (by decide +kernel))
  have h1 := hr 3 2 (pos (bnode 40 3 2) 0 (by decide +kernel) (by decide +kernel))
  have h2 := hr 2 0 (pos (bnode 40 2 0) 0 (by decide +kernel) (by decide +kernel))
  omega

theorem base_edge40_0 : SafeCore (mutate (base 40) 0) := by
  have he := mutation_equal (bnode 40) (prelabel (zero param4_0 param4_1 param4_2 param4_3 1) perm6.symm) 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 40) 0 = _ from he]
  exact Safe.framed (region4_safe 1) perm6.symm

theorem base_edge40_1 : SafeCore (mutate (base 40) 1) := by
  have he := mutation_equal (bnode 40) (prelabel (bnode 28) perm0.symm) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 40) 1 = _ from he]
  exact Safe.framed (base_safe 28) perm0.symm

theorem base_edge40_2 : SafeCore (mutate (base 40) 2) := by
  have he := mutation_equal (bnode 40) (preverse (prelabel (root [49] [539] [94] [11] [2] [1]) perm12.symm)) 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (base_safe 40) 2
  rw [show mutate (base 40) 2 = _ from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [49] [539] [94] [11] [2] [1] 0 (by decide +kernel) (by decide +kernel)) perm12.symm)

theorem base_edge40_3 : SafeCore (mutate (base 40) 3) := by
  have he := mutation_equal (bnode 40) (prelabel (bnode 39) perm3.symm) 3 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 40) 3 = _ from he]
  exact Safe.framed (base_safe 39) perm3.symm

theorem base_cyclic41 : ¬Acyclic (base 41) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (bnode 41 0 3) 0 (by decide +kernel) (by decide +kernel))
  have h1 := hr 3 1 (pos (bnode 41 3 1) 0 (by decide +kernel) (by decide +kernel))
  have h2 := hr 1 0 (pos (bnode 41 1 0) 0 (by decide +kernel) (by decide +kernel))
  omega

theorem base_edge41_0 : SafeCore (mutate (base 41) 0) := by
  have he := mutation_equal (bnode 41) (preverse (prelabel (root [4] [41] [15] [11] [4] [1]) perm4.symm)) 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (base_safe 41) 0
  rw [show mutate (base 41) 0 = _ from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [4] [41] [15] [11] [4] [1] 0 (by decide +kernel) (by decide +kernel)) perm4.symm)

theorem base_edge41_1 : SafeCore (mutate (base 41) 1) := by
  have he := mutation_equal (bnode 41) (prelabel (bnode 51) perm5.symm) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 41) 1 = _ from he]
  exact Safe.framed (base_safe 51) perm5.symm

theorem base_edge41_2 : SafeCore (mutate (base 41) 2) := by
  have he := mutation_equal (bnode 41) (prelabel (bnode 42) perm4.symm) 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 41) 2 = _ from he]
  exact Safe.framed (base_safe 42) perm4.symm

theorem base_edge41_3 : SafeCore (mutate (base 41) 3) := by
  have he := mutation_equal (bnode 41) (prelabel (bnode 30) perm3.symm) 3 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 41) 3 = _ from he]
  exact Safe.framed (base_safe 30) perm3.symm

theorem base_cyclic42 : ¬Acyclic (base 42) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 1 2 (pos (bnode 42 1 2) 0 (by decide +kernel) (by decide +kernel))
  have h1 := hr 2 3 (pos (bnode 42 2 3) 0 (by decide +kernel) (by decide +kernel))
  have h2 := hr 3 1 (pos (bnode 42 3 1) 0 (by decide +kernel) (by decide +kernel))
  omega

theorem base_edge42_0 : SafeCore (mutate (base 42) 0) := by
  have he := mutation_equal (bnode 42) (prelabel (zero param5_0 param5_1 param5_2 param5_3 1) perm6.symm) 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 42) 0 = _ from he]
  exact Safe.framed (region5_safe 1) perm6.symm

theorem base_edge42_1 : SafeCore (mutate (base 42) 1) := by
  have he := mutation_equal (bnode 42) (prelabel (bnode 31) perm0.symm) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 42) 1 = _ from he]
  exact Safe.framed (base_safe 31) perm0.symm

theorem base_edge42_2 : SafeCore (mutate (base 42) 2) := by
  have he := mutation_equal (bnode 42) (preverse (prelabel (bnode 52) perm7.symm)) 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 42) 2 = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 52) perm7.symm)

theorem base_edge42_3 : SafeCore (mutate (base 42) 3) := by
  have he := mutation_equal (bnode 42) (prelabel (bnode 41) perm3.symm) 3 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 42) 3 = _ from he]
  exact Safe.framed (base_safe 41) perm3.symm

theorem base_cyclic43 : ¬Acyclic (base 43) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (bnode 43 0 3) 0 (by decide +kernel) (by decide +kernel))
  have h1 := hr 3 1 (pos (bnode 43 3 1) 0 (by decide +kernel) (by decide +kernel))
  have h2 := hr 1 0 (pos (bnode 43 1 0) 0 (by decide +kernel) (by decide +kernel))
  omega

theorem base_edge43_0 : SafeCore (mutate (base 43) 0) := by
  have he := mutation_equal (bnode 43) (prelabel (fork [64] [239] [19] [15292] [1217] [5]) perm4.symm) 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (base_safe 43)
  rw [show mutate (base 43) 0 = _ from he]
  exact IsFork.relabelled (fork_sound [64] [239] [19] [15292] [1217] [5] 0 (by decide +kernel) (by decide +kernel)) perm4.symm

theorem base_edge43_1 : SafeCore (mutate (base 43) 1) := by
  have he := mutation_equal (bnode 43) (preverse (prelabel (fork [4] [239] [5] [892] [19] [19]) perm10.symm)) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (base_safe 43)
  rw [show mutate (base 43) 1 = _ from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [4] [239] [5] [892] [19] [19] 0 (by decide +kernel) (by decide +kernel)) perm10.symm)

theorem base_edge43_2 : SafeCore (mutate (base 43) 2) := by
  have he := mutation_equal (bnode 43) (preverse (prelabel (bnode 53) perm7.symm)) 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 43) 2 = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 53) perm7.symm)

theorem base_edge43_3 : SafeCore (mutate (base 43) 3) := by
  have he := mutation_equal (bnode 43) (prelabel (bnode 33) perm5.symm) 3 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 43) 3 = _ from he]
  exact Safe.framed (base_safe 33) perm5.symm

theorem base_cyclic44 : ¬Acyclic (base 44) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (bnode 44 0 3) 0 (by decide +kernel) (by decide +kernel))
  have h1 := hr 3 1 (pos (bnode 44 3 1) 0 (by decide +kernel) (by decide +kernel))
  have h2 := hr 1 0 (pos (bnode 44 1 0) 0 (by decide +kernel) (by decide +kernel))
  omega

theorem base_edge44_0 : SafeCore (mutate (base 44) 0) := by
  have he := mutation_equal (bnode 44) (prelabel (fork [19] [2] [83] [37] [1576] [4]) perm5.symm) 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (base_safe 44)
  rw [show mutate (base 44) 0 = _ from he]
  exact IsFork.relabelled (fork_sound [19] [2] [83] [37] [1576] [4] 0 (by decide +kernel) (by decide +kernel)) perm5.symm

theorem base_edge44_1 : SafeCore (mutate (base 44) 1) := by
  have he := mutation_equal (bnode 44) (prelabel (generic param9_0 param9_1 param9_2 param9_3 0) perm17.symm) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 44) 1 = _ from he]
  exact Safe.framed (region9_safe 0) perm17.symm

theorem base_edge44_2 : SafeCore (mutate (base 44) 2) := by
  have he := mutation_equal (bnode 44) (preverse (prelabel (bnode 45) perm6.symm)) 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 44) 2 = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 45) perm6.symm)

theorem base_edge44_3 : SafeCore (mutate (base 44) 3) := by
  have he := mutation_equal (bnode 44) (prelabel (bnode 33) perm1.symm) 3 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 44) 3 = _ from he]
  exact Safe.framed (base_safe 33) perm1.symm

theorem base_cyclic45 : ¬Acyclic (base 45) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (bnode 45 0 3) 0 (by decide +kernel) (by decide +kernel))
  have h1 := hr 3 1 (pos (bnode 45 3 1) 0 (by decide +kernel) (by decide +kernel))
  have h2 := hr 1 0 (pos (bnode 45 1 0) 0 (by decide +kernel) (by decide +kernel))
  omega

theorem base_edge45_0 : SafeCore (mutate (base 45) 0) := by
  have he := mutation_equal (bnode 45) (prelabel (fork [5] [4] [83] [19] [398] [2]) perm5.symm) 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (base_safe 45)
  rw [show mutate (base 45) 0 = _ from he]
  exact IsFork.relabelled (fork_sound [5] [4] [83] [19] [398] [2] 0 (by decide +kernel) (by decide +kernel)) perm5.symm

theorem base_edge45_1 : SafeCore (mutate (base 45) 1) := by
  have he := mutation_equal (bnode 45) (preverse (prelabel (root [83] [170] [1406] [2] [17] [1]) perm6.symm)) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (base_safe 45) 1
  rw [show mutate (base 45) 1 = _ from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [83] [170] [1406] [2] [17] [1] 0 (by decide +kernel) (by decide +kernel)) perm6.symm)

theorem base_edge45_2 : SafeCore (mutate (base 45) 2) := by
  have he := mutation_equal (bnode 45) (preverse (prelabel (bnode 44) perm6.symm)) 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 45) 2 = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 44) perm6.symm)

theorem base_edge45_3 : SafeCore (mutate (base 45) 3) := by
  have he := mutation_equal (bnode 45) (prelabel (bnode 34) perm21.symm) 3 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 45) 3 = _ from he]
  exact Safe.framed (base_safe 34) perm21.symm

theorem base_cyclic46 : ¬Acyclic (base 46) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (bnode 46 0 3) 0 (by decide +kernel) (by decide +kernel))
  have h1 := hr 3 1 (pos (bnode 46 3 1) 0 (by decide +kernel) (by decide +kernel))
  have h2 := hr 1 0 (pos (bnode 46 1 0) 0 (by decide +kernel) (by decide +kernel))
  omega

theorem base_edge46_0 : SafeCore (mutate (base 46) 0) := by
  have he := mutation_equal (bnode 46) (prelabel (bnode 48) perm21.symm) 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 46) 0 = _ from he]
  exact Safe.framed (base_safe 48) perm21.symm

theorem base_edge46_1 : SafeCore (mutate (base 46) 1) := by
  have he := mutation_equal (bnode 46) (preverse (prelabel (root [56] [449] [162] [8] [3] [1]) perm6.symm)) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (base_safe 46) 1
  rw [show mutate (base 46) 1 = _ from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [56] [449] [162] [8] [3] [1] 0 (by decide +kernel) (by decide +kernel)) perm6.symm)

theorem base_edge46_2 : SafeCore (mutate (base 46) 2) := by
  have he := mutation_equal (bnode 46) (preverse (prelabel (generic param6_0 param6_1 param6_2 param6_3 0) perm3.symm)) 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 46) 2 = _ from he]
  exact Safe.reversed (Safe.framed (region6_safe 0) perm3.symm)

theorem base_edge46_3 : SafeCore (mutate (base 46) 3) := by
  have he := mutation_equal (bnode 46) (prelabel (bnode 35) perm1.symm) 3 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 46) 3 = _ from he]
  exact Safe.framed (base_safe 35) perm1.symm

theorem base_cyclic47 : ¬Acyclic (base 47) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (bnode 47 0 3) 0 (by decide +kernel) (by decide +kernel))
  have h1 := hr 3 1 (pos (bnode 47 3 1) 0 (by decide +kernel) (by decide +kernel))
  have h2 := hr 1 0 (pos (bnode 47 1 0) 0 (by decide +kernel) (by decide +kernel))
  omega

theorem base_edge47_0 : SafeCore (mutate (base 47) 0) := by
  have he := mutation_equal (bnode 47) (prelabel (fork [3] [2] [32] [5] [85] [5]) perm5.symm) 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (base_safe 47)
  rw [show mutate (base 47) 0 = _ from he]
  exact IsFork.relabelled (fork_sound [3] [2] [32] [5] [85] [5] 0 (by decide +kernel) (by decide +kernel)) perm5.symm

theorem base_edge47_1 : SafeCore (mutate (base 47) 1) := by
  have he := mutation_equal (bnode 47) (preverse (prelabel (root [32] [162] [349] [5] [11] [1]) perm6.symm)) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (base_safe 47) 1
  rw [show mutate (base 47) 1 = _ from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [32] [162] [349] [5] [11] [1] 0 (by decide +kernel) (by decide +kernel)) perm6.symm)

theorem base_edge47_2 : SafeCore (mutate (base 47) 2) := by
  have he := mutation_equal (bnode 47) (preverse (prelabel (generic param7_0 param7_1 param7_2 param7_3 2) perm16.symm)) 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 47) 2 = _ from he]
  exact Safe.reversed (Safe.framed (region7_safe 2) perm16.symm)

theorem base_edge47_3 : SafeCore (mutate (base 47) 3) := by
  have he := mutation_equal (bnode 47) (prelabel (bnode 36) perm21.symm) 3 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 47) 3 = _ from he]
  exact Safe.framed (base_safe 36) perm21.symm

theorem base_cyclic48 : ¬Acyclic (base 48) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (bnode 48 0 3) 0 (by decide +kernel) (by decide +kernel))
  have h1 := hr 3 1 (pos (bnode 48 3 1) 0 (by decide +kernel) (by decide +kernel))
  have h2 := hr 1 0 (pos (bnode 48 1 0) 0 (by decide +kernel) (by decide +kernel))
  omega

theorem base_edge48_0 : SafeCore (mutate (base 48) 0) := by
  have he := mutation_equal (bnode 48) (prelabel (fork [6] [5] [333] [29] [1942] [8]) perm5.symm) 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (base_safe 48)
  rw [show mutate (base 48) 0 = _ from he]
  exact IsFork.relabelled (fork_sound [6] [5] [333] [29] [1942] [8] 0 (by decide +kernel) (by decide +kernel)) perm5.symm

theorem base_edge48_1 : SafeCore (mutate (base 48) 1) := by
  have he := mutation_equal (bnode 48) (preverse (prelabel (root [333] [2669] [18642] [8] [56] [1]) perm6.symm)) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (base_safe 48) 1
  rw [show mutate (base 48) 1 = _ from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [333] [2669] [18642] [8] [56] [1] 0 (by decide +kernel) (by decide +kernel)) perm6.symm)

theorem base_edge48_2 : SafeCore (mutate (base 48) 2) := by
  have he := mutation_equal (bnode 48) (preverse (prelabel (generic param6_0 param6_1 param6_2 param6_3 2) perm16.symm)) 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 48) 2 = _ from he]
  exact Safe.reversed (Safe.framed (region6_safe 2) perm16.symm)

theorem base_edge48_3 : SafeCore (mutate (base 48) 3) := by
  have he := mutation_equal (bnode 48) (prelabel (bnode 46) perm21.symm) 3 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 48) 3 = _ from he]
  exact Safe.framed (base_safe 46) perm21.symm

theorem base_cyclic49 : ¬Acyclic (base 49) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (bnode 49 0 3) 0 (by decide +kernel) (by decide +kernel))
  have h1 := hr 3 1 (pos (bnode 49 3 1) 0 (by decide +kernel) (by decide +kernel))
  have h2 := hr 1 0 (pos (bnode 49 1 0) 0 (by decide +kernel) (by decide +kernel))
  omega

theorem base_edge49_0 : SafeCore (mutate (base 49) 0) := by
  have he := mutation_equal (bnode 49) (prelabel (bnode 50) perm21.symm) 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 49) 0 = _ from he]
  exact Safe.framed (base_safe 50) perm21.symm

theorem base_edge49_1 : SafeCore (mutate (base 49) 1) := by
  have he := mutation_equal (bnode 49) (preverse (prelabel (root [29] [146] [112] [5] [4] [1]) perm6.symm)) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (base_safe 49) 1
  rw [show mutate (base 49) 1 = _ from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [29] [146] [112] [5] [4] [1] 0 (by decide +kernel) (by decide +kernel)) perm6.symm)

theorem base_edge49_2 : SafeCore (mutate (base 49) 2) := by
  have he := mutation_equal (bnode 49) (preverse (prelabel (generic param8_0 param8_1 param8_2 param8_3 0) perm3.symm)) 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 49) 2 = _ from he]
  exact Safe.reversed (Safe.framed (region8_safe 0) perm3.symm)

theorem base_edge49_3 : SafeCore (mutate (base 49) 3) := by
  have he := mutation_equal (bnode 49) (prelabel (bnode 37) perm1.symm) 3 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 49) 3 = _ from he]
  exact Safe.framed (base_safe 37) perm1.symm

theorem base_cyclic50 : ¬Acyclic (base 50) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (bnode 50 0 3) 0 (by decide +kernel) (by decide +kernel))
  have h1 := hr 3 1 (pos (bnode 50 3 1) 0 (by decide +kernel) (by decide +kernel))
  have h2 := hr 1 0 (pos (bnode 50 1 0) 0 (by decide +kernel) (by decide +kernel))
  omega

theorem base_edge50_0 : SafeCore (mutate (base 50) 0) := by
  have he := mutation_equal (bnode 50) (prelabel (fork [4] [3] [112] [11] [419] [5]) perm5.symm) 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (base_safe 50)
  rw [show mutate (base 50) 0 = _ from he]
  exact IsFork.relabelled (fork_sound [4] [3] [112] [11] [419] [5] 0 (by decide +kernel) (by decide +kernel)) perm5.symm

theorem base_edge50_1 : SafeCore (mutate (base 50) 1) := by
  have he := mutation_equal (bnode 50) (preverse (prelabel (root [112] [563] [3244] [5] [29] [1]) perm6.symm)) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (base_safe 50) 1
  rw [show mutate (base 50) 1 = _ from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [112] [563] [3244] [5] [29] [1] 0 (by decide +kernel) (by decide +kernel)) perm6.symm)

theorem base_edge50_2 : SafeCore (mutate (base 50) 2) := by
  have he := mutation_equal (bnode 50) (preverse (prelabel (generic param8_0 param8_1 param8_2 param8_3 2) perm16.symm)) 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 50) 2 = _ from he]
  exact Safe.reversed (Safe.framed (region8_safe 2) perm16.symm)

theorem base_edge50_3 : SafeCore (mutate (base 50) 3) := by
  have he := mutation_equal (bnode 50) (prelabel (bnode 49) perm21.symm) 3 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 50) 3 = _ from he]
  exact Safe.framed (base_safe 49) perm21.symm

theorem base_cyclic51 : ¬Acyclic (base 51) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (bnode 51 0 3) 0 (by decide +kernel) (by decide +kernel))
  have h1 := hr 3 1 (pos (bnode 51 3 1) 0 (by decide +kernel) (by decide +kernel))
  have h2 := hr 1 0 (pos (bnode 51 1 0) 0 (by decide +kernel) (by decide +kernel))
  omega

theorem base_edge51_0 : SafeCore (mutate (base 51) 0) := by
  have he := mutation_equal (bnode 51) (preverse (prelabel (root [11] [164] [316] [15] [29] [1]) perm5.symm)) 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (base_safe 51) 0
  rw [show mutate (base 51) 0 = _ from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [11] [164] [316] [15] [29] [1] 0 (by decide +kernel) (by decide +kernel)) perm5.symm)

theorem base_edge51_1 : SafeCore (mutate (base 51) 1) := by
  have he := mutation_equal (bnode 51) (prelabel (bnode 55) perm5.symm) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 51) 1 = _ from he]
  exact Safe.framed (base_safe 55) perm5.symm

theorem base_edge51_2 : SafeCore (mutate (base 51) 2) := by
  have he := mutation_equal (bnode 51) (prelabel (bnode 56) perm1.symm) 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 51) 2 = _ from he]
  exact Safe.framed (base_safe 56) perm1.symm

theorem base_edge51_3 : SafeCore (mutate (base 51) 3) := by
  have he := mutation_equal (bnode 51) (prelabel (bnode 41) perm5.symm) 3 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 51) 3 = _ from he]
  exact Safe.framed (base_safe 41) perm5.symm

theorem base_cyclic52 : ¬Acyclic (base 52) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (bnode 52 0 3) 0 (by decide +kernel) (by decide +kernel))
  have h1 := hr 3 1 (pos (bnode 52 3 1) 0 (by decide +kernel) (by decide +kernel))
  have h2 := hr 1 0 (pos (bnode 52 1 0) 0 (by decide +kernel) (by decide +kernel))
  omega

theorem base_edge52_0 : SafeCore (mutate (base 52) 0) := by
  have he := mutation_equal (bnode 52) (prelabel (fork [4] [3] [44] [11] [165] [4]) perm5.symm) 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (base_safe 52)
  rw [show mutate (base 52) 0 = _ from he]
  exact IsFork.relabelled (fork_sound [4] [3] [44] [11] [165] [4] 0 (by decide +kernel) (by decide +kernel)) perm5.symm

theorem base_edge52_1 : SafeCore (mutate (base 52) 1) := by
  have he := mutation_equal (bnode 52) (preverse (prelabel (root [44] [179] [480] [4] [11] [1]) perm6.symm)) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (base_safe 52) 1
  rw [show mutate (base 52) 1 = _ from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [44] [179] [480] [4] [11] [1] 0 (by decide +kernel) (by decide +kernel)) perm6.symm)

theorem base_edge52_2 : SafeCore (mutate (base 52) 2) := by
  have he := mutation_equal (bnode 52) (preverse (prelabel (bnode 56) perm6.symm)) 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 52) 2 = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 56) perm6.symm)

theorem base_edge52_3 : SafeCore (mutate (base 52) 3) := by
  have he := mutation_equal (bnode 52) (preverse (prelabel (bnode 42) perm7.symm)) 3 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 52) 3 = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 42) perm7.symm)

theorem base_cyclic53 : ¬Acyclic (base 53) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (bnode 53 0 3) 0 (by decide +kernel) (by decide +kernel))
  have h1 := hr 3 1 (pos (bnode 53 3 1) 0 (by decide +kernel) (by decide +kernel))
  have h2 := hr 1 0 (pos (bnode 53 1 0) 0 (by decide +kernel) (by decide +kernel))
  omega

theorem base_edge53_0 : SafeCore (mutate (base 53) 0) := by
  have he := mutation_equal (bnode 53) (prelabel (bnode 54) perm21.symm) 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 53) 0 = _ from he]
  exact Safe.framed (base_safe 54) perm21.symm

theorem base_edge53_1 : SafeCore (mutate (base 53) 1) := by
  have he := mutation_equal (bnode 53) (preverse (prelabel (root [334] [21377] [6341] [64] [19] [1]) perm6.symm)) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (base_safe 53) 1
  rw [show mutate (base 53) 1 = _ from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [334] [21377] [6341] [64] [19] [1] 0 (by decide +kernel) (by decide +kernel)) perm6.symm)

theorem base_edge53_2 : SafeCore (mutate (base 53) 2) := by
  have he := mutation_equal (bnode 53) (preverse (prelabel (generic param9_0 param9_1 param9_2 param9_3 0) perm3.symm)) 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 53) 2 = _ from he]
  exact Safe.reversed (Safe.framed (region9_safe 0) perm3.symm)

theorem base_edge53_3 : SafeCore (mutate (base 53) 3) := by
  have he := mutation_equal (bnode 53) (preverse (prelabel (bnode 43) perm7.symm)) 3 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 53) 3 = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 43) perm7.symm)

theorem base_cyclic54 : ¬Acyclic (base 54) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (bnode 54 0 3) 0 (by decide +kernel) (by decide +kernel))
  have h1 := hr 3 1 (pos (bnode 54 3 1) 0 (by decide +kernel) (by decide +kernel))
  have h2 := hr 1 0 (pos (bnode 54 1 0) 0 (by decide +kernel) (by decide +kernel))
  omega

theorem base_edge54_0 : SafeCore (mutate (base 54) 0) := by
  have he := mutation_equal (bnode 54) (prelabel (fork [5] [4] [1651] [19] [7921] [64]) perm5.symm) 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (base_safe 54)
  rw [show mutate (base 54) 0 = _ from he]
  exact IsFork.relabelled (fork_sound [5] [4] [1651] [19] [7921] [64] 0 (by decide +kernel) (by decide +kernel)) perm5.symm

theorem base_edge54_1 : SafeCore (mutate (base 54) 1) := by
  have he := mutation_equal (bnode 54) (preverse (prelabel (root [1651] [105668] [551429] [64] [334] [1]) perm6.symm)) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (base_safe 54) 1
  rw [show mutate (base 54) 1 = _ from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [1651] [105668] [551429] [64] [334] [1] 0 (by decide +kernel) (by decide +kernel)) perm6.symm)

theorem base_edge54_2 : SafeCore (mutate (base 54) 2) := by
  have he := mutation_equal (bnode 54) (preverse (prelabel (generic param9_0 param9_1 param9_2 param9_3 2) perm16.symm)) 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 54) 2 = _ from he]
  exact Safe.reversed (Safe.framed (region9_safe 2) perm16.symm)

theorem base_edge54_3 : SafeCore (mutate (base 54) 3) := by
  have he := mutation_equal (bnode 54) (prelabel (bnode 53) perm21.symm) 3 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 54) 3 = _ from he]
  exact Safe.framed (base_safe 53) perm21.symm

theorem base_cyclic55 : ¬Acyclic (base 55) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (bnode 55 0 3) 0 (by decide +kernel) (by decide +kernel))
  have h1 := hr 3 1 (pos (bnode 55 3 1) 0 (by decide +kernel) (by decide +kernel))
  have h2 := hr 1 0 (pos (bnode 55 1 0) 0 (by decide +kernel) (by decide +kernel))
  omega

theorem base_edge55_0 : SafeCore (mutate (base 55) 0) := by
  have he := mutation_equal (bnode 55) (prelabel (fork [29] [76] [15] [2201] [436] [4]) perm4.symm) 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (base_safe 55)
  rw [show mutate (base 55) 0 = _ from he]
  exact IsFork.relabelled (fork_sound [29] [76] [15] [2201] [436] [4] 0 (by decide +kernel) (by decide +kernel)) perm4.symm

theorem base_edge55_1 : SafeCore (mutate (base 55) 1) := by
  have he := mutation_equal (bnode 55) (preverse (prelabel (fork [3] [76] [4] [199] [11] [15]) perm10.symm)) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (base_safe 55)
  rw [show mutate (base 55) 1 = _ from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [3] [76] [4] [199] [11] [15] 0 (by decide +kernel) (by decide +kernel)) perm10.symm)

theorem base_edge55_2 : SafeCore (mutate (base 55) 2) := by
  have he := mutation_equal (bnode 55) (preverse (prelabel (bnode 57) perm7.symm)) 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 55) 2 = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 57) perm7.symm)

theorem base_edge55_3 : SafeCore (mutate (base 55) 3) := by
  have he := mutation_equal (bnode 55) (prelabel (bnode 51) perm5.symm) 3 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 55) 3 = _ from he]
  exact Safe.framed (base_safe 51) perm5.symm

theorem base_cyclic56 : ¬Acyclic (base 56) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (bnode 56 0 3) 0 (by decide +kernel) (by decide +kernel))
  have h1 := hr 3 1 (pos (bnode 56 3 1) 0 (by decide +kernel) (by decide +kernel))
  have h2 := hr 1 0 (pos (bnode 56 1 0) 0 (by decide +kernel) (by decide +kernel))
  omega

theorem base_edge56_0 : SafeCore (mutate (base 56) 0) := by
  have he := mutation_equal (bnode 56) (prelabel (fork [15] [4] [44] [59] [659] [3]) perm5.symm) 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (base_safe 56)
  rw [show mutate (base 56) 0 = _ from he]
  exact IsFork.relabelled (fork_sound [15] [4] [44] [59] [659] [3] 0 (by decide +kernel) (by decide +kernel)) perm5.symm

theorem base_edge56_1 : SafeCore (mutate (base 56) 1) := by
  have he := mutation_equal (bnode 56) (prelabel (generic param10_0 param10_1 param10_2 param10_3 0) perm17.symm) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 56) 1 = _ from he]
  exact Safe.framed (region10_safe 0) perm17.symm

theorem base_edge56_2 : SafeCore (mutate (base 56) 2) := by
  have he := mutation_equal (bnode 56) (preverse (prelabel (bnode 52) perm6.symm)) 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 56) 2 = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 52) perm6.symm)

theorem base_edge56_3 : SafeCore (mutate (base 56) 3) := by
  have he := mutation_equal (bnode 56) (prelabel (bnode 51) perm1.symm) 3 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 56) 3 = _ from he]
  exact Safe.framed (base_safe 51) perm1.symm

theorem base_cyclic57 : ¬Acyclic (base 57) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (bnode 57 0 3) 0 (by decide +kernel) (by decide +kernel))
  have h1 := hr 3 1 (pos (bnode 57 3 1) 0 (by decide +kernel) (by decide +kernel))
  have h2 := hr 1 0 (pos (bnode 57 1 0) 0 (by decide +kernel) (by decide +kernel))
  omega

theorem base_edge57_0 : SafeCore (mutate (base 57) 0) := by
  have he := mutation_equal (bnode 57) (prelabel (bnode 58) perm21.symm) 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 57) 0 = _ from he]
  exact Safe.framed (base_safe 58) perm21.symm

theorem base_edge57_1 : SafeCore (mutate (base 57) 1) := by
  have he := mutation_equal (bnode 57) (preverse (prelabel (root [136] [3945] [2036] [29] [15] [1]) perm6.symm)) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (base_safe 57) 1
  rw [show mutate (base 57) 1 = _ from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [136] [3945] [2036] [29] [15] [1] 0 (by decide +kernel) (by decide +kernel)) perm6.symm)

theorem base_edge57_2 : SafeCore (mutate (base 57) 2) := by
  have he := mutation_equal (bnode 57) (preverse (prelabel (generic param10_0 param10_1 param10_2 param10_3 0) perm3.symm)) 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 57) 2 = _ from he]
  exact Safe.reversed (Safe.framed (region10_safe 0) perm3.symm)

theorem base_edge57_3 : SafeCore (mutate (base 57) 3) := by
  have he := mutation_equal (bnode 57) (preverse (prelabel (bnode 55) perm7.symm)) 3 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 57) 3 = _ from he]
  exact Safe.reversed (Safe.framed (base_safe 55) perm7.symm)

theorem base_cyclic58 : ¬Acyclic (base 58) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (bnode 58 0 3) 0 (by decide +kernel) (by decide +kernel))
  have h1 := hr 3 1 (pos (bnode 58 3 1) 0 (by decide +kernel) (by decide +kernel))
  have h2 := hr 1 0 (pos (bnode 58 1 0) 0 (by decide +kernel) (by decide +kernel))
  omega

theorem base_edge58_0 : SafeCore (mutate (base 58) 0) := by
  have he := mutation_equal (bnode 58) (prelabel (fork [4] [3] [529] [11] [1980] [29]) perm5.symm) 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (base_safe 58)
  rw [show mutate (base 58) 0 = _ from he]
  exact IsFork.relabelled (fork_sound [4] [3] [529] [11] [1980] [29] 0 (by decide +kernel) (by decide +kernel)) perm5.symm

theorem base_edge58_1 : SafeCore (mutate (base 58) 1) := by
  have he := mutation_equal (bnode 58) (preverse (prelabel (root [529] [15344] [71940] [29] [136] [1]) perm6.symm)) 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (base_safe 58) 1
  rw [show mutate (base 58) 1 = _ from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [529] [15344] [71940] [29] [136] [1] 0 (by decide +kernel) (by decide +kernel)) perm6.symm)

theorem base_edge58_2 : SafeCore (mutate (base 58) 2) := by
  have he := mutation_equal (bnode 58) (preverse (prelabel (generic param10_0 param10_1 param10_2 param10_3 2) perm16.symm)) 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 58) 2 = _ from he]
  exact Safe.reversed (Safe.framed (region10_safe 2) perm16.symm)

theorem base_edge58_3 : SafeCore (mutate (base 58) 3) := by
  have he := mutation_equal (bnode 58) (prelabel (bnode 57) perm21.symm) 3 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (base 58) 3 = _ from he]
  exact Safe.framed (base_safe 57) perm21.symm

theorem node_cyclic0 (t : Int) (ht : 0≤t) : ¬Acyclic (node t 0) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 0 0 2) t ht (by decide +kernel))
  have h1 := hr 2 1 (pos (pnode 0 2 1) t ht (by decide +kernel))
  have h2 := hr 1 0 (pos (pnode 0 1 0) t ht (by decide +kernel))
  omega

theorem node_edge0_0 (t : Int) (ht : 0≤t) : SafeCore (mutate (node t 0) 0) := by
  have he := mutation_equal (pnode 0) (preverse (prelabel (pnode 3) perm1.symm)) 0 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (node t 0) 0 = _ from he]
  exact Safe.reversed (Safe.framed (node_safe t ht 3) perm1.symm)

theorem node_edge0_1 (t : Int) (ht : 0≤t) : SafeCore (mutate (node t 0) 1) := by
  have he := mutation_equal (pnode 0) (prelabel (generic param0_0 param0_1 param0_2 param0_3 0) perm17.symm) 1 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (node t 0) 1 = _ from he]
  exact Safe.framed (region0_safe t ht 0) perm17.symm

theorem node_edge0_2 (t : Int) (ht : 0≤t) : SafeCore (mutate (node t 0) 2) := by
  have he := mutation_equal (pnode 0) (preverse (prelabel (ptail [3,1] 3) perm21.symm)) 2 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse,ptail_eval] at he
  rw [show mutate (node t 0) 2 = _ from he]
  exact Safe.reversed (Safe.framed (tail_safe (eval [3,1] t) (by simpa [eval] using le [3] [3,1] t ht (by decide +kernel)) 3) perm21.symm)

theorem node_edge0_3 (t : Int) (ht : 0≤t) : SafeCore (mutate (node t 0) 3) := by
  have he := mutation_equal (pnode 0) (prelabel (ptail [5,1] 1) perm1.symm) 3 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse,ptail_eval] at he
  rw [show mutate (node t 0) 3 = _ from he]
  exact Safe.framed (tail_safe (eval [5,1] t) (by simpa [eval] using le [3] [5,1] t ht (by decide +kernel)) 1) perm1.symm

theorem node_cyclic1 (t : Int) (ht : 0≤t) : ¬Acyclic (node t 1) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 1 0 3) t ht (by decide +kernel))
  have h1 := hr 3 1 (pos (pnode 1 3 1) t ht (by decide +kernel))
  have h2 := hr 1 0 (pos (pnode 1 1 0) t ht (by decide +kernel))
  omega

theorem node_edge1_0 (t : Int) (ht : 0≤t) : SafeCore (mutate (node t 1) 0) := by
  have he := mutation_equal (pnode 1) (prelabel (ptail [9,1] 1) perm21.symm) 0 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse,ptail_eval] at he
  rw [show mutate (node t 1) 0 = _ from he]
  exact Safe.framed (tail_safe (eval [9,1] t) (by simpa [eval] using le [3] [9,1] t ht (by decide +kernel)) 1) perm21.symm

theorem node_edge1_1 (t : Int) (ht : 0≤t) : SafeCore (mutate (node t 1) 1) := by
  have he := mutation_equal (pnode 1) (preverse (prelabel (pnode 6) perm19.symm)) 1 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (node t 1) 1 = _ from he]
  exact Safe.reversed (Safe.framed (node_safe t ht 6) perm19.symm)

theorem node_edge1_2 (t : Int) (ht : 0≤t) : SafeCore (mutate (node t 1) 2) := by
  have he := mutation_equal (pnode 1) (prelabel (ptail [7,1] 0) perm1.symm) 2 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse,ptail_eval] at he
  rw [show mutate (node t 1) 2 = _ from he]
  exact Safe.framed (tail_safe (eval [7,1] t) (by simpa [eval] using le [3] [7,1] t ht (by decide +kernel)) 0) perm1.symm

theorem node_edge1_3 (t : Int) (ht : 0≤t) : SafeCore (mutate (node t 1) 3) := by
  have he := mutation_equal (pnode 1) (prelabel (ptail [3,1] 1) perm21.symm) 3 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse,ptail_eval] at he
  rw [show mutate (node t 1) 3 = _ from he]
  exact Safe.framed (tail_safe (eval [3,1] t) (by simpa [eval] using le [3] [3,1] t ht (by decide +kernel)) 1) perm21.symm

theorem node_cyclic2 (t : Int) (ht : 0≤t) : ¬Acyclic (node t 2) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 2 0 3) t ht (by decide +kernel))
  have h1 := hr 3 1 (pos (pnode 2 3 1) t ht (by decide +kernel))
  have h2 := hr 1 0 (pos (pnode 2 1 0) t ht (by decide +kernel))
  omega

theorem node_edge2_0 (t : Int) (ht : 0≤t) : SafeCore (mutate (node t 2) 0) := by
  have he := mutation_equal (pnode 2) (prelabel (ptail [9,1] 2) perm21.symm) 0 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse,ptail_eval] at he
  rw [show mutate (node t 2) 0 = _ from he]
  exact Safe.framed (tail_safe (eval [9,1] t) (by simpa [eval] using le [3] [9,1] t ht (by decide +kernel)) 2) perm21.symm

theorem node_edge2_1 (t : Int) (ht : 0≤t) : SafeCore (mutate (node t 2) 1) := by
  have he := mutation_equal (pnode 2) (preverse (prelabel (root [6,1] [25,4] [16,9,1] [4] [3,1] [1]) perm6.symm)) 1 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (node_safe t ht 2) 1
  rw [show mutate (node t 2) 1 = _ from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [6,1] [25,4] [16,9,1] [4] [3,1] [1] t ht (by decide +kernel)) perm6.symm)

theorem node_edge2_2 (t : Int) (ht : 0≤t) : SafeCore (mutate (node t 2) 2) := by
  have he := mutation_equal (pnode 2) (preverse (prelabel (ptail [7,1] 3) perm20.symm)) 2 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse,ptail_eval] at he
  rw [show mutate (node t 2) 2 = _ from he]
  exact Safe.reversed (Safe.framed (tail_safe (eval [7,1] t) (by simpa [eval] using le [3] [7,1] t ht (by decide +kernel)) 3) perm20.symm)

theorem node_edge2_3 (t : Int) (ht : 0≤t) : SafeCore (mutate (node t 2) 3) := by
  have he := mutation_equal (pnode 2) (prelabel (ptail [3,1] 2) perm21.symm) 3 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse,ptail_eval] at he
  rw [show mutate (node t 2) 3 = _ from he]
  exact Safe.framed (tail_safe (eval [3,1] t) (by simpa [eval] using le [3] [3,1] t ht (by decide +kernel)) 2) perm21.symm

theorem node_cyclic3 (t : Int) (ht : 0≤t) : ¬Acyclic (node t 3) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 3 0 2) t ht (by decide +kernel))
  have h1 := hr 2 1 (pos (pnode 3 2 1) t ht (by decide +kernel))
  have h2 := hr 1 0 (pos (pnode 3 1 0) t ht (by decide +kernel))
  omega

theorem node_edge3_0 (t : Int) (ht : 0≤t) : SafeCore (mutate (node t 3) 0) := by
  have he := mutation_equal (pnode 3) (preverse (prelabel (pnode 0) perm1.symm)) 0 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (node t 3) 0 = _ from he]
  exact Safe.reversed (Safe.framed (node_safe t ht 0) perm1.symm)

theorem node_edge3_1 (t : Int) (ht : 0≤t) : SafeCore (mutate (node t 3) 1) := by
  have he := mutation_equal (pnode 3) (preverse (prelabel (root [6,1] [29,11,1] [23,4] [5,1] [4] [1]) perm6.symm)) 1 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (node_safe t ht 3) 1
  rw [show mutate (node t 3) 1 = _ from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [6,1] [29,11,1] [23,4] [5,1] [4] [1] t ht (by decide +kernel)) perm6.symm)

theorem node_edge3_2 (t : Int) (ht : 0≤t) : SafeCore (mutate (node t 3) 2) := by
  have he := mutation_equal (pnode 3) (preverse (prelabel (ptail [9,1] 0) perm21.symm)) 2 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse,ptail_eval] at he
  rw [show mutate (node t 3) 2 = _ from he]
  exact Safe.reversed (Safe.framed (tail_safe (eval [9,1] t) (by simpa [eval] using le [3] [9,1] t ht (by decide +kernel)) 0) perm21.symm)

theorem node_edge3_3 (t : Int) (ht : 0≤t) : SafeCore (mutate (node t 3) 3) := by
  have he := mutation_equal (pnode 3) (preverse (prelabel (ptail [5,1] 2) perm15.symm)) 3 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse,ptail_eval] at he
  rw [show mutate (node t 3) 3 = _ from he]
  exact Safe.reversed (Safe.framed (tail_safe (eval [5,1] t) (by simpa [eval] using le [3] [5,1] t ht (by decide +kernel)) 2) perm15.symm)

theorem node_cyclic4 (t : Int) (ht : 0≤t) : ¬Acyclic (node t 4) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 4 0 3) t ht (by decide +kernel))
  have h1 := hr 3 1 (pos (pnode 4 3 1) t ht (by decide +kernel))
  have h2 := hr 1 0 (pos (pnode 4 1 0) t ht (by decide +kernel))
  omega

theorem node_edge4_0 (t : Int) (ht : 0≤t) : SafeCore (mutate (node t 4) 0) := by
  have he := mutation_equal (pnode 4) (prelabel (pnode 5) perm21.symm) 0 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (node t 4) 0 = _ from he]
  exact Safe.framed (node_safe t ht 5) perm21.symm

theorem node_edge4_1 (t : Int) (ht : 0≤t) : SafeCore (mutate (node t 4) 1) := by
  have he := mutation_equal (pnode 4) (prelabel (generic param1_0 param1_1 param1_2 param1_3 0) perm17.symm) 1 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (node t 4) 1 = _ from he]
  exact Safe.framed (region1_safe t ht 0) perm17.symm

theorem node_edge4_2 (t : Int) (ht : 0≤t) : SafeCore (mutate (node t 4) 2) := by
  have he := mutation_equal (pnode 4) (preverse (prelabel (generic param0_0 param0_1 param0_2 param0_3 0) perm3.symm)) 2 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (node t 4) 2 = _ from he]
  exact Safe.reversed (Safe.framed (region0_safe t ht 0) perm3.symm)

theorem node_edge4_3 (t : Int) (ht : 0≤t) : SafeCore (mutate (node t 4) 3) := by
  have he := mutation_equal (pnode 4) (prelabel (pnode 9) perm1.symm) 3 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (node t 4) 3 = _ from he]
  exact Safe.framed (node_safe t ht 9) perm1.symm

theorem node_cyclic5 (t : Int) (ht : 0≤t) : ¬Acyclic (node t 5) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 5 0 3) t ht (by decide +kernel))
  have h1 := hr 3 1 (pos (pnode 5 3 1) t ht (by decide +kernel))
  have h2 := hr 1 0 (pos (pnode 5 1 0) t ht (by decide +kernel))
  omega

theorem node_edge5_0 (t : Int) (ht : 0≤t) : SafeCore (mutate (node t 5) 0) := by
  have he := mutation_equal (pnode 5) (prelabel (fork [3,1] [2,1] [32,35,11,1] [5,5,1] [85,129,67,14,1] [5,1]) perm5.symm) 0 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (node_safe t ht 5)
  rw [show mutate (node t 5) 0 = _ from he]
  exact IsFork.relabelled (fork_sound [3,1] [2,1] [32,35,11,1] [5,5,1] [85,129,67,14,1] [5,1] t ht (by decide +kernel)) perm5.symm

theorem node_edge5_1 (t : Int) (ht : 0≤t) : SafeCore (mutate (node t 5) 1) := by
  have he := mutation_equal (pnode 5) (preverse (prelabel (root [32,35,11,1] [162,208,90,16,1] [349,640,433,134,19,1] [5,1] [11,8,1] [1]) perm6.symm)) 1 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (node_safe t ht 5) 1
  rw [show mutate (node t 5) 1 = _ from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [32,35,11,1] [162,208,90,16,1] [349,640,433,134,19,1] [5,1] [11,8,1] [1] t ht (by decide +kernel)) perm6.symm)

theorem node_edge5_2 (t : Int) (ht : 0≤t) : SafeCore (mutate (node t 5) 2) := by
  have he := mutation_equal (pnode 5) (preverse (prelabel (generic param0_0 param0_1 param0_2 param0_3 2) perm16.symm)) 2 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (node t 5) 2 = _ from he]
  exact Safe.reversed (Safe.framed (region0_safe t ht 2) perm16.symm)

theorem node_edge5_3 (t : Int) (ht : 0≤t) : SafeCore (mutate (node t 5) 3) := by
  have he := mutation_equal (pnode 5) (prelabel (pnode 4) perm21.symm) 3 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (node t 5) 3 = _ from he]
  exact Safe.framed (node_safe t ht 4) perm21.symm

theorem node_cyclic6 (t : Int) (ht : 0≤t) : ¬Acyclic (node t 6) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 6 0 3) t ht (by decide +kernel))
  have h1 := hr 3 1 (pos (pnode 6 3 1) t ht (by decide +kernel))
  have h2 := hr 1 0 (pos (pnode 6 1 0) t ht (by decide +kernel))
  omega

theorem node_edge6_0 (t : Int) (ht : 0≤t) : SafeCore (mutate (node t 6) 0) := by
  have he := mutation_equal (pnode 6) (preverse (prelabel (root [3,1] [11,7,1] [42,42,12,1] [4,1] [16,9,1] [1]) perm5.symm)) 0 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (node_safe t ht 6) 0
  rw [show mutate (node t 6) 0 = _ from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [3,1] [11,7,1] [42,42,12,1] [4,1] [16,9,1] [1] t ht (by decide +kernel)) perm5.symm)

theorem node_edge6_1 (t : Int) (ht : 0≤t) : SafeCore (mutate (node t 6) 1) := by
  have he := mutation_equal (pnode 6) (preverse (prelabel (pnode 10) perm19.symm)) 1 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (node t 6) 1 = _ from he]
  exact Safe.reversed (Safe.framed (node_safe t ht 10) perm19.symm)

theorem node_edge6_2 (t : Int) (ht : 0≤t) : SafeCore (mutate (node t 6) 2) := by
  have he := mutation_equal (pnode 6) (prelabel (pnode 11) perm1.symm) 2 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (node t 6) 2 = _ from he]
  exact Safe.framed (node_safe t ht 11) perm1.symm

theorem node_edge6_3 (t : Int) (ht : 0≤t) : SafeCore (mutate (node t 6) 3) := by
  have he := mutation_equal (pnode 6) (preverse (prelabel (pnode 1) perm11.symm)) 3 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (node t 6) 3 = _ from he]
  exact Safe.reversed (Safe.framed (node_safe t ht 1) perm11.symm)

theorem node_cyclic7 (t : Int) (ht : 0≤t) : ¬Acyclic (node t 7) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 7 0 3) t ht (by decide +kernel))
  have h1 := hr 3 1 (pos (pnode 7 3 1) t ht (by decide +kernel))
  have h2 := hr 1 0 (pos (pnode 7 1 0) t ht (by decide +kernel))
  omega

theorem node_edge7_0 (t : Int) (ht : 0≤t) : SafeCore (mutate (node t 7) 0) := by
  have he := mutation_equal (pnode 7) (prelabel (pnode 8) perm21.symm) 0 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (node t 7) 0 = _ from he]
  exact Safe.framed (node_safe t ht 8) perm21.symm

theorem node_edge7_1 (t : Int) (ht : 0≤t) : SafeCore (mutate (node t 7) 1) := by
  have he := mutation_equal (pnode 7) (preverse (prelabel (root [56,51,13,1] [449,800,517,150,20,1] [162,208,90,16,1] [8,7,1] [3,1] [1]) perm6.symm)) 1 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (node_safe t ht 7) 1
  rw [show mutate (node t 7) 1 = _ from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [56,51,13,1] [449,800,517,150,20,1] [162,208,90,16,1] [8,7,1] [3,1] [1] t ht (by decide +kernel)) perm6.symm)

theorem node_edge7_2 (t : Int) (ht : 0≤t) : SafeCore (mutate (node t 7) 2) := by
  have he := mutation_equal (pnode 7) (preverse (prelabel (generic param1_0 param1_1 param1_2 param1_3 0) perm3.symm)) 2 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (node t 7) 2 = _ from he]
  exact Safe.reversed (Safe.framed (region1_safe t ht 0) perm3.symm)

theorem node_edge7_3 (t : Int) (ht : 0≤t) : SafeCore (mutate (node t 7) 3) := by
  have he := mutation_equal (pnode 7) (prelabel (pnode 12) perm1.symm) 3 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (node t 7) 3 = _ from he]
  exact Safe.framed (node_safe t ht 12) perm1.symm

theorem node_cyclic8 (t : Int) (ht : 0≤t) : ¬Acyclic (node t 8) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 8 0 3) t ht (by decide +kernel))
  have h1 := hr 3 1 (pos (pnode 8 3 1) t ht (by decide +kernel))
  have h2 := hr 1 0 (pos (pnode 8 1 0) t ht (by decide +kernel))
  omega

theorem node_edge8_0 (t : Int) (ht : 0≤t) : SafeCore (mutate (node t 8) 0) := by
  have he := mutation_equal (pnode 8) (prelabel (fork [6,1] [5,1] [333,361,129,19,1] [29,11,1] [1942,2448,1122,242,25,1] [8,7,1]) perm5.symm) 0 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (node_safe t ht 8)
  rw [show mutate (node t 8) 0 = _ from he]
  exact IsFork.relabelled (fork_sound [6,1] [5,1] [333,361,129,19,1] [29,11,1] [1942,2448,1122,242,25,1] [8,7,1] t ht (by decide +kernel)) perm5.symm

theorem node_edge8_1 (t : Int) (ht : 0≤t) : SafeCore (mutate (node t 8) 1) := by
  have he := mutation_equal (pnode 8) (preverse (prelabel (root [333,361,129,19,1] [2669,5220,3892,1416,270,26,1] [18642,37198,29964,12669,3063,427,32,1] [8,7,1] [56,51,13,1] [1]) perm6.symm)) 1 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (node_safe t ht 8) 1
  rw [show mutate (node t 8) 1 = _ from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [333,361,129,19,1] [2669,5220,3892,1416,270,26,1] [18642,37198,29964,12669,3063,427,32,1] [8,7,1] [56,51,13,1] [1] t ht (by decide +kernel)) perm6.symm)

theorem node_edge8_2 (t : Int) (ht : 0≤t) : SafeCore (mutate (node t 8) 2) := by
  have he := mutation_equal (pnode 8) (preverse (prelabel (generic param1_0 param1_1 param1_2 param1_3 2) perm16.symm)) 2 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (node t 8) 2 = _ from he]
  exact Safe.reversed (Safe.framed (region1_safe t ht 2) perm16.symm)

theorem node_edge8_3 (t : Int) (ht : 0≤t) : SafeCore (mutate (node t 8) 3) := by
  have he := mutation_equal (pnode 8) (prelabel (pnode 7) perm21.symm) 3 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (node t 8) 3 = _ from he]
  exact Safe.framed (node_safe t ht 7) perm21.symm

theorem node_cyclic9 (t : Int) (ht : 0≤t) : ¬Acyclic (node t 9) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 9 0 3) t ht (by decide +kernel))
  have h1 := hr 3 1 (pos (pnode 9 3 1) t ht (by decide +kernel))
  have h2 := hr 1 0 (pos (pnode 9 1 0) t ht (by decide +kernel))
  omega

theorem node_edge9_0 (t : Int) (ht : 0≤t) : SafeCore (mutate (node t 9) 0) := by
  have he := mutation_equal (pnode 9) (preverse (prelabel (root [2,1] [5,5,1] [11,21,9,1] [3,1] [8,7,1] [1]) perm5.symm)) 0 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (node_safe t ht 9) 0
  rw [show mutate (node t 9) 0 = _ from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [2,1] [5,5,1] [11,21,9,1] [3,1] [8,7,1] [1] t ht (by decide +kernel)) perm5.symm)

theorem node_edge9_1 (t : Int) (ht : 0≤t) : SafeCore (mutate (node t 9) 1) := by
  have he := mutation_equal (pnode 9) (preverse (prelabel (pnode 12) perm19.symm)) 1 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (node t 9) 1 = _ from he]
  exact Safe.reversed (Safe.framed (node_safe t ht 12) perm19.symm)

theorem node_edge9_2 (t : Int) (ht : 0≤t) : SafeCore (mutate (node t 9) 2) := by
  have he := mutation_equal (pnode 9) (prelabel (pnode 4) perm1.symm) 2 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (node t 9) 2 = _ from he]
  exact Safe.framed (node_safe t ht 4) perm1.symm

theorem node_edge9_3 (t : Int) (ht : 0≤t) : SafeCore (mutate (node t 9) 3) := by
  have he := mutation_equal (pnode 9) (preverse (prelabel (ptail [5,1] 1) perm11.symm)) 3 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse,ptail_eval] at he
  rw [show mutate (node t 9) 3 = _ from he]
  exact Safe.reversed (Safe.framed (tail_safe (eval [5,1] t) (by simpa [eval] using le [3] [5,1] t ht (by decide +kernel)) 1) perm11.symm)

theorem node_cyclic10 (t : Int) (ht : 0≤t) : ¬Acyclic (node t 10) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 10 0 3) t ht (by decide +kernel))
  have h1 := hr 3 1 (pos (pnode 10 3 1) t ht (by decide +kernel))
  have h2 := hr 1 0 (pos (pnode 10 1 0) t ht (by decide +kernel))
  omega

theorem node_edge10_0 (t : Int) (ht : 0≤t) : SafeCore (mutate (node t 10) 0) := by
  have he := mutation_equal (pnode 10) (prelabel (fork [6,1] [93,69,15,1] [7,1] [542,498,158,21,1] [41,13,1] [4,1]) perm4.symm) 0 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (node_safe t ht 10)
  rw [show mutate (node t 10) 0 = _ from he]
  exact IsFork.relabelled (fork_sound [6,1] [93,69,15,1] [7,1] [542,498,158,21,1] [41,13,1] [4,1] t ht (by decide +kernel)) perm4.symm

theorem node_edge10_1 (t : Int) (ht : 0≤t) : SafeCore (mutate (node t 10) 1) := by
  have he := mutation_equal (pnode 10) (preverse (prelabel (fork [16,9,1] [93,69,15,1] [4,1] [1482,1940,954,220,24,1] [65,52,13,1] [7,1]) perm10.symm)) 1 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (node_safe t ht 10)
  rw [show mutate (node t 10) 1 = _ from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [16,9,1] [93,69,15,1] [4,1] [1482,1940,954,220,24,1] [65,52,13,1] [7,1] t ht (by decide +kernel)) perm10.symm)

theorem node_edge10_2 (t : Int) (ht : 0≤t) : SafeCore (mutate (node t 10) 2) := by
  have he := mutation_equal (pnode 10) (prelabel (pnode 13) perm1.symm) 2 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (node t 10) 2 = _ from he]
  exact Safe.framed (node_safe t ht 13) perm1.symm

theorem node_edge10_3 (t : Int) (ht : 0≤t) : SafeCore (mutate (node t 10) 3) := by
  have he := mutation_equal (pnode 10) (preverse (prelabel (pnode 6) perm11.symm)) 3 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (node t 10) 3 = _ from he]
  exact Safe.reversed (Safe.framed (node_safe t ht 6) perm11.symm)

theorem node_cyclic11 (t : Int) (ht : 0≤t) : ¬Acyclic (node t 11) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 11 0 3) t ht (by decide +kernel))
  have h1 := hr 3 1 (pos (pnode 11 3 1) t ht (by decide +kernel))
  have h2 := hr 1 0 (pos (pnode 11 1 0) t ht (by decide +kernel))
  omega

theorem node_edge11_0 (t : Int) (ht : 0≤t) : SafeCore (mutate (node t 11) 0) := by
  have he := mutation_equal (pnode 11) (prelabel (pnode 14) perm21.symm) 0 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (node t 11) 0 = _ from he]
  exact Safe.framed (node_safe t ht 14) perm21.symm

theorem node_edge11_1 (t : Int) (ht : 0≤t) : SafeCore (mutate (node t 11) 1) := by
  have he := mutation_equal (pnode 11) (prelabel (generic param2_0 param2_1 param2_2 param2_3 0) perm17.symm) 1 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (node t 11) 1 = _ from he]
  exact Safe.framed (region2_safe t ht 0) perm17.symm

theorem node_edge11_2 (t : Int) (ht : 0≤t) : SafeCore (mutate (node t 11) 2) := by
  have he := mutation_equal (pnode 11) (preverse (prelabel (generic param3_0 param3_1 param3_2 param3_3 0) perm3.symm)) 2 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (node t 11) 2 = _ from he]
  exact Safe.reversed (Safe.framed (region3_safe t ht 0) perm3.symm)

theorem node_edge11_3 (t : Int) (ht : 0≤t) : SafeCore (mutate (node t 11) 3) := by
  have he := mutation_equal (pnode 11) (prelabel (pnode 6) perm1.symm) 3 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (node t 11) 3 = _ from he]
  exact Safe.framed (node_safe t ht 6) perm1.symm

theorem node_cyclic12 (t : Int) (ht : 0≤t) : ¬Acyclic (node t 12) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 12 0 3) t ht (by decide +kernel))
  have h1 := hr 3 1 (pos (pnode 12 3 1) t ht (by decide +kernel))
  have h2 := hr 1 0 (pos (pnode 12 1 0) t ht (by decide +kernel))
  omega

theorem node_edge12_0 (t : Int) (ht : 0≤t) : SafeCore (mutate (node t 12) 0) := by
  have he := mutation_equal (pnode 12) (prelabel (fork [5,1] [38,42,12,1] [6,1] [182,241,101,17,1] [29,11,1] [3,1]) perm4.symm) 0 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (node_safe t ht 12)
  rw [show mutate (node t 12) 0 = _ from he]
  exact IsFork.relabelled (fork_sound [5,1] [38,42,12,1] [6,1] [182,241,101,17,1] [29,11,1] [3,1] t ht (by decide +kernel)) perm4.symm

theorem node_edge12_1 (t : Int) (ht : 0≤t) : SafeCore (mutate (node t 12) 1) := by
  have he := mutation_equal (pnode 12) (preverse (prelabel (fork [8,7,1] [38,42,12,1] [3,1] [299,601,428,134,19,1] [25,29,10,1] [6,1]) perm10.symm)) 1 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (node_safe t ht 12)
  rw [show mutate (node t 12) 1 = _ from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [8,7,1] [38,42,12,1] [3,1] [299,601,428,134,19,1] [25,29,10,1] [6,1] t ht (by decide +kernel)) perm10.symm)

theorem node_edge12_2 (t : Int) (ht : 0≤t) : SafeCore (mutate (node t 12) 2) := by
  have he := mutation_equal (pnode 12) (prelabel (pnode 7) perm1.symm) 2 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (node t 12) 2 = _ from he]
  exact Safe.framed (node_safe t ht 7) perm1.symm

theorem node_edge12_3 (t : Int) (ht : 0≤t) : SafeCore (mutate (node t 12) 3) := by
  have he := mutation_equal (pnode 12) (preverse (prelabel (pnode 9) perm11.symm)) 3 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (node t 12) 3 = _ from he]
  exact Safe.reversed (Safe.framed (node_safe t ht 9) perm11.symm)

theorem node_cyclic13 (t : Int) (ht : 0≤t) : ¬Acyclic (node t 13) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 13 0 3) t ht (by decide +kernel))
  have h1 := hr 3 1 (pos (pnode 13 3 1) t ht (by decide +kernel))
  have h2 := hr 1 0 (pos (pnode 13 1 0) t ht (by decide +kernel))
  omega

theorem node_edge13_0 (t : Int) (ht : 0≤t) : SafeCore (mutate (node t 13) 0) := by
  have he := mutation_equal (pnode 13) (prelabel (pnode 15) perm21.symm) 0 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (node t 13) 0 = _ from he]
  exact Safe.framed (node_safe t ht 15) perm21.symm

theorem node_edge13_1 (t : Int) (ht : 0≤t) : SafeCore (mutate (node t 13) 1) := by
  have he := mutation_equal (pnode 13) (preverse (prelabel (root [121,80,16,1] [1937,2369,1097,240,25,1] [477,440,144,20,1] [16,9,1] [4,1] [1]) perm6.symm)) 1 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (node_safe t ht 13) 1
  rw [show mutate (node t 13) 1 = _ from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [121,80,16,1] [1937,2369,1097,240,25,1] [477,440,144,20,1] [16,9,1] [4,1] [1] t ht (by decide +kernel)) perm6.symm)

theorem node_edge13_2 (t : Int) (ht : 0≤t) : SafeCore (mutate (node t 13) 2) := by
  have he := mutation_equal (pnode 13) (preverse (prelabel (generic param2_0 param2_1 param2_2 param2_3 0) perm3.symm)) 2 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (node t 13) 2 = _ from he]
  exact Safe.reversed (Safe.framed (region2_safe t ht 0) perm3.symm)

theorem node_edge13_3 (t : Int) (ht : 0≤t) : SafeCore (mutate (node t 13) 3) := by
  have he := mutation_equal (pnode 13) (prelabel (pnode 10) perm1.symm) 3 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (node t 13) 3 = _ from he]
  exact Safe.framed (node_safe t ht 10) perm1.symm

theorem node_cyclic14 (t : Int) (ht : 0≤t) : ¬Acyclic (node t 14) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 14 0 3) t ht (by decide +kernel))
  have h1 := hr 3 1 (pos (pnode 14 3 1) t ht (by decide +kernel))
  have h2 := hr 1 0 (pos (pnode 14 1 0) t ht (by decide +kernel))
  omega

theorem node_edge14_0 (t : Int) (ht : 0≤t) : SafeCore (mutate (node t 14) 0) := by
  have he := mutation_equal (pnode 14) (prelabel (fork [4,1] [3,1] [79,60,14,1] [11,7,1] [296,309,115,18,1] [6,1]) perm5.symm) 0 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (node_safe t ht 14)
  rw [show mutate (node t 14) 0 = _ from he]
  exact IsFork.relabelled (fork_sound [4,1] [3,1] [79,60,14,1] [11,7,1] [296,309,115,18,1] [6,1] t ht (by decide +kernel)) perm5.symm

theorem node_edge14_1 (t : Int) (ht : 0≤t) : SafeCore (mutate (node t 14) 1) := by
  have he := mutation_equal (pnode 14) (preverse (prelabel (root [79,60,14,1] [477,440,144,20,1] [1576,1989,959,220,24,1] [6,1] [20,10,1] [1]) perm6.symm)) 1 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (node_safe t ht 14) 1
  rw [show mutate (node t 14) 1 = _ from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [79,60,14,1] [477,440,144,20,1] [1576,1989,959,220,24,1] [6,1] [20,10,1] [1] t ht (by decide +kernel)) perm6.symm)

theorem node_edge14_2 (t : Int) (ht : 0≤t) : SafeCore (mutate (node t 14) 2) := by
  have he := mutation_equal (pnode 14) (preverse (prelabel (generic param3_0 param3_1 param3_2 param3_3 2) perm16.symm)) 2 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (node t 14) 2 = _ from he]
  exact Safe.reversed (Safe.framed (region3_safe t ht 2) perm16.symm)

theorem node_edge14_3 (t : Int) (ht : 0≤t) : SafeCore (mutate (node t 14) 3) := by
  have he := mutation_equal (pnode 14) (prelabel (pnode 11) perm21.symm) 3 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (node t 14) 3 = _ from he]
  exact Safe.framed (node_safe t ht 11) perm21.symm

theorem node_cyclic15 (t : Int) (ht : 0≤t) : ¬Acyclic (node t 15) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 15 0 3) t ht (by decide +kernel))
  have h1 := hr 3 1 (pos (pnode 15 3 1) t ht (by decide +kernel))
  have h2 := hr 1 0 (pos (pnode 15 1 0) t ht (by decide +kernel))
  omega

theorem node_edge15_0 (t : Int) (ht : 0≤t) : SafeCore (mutate (node t 15) 0) := by
  have he := mutation_equal (pnode 15) (prelabel (fork [7,1] [6,1] [843,680,192,23,1] [41,13,1] [5780,5523,2008,352,30,1] [16,9,1]) perm5.symm) 0 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (node_safe t ht 15)
  rw [show mutate (node t 15) 0 = _ from he]
  exact IsFork.relabelled (fork_sound [7,1] [6,1] [843,680,192,23,1] [41,13,1] [5780,5523,2008,352,30,1] [16,9,1] t ht (by decide +kernel)) perm5.symm

theorem node_edge15_1 (t : Int) (ht : 0≤t) : SafeCore (mutate (node t 15) 1) := by
  have he := mutation_equal (pnode 15) (preverse (prelabel (root [843,680,192,23,1] [13494,18468,10035,2776,415,32,1] [101996,149719,91120,29866,5713,640,39,1] [16,9,1] [121,80,16,1] [1]) perm6.symm)) 1 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (node_safe t ht 15) 1
  rw [show mutate (node t 15) 1 = _ from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [843,680,192,23,1] [13494,18468,10035,2776,415,32,1] [101996,149719,91120,29866,5713,640,39,1] [16,9,1] [121,80,16,1] [1] t ht (by decide +kernel)) perm6.symm)

theorem node_edge15_2 (t : Int) (ht : 0≤t) : SafeCore (mutate (node t 15) 2) := by
  have he := mutation_equal (pnode 15) (preverse (prelabel (generic param2_0 param2_1 param2_2 param2_3 2) perm16.symm)) 2 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (node t 15) 2 = _ from he]
  exact Safe.reversed (Safe.framed (region2_safe t ht 2) perm16.symm)

theorem node_edge15_3 (t : Int) (ht : 0≤t) : SafeCore (mutate (node t 15) 3) := by
  have he := mutation_equal (pnode 15) (prelabel (pnode 13) perm21.symm) 3 t ht (by decide +kernel) (by decide +kernel)
  simp only [matrix_relabel,matrix_reverse] at he
  rw [show mutate (node t 15) 3 = _ from he]
  exact Safe.framed (node_safe t ht 13) perm21.symm

theorem core_skew (B : Matrix 4) (hB : Core B) : SkewSymmetric B := by
  cases hB with
  | node t ht i =>
    have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 ∨ i=15 := by omega
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp only [node,pnode,matrix_six] <;> exact ofSix_skew _ _ _ _ _ _
  | base i =>
    have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 ∨ i=15 ∨ i=16 ∨ i=17 ∨ i=18 ∨ i=19 ∨ i=20 ∨ i=21 ∨ i=22 ∨ i=23 ∨ i=24 ∨ i=25 ∨ i=26 ∨ i=27 ∨ i=28 ∨ i=29 ∨ i=30 ∨ i=31 ∨ i=32 ∨ i=33 ∨ i=34 ∨ i=35 ∨ i=36 ∨ i=37 ∨ i=38 ∨ i=39 ∨ i=40 ∨ i=41 ∨ i=42 ∨ i=43 ∨ i=44 ∨ i=45 ∨ i=46 ∨ i=47 ∨ i=48 ∨ i=49 ∨ i=50 ∨ i=51 ∨ i=52 ∨ i=53 ∨ i=54 ∨ i=55 ∨ i=56 ∨ i=57 ∨ i=58 := by omega
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp only [base,bnode,matrix_six] <;> exact ofSix_skew _ _ _ _ _ _
theorem core_cyclic (B : Matrix 4) (hB : Core B) : ¬Acyclic B := by
  cases hB with
  | node t ht i =>
    have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 ∨ i=15 := by omega
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact node_cyclic0 t ht
    · exact node_cyclic1 t ht
    · exact node_cyclic2 t ht
    · exact node_cyclic3 t ht
    · exact node_cyclic4 t ht
    · exact node_cyclic5 t ht
    · exact node_cyclic6 t ht
    · exact node_cyclic7 t ht
    · exact node_cyclic8 t ht
    · exact node_cyclic9 t ht
    · exact node_cyclic10 t ht
    · exact node_cyclic11 t ht
    · exact node_cyclic12 t ht
    · exact node_cyclic13 t ht
    · exact node_cyclic14 t ht
    · exact node_cyclic15 t ht
  | base i =>
    have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 ∨ i=15 ∨ i=16 ∨ i=17 ∨ i=18 ∨ i=19 ∨ i=20 ∨ i=21 ∨ i=22 ∨ i=23 ∨ i=24 ∨ i=25 ∨ i=26 ∨ i=27 ∨ i=28 ∨ i=29 ∨ i=30 ∨ i=31 ∨ i=32 ∨ i=33 ∨ i=34 ∨ i=35 ∨ i=36 ∨ i=37 ∨ i=38 ∨ i=39 ∨ i=40 ∨ i=41 ∨ i=42 ∨ i=43 ∨ i=44 ∨ i=45 ∨ i=46 ∨ i=47 ∨ i=48 ∨ i=49 ∨ i=50 ∨ i=51 ∨ i=52 ∨ i=53 ∨ i=54 ∨ i=55 ∨ i=56 ∨ i=57 ∨ i=58 := by omega
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact base_cyclic0
    · exact base_cyclic1
    · exact base_cyclic2
    · exact base_cyclic3
    · exact base_cyclic4
    · exact base_cyclic5
    · exact base_cyclic6
    · exact base_cyclic7
    · exact base_cyclic8
    · exact base_cyclic9
    · exact base_cyclic10
    · exact base_cyclic11
    · exact base_cyclic12
    · exact base_cyclic13
    · exact base_cyclic14
    · exact base_cyclic15
    · exact base_cyclic16
    · exact base_cyclic17
    · exact base_cyclic18
    · exact base_cyclic19
    · exact base_cyclic20
    · exact base_cyclic21
    · exact base_cyclic22
    · exact base_cyclic23
    · exact base_cyclic24
    · exact base_cyclic25
    · exact base_cyclic26
    · exact base_cyclic27
    · exact base_cyclic28
    · exact base_cyclic29
    · exact base_cyclic30
    · exact base_cyclic31
    · exact base_cyclic32
    · exact base_cyclic33
    · exact base_cyclic34
    · exact base_cyclic35
    · exact base_cyclic36
    · exact base_cyclic37
    · exact base_cyclic38
    · exact base_cyclic39
    · exact base_cyclic40
    · exact base_cyclic41
    · exact base_cyclic42
    · exact base_cyclic43
    · exact base_cyclic44
    · exact base_cyclic45
    · exact base_cyclic46
    · exact base_cyclic47
    · exact base_cyclic48
    · exact base_cyclic49
    · exact base_cyclic50
    · exact base_cyclic51
    · exact base_cyclic52
    · exact base_cyclic53
    · exact base_cyclic54
    · exact base_cyclic55
    · exact base_cyclic56
    · exact base_cyclic57
    · exact base_cyclic58
theorem core_edges (B : Matrix 4) (hB : Core B) : ∀ k, SafeCore (mutate B k) := by
  cases hB with
  | node t ht i =>
    have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 ∨ i=15 := by omega
    intro k
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rcases fin4 k with rfl|rfl|rfl|rfl
    · exact node_edge0_0 t ht
    · exact node_edge0_1 t ht
    · exact node_edge0_2 t ht
    · exact node_edge0_3 t ht
    · exact node_edge1_0 t ht
    · exact node_edge1_1 t ht
    · exact node_edge1_2 t ht
    · exact node_edge1_3 t ht
    · exact node_edge2_0 t ht
    · exact node_edge2_1 t ht
    · exact node_edge2_2 t ht
    · exact node_edge2_3 t ht
    · exact node_edge3_0 t ht
    · exact node_edge3_1 t ht
    · exact node_edge3_2 t ht
    · exact node_edge3_3 t ht
    · exact node_edge4_0 t ht
    · exact node_edge4_1 t ht
    · exact node_edge4_2 t ht
    · exact node_edge4_3 t ht
    · exact node_edge5_0 t ht
    · exact node_edge5_1 t ht
    · exact node_edge5_2 t ht
    · exact node_edge5_3 t ht
    · exact node_edge6_0 t ht
    · exact node_edge6_1 t ht
    · exact node_edge6_2 t ht
    · exact node_edge6_3 t ht
    · exact node_edge7_0 t ht
    · exact node_edge7_1 t ht
    · exact node_edge7_2 t ht
    · exact node_edge7_3 t ht
    · exact node_edge8_0 t ht
    · exact node_edge8_1 t ht
    · exact node_edge8_2 t ht
    · exact node_edge8_3 t ht
    · exact node_edge9_0 t ht
    · exact node_edge9_1 t ht
    · exact node_edge9_2 t ht
    · exact node_edge9_3 t ht
    · exact node_edge10_0 t ht
    · exact node_edge10_1 t ht
    · exact node_edge10_2 t ht
    · exact node_edge10_3 t ht
    · exact node_edge11_0 t ht
    · exact node_edge11_1 t ht
    · exact node_edge11_2 t ht
    · exact node_edge11_3 t ht
    · exact node_edge12_0 t ht
    · exact node_edge12_1 t ht
    · exact node_edge12_2 t ht
    · exact node_edge12_3 t ht
    · exact node_edge13_0 t ht
    · exact node_edge13_1 t ht
    · exact node_edge13_2 t ht
    · exact node_edge13_3 t ht
    · exact node_edge14_0 t ht
    · exact node_edge14_1 t ht
    · exact node_edge14_2 t ht
    · exact node_edge14_3 t ht
    · exact node_edge15_0 t ht
    · exact node_edge15_1 t ht
    · exact node_edge15_2 t ht
    · exact node_edge15_3 t ht
  | base i =>
    have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 ∨ i=15 ∨ i=16 ∨ i=17 ∨ i=18 ∨ i=19 ∨ i=20 ∨ i=21 ∨ i=22 ∨ i=23 ∨ i=24 ∨ i=25 ∨ i=26 ∨ i=27 ∨ i=28 ∨ i=29 ∨ i=30 ∨ i=31 ∨ i=32 ∨ i=33 ∨ i=34 ∨ i=35 ∨ i=36 ∨ i=37 ∨ i=38 ∨ i=39 ∨ i=40 ∨ i=41 ∨ i=42 ∨ i=43 ∨ i=44 ∨ i=45 ∨ i=46 ∨ i=47 ∨ i=48 ∨ i=49 ∨ i=50 ∨ i=51 ∨ i=52 ∨ i=53 ∨ i=54 ∨ i=55 ∨ i=56 ∨ i=57 ∨ i=58 := by omega
    intro k
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rcases fin4 k with rfl|rfl|rfl|rfl
    · exact base_edge0_0
    · exact base_edge0_1
    · exact base_edge0_2
    · exact base_edge0_3
    · exact base_edge1_0
    · exact base_edge1_1
    · exact base_edge1_2
    · exact base_edge1_3
    · exact base_edge2_0
    · exact base_edge2_1
    · exact base_edge2_2
    · exact base_edge2_3
    · exact base_edge3_0
    · exact base_edge3_1
    · exact base_edge3_2
    · exact base_edge3_3
    · exact base_edge4_0
    · exact base_edge4_1
    · exact base_edge4_2
    · exact base_edge4_3
    · exact base_edge5_0
    · exact base_edge5_1
    · exact base_edge5_2
    · exact base_edge5_3
    · exact base_edge6_0
    · exact base_edge6_1
    · exact base_edge6_2
    · exact base_edge6_3
    · exact base_edge7_0
    · exact base_edge7_1
    · exact base_edge7_2
    · exact base_edge7_3
    · exact base_edge8_0
    · exact base_edge8_1
    · exact base_edge8_2
    · exact base_edge8_3
    · exact base_edge9_0
    · exact base_edge9_1
    · exact base_edge9_2
    · exact base_edge9_3
    · exact base_edge10_0
    · exact base_edge10_1
    · exact base_edge10_2
    · exact base_edge10_3
    · exact base_edge11_0
    · exact base_edge11_1
    · exact base_edge11_2
    · exact base_edge11_3
    · exact base_edge12_0
    · exact base_edge12_1
    · exact base_edge12_2
    · exact base_edge12_3
    · exact base_edge13_0
    · exact base_edge13_1
    · exact base_edge13_2
    · exact base_edge13_3
    · exact base_edge14_0
    · exact base_edge14_1
    · exact base_edge14_2
    · exact base_edge14_3
    · exact base_edge15_0
    · exact base_edge15_1
    · exact base_edge15_2
    · exact base_edge15_3
    · exact base_edge16_0
    · exact base_edge16_1
    · exact base_edge16_2
    · exact base_edge16_3
    · exact base_edge17_0
    · exact base_edge17_1
    · exact base_edge17_2
    · exact base_edge17_3
    · exact base_edge18_0
    · exact base_edge18_1
    · exact base_edge18_2
    · exact base_edge18_3
    · exact base_edge19_0
    · exact base_edge19_1
    · exact base_edge19_2
    · exact base_edge19_3
    · exact base_edge20_0
    · exact base_edge20_1
    · exact base_edge20_2
    · exact base_edge20_3
    · exact base_edge21_0
    · exact base_edge21_1
    · exact base_edge21_2
    · exact base_edge21_3
    · exact base_edge22_0
    · exact base_edge22_1
    · exact base_edge22_2
    · exact base_edge22_3
    · exact base_edge23_0
    · exact base_edge23_1
    · exact base_edge23_2
    · exact base_edge23_3
    · exact base_edge24_0
    · exact base_edge24_1
    · exact base_edge24_2
    · exact base_edge24_3
    · exact base_edge25_0
    · exact base_edge25_1
    · exact base_edge25_2
    · exact base_edge25_3
    · exact base_edge26_0
    · exact base_edge26_1
    · exact base_edge26_2
    · exact base_edge26_3
    · exact base_edge27_0
    · exact base_edge27_1
    · exact base_edge27_2
    · exact base_edge27_3
    · exact base_edge28_0
    · exact base_edge28_1
    · exact base_edge28_2
    · exact base_edge28_3
    · exact base_edge29_0
    · exact base_edge29_1
    · exact base_edge29_2
    · exact base_edge29_3
    · exact base_edge30_0
    · exact base_edge30_1
    · exact base_edge30_2
    · exact base_edge30_3
    · exact base_edge31_0
    · exact base_edge31_1
    · exact base_edge31_2
    · exact base_edge31_3
    · exact base_edge32_0
    · exact base_edge32_1
    · exact base_edge32_2
    · exact base_edge32_3
    · exact base_edge33_0
    · exact base_edge33_1
    · exact base_edge33_2
    · exact base_edge33_3
    · exact base_edge34_0
    · exact base_edge34_1
    · exact base_edge34_2
    · exact base_edge34_3
    · exact base_edge35_0
    · exact base_edge35_1
    · exact base_edge35_2
    · exact base_edge35_3
    · exact base_edge36_0
    · exact base_edge36_1
    · exact base_edge36_2
    · exact base_edge36_3
    · exact base_edge37_0
    · exact base_edge37_1
    · exact base_edge37_2
    · exact base_edge37_3
    · exact base_edge38_0
    · exact base_edge38_1
    · exact base_edge38_2
    · exact base_edge38_3
    · exact base_edge39_0
    · exact base_edge39_1
    · exact base_edge39_2
    · exact base_edge39_3
    · exact base_edge40_0
    · exact base_edge40_1
    · exact base_edge40_2
    · exact base_edge40_3
    · exact base_edge41_0
    · exact base_edge41_1
    · exact base_edge41_2
    · exact base_edge41_3
    · exact base_edge42_0
    · exact base_edge42_1
    · exact base_edge42_2
    · exact base_edge42_3
    · exact base_edge43_0
    · exact base_edge43_1
    · exact base_edge43_2
    · exact base_edge43_3
    · exact base_edge44_0
    · exact base_edge44_1
    · exact base_edge44_2
    · exact base_edge44_3
    · exact base_edge45_0
    · exact base_edge45_1
    · exact base_edge45_2
    · exact base_edge45_3
    · exact base_edge46_0
    · exact base_edge46_1
    · exact base_edge46_2
    · exact base_edge46_3
    · exact base_edge47_0
    · exact base_edge47_1
    · exact base_edge47_2
    · exact base_edge47_3
    · exact base_edge48_0
    · exact base_edge48_1
    · exact base_edge48_2
    · exact base_edge48_3
    · exact base_edge49_0
    · exact base_edge49_1
    · exact base_edge49_2
    · exact base_edge49_3
    · exact base_edge50_0
    · exact base_edge50_1
    · exact base_edge50_2
    · exact base_edge50_3
    · exact base_edge51_0
    · exact base_edge51_1
    · exact base_edge51_2
    · exact base_edge51_3
    · exact base_edge52_0
    · exact base_edge52_1
    · exact base_edge52_2
    · exact base_edge52_3
    · exact base_edge53_0
    · exact base_edge53_1
    · exact base_edge53_2
    · exact base_edge53_3
    · exact base_edge54_0
    · exact base_edge54_1
    · exact base_edge54_2
    · exact base_edge54_3
    · exact base_edge55_0
    · exact base_edge55_1
    · exact base_edge55_2
    · exact base_edge55_3
    · exact base_edge56_0
    · exact base_edge56_1
    · exact base_edge56_2
    · exact base_edge56_3
    · exact base_edge57_0
    · exact base_edge57_1
    · exact base_edge57_2
    · exact base_edge57_3
    · exact base_edge58_0
    · exact base_edge58_1
    · exact base_edge58_2
    · exact base_edge58_3
theorem core_NMA {B : Matrix 4} (hB : Core B) : ¬MutationAcyclic B :=
  safe_NMA data rules Core core_skew core_cyclic core_edges (Safe.central hB)

theorem nma_q184 : ¬MutationAcyclic (ofSix (-2) (-2) (1) (-1) (-1) (1)) := by
  have he : ofSix (-2) (-2) (1) (-1) (-1) (1) = (relabel (base 0) perm0.symm) := by funext a b; revert a b; decide
  rw [he]
  exact safe_NMA data rules Core core_skew core_cyclic core_edges
    (Safe.framed (base_safe 0) perm0.symm)

theorem nma_q197 : ¬MutationAcyclic (ofSix (-2) (-2) (1) (-1) (2) (-1)) := by
  have he : ofSix (-2) (-2) (1) (-1) (2) (-1) = (relabel (base 25) perm0.symm) := by funext a b; revert a b; decide
  rw [he]
  exact safe_NMA data rules Core core_skew core_cyclic core_edges
    (Safe.framed (base_safe 25) perm0.symm)

theorem nma_q268 : ¬MutationAcyclic (ofSix (-2) (-1) (-1) (-2) (1) (-1)) := by
  have he : ofSix (-2) (-1) (-1) (-2) (1) (-1) = (relabel (base 14) perm0.symm) := by funext a b; revert a b; decide
  rw [he]
  exact safe_NMA data rules Core core_skew core_cyclic core_edges
    (Safe.framed (base_safe 14) perm0.symm)

theorem nma_q290 : ¬MutationAcyclic (ofSix (-2) (-1) (-1) (-1) (2) (-1)) := by
  have he : ofSix (-2) (-1) (-1) (-1) (2) (-1) = (reverse (relabel (base 0) perm10.symm)) := by funext a b; revert a b; decide
  rw [he]
  exact safe_NMA data rules Core core_skew core_cyclic core_edges
    (Safe.reversed (Safe.framed (base_safe 0) perm10.symm))

theorem nma_q420 : ¬MutationAcyclic (ofSix (-2) (-1) (1) (-2) (-1) (1)) := by
  have he : ofSix (-2) (-1) (1) (-2) (-1) (1) = (reverse (relabel (base 14) perm14.symm)) := by funext a b; revert a b; decide
  rw [he]
  exact safe_NMA data rules Core core_skew core_cyclic core_edges
    (Safe.reversed (Safe.framed (base_safe 14) perm14.symm))

end QuiverProofs.Q184Corridor
