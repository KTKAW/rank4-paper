import QuiverProofs.QFamilyPolynomialInterfaces
namespace QuiverProofs.Rank4StructureRound2.RFamily
open PolynomialCertificate QFamilyPolynomialInterfaces RecursiveRegions Forks Regions
set_option maxHeartbeats 12000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
def perm0 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | _ => 3),(fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | _ => 3),by decide,by decide⟩
def perm1 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | _ => 2),(fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | _ => 2),by decide,by decide⟩
def perm2 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | _ => 3),(fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | _ => 3),by decide,by decide⟩
def perm3 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | _ => 1),(fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | _ => 2),by decide,by decide⟩
def perm4 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | _ => 2),(fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | _ => 1),by decide,by decide⟩
def perm5 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | _ => 1),(fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | _ => 1),by decide,by decide⟩
def perm6 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | _ => 3),(fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | _ => 3),by decide,by decide⟩
def perm7 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | _ => 2),(fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | _ => 2),by decide,by decide⟩
def perm8 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 0 | _ => 3),(fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 1 | _ => 3),by decide,by decide⟩
def perm9 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | _ => 0),(fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | _ => 2),by decide,by decide⟩
def perm10 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 0 | _ => 2),(fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 3 | _ => 1),by decide,by decide⟩
def perm11 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | _ => 0),(fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | _ => 1),by decide,by decide⟩
def perm12 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 1 | _ => 3),(fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 0 | _ => 3),by decide,by decide⟩
def perm13 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 3 | _ => 1),(fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 0 | _ => 2),by decide,by decide⟩
def perm14 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | _ => 3),(fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | _ => 3),by decide,by decide⟩
def perm15 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 3 | _ => 0),(fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 0 | _ => 2),by decide,by decide⟩
def perm16 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | _ => 1),(fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | _ => 1),by decide,by decide⟩
def perm17 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | _ => 0),(fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | _ => 1),by decide,by decide⟩
def perm18 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | _ => 2),(fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | _ => 0),by decide,by decide⟩
def perm19 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | _ => 1),(fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | _ => 0),by decide,by decide⟩
def perm20 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 0 | _ => 2),(fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 3 | _ => 0),by decide,by decide⟩
def perm21 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | _ => 0),(fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | _ => 0),by decide,by decide⟩
def perm22 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | _ => 1),(fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | _ => 0),by decide,by decide⟩
def perm23 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | _ => 0),(fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | _ => 0),by decide,by decide⟩

namespace Boundary2
private theorem finCore (i : Fin 27) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 ∨ i=15 ∨ i=16 ∨ i=17 ∨ i=18 ∨ i=19 ∨ i=20 ∨ i=21 ∨ i=22 ∨ i=23 ∨ i=24 ∨ i=25 ∨ i=26 := by omega

def pnode (i : Fin 27) : PMatrix := match i.val with
  | 0 => six [] [1] [-2] [2] [-2] [3]
  | 1 => six [] [-1] [2] [2] [-2] [1]
  | 2 => six [] [-1] [1] [-2] [4] [-3]
  | 3 => six [4] [-1] [-2] [] [2] [-1]
  | 4 => six [] [-1] [1] [2] [-4] [5]
  | 5 => six [] [2] [-1] [10] [-4] [3]
  | 6 => six [-4] [1] [2] [-4] [-6] [-1]
  | 7 => six [-4] [-1] [6] [] [-2] [-1]
  | 8 => six [-2] [1] [1] [-2] [6] [-5]
  | 9 => six [4] [-1] [-1] [-18] [4] [-5]
  | 10 => six [] [-2] [1] [10] [-4] [1]
  | 11 => six [8] [3] [-2] [-4] [6] [1]
  | 12 => six [4] [1] [-6] [] [22] [5]
  | 13 => six [8] [5] [-6] [] [2] [1]
  | 14 => six [2] [-1] [-1] [] [8] [-5]
  | 15 => six [-2] [6] [-1] [28] [-6] [5]
  | 16 => six [-4] [1] [1] [-22] [] [-5]
  | 17 => six [4] [1] [-6] [18] [-86] [5]
  | 18 => six [-20] [2] [1] [-10] [6] [-1]
  | 19 => six [20] [-3] [1] [4] [6] [-1]
  | 20 => six [-6] [-1] [1] [40] [-8] [5]
  | 21 => six [2] [-6] [1] [40] [-6] [-1]
  | 22 => six [18] [-1] [1] [22] [-110] [5]
  | 23 => six [-4] [-1] [6] [18] [-110] [-1]
  | 24 => six [6] [2] [-1] [56] [-20] [3]
  | 25 => six [40] [1] [-6] [-6] [238] [5]
  | _ => six [-110] [6] [-1] [-656] [18] [5]

def node (t : Int) (i : Fin 27) : Matrix 4 := matrix (pnode i) t
def Core (t : Int) (B : Matrix 4) : Prop := ∃ i, B=node t i
abbrev SafeCore (t : Int) := Safe data (Core t)
theorem node_safe (t : Int) (i : Fin 27) : SafeCore t (node t i) := Safe.central ⟨i,rfl⟩

def param0_0 : P := [2]
def param0_1 : P := [20]
def param0_2 : P := [6]
def param0_3 : P := [10]
theorem domain0 (t : Int) (ht : 0≤t) : GenericStrip.Domain (eval param0_0 t) (eval param0_1 t) (eval param0_2 t) (eval param0_3 t) :=
  generic_domain param0_0 param0_1 param0_2 param0_3 t ht (by decide)

def region0 (t : Int) (ht : 0≤t) : Region := .inl (.inl ⟨eval param0_0 t,⟨eval param0_1 t,eval param0_2 t,eval param0_3 t⟩,domain0 t ht⟩)

theorem parent0_0 (t : Int) (ht : 0≤t) :
    data.parent (region0 t ht) (0 : Fin 3)=(relabel (node t 19) perm5.symm) := by
  have he := mutation_equal (generic param0_0 param0_1 param0_2 param0_3 0) (prelabel (pnode 19) perm5.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent0_1 (t : Int) (ht : 0≤t) :
    data.parent (region0 t ht) (1 : Fin 3)=(reverse (relabel (node t 10) perm5.symm)) := by
  have he := mutation_equal (generic param0_0 param0_1 param0_2 param0_3 0) (preverse (prelabel (pnode 10) perm5.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent0_2 (t : Int) (ht : 0≤t) :
    data.parent (region0 t ht) (2 : Fin 3)=(reverse (relabel (node t 24) perm5.symm)) := by
  have he := mutation_equal (generic param0_0 param0_1 param0_2 param0_3 2) (preverse (prelabel (pnode 24) perm5.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parents0_safe (t : Int) (ht : 0≤t) (p : Fin 3) :
    SafeCore t (data.parent (region0 t ht) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hp with rfl|rfl|rfl
  · rw [parent0_0 t ht]
    exact Safe.framed (node_safe t 19) perm5.symm
  · rw [parent0_1 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 10) perm5.symm)
  · rw [parent0_2 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 24) perm5.symm)

theorem region0_safe (t : Int) (ht : 0≤t) (i : Fin 3) :
    SafeCore t (matrix (generic param0_0 param0_1 param0_2 param0_3 i) t) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core t) (region0 t ht) (parents0_safe t ht) (0,Fin.castLE (by decide) i)

def param1_0 : P := [5]
def param1_1 : P := [40]
def param1_2 : P := [6]
def param1_3 : P := [8]
theorem domain1 (t : Int) (ht : 0≤t) : GenericStrip.Domain (eval param1_0 t) (eval param1_1 t) (eval param1_2 t) (eval param1_3 t) :=
  generic_domain param1_0 param1_1 param1_2 param1_3 t ht (by decide)

def region1 (t : Int) (ht : 0≤t) : Region := .inl (.inl ⟨eval param1_0 t,⟨eval param1_1 t,eval param1_2 t,eval param1_3 t⟩,domain1 t ht⟩)

theorem parent1_0 (t : Int) (ht : 0≤t) :
    data.parent (region1 t ht) (0 : Fin 3)=(reverse (relabel (node t 21) perm16.symm)) := by
  have he := mutation_equal (generic param1_0 param1_1 param1_2 param1_3 0) (preverse (prelabel (pnode 21) perm16.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent1_1 (t : Int) (ht : 0≤t) :
    data.parent (region1 t ht) (1 : Fin 3)=(reverse (relabel (node t 14) perm10.symm)) := by
  have he := mutation_equal (generic param1_0 param1_1 param1_2 param1_3 0) (preverse (prelabel (pnode 14) perm10.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent1_2 (t : Int) (ht : 0≤t) :
    data.parent (region1 t ht) (2 : Fin 3)=(reverse (relabel (node t 25) perm10.symm)) := by
  have he := mutation_equal (generic param1_0 param1_1 param1_2 param1_3 2) (preverse (prelabel (pnode 25) perm10.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parents1_safe (t : Int) (ht : 0≤t) (p : Fin 3) :
    SafeCore t (data.parent (region1 t ht) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hp with rfl|rfl|rfl
  · rw [parent1_0 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 21) perm16.symm)
  · rw [parent1_1 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 14) perm10.symm)
  · rw [parent1_2 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 25) perm10.symm)

theorem region1_safe (t : Int) (ht : 0≤t) (i : Fin 3) :
    SafeCore t (matrix (generic param1_0 param1_1 param1_2 param1_3 i) t) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core t) (region1 t ht) (parents1_safe t ht) (0,Fin.castLE (by decide) i)

def param2_0 : P := [5]
def param2_1 : P := [110]
def param2_2 : P := [18]
def param2_3 : P := [22]
theorem domain2 (t : Int) (ht : 0≤t) : GenericStrip.Domain (eval param2_0 t) (eval param2_1 t) (eval param2_2 t) (eval param2_3 t) :=
  generic_domain param2_0 param2_1 param2_2 param2_3 t ht (by decide)

def region2 (t : Int) (ht : 0≤t) : Region := .inl (.inl ⟨eval param2_0 t,⟨eval param2_1 t,eval param2_2 t,eval param2_3 t⟩,domain2 t ht⟩)

theorem parent2_0 (t : Int) (ht : 0≤t) :
    data.parent (region2 t ht) (0 : Fin 3)=(relabel (node t 23) perm17.symm) := by
  have he := mutation_equal (generic param2_0 param2_1 param2_2 param2_3 0) (prelabel (pnode 23) perm17.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent2_1 (t : Int) (ht : 0≤t) :
    data.parent (region2 t ht) (1 : Fin 3)=(relabel (node t 16) perm11.symm) := by
  have he := mutation_equal (generic param2_0 param2_1 param2_2 param2_3 0) (prelabel (pnode 16) perm11.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent2_2 (t : Int) (ht : 0≤t) :
    data.parent (region2 t ht) (2 : Fin 3)=(relabel (node t 26) perm11.symm) := by
  have he := mutation_equal (generic param2_0 param2_1 param2_2 param2_3 2) (prelabel (pnode 26) perm11.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parents2_safe (t : Int) (ht : 0≤t) (p : Fin 3) :
    SafeCore t (data.parent (region2 t ht) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hp with rfl|rfl|rfl
  · rw [parent2_0 t ht]
    exact Safe.framed (node_safe t 23) perm17.symm
  · rw [parent2_1 t ht]
    exact Safe.framed (node_safe t 16) perm11.symm
  · rw [parent2_2 t ht]
    exact Safe.framed (node_safe t 26) perm11.symm

theorem region2_safe (t : Int) (ht : 0≤t) (i : Fin 3) :
    SafeCore t (matrix (generic param2_0 param2_1 param2_2 param2_3 i) t) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core t) (region2 t ht) (parents2_safe t ht) (0,Fin.castLE (by decide) i)

def param3_0 : P := [4]
def param3_1 : P := [2]
def param3_2 : P := [10]
def param3_3 : P := [37]
theorem domain3 (t : Int) (ht : 0≤t) : UnitZeroStrip.Domain (eval param3_0 t) (eval param3_1 t) (eval param3_2 t) (eval param3_3 t) :=
  zero_domain param3_0 param3_1 param3_2 param3_3 t ht (by decide)

def region3 (t : Int) (ht : 0≤t) : Region := .inl (.inr (.n (eval param3_0 t) ⟨eval param3_1 t,eval param3_2 t,eval param3_3 t⟩ (domain3 t ht)))

theorem parent3_0 (t : Int) (ht : 0≤t) :
    data.parent (region3 t ht) (0 : Fin 2)=(reverse (relabel (node t 5) perm0.symm)) := by
  have he := mutation_equal (zero param3_0 param3_1 param3_2 param3_3 0) (preverse (prelabel (pnode 5) perm0.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,zero_eval] at he
  exact he

theorem parent3_1 (t : Int) (ht : 0≤t) :
    data.parent (region3 t ht) (1 : Fin 2)=(reverse (relabel (node t 10) perm0.symm)) := by
  have he := mutation_equal (zero param3_0 param3_1 param3_2 param3_3 1) (preverse (prelabel (pnode 10) perm0.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,zero_eval] at he
  exact he

theorem parents3_safe (t : Int) (ht : 0≤t) (p : Fin 2) :
    SafeCore t (data.parent (region3 t ht) p) := by
  have hp : p=0 ∨ p=1 := by change p=(0 : Fin 2) ∨ p=(1 : Fin 2); omega
  rcases hp with rfl|rfl
  · rw [parent3_0 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 5) perm0.symm)
  · rw [parent3_1 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 10) perm0.symm)

theorem region3_safe (t : Int) (ht : 0≤t) (i : Fin 2) :
    SafeCore t (matrix (zero param3_0 param3_1 param3_2 param3_3 i) t) := by
  rw [zero_eval]
  exact Safe.region (D:=data) (core:=Core t) (region3 t ht) (parents3_safe t ht) (0,Fin.castLE (by decide) i)

def param4_0 : P := [4]
def param4_1 : P := [5]
def param4_2 : P := [22]
def param4_3 : P := [82]
theorem domain4 (t : Int) (ht : 0≤t) : UnitZeroStrip.Domain (eval param4_0 t) (eval param4_1 t) (eval param4_2 t) (eval param4_3 t) :=
  zero_domain param4_0 param4_1 param4_2 param4_3 t ht (by decide)

def region4 (t : Int) (ht : 0≤t) : Region := .inl (.inr (.n (eval param4_0 t) ⟨eval param4_1 t,eval param4_2 t,eval param4_3 t⟩ (domain4 t ht)))

theorem parent4_0 (t : Int) (ht : 0≤t) :
    data.parent (region4 t ht) (0 : Fin 2)=(reverse (relabel (node t 12) perm20.symm)) := by
  have he := mutation_equal (zero param4_0 param4_1 param4_2 param4_3 0) (preverse (prelabel (pnode 12) perm20.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,zero_eval] at he
  exact he

theorem parent4_1 (t : Int) (ht : 0≤t) :
    data.parent (region4 t ht) (1 : Fin 2)=(relabel (node t 16) perm21.symm) := by
  have he := mutation_equal (zero param4_0 param4_1 param4_2 param4_3 1) (prelabel (pnode 16) perm21.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,zero_eval] at he
  exact he

theorem parents4_safe (t : Int) (ht : 0≤t) (p : Fin 2) :
    SafeCore t (data.parent (region4 t ht) p) := by
  have hp : p=0 ∨ p=1 := by change p=(0 : Fin 2) ∨ p=(1 : Fin 2); omega
  rcases hp with rfl|rfl
  · rw [parent4_0 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 12) perm20.symm)
  · rw [parent4_1 t ht]
    exact Safe.framed (node_safe t 16) perm21.symm

theorem region4_safe (t : Int) (ht : 0≤t) (i : Fin 2) :
    SafeCore t (matrix (zero param4_0 param4_1 param4_2 param4_3 i) t) := by
  rw [zero_eval]
  exact Safe.region (D:=data) (core:=Core t) (region4 t ht) (parents4_safe t ht) (0,Fin.castLE (by decide) i)

def param5_0 : P := [2]
def param5_1 : P := [5]
def param5_2 : P := [8]
def param5_3 : P := [10]
theorem domain5 (t : Int) (ht : 0≤t) : UnitZeroStrip.Domain (eval param5_0 t) (eval param5_1 t) (eval param5_2 t) (eval param5_3 t) :=
  zero_domain param5_0 param5_1 param5_2 param5_3 t ht (by decide)

def region5 (t : Int) (ht : 0≤t) : Region := .inl (.inr (.n (eval param5_0 t) ⟨eval param5_1 t,eval param5_2 t,eval param5_3 t⟩ (domain5 t ht)))

theorem parent5_0 (t : Int) (ht : 0≤t) :
    data.parent (region5 t ht) (0 : Fin 2)=(relabel (node t 13) perm14.symm) := by
  have he := mutation_equal (zero param5_0 param5_1 param5_2 param5_3 0) (prelabel (pnode 13) perm14.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,zero_eval] at he
  exact he

theorem parent5_1 (t : Int) (ht : 0≤t) :
    data.parent (region5 t ht) (1 : Fin 2)=(reverse (relabel (node t 14) perm20.symm)) := by
  have he := mutation_equal (zero param5_0 param5_1 param5_2 param5_3 1) (preverse (prelabel (pnode 14) perm20.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,zero_eval] at he
  exact he

theorem parents5_safe (t : Int) (ht : 0≤t) (p : Fin 2) :
    SafeCore t (data.parent (region5 t ht) p) := by
  have hp : p=0 ∨ p=1 := by change p=(0 : Fin 2) ∨ p=(1 : Fin 2); omega
  rcases hp with rfl|rfl
  · rw [parent5_0 t ht]
    exact Safe.framed (node_safe t 13) perm14.symm
  · rw [parent5_1 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 14) perm20.symm)

theorem region5_safe (t : Int) (ht : 0≤t) (i : Fin 2) :
    SafeCore t (matrix (zero param5_0 param5_1 param5_2 param5_3 i) t) := by
  rw [zero_eval]
  exact Safe.region (D:=data) (core:=Core t) (region5 t ht) (parents5_safe t ht) (0,Fin.castLE (by decide) i)

theorem node_skew (t : Int) (i : Fin 27) : SkewSymmetric (node t i) := by
  rcases finCore i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp only [node,pnode,matrix_six] <;> exact ofSix_skew _ _ _ _ _ _

theorem cyclic0 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 0) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 0 0 2) t ht (by decide))
  have h1 := hr 2 3 (pos (pnode 0 2 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 0 3 0) t ht (by decide))
  omega

theorem cyclic1 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 1) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 1 2 (pos (pnode 1 1 2) t ht (by decide))
  have h1 := hr 2 3 (pos (pnode 1 2 3) t ht (by decide))
  have h2 := hr 3 1 (pos (pnode 1 3 1) t ht (by decide))
  omega

theorem cyclic2 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 2) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 2 0 3) t ht (by decide))
  have h1 := hr 3 2 (pos (pnode 2 3 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 2 2 0) t ht (by decide))
  omega

theorem cyclic3 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 3) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 3 0 1) t ht (by decide))
  have h1 := hr 1 3 (pos (pnode 3 1 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 3 3 0) t ht (by decide))
  omega

theorem cyclic4 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 4) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 1 2 (pos (pnode 4 1 2) t ht (by decide))
  have h1 := hr 2 3 (pos (pnode 4 2 3) t ht (by decide))
  have h2 := hr 3 1 (pos (pnode 4 3 1) t ht (by decide))
  omega

theorem cyclic5 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 5) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 5 0 2) t ht (by decide))
  have h1 := hr 2 3 (pos (pnode 5 2 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 5 3 0) t ht (by decide))
  omega

theorem cyclic6 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 6) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 6 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 6 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 6 1 0) t ht (by decide))
  omega

theorem cyclic7 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 7) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 7 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (pnode 7 3 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 7 1 0) t ht (by decide))
  omega

theorem cyclic8 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 8) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 8 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 8 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 8 1 0) t ht (by decide))
  omega

theorem cyclic9 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 9) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 9 0 1) t ht (by decide))
  have h1 := hr 1 3 (pos (pnode 9 1 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 9 3 0) t ht (by decide))
  omega

theorem cyclic10 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 10) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 1 2 (pos (pnode 10 1 2) t ht (by decide))
  have h1 := hr 2 3 (pos (pnode 10 2 3) t ht (by decide))
  have h2 := hr 3 1 (pos (pnode 10 3 1) t ht (by decide))
  omega

theorem cyclic11 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 11) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 11 0 1) t ht (by decide))
  have h1 := hr 1 3 (pos (pnode 11 1 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 11 3 0) t ht (by decide))
  omega

theorem cyclic12 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 12) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 12 0 1) t ht (by decide))
  have h1 := hr 1 3 (pos (pnode 12 1 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 12 3 0) t ht (by decide))
  omega

theorem cyclic13 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 13) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 13 0 1) t ht (by decide))
  have h1 := hr 1 3 (pos (pnode 13 1 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 13 3 0) t ht (by decide))
  omega

theorem cyclic14 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 14) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 14 0 1) t ht (by decide))
  have h1 := hr 1 3 (pos (pnode 14 1 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 14 3 0) t ht (by decide))
  omega

theorem cyclic15 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 15) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 15 0 2) t ht (by decide))
  have h1 := hr 2 3 (pos (pnode 15 2 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 15 3 0) t ht (by decide))
  omega

theorem cyclic16 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 16) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 16 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 16 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 16 1 0) t ht (by decide))
  omega

theorem cyclic17 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 17) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 17 0 2) t ht (by decide))
  have h1 := hr 2 3 (pos (pnode 17 2 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 17 3 0) t ht (by decide))
  omega

theorem cyclic18 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 18) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 18 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 18 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 18 1 0) t ht (by decide))
  omega

theorem cyclic19 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 19) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 19 0 1) t ht (by decide))
  have h1 := hr 1 2 (pos (pnode 19 1 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 19 2 0) t ht (by decide))
  omega

theorem cyclic20 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 20) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 20 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (pnode 20 3 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 20 1 0) t ht (by decide))
  omega

theorem cyclic21 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 21) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 21 0 1) t ht (by decide))
  have h1 := hr 1 2 (pos (pnode 21 1 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 21 2 0) t ht (by decide))
  omega

theorem cyclic22 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 22) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 22 0 1) t ht (by decide))
  have h1 := hr 1 2 (pos (pnode 22 1 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 22 2 0) t ht (by decide))
  omega

theorem cyclic23 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 23) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 23 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (pnode 23 3 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 23 1 0) t ht (by decide))
  omega

theorem cyclic24 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 24) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 24 0 2) t ht (by decide))
  have h1 := hr 2 3 (pos (pnode 24 2 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 24 3 0) t ht (by decide))
  omega

theorem cyclic25 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 25) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 25 0 1) t ht (by decide))
  have h1 := hr 1 3 (pos (pnode 25 1 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 25 3 0) t ht (by decide))
  omega

theorem cyclic26 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 26) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 26 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 26 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 26 1 0) t ht (by decide))
  omega

theorem edge0_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 0) 0) := by
  have he := mutation_equal (pnode 0) (prelabel (pnode 1) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 0) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 1) perm0.symm

theorem edge0_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 0) 1) := by
  have he := mutation_equal (pnode 0) (preverse (prelabel (pnode 1) perm0.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 0) t) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (node_safe t 1) perm0.symm)

theorem edge0_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 0) 2) := by
  have he := mutation_equal (pnode 0) (prelabel (pnode 2) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 0) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 2) perm0.symm

theorem edge0_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 0) 3) := by
  have he := mutation_equal (pnode 0) (prelabel (root [3] [5] [4] [2] [2] []) perm22.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 0) 3
  rw [show mutate (node t 0) 3=(relabel (matrix (root [3] [5] [4] [2] [2] []) t) perm22.symm) from he]
  exact IsRoot.relabelled (root_sound [3] [5] [4] [2] [2] [] t ht (by decide)) perm22.symm

theorem edge1_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 1) 0) := by
  have he := mutation_equal (pnode 1) (prelabel (pnode 0) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 1) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 0) perm0.symm

theorem edge1_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 1) 1) := by
  have he := mutation_equal (pnode 1) (preverse (prelabel (pnode 0) perm0.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 1) t) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (node_safe t 0) perm0.symm)

theorem edge1_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 1) 2) := by
  have he := mutation_equal (pnode 1) (preverse (prelabel (pnode 1) perm21.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 1) t) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (node_safe t 1) perm21.symm)

theorem edge1_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 1) 3) := by
  have he := mutation_equal (pnode 1) (prelabel (pnode 3) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 1) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 3) perm0.symm

theorem edge2_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 2) 0) := by
  have he := mutation_equal (pnode 2) (preverse (prelabel (pnode 3) perm20.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 2) t) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (node_safe t 3) perm20.symm)

theorem edge2_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 2) 1) := by
  have he := mutation_equal (pnode 2) (prelabel (pnode 4) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 2) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 4) perm0.symm

theorem edge2_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 2) 2) := by
  have he := mutation_equal (pnode 2) (prelabel (pnode 0) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 2) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 0) perm0.symm

theorem edge2_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 2) 3) := by
  have he := mutation_equal (pnode 2) (prelabel (pnode 5) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 2) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 5) perm0.symm

theorem edge3_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 3) 0) := by
  have he := mutation_equal (pnode 3) (prelabel (pnode 6) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 3) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 6) perm0.symm

theorem edge3_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 3) 1) := by
  have he := mutation_equal (pnode 3) (prelabel (pnode 7) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 3) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 7) perm0.symm

theorem edge3_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 3) 2) := by
  have he := mutation_equal (pnode 3) (preverse (prelabel (pnode 2) perm15.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 3) t) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (node_safe t 2) perm15.symm)

theorem edge3_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 3) 3) := by
  have he := mutation_equal (pnode 3) (prelabel (pnode 1) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 3) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 1) perm0.symm

theorem edge4_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 4) 0) := by
  have he := mutation_equal (pnode 4) (preverse (prelabel (pnode 7) perm20.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 4) t) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (node_safe t 7) perm20.symm)

theorem edge4_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 4) 1) := by
  have he := mutation_equal (pnode 4) (prelabel (pnode 2) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 4) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 2) perm0.symm

theorem edge4_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 4) 2) := by
  have he := mutation_equal (pnode 4) (prelabel (pnode 8) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 4) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 8) perm0.symm

theorem edge4_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 4) 3) := by
  have he := mutation_equal (pnode 4) (prelabel (pnode 9) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 4) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 9) perm0.symm

theorem edge5_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 5) 0) := by
  have he := mutation_equal (pnode 5) (prelabel (pnode 10) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 5) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 10) perm0.symm

theorem edge5_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 5) 1) := by
  have he := mutation_equal (pnode 5) (preverse (prelabel (zero param3_0 param3_1 param3_2 param3_3 0) perm0.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 5) t) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (region3_safe t ht 0) perm0.symm)

theorem edge5_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 5) 2) := by
  have he := mutation_equal (pnode 5) (preverse (prelabel (root [3] [5] [26] [2] [10] []) perm16.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 5) 2
  rw [show mutate (node t 5) 2=(reverse (relabel (matrix (root [3] [5] [26] [2] [10] []) t) perm16.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [3] [5] [26] [2] [10] [] t ht (by decide)) perm16.symm)

theorem edge5_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 5) 3) := by
  have he := mutation_equal (pnode 5) (prelabel (pnode 2) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 5) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 2) perm0.symm

theorem edge6_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 6) 0) := by
  have he := mutation_equal (pnode 6) (prelabel (pnode 3) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 6) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 3) perm0.symm

theorem edge6_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 6) 1) := by
  have he := mutation_equal (pnode 6) (preverse (prelabel (root [4] [15] [22] [4] [6] [1]) perm6.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 6) 1
  rw [show mutate (node t 6) 1=(reverse (relabel (matrix (root [4] [15] [22] [4] [6] [1]) t) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [4] [15] [22] [4] [6] [1] t ht (by decide)) perm6.symm)

theorem edge6_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 6) 2) := by
  have he := mutation_equal (pnode 6) (preverse (prelabel (pnode 10) perm1.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 6) t) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (node_safe t 10) perm1.symm)

theorem edge6_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 6) 3) := by
  have he := mutation_equal (pnode 6) (prelabel (pnode 11) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 6) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 11) perm0.symm

theorem edge7_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 7) 0) := by
  have he := mutation_equal (pnode 7) (prelabel (pnode 12) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 7) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 12) perm0.symm

theorem edge7_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 7) 1) := by
  have he := mutation_equal (pnode 7) (prelabel (pnode 3) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 7) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 3) perm0.symm

theorem edge7_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 7) 2) := by
  have he := mutation_equal (pnode 7) (preverse (prelabel (pnode 4) perm15.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 7) t) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (node_safe t 4) perm15.symm)

theorem edge7_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 7) 3) := by
  have he := mutation_equal (pnode 7) (prelabel (pnode 13) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 7) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 13) perm0.symm

theorem edge8_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 8) 0) := by
  have he := mutation_equal (pnode 8) (prelabel (pnode 14) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 8) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 14) perm0.symm

theorem edge8_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 8) 1) := by
  have he := mutation_equal (pnode 8) (prelabel (root [2] [3] [7] [2] [6] [1]) perm8.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 8) 1
  rw [show mutate (node t 8) 1=(relabel (matrix (root [2] [3] [7] [2] [6] [1]) t) perm8.symm) from he]
  exact IsRoot.relabelled (root_sound [2] [3] [7] [2] [6] [1] t ht (by decide)) perm8.symm

theorem edge8_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 8) 2) := by
  have he := mutation_equal (pnode 8) (prelabel (pnode 4) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 8) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 4) perm0.symm

theorem edge8_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 8) 3) := by
  have he := mutation_equal (pnode 8) (prelabel (pnode 15) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 8) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 15) perm0.symm

theorem edge9_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 9) 0) := by
  have he := mutation_equal (pnode 9) (prelabel (pnode 16) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 9) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 16) perm0.symm

theorem edge9_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 9) 1) := by
  have he := mutation_equal (pnode 9) (preverse (prelabel (root [4] [15] [67] [4] [18] [1]) perm10.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 9) 1
  rw [show mutate (node t 9) 1=(reverse (relabel (matrix (root [4] [15] [67] [4] [18] [1]) t) perm10.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [4] [15] [67] [4] [18] [1] t ht (by decide)) perm10.symm)

theorem edge9_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 9) 2) := by
  have he := mutation_equal (pnode 9) (prelabel (pnode 17) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 9) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 17) perm0.symm

theorem edge9_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 9) 3) := by
  have he := mutation_equal (pnode 9) (prelabel (pnode 4) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 9) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 4) perm0.symm

theorem edge10_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 10) 0) := by
  have he := mutation_equal (pnode 10) (prelabel (pnode 5) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 10) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 5) perm0.symm

theorem edge10_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 10) 1) := by
  have he := mutation_equal (pnode 10) (preverse (prelabel (zero param3_0 param3_1 param3_2 param3_3 1) perm0.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 10) t) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (region3_safe t ht 1) perm0.symm)

theorem edge10_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 10) 2) := by
  have he := mutation_equal (pnode 10) (prelabel (pnode 18) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 10) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 18) perm0.symm

theorem edge10_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 10) 3) := by
  have he := mutation_equal (pnode 10) (preverse (prelabel (pnode 6) perm1.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 10) t) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (node_safe t 6) perm1.symm)

theorem edge11_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 11) 0) := by
  have he := mutation_equal (pnode 11) (preverse (prelabel (fork [2] [8] [3] [10] [5] [4]) perm4.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (node_safe t 11)
  rw [show mutate (node t 11) 0=(reverse (relabel (matrix (fork [2] [8] [3] [10] [5] [4]) t) perm4.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [2] [8] [3] [10] [5] [4] t ht (by decide)) perm4.symm)

theorem edge11_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 11) 1) := by
  have he := mutation_equal (pnode 11) (prelabel (fork [6] [8] [4] [46] [25] [3]) perm10.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (node_safe t 11)
  rw [show mutate (node t 11) 1=(relabel (matrix (fork [6] [8] [4] [46] [25] [3]) t) perm10.symm) from he]
  exact IsFork.relabelled (fork_sound [6] [8] [4] [46] [25] [3] t ht (by decide)) perm10.symm

theorem edge11_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 11) 2) := by
  have he := mutation_equal (pnode 11) (prelabel (pnode 19) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 11) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 19) perm0.symm

theorem edge11_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 11) 3) := by
  have he := mutation_equal (pnode 11) (prelabel (pnode 6) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 11) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 6) perm0.symm

theorem edge12_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 12) 0) := by
  have he := mutation_equal (pnode 12) (prelabel (pnode 7) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 12) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 7) perm0.symm

theorem edge12_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 12) 1) := by
  have he := mutation_equal (pnode 12) (preverse (prelabel (zero param4_0 param4_1 param4_2 param4_3 0) perm15.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 12) t) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (region4_safe t ht 0) perm15.symm)

theorem edge12_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 12) 2) := by
  have he := mutation_equal (pnode 12) (preverse (prelabel (pnode 16) perm1.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 12) t) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (node_safe t 16) perm1.symm)

theorem edge12_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 12) 3) := by
  have he := mutation_equal (pnode 12) (preverse (prelabel (root [6] [128] [29] [22] [5] []) perm18.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 12) 3
  rw [show mutate (node t 12) 3=(reverse (relabel (matrix (root [6] [128] [29] [22] [5] []) t) perm18.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [6] [128] [29] [22] [5] [] t ht (by decide)) perm18.symm)

theorem edge13_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 13) 0) := by
  have he := mutation_equal (pnode 13) (prelabel (root [6] [46] [29] [8] [5] []) perm4.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 13) 0
  rw [show mutate (node t 13) 0=(relabel (matrix (root [6] [46] [29] [8] [5] []) t) perm4.symm) from he]
  exact IsRoot.relabelled (root_sound [6] [46] [29] [8] [5] [] t ht (by decide)) perm4.symm

theorem edge13_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 13) 1) := by
  have he := mutation_equal (pnode 13) (prelabel (zero param5_0 param5_1 param5_2 param5_3 0) perm14.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 13) t) 1)
  rw [he]
  exact Safe.framed (region5_safe t ht 0) perm14.symm

theorem edge13_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 13) 2) := by
  have he := mutation_equal (pnode 13) (preverse (prelabel (pnode 14) perm21.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 13) t) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (node_safe t 14) perm21.symm)

theorem edge13_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 13) 3) := by
  have he := mutation_equal (pnode 13) (prelabel (pnode 7) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 13) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 7) perm0.symm

theorem edge14_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 14) 0) := by
  have he := mutation_equal (pnode 14) (prelabel (pnode 8) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 14) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 8) perm0.symm

theorem edge14_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 14) 1) := by
  have he := mutation_equal (pnode 14) (preverse (prelabel (zero param5_0 param5_1 param5_2 param5_3 1) perm15.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 14) t) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (region5_safe t ht 1) perm15.symm)

theorem edge14_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 14) 2) := by
  have he := mutation_equal (pnode 14) (preverse (prelabel (pnode 13) perm21.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 14) t) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (node_safe t 13) perm21.symm)

theorem edge14_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 14) 3) := by
  have he := mutation_equal (pnode 14) (prelabel (pnode 20) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 14) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 20) perm0.symm

theorem edge15_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 15) 0) := by
  have he := mutation_equal (pnode 15) (prelabel (pnode 21) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 15) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 21) perm0.symm

theorem edge15_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 15) 1) := by
  have he := mutation_equal (pnode 15) (preverse (prelabel (fork [6] [28] [2] [163] [13] [6]) perm11.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (node_safe t 15)
  rw [show mutate (node t 15) 1=(reverse (relabel (matrix (fork [6] [28] [2] [163] [13] [6]) t) perm11.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [6] [28] [2] [163] [13] [6] t ht (by decide)) perm11.symm)

theorem edge15_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 15) 2) := by
  have he := mutation_equal (pnode 15) (prelabel (fork [5] [28] [6] [134] [29] [2]) perm17.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 2 (node_safe t 15)
  rw [show mutate (node t 15) 2=(relabel (matrix (fork [5] [28] [6] [134] [29] [2]) t) perm17.symm) from he]
  exact IsFork.relabelled (fork_sound [5] [28] [6] [134] [29] [2] t ht (by decide)) perm17.symm

theorem edge15_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 15) 3) := by
  have he := mutation_equal (pnode 15) (prelabel (pnode 8) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 15) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 8) perm0.symm

theorem edge16_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 16) 0) := by
  have he := mutation_equal (pnode 16) (prelabel (pnode 9) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 16) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 9) perm0.symm

theorem edge16_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 16) 1) := by
  have he := mutation_equal (pnode 16) (prelabel (zero param4_0 param4_1 param4_2 param4_3 1) perm21.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 16) t) 1)
  rw [he]
  exact Safe.framed (region4_safe t ht 1) perm21.symm

theorem edge16_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 16) 2) := by
  have he := mutation_equal (pnode 16) (prelabel (pnode 22) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 16) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 22) perm0.symm

theorem edge16_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 16) 3) := by
  have he := mutation_equal (pnode 16) (preverse (prelabel (pnode 12) perm1.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 16) t) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (node_safe t 12) perm1.symm)

theorem edge17_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 17) 0) := by
  have he := mutation_equal (pnode 17) (prelabel (pnode 23) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 17) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 23) perm0.symm

theorem edge17_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 17) 1) := by
  have he := mutation_equal (pnode 17) (prelabel (fork [18] [86] [4] [1543] [73] [6]) perm9.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (node_safe t 17)
  rw [show mutate (node t 17) 1=(relabel (matrix (fork [18] [86] [4] [1543] [73] [6]) t) perm9.symm) from he]
  exact IsFork.relabelled (fork_sound [18] [86] [4] [1543] [73] [6] t ht (by decide)) perm9.symm

theorem edge17_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 17) 2) := by
  have he := mutation_equal (pnode 17) (prelabel (pnode 9) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 17) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 9) perm0.symm

theorem edge17_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 17) 3) := by
  have he := mutation_equal (pnode 17) (preverse (prelabel (fork [5] [86] [6] [412] [29] [4]) perm23.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 3 (node_safe t 17)
  rw [show mutate (node t 17) 3=(reverse (relabel (matrix (fork [5] [86] [6] [412] [29] [4]) t) perm23.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [5] [86] [6] [412] [29] [4] t ht (by decide)) perm23.symm)

theorem edge18_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 18) 0) := by
  have he := mutation_equal (pnode 18) (preverse (prelabel (generic param0_0 param0_1 param0_2 param0_3 1) perm5.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 18) t) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (region0_safe t ht 1) perm5.symm)

theorem edge18_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 18) 1) := by
  have he := mutation_equal (pnode 18) (prelabel (root [10] [198] [59] [20] [6] [1]) perm8.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 18) 1
  rw [show mutate (node t 18) 1=(relabel (matrix (root [10] [198] [59] [20] [6] [1]) t) perm8.symm) from he]
  exact IsRoot.relabelled (root_sound [10] [198] [59] [20] [6] [1] t ht (by decide)) perm8.symm

theorem edge18_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 18) 2) := by
  have he := mutation_equal (pnode 18) (prelabel (pnode 10) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 18) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 10) perm0.symm

theorem edge18_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 18) 3) := by
  have he := mutation_equal (pnode 18) (preverse (prelabel (pnode 19) perm0.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 18) t) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (node_safe t 19) perm0.symm)

theorem edge19_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 19) 0) := by
  have he := mutation_equal (pnode 19) (preverse (prelabel (pnode 24) perm21.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 19) t) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (node_safe t 24) perm21.symm)

theorem edge19_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 19) 1) := by
  have he := mutation_equal (pnode 19) (prelabel (root [20] [121] [77] [6] [4] [1]) perm7.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 19) 1
  rw [show mutate (node t 19) 1=(relabel (matrix (root [20] [121] [77] [6] [4] [1]) t) perm7.symm) from he]
  exact IsRoot.relabelled (root_sound [20] [121] [77] [6] [4] [1] t ht (by decide)) perm7.symm

theorem edge19_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 19) 2) := by
  have he := mutation_equal (pnode 19) (prelabel (pnode 11) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 19) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 11) perm0.symm

theorem edge19_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 19) 3) := by
  have he := mutation_equal (pnode 19) (preverse (prelabel (pnode 18) perm0.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 19) t) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (node_safe t 18) perm0.symm)

theorem edge20_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 20) 0) := by
  have he := mutation_equal (pnode 20) (prelabel (pnode 21) perm21.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 20) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 21) perm21.symm

theorem edge20_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 20) 1) := by
  have he := mutation_equal (pnode 20) (prelabel (root [8] [315] [47] [40] [6] [1]) perm11.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 20) 1
  rw [show mutate (node t 20) 1=(relabel (matrix (root [8] [315] [47] [40] [6] [1]) t) perm11.symm) from he]
  exact IsRoot.relabelled (root_sound [8] [315] [47] [40] [6] [1] t ht (by decide)) perm11.symm

theorem edge20_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 20) 2) := by
  have he := mutation_equal (pnode 20) (preverse (prelabel (generic param1_0 param1_1 param1_2 param1_3 1) perm13.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 20) t) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (region1_safe t ht 1) perm13.symm)

theorem edge20_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 20) 3) := by
  have he := mutation_equal (pnode 20) (prelabel (pnode 14) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 20) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 14) perm0.symm

theorem edge21_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 21) 0) := by
  have he := mutation_equal (pnode 21) (prelabel (pnode 15) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 21) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 15) perm0.symm

theorem edge21_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 21) 1) := by
  have he := mutation_equal (pnode 21) (preverse (prelabel (root [40] [241] [74] [6] [2] [1]) perm9.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 21) 1
  rw [show mutate (node t 21) 1=(reverse (relabel (matrix (root [40] [241] [74] [6] [2] [1]) t) perm9.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [40] [241] [74] [6] [2] [1] t ht (by decide)) perm9.symm)

theorem edge21_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 21) 2) := by
  have he := mutation_equal (pnode 21) (prelabel (pnode 25) perm15.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 21) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 25) perm15.symm

theorem edge21_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 21) 3) := by
  have he := mutation_equal (pnode 21) (prelabel (pnode 20) perm21.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 21) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 20) perm21.symm

theorem edge22_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 22) 0) := by
  have he := mutation_equal (pnode 22) (prelabel (pnode 23) perm14.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 22) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 23) perm14.symm

theorem edge22_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 22) 1) := by
  have he := mutation_equal (pnode 22) (preverse (prelabel (root [22] [2415] [395] [110] [18] [1]) perm9.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 22) 1
  rw [show mutate (node t 22) 1=(reverse (relabel (matrix (root [22] [2415] [395] [110] [18] [1]) t) perm9.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [22] [2415] [395] [110] [18] [1] t ht (by decide)) perm9.symm)

theorem edge22_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 22) 2) := by
  have he := mutation_equal (pnode 22) (prelabel (pnode 16) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 22) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 16) perm0.symm

theorem edge22_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 22) 3) := by
  have he := mutation_equal (pnode 22) (prelabel (generic param2_0 param2_1 param2_2 param2_3 1) perm19.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 22) t) 3)
  rw [he]
  exact Safe.framed (region2_safe t ht 1) perm19.symm

theorem edge23_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 23) 0) := by
  have he := mutation_equal (pnode 23) (prelabel (pnode 17) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 23) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 17) perm0.symm

theorem edge23_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 23) 1) := by
  have he := mutation_equal (pnode 23) (prelabel (root [110] [1981] [434] [18] [4] [1]) perm11.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 23) 1
  rw [show mutate (node t 23) 1=(relabel (matrix (root [110] [1981] [434] [18] [4] [1]) t) perm11.symm) from he]
  exact IsRoot.relabelled (root_sound [110] [1981] [434] [18] [4] [1] t ht (by decide)) perm11.symm

theorem edge23_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 23) 2) := by
  have he := mutation_equal (pnode 23) (prelabel (pnode 22) perm14.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 23) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 22) perm14.symm

theorem edge23_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 23) 3) := by
  have he := mutation_equal (pnode 23) (prelabel (pnode 26) perm20.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 23) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 26) perm20.symm

theorem edge24_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 24) 0) := by
  have he := mutation_equal (pnode 24) (preverse (prelabel (generic param0_0 param0_1 param0_2 param0_3 2) perm5.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 24) t) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (region0_safe t ht 2) perm5.symm)

theorem edge24_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 24) 1) := by
  have he := mutation_equal (pnode 24) (preverse (prelabel (root [56] [338] [1117] [6] [20] [1]) perm8.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 24) 1
  rw [show mutate (node t 24) 1=(reverse (relabel (matrix (root [56] [338] [1117] [6] [20] [1]) t) perm8.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [56] [338] [1117] [6] [20] [1] t ht (by decide)) perm8.symm)

theorem edge24_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 24) 2) := by
  have he := mutation_equal (pnode 24) (prelabel (fork [3] [2] [56] [5] [148] [6]) perm16.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 2 (node_safe t 24)
  rw [show mutate (node t 24) 2=(relabel (matrix (fork [3] [2] [56] [5] [148] [6]) t) perm16.symm) from he]
  exact IsFork.relabelled (fork_sound [3] [2] [56] [5] [148] [6] t ht (by decide)) perm16.symm

theorem edge24_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 24) 3) := by
  have he := mutation_equal (pnode 24) (preverse (prelabel (pnode 19) perm21.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 24) t) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (node_safe t 19) perm21.symm)

theorem edge25_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 25) 0) := by
  have he := mutation_equal (pnode 25) (prelabel (pnode 21) perm20.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 25) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 21) perm20.symm

theorem edge25_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 25) 1) := by
  have he := mutation_equal (pnode 25) (preverse (prelabel (root [238] [1433] [9514] [6] [40] [1]) perm11.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 25) 1
  rw [show mutate (node t 25) 1=(reverse (relabel (matrix (root [238] [1433] [9514] [6] [40] [1]) t) perm11.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [238] [1433] [9514] [6] [40] [1] t ht (by decide)) perm11.symm)

theorem edge25_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 25) 2) := by
  have he := mutation_equal (pnode 25) (preverse (prelabel (generic param1_0 param1_1 param1_2 param1_3 2) perm13.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 25) t) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (region1_safe t ht 2) perm13.symm)

theorem edge25_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 25) 3) := by
  have he := mutation_equal (pnode 25) (prelabel (fork [6] [5] [238] [29] [1388] [6]) perm19.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 3 (node_safe t 25)
  rw [show mutate (node t 25) 3=(relabel (matrix (fork [6] [5] [238] [29] [1388] [6]) t) perm19.symm) from he]
  exact IsFork.relabelled (fork_sound [6] [5] [238] [29] [1388] [6] t ht (by decide)) perm19.symm

theorem edge26_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 26) 0) := by
  have he := mutation_equal (pnode 26) (prelabel (pnode 23) perm15.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 26) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 23) perm15.symm

theorem edge26_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 26) 1) := by
  have he := mutation_equal (pnode 26) (prelabel (root [656] [11813] [72154] [18] [110] [1]) perm9.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 26) 1
  rw [show mutate (node t 26) 1=(relabel (matrix (root [656] [11813] [72154] [18] [110] [1]) t) perm9.symm) from he]
  exact IsRoot.relabelled (root_sound [656] [11813] [72154] [18] [110] [1] t ht (by decide)) perm9.symm

theorem edge26_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 26) 2) := by
  have he := mutation_equal (pnode 26) (preverse (prelabel (fork [6] [5] [656] [29] [3826] [18]) perm13.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 2 (node_safe t 26)
  rw [show mutate (node t 26) 2=(reverse (relabel (matrix (fork [6] [5] [656] [29] [3826] [18]) t) perm13.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [6] [5] [656] [29] [3826] [18] t ht (by decide)) perm13.symm)

theorem edge26_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 26) 3) := by
  have he := mutation_equal (pnode 26) (prelabel (generic param2_0 param2_1 param2_2 param2_3 2) perm19.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 26) t) 3)
  rw [he]
  exact Safe.framed (region2_safe t ht 2) perm19.symm

theorem all_cyclic (t : Int) (ht : 0≤t) (i : Fin 27) : ¬ Acyclic (node t i) := by
  rcases finCore i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact cyclic0 t ht
  · exact cyclic1 t ht
  · exact cyclic2 t ht
  · exact cyclic3 t ht
  · exact cyclic4 t ht
  · exact cyclic5 t ht
  · exact cyclic6 t ht
  · exact cyclic7 t ht
  · exact cyclic8 t ht
  · exact cyclic9 t ht
  · exact cyclic10 t ht
  · exact cyclic11 t ht
  · exact cyclic12 t ht
  · exact cyclic13 t ht
  · exact cyclic14 t ht
  · exact cyclic15 t ht
  · exact cyclic16 t ht
  · exact cyclic17 t ht
  · exact cyclic18 t ht
  · exact cyclic19 t ht
  · exact cyclic20 t ht
  · exact cyclic21 t ht
  · exact cyclic22 t ht
  · exact cyclic23 t ht
  · exact cyclic24 t ht
  · exact cyclic25 t ht
  · exact cyclic26 t ht

theorem all_edges (t : Int) (ht : 0≤t) (i : Fin 27) (k : Fin 4) : SafeCore t (mutate (node t i) k) := by
  have hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
  rcases finCore i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rcases hk with rfl|rfl|rfl|rfl
  · exact edge0_0 t ht
  · exact edge0_1 t ht
  · exact edge0_2 t ht
  · exact edge0_3 t ht
  · exact edge1_0 t ht
  · exact edge1_1 t ht
  · exact edge1_2 t ht
  · exact edge1_3 t ht
  · exact edge2_0 t ht
  · exact edge2_1 t ht
  · exact edge2_2 t ht
  · exact edge2_3 t ht
  · exact edge3_0 t ht
  · exact edge3_1 t ht
  · exact edge3_2 t ht
  · exact edge3_3 t ht
  · exact edge4_0 t ht
  · exact edge4_1 t ht
  · exact edge4_2 t ht
  · exact edge4_3 t ht
  · exact edge5_0 t ht
  · exact edge5_1 t ht
  · exact edge5_2 t ht
  · exact edge5_3 t ht
  · exact edge6_0 t ht
  · exact edge6_1 t ht
  · exact edge6_2 t ht
  · exact edge6_3 t ht
  · exact edge7_0 t ht
  · exact edge7_1 t ht
  · exact edge7_2 t ht
  · exact edge7_3 t ht
  · exact edge8_0 t ht
  · exact edge8_1 t ht
  · exact edge8_2 t ht
  · exact edge8_3 t ht
  · exact edge9_0 t ht
  · exact edge9_1 t ht
  · exact edge9_2 t ht
  · exact edge9_3 t ht
  · exact edge10_0 t ht
  · exact edge10_1 t ht
  · exact edge10_2 t ht
  · exact edge10_3 t ht
  · exact edge11_0 t ht
  · exact edge11_1 t ht
  · exact edge11_2 t ht
  · exact edge11_3 t ht
  · exact edge12_0 t ht
  · exact edge12_1 t ht
  · exact edge12_2 t ht
  · exact edge12_3 t ht
  · exact edge13_0 t ht
  · exact edge13_1 t ht
  · exact edge13_2 t ht
  · exact edge13_3 t ht
  · exact edge14_0 t ht
  · exact edge14_1 t ht
  · exact edge14_2 t ht
  · exact edge14_3 t ht
  · exact edge15_0 t ht
  · exact edge15_1 t ht
  · exact edge15_2 t ht
  · exact edge15_3 t ht
  · exact edge16_0 t ht
  · exact edge16_1 t ht
  · exact edge16_2 t ht
  · exact edge16_3 t ht
  · exact edge17_0 t ht
  · exact edge17_1 t ht
  · exact edge17_2 t ht
  · exact edge17_3 t ht
  · exact edge18_0 t ht
  · exact edge18_1 t ht
  · exact edge18_2 t ht
  · exact edge18_3 t ht
  · exact edge19_0 t ht
  · exact edge19_1 t ht
  · exact edge19_2 t ht
  · exact edge19_3 t ht
  · exact edge20_0 t ht
  · exact edge20_1 t ht
  · exact edge20_2 t ht
  · exact edge20_3 t ht
  · exact edge21_0 t ht
  · exact edge21_1 t ht
  · exact edge21_2 t ht
  · exact edge21_3 t ht
  · exact edge22_0 t ht
  · exact edge22_1 t ht
  · exact edge22_2 t ht
  · exact edge22_3 t ht
  · exact edge23_0 t ht
  · exact edge23_1 t ht
  · exact edge23_2 t ht
  · exact edge23_3 t ht
  · exact edge24_0 t ht
  · exact edge24_1 t ht
  · exact edge24_2 t ht
  · exact edge24_3 t ht
  · exact edge25_0 t ht
  · exact edge25_1 t ht
  · exact edge25_2 t ht
  · exact edge25_3 t ht
  · exact edge26_0 t ht
  · exact edge26_1 t ht
  · exact edge26_2 t ht
  · exact edge26_3 t ht

theorem NMA (t : Int) (ht : 0≤t) : ¬ MutationAcyclic (node t 0) := by
  apply safe_NMA data rules (Core t)
  · rintro B ⟨i,rfl⟩; exact node_skew t i
  · rintro B ⟨i,rfl⟩; exact all_cyclic t ht i
  · rintro B ⟨i,rfl⟩ k; exact all_edges t ht i k
  · exact node_safe t 0
end Boundary2
namespace Boundary3
private theorem finCore (i : Fin 83) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 ∨ i=15 ∨ i=16 ∨ i=17 ∨ i=18 ∨ i=19 ∨ i=20 ∨ i=21 ∨ i=22 ∨ i=23 ∨ i=24 ∨ i=25 ∨ i=26 ∨ i=27 ∨ i=28 ∨ i=29 ∨ i=30 ∨ i=31 ∨ i=32 ∨ i=33 ∨ i=34 ∨ i=35 ∨ i=36 ∨ i=37 ∨ i=38 ∨ i=39 ∨ i=40 ∨ i=41 ∨ i=42 ∨ i=43 ∨ i=44 ∨ i=45 ∨ i=46 ∨ i=47 ∨ i=48 ∨ i=49 ∨ i=50 ∨ i=51 ∨ i=52 ∨ i=53 ∨ i=54 ∨ i=55 ∨ i=56 ∨ i=57 ∨ i=58 ∨ i=59 ∨ i=60 ∨ i=61 ∨ i=62 ∨ i=63 ∨ i=64 ∨ i=65 ∨ i=66 ∨ i=67 ∨ i=68 ∨ i=69 ∨ i=70 ∨ i=71 ∨ i=72 ∨ i=73 ∨ i=74 ∨ i=75 ∨ i=76 ∨ i=77 ∨ i=78 ∨ i=79 ∨ i=80 ∨ i=81 ∨ i=82 := by omega

def pnode (i : Fin 83) : PMatrix := match i.val with
  | 0 => six [] [1] [-4] [2] [-3] [5]
  | 1 => six [] [-1] [4] [2] [-3] [1]
  | 2 => six [] [-1] [1] [-2] [7] [-5]
  | 3 => six [-2] [1] [4] [-2] [-1] [-1]
  | 4 => six [12] [-1] [-4] [-1] [3] [-1]
  | 5 => six [] [1] [-1] [-2] [7] [-4]
  | 6 => six [] [-1] [1] [2] [-7] [9]
  | 7 => six [] [4] [-1] [33] [-7] [5]
  | 8 => six [2] [-3] [2] [2] [1] [-1]
  | 9 => six [2] [5] [-4] [-2] [1] [1]
  | 10 => six [-12] [1] [4] [-13] [-45] [-1]
  | 11 => six [-12] [-1] [32] [1] [-3] [2]
  | 12 => six [12] [1] [-5] [1] [2] [1]
  | 13 => six [] [1] [-1] [2] [-7] [10]
  | 14 => six [-7] [1] [1] [26] [-7] [4]
  | 15 => six [-2] [1] [1] [-2] [11] [-9]
  | 16 => six [7] [-1] [-1] [-61] [7] [-9]
  | 17 => six [] [-4] [1] [33] [-7] [1]
  | 18 => six [-4] [3] [-1] [-2] [1] [1]
  | 19 => six [2] [-1] [-2] [3] [-1] [1]
  | 20 => six [-2] [5] [-2] [2] [-1] [3]
  | 21 => six [1] [-1] [4] [13] [-58] [1]
  | 22 => six [168] [5] [-4] [-13] [45] [1]
  | 23 => six [12] [1] [-32] [1] [381] [34]
  | 24 => six [-13] [1] [32] [-1] [-1] [-2]
  | 25 => six [-12] [-1] [5] [1] [-58] [-4]
  | 26 => six [-12] [13] [19] [-1] [-2] [1]
  | 27 => six [] [-1] [9] [-2] [13] [-10]
  | 28 => six [] [-9] [1] [-68] [7] [-10]
  | 29 => six [-7] [-1] [5] [-26] [97] [-4]
  | 30 => six [2] [-1] [-1] [] [13] [-9]
  | 31 => six [-2] [10] [-1] [97] [-11] [9]
  | 32 => six [-7] [1] [1] [-68] [] [-9]
  | 33 => six [7] [1] [-10] [61] [-542] [9]
  | 34 => six [-132] [4] [1] [-33] [26] [-1]
  | 35 => six [4] [-3] [1] [10] [1] [-2]
  | 36 => six [4] [-5] [-1] [2] [-1] [3]
  | 37 => six [-5] [2] [1] [-2] [-1] [-1]
  | 38 => six [-1] [12] [4] [-13] [58] [-753]
  | 39 => six [233] [-1] [-4] [-45] [58] [-1]
  | 40 => six [233] [-5] [1] [13] [45] [-1]
  | 41 => six [-12] [13] [4540] [-1] [-381] [34]
  | 42 => six [12] [-1] [2] [-1] [415] [-34]
  | 43 => six [13] [-1] [-32] [12] [415] [-2]
  | 44 => six [19] [65] [-32] [-1] [1] [2]
  | 45 => six [12] [-1] [-691] [-1] [58] [-62]
  | 46 => six [26] [13] [-19] [-3] [2] [-1]
  | 47 => six [7] [1] [-5] [-26] [132] [1]
  | 48 => six [-11] [-1] [1] [117] [-13] [9]
  | 49 => six [2] [-10] [1] [117] [-11] [-1]
  | 50 => six [61] [-1] [1] [68] [-612] [9]
  | 51 => six [-7] [-1] [10] [61] [-612] [-1]
  | 52 => six [26] [4] [-1] [653] [-132] [5]
  | 53 => six [-4] [37] [5] [-10] [-1] [-2]
  | 54 => six [4] [-1] [-1] [12] [-1] [2]
  | 55 => six [-4] [5] [1] [-18] [-5] [3]
  | 56 => six [4] [-8] [1] [-1] [1] [-3]
  | 57 => six [5] [-2] [-1] [8] [4] [-1]
  | 58 => six [5] [-8] [-4] [2] [1] [-1]
  | 59 => six [1] [-12] [-4] [-1] [62] [-753]
  | 60 => six [-45] [1] [-4] [233] [-1152] [5]
  | 61 => six [1] [-13] [4982] [1] [-381] [-34]
  | 62 => six [-12] [-1] [4982] [1] [-415] [381]
  | 63 => six [-19] [65] [-13] [1] [-1] [3]
  | 64 => six [-65] [-19] [182] [1] [-3] [2]
  | 65 => six [-12] [1] [691] [-13] [-8234] [-62]
  | 66 => six [117] [1] [-10] [-11] [1168] [9]
  | 67 => six [-612] [10] [-1] [-6113] [61] [9]
  | 68 => six [1] [47] [-5] [-10] [1] [2]
  | 69 => six [-4] [47] [-1] [-12] [1] [-10]
  | 70 => six [-8] [1] [-1] [-12] [23] [-2]
  | 71 => six [1] [5] [-1] [-33] [5] [-3]
  | 72 => six [-4] [8] [-1] [-33] [1] [5]
  | 73 => six [4] [8] [-23] [1] [-2] [3]
  | 74 => six [-11] [2] [-3] [-8] [4] [1]
  | 75 => six [1] [12] [-9040] [1] [-691] [753]
  | 76 => six [-1] [13] [-4982] [-12] [-381] [64732]
  | 77 => six [1] [-1] [691] [13] [-9040] [62]
  | 78 => six [-1] [-47] [5] [-10] [-4] [-233]
  | 79 => six [8] [-1] [1] [-4] [23] [-3]
  | 80 => six [23] [-3] [1] [65] [-8] [-2]
  | 81 => six [-1] [5] [4] [33] [-5] [162]
  | _ => six [-1] [12] [691] [-13] [9040] [-117458]

def node (t : Int) (i : Fin 83) : Matrix 4 := matrix (pnode i) t
def Core (t : Int) (B : Matrix 4) : Prop := ∃ i, B=node t i
abbrev SafeCore (t : Int) := Safe data (Core t)
theorem node_safe (t : Int) (i : Fin 83) : SafeCore t (node t i) := Safe.central ⟨i,rfl⟩

def param0_0 : P := [4]
def param0_1 : P := [132]
def param0_2 : P := [26]
def param0_3 : P := [33]
theorem domain0 (t : Int) (ht : 0≤t) : GenericStrip.Domain (eval param0_0 t) (eval param0_1 t) (eval param0_2 t) (eval param0_3 t) :=
  generic_domain param0_0 param0_1 param0_2 param0_3 t ht (by decide)

def region0 (t : Int) (ht : 0≤t) : Region := .inl (.inl ⟨eval param0_0 t,⟨eval param0_1 t,eval param0_2 t,eval param0_3 t⟩,domain0 t ht⟩)

theorem parent0_0 (t : Int) (ht : 0≤t) :
    data.parent (region0 t ht) (0 : Fin 3)=(reverse (relabel (node t 47) perm17.symm)) := by
  have he := mutation_equal (generic param0_0 param0_1 param0_2 param0_3 0) (preverse (prelabel (pnode 47) perm17.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent0_1 (t : Int) (ht : 0≤t) :
    data.parent (region0 t ht) (1 : Fin 3)=(reverse (relabel (node t 17) perm5.symm)) := by
  have he := mutation_equal (generic param0_0 param0_1 param0_2 param0_3 0) (preverse (prelabel (pnode 17) perm5.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent0_2 (t : Int) (ht : 0≤t) :
    data.parent (region0 t ht) (2 : Fin 3)=(reverse (relabel (node t 52) perm5.symm)) := by
  have he := mutation_equal (generic param0_0 param0_1 param0_2 param0_3 2) (preverse (prelabel (pnode 52) perm5.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parents0_safe (t : Int) (ht : 0≤t) (p : Fin 3) :
    SafeCore t (data.parent (region0 t ht) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hp with rfl|rfl|rfl
  · rw [parent0_0 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 47) perm17.symm)
  · rw [parent0_1 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 17) perm5.symm)
  · rw [parent0_2 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 52) perm5.symm)

theorem region0_safe (t : Int) (ht : 0≤t) (i : Fin 3) :
    SafeCore t (matrix (generic param0_0 param0_1 param0_2 param0_3 i) t) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core t) (region0 t ht) (parents0_safe t ht) (0,Fin.castLE (by decide) i)

def param1_0 : P := [4]
def param1_1 : P := [233]
def param1_2 : P := [45]
def param1_3 : P := [58]
theorem domain1 (t : Int) (ht : 0≤t) : GenericStrip.Domain (eval param1_0 t) (eval param1_1 t) (eval param1_2 t) (eval param1_3 t) :=
  generic_domain param1_0 param1_1 param1_2 param1_3 t ht (by decide)

def region1 (t : Int) (ht : 0≤t) : Region := .inl (.inl ⟨eval param1_0 t,⟨eval param1_1 t,eval param1_2 t,eval param1_3 t⟩,domain1 t ht⟩)

theorem parent1_0 (t : Int) (ht : 0≤t) :
    data.parent (region1 t ht) (0 : Fin 3)=(relabel (node t 40) perm5.symm) := by
  have he := mutation_equal (generic param1_0 param1_1 param1_2 param1_3 0) (prelabel (pnode 40) perm5.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent1_1 (t : Int) (ht : 0≤t) :
    data.parent (region1 t ht) (1 : Fin 3)=(relabel (node t 21) perm4.symm) := by
  have he := mutation_equal (generic param1_0 param1_1 param1_2 param1_3 0) (prelabel (pnode 21) perm4.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent1_2 (t : Int) (ht : 0≤t) :
    data.parent (region1 t ht) (2 : Fin 3)=(relabel (node t 60) perm4.symm) := by
  have he := mutation_equal (generic param1_0 param1_1 param1_2 param1_3 2) (prelabel (pnode 60) perm4.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parents1_safe (t : Int) (ht : 0≤t) (p : Fin 3) :
    SafeCore t (data.parent (region1 t ht) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hp with rfl|rfl|rfl
  · rw [parent1_0 t ht]
    exact Safe.framed (node_safe t 40) perm5.symm
  · rw [parent1_1 t ht]
    exact Safe.framed (node_safe t 21) perm4.symm
  · rw [parent1_2 t ht]
    exact Safe.framed (node_safe t 60) perm4.symm

theorem region1_safe (t : Int) (ht : 0≤t) (i : Fin 3) :
    SafeCore t (matrix (generic param1_0 param1_1 param1_2 param1_3 i) t) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core t) (region1 t ht) (parents1_safe t ht) (0,Fin.castLE (by decide) i)

def param2_0 : P := [2]
def param2_1 : P := [65]
def param2_2 : P := [19]
def param2_3 : P := [32]
theorem domain2 (t : Int) (ht : 0≤t) : GenericStrip.Domain (eval param2_0 t) (eval param2_1 t) (eval param2_2 t) (eval param2_3 t) :=
  generic_domain param2_0 param2_1 param2_2 param2_3 t ht (by decide)

def region2 (t : Int) (ht : 0≤t) : Region := .inl (.inl ⟨eval param2_0 t,⟨eval param2_1 t,eval param2_2 t,eval param2_3 t⟩,domain2 t ht⟩)

theorem parent2_0 (t : Int) (ht : 0≤t) :
    data.parent (region2 t ht) (0 : Fin 3)=(reverse (relabel (node t 63) perm20.symm)) := by
  have he := mutation_equal (generic param2_0 param2_1 param2_2 param2_3 0) (preverse (prelabel (pnode 63) perm20.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent2_1 (t : Int) (ht : 0≤t) :
    data.parent (region2 t ht) (1 : Fin 3)=(reverse (relabel (node t 24) perm20.symm)) := by
  have he := mutation_equal (generic param2_0 param2_1 param2_2 param2_3 0) (preverse (prelabel (pnode 24) perm20.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent2_2 (t : Int) (ht : 0≤t) :
    data.parent (region2 t ht) (2 : Fin 3)=(reverse (relabel (node t 64) perm20.symm)) := by
  have he := mutation_equal (generic param2_0 param2_1 param2_2 param2_3 2) (preverse (prelabel (pnode 64) perm20.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parents2_safe (t : Int) (ht : 0≤t) (p : Fin 3) :
    SafeCore t (data.parent (region2 t ht) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hp with rfl|rfl|rfl
  · rw [parent2_0 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 63) perm20.symm)
  · rw [parent2_1 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 24) perm20.symm)
  · rw [parent2_2 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 64) perm20.symm)

theorem region2_safe (t : Int) (ht : 0≤t) (i : Fin 3) :
    SafeCore t (matrix (generic param2_0 param2_1 param2_2 param2_3 i) t) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core t) (region2 t ht) (parents2_safe t ht) (0,Fin.castLE (by decide) i)

def param3_0 : P := [9]
def param3_1 : P := [117]
def param3_2 : P := [11]
def param3_3 : P := [13]
theorem domain3 (t : Int) (ht : 0≤t) : GenericStrip.Domain (eval param3_0 t) (eval param3_1 t) (eval param3_2 t) (eval param3_3 t) :=
  generic_domain param3_0 param3_1 param3_2 param3_3 t ht (by decide)

def region3 (t : Int) (ht : 0≤t) : Region := .inl (.inl ⟨eval param3_0 t,⟨eval param3_1 t,eval param3_2 t,eval param3_3 t⟩,domain3 t ht⟩)

theorem parent3_0 (t : Int) (ht : 0≤t) :
    data.parent (region3 t ht) (0 : Fin 3)=(reverse (relabel (node t 49) perm16.symm)) := by
  have he := mutation_equal (generic param3_0 param3_1 param3_2 param3_3 0) (preverse (prelabel (pnode 49) perm16.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent3_1 (t : Int) (ht : 0≤t) :
    data.parent (region3 t ht) (1 : Fin 3)=(reverse (relabel (node t 30) perm10.symm)) := by
  have he := mutation_equal (generic param3_0 param3_1 param3_2 param3_3 0) (preverse (prelabel (pnode 30) perm10.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent3_2 (t : Int) (ht : 0≤t) :
    data.parent (region3 t ht) (2 : Fin 3)=(reverse (relabel (node t 66) perm10.symm)) := by
  have he := mutation_equal (generic param3_0 param3_1 param3_2 param3_3 2) (preverse (prelabel (pnode 66) perm10.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parents3_safe (t : Int) (ht : 0≤t) (p : Fin 3) :
    SafeCore t (data.parent (region3 t ht) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hp with rfl|rfl|rfl
  · rw [parent3_0 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 49) perm16.symm)
  · rw [parent3_1 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 30) perm10.symm)
  · rw [parent3_2 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 66) perm10.symm)

theorem region3_safe (t : Int) (ht : 0≤t) (i : Fin 3) :
    SafeCore t (matrix (generic param3_0 param3_1 param3_2 param3_3 i) t) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core t) (region3 t ht) (parents3_safe t ht) (0,Fin.castLE (by decide) i)

def param4_0 : P := [9]
def param4_1 : P := [612]
def param4_2 : P := [61]
def param4_3 : P := [68]
theorem domain4 (t : Int) (ht : 0≤t) : GenericStrip.Domain (eval param4_0 t) (eval param4_1 t) (eval param4_2 t) (eval param4_3 t) :=
  generic_domain param4_0 param4_1 param4_2 param4_3 t ht (by decide)

def region4 (t : Int) (ht : 0≤t) : Region := .inl (.inl ⟨eval param4_0 t,⟨eval param4_1 t,eval param4_2 t,eval param4_3 t⟩,domain4 t ht⟩)

theorem parent4_0 (t : Int) (ht : 0≤t) :
    data.parent (region4 t ht) (0 : Fin 3)=(relabel (node t 51) perm17.symm) := by
  have he := mutation_equal (generic param4_0 param4_1 param4_2 param4_3 0) (prelabel (pnode 51) perm17.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent4_1 (t : Int) (ht : 0≤t) :
    data.parent (region4 t ht) (1 : Fin 3)=(relabel (node t 32) perm11.symm) := by
  have he := mutation_equal (generic param4_0 param4_1 param4_2 param4_3 0) (prelabel (pnode 32) perm11.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent4_2 (t : Int) (ht : 0≤t) :
    data.parent (region4 t ht) (2 : Fin 3)=(relabel (node t 67) perm11.symm) := by
  have he := mutation_equal (generic param4_0 param4_1 param4_2 param4_3 2) (prelabel (pnode 67) perm11.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parents4_safe (t : Int) (ht : 0≤t) (p : Fin 3) :
    SafeCore t (data.parent (region4 t ht) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hp with rfl|rfl|rfl
  · rw [parent4_0 t ht]
    exact Safe.framed (node_safe t 51) perm17.symm
  · rw [parent4_1 t ht]
    exact Safe.framed (node_safe t 32) perm11.symm
  · rw [parent4_2 t ht]
    exact Safe.framed (node_safe t 67) perm11.symm

theorem region4_safe (t : Int) (ht : 0≤t) (i : Fin 3) :
    SafeCore t (matrix (generic param4_0 param4_1 param4_2 param4_3 i) t) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core t) (region4 t ht) (parents4_safe t ht) (0,Fin.castLE (by decide) i)

def param5_0 : P := [2]
def param5_1 : P := [8]
def param5_2 : P := [4]
def param5_3 : P := [5]
theorem domain5 (t : Int) (ht : 0≤t) : GenericStrip.Domain (eval param5_0 t) (eval param5_1 t) (eval param5_2 t) (eval param5_3 t) :=
  generic_domain param5_0 param5_1 param5_2 param5_3 t ht (by decide)

def region5 (t : Int) (ht : 0≤t) : Region := .inl (.inl ⟨eval param5_0 t,⟨eval param5_1 t,eval param5_2 t,eval param5_3 t⟩,domain5 t ht⟩)

theorem parent5_0 (t : Int) (ht : 0≤t) :
    data.parent (region5 t ht) (0 : Fin 3)=(relabel (node t 56) perm20.symm) := by
  have he := mutation_equal (generic param5_0 param5_1 param5_2 param5_3 0) (prelabel (pnode 56) perm20.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent5_1 (t : Int) (ht : 0≤t) :
    data.parent (region5 t ht) (1 : Fin 3)=(relabel (node t 37) perm22.symm) := by
  have he := mutation_equal (generic param5_0 param5_1 param5_2 param5_3 0) (prelabel (pnode 37) perm22.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent5_2 (t : Int) (ht : 0≤t) :
    data.parent (region5 t ht) (2 : Fin 3)=(relabel (node t 73) perm18.symm) := by
  have he := mutation_equal (generic param5_0 param5_1 param5_2 param5_3 2) (prelabel (pnode 73) perm18.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parents5_safe (t : Int) (ht : 0≤t) (p : Fin 3) :
    SafeCore t (data.parent (region5 t ht) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hp with rfl|rfl|rfl
  · rw [parent5_0 t ht]
    exact Safe.framed (node_safe t 56) perm20.symm
  · rw [parent5_1 t ht]
    exact Safe.framed (node_safe t 37) perm22.symm
  · rw [parent5_2 t ht]
    exact Safe.framed (node_safe t 73) perm18.symm

theorem region5_safe (t : Int) (ht : 0≤t) (i : Fin 3) :
    SafeCore t (matrix (generic param5_0 param5_1 param5_2 param5_3 i) t) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core t) (region5 t ht) (parents5_safe t ht) (0,Fin.castLE (by decide) i)

def param6_0 : P := [12]
def param6_1 : P := [4982]
def param6_2 : P := [381]
def param6_3 : P := [415]
theorem domain6 (t : Int) (ht : 0≤t) : GenericStrip.Domain (eval param6_0 t) (eval param6_1 t) (eval param6_2 t) (eval param6_3 t) :=
  generic_domain param6_0 param6_1 param6_2 param6_3 t ht (by decide)

def region6 (t : Int) (ht : 0≤t) : Region := .inl (.inl ⟨eval param6_0 t,⟨eval param6_1 t,eval param6_2 t,eval param6_3 t⟩,domain6 t ht⟩)

theorem parent6_0 (t : Int) (ht : 0≤t) :
    data.parent (region6 t ht) (0 : Fin 3)=(relabel (node t 61) perm0.symm) := by
  have he := mutation_equal (generic param6_0 param6_1 param6_2 param6_3 0) (prelabel (pnode 61) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent6_1 (t : Int) (ht : 0≤t) :
    data.parent (region6 t ht) (1 : Fin 3)=(relabel (node t 42) perm2.symm) := by
  have he := mutation_equal (generic param6_0 param6_1 param6_2 param6_3 0) (prelabel (pnode 42) perm2.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent6_2 (t : Int) (ht : 0≤t) :
    data.parent (region6 t ht) (2 : Fin 3)=(relabel (node t 76) perm6.symm) := by
  have he := mutation_equal (generic param6_0 param6_1 param6_2 param6_3 2) (prelabel (pnode 76) perm6.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parents6_safe (t : Int) (ht : 0≤t) (p : Fin 3) :
    SafeCore t (data.parent (region6 t ht) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hp with rfl|rfl|rfl
  · rw [parent6_0 t ht]
    exact Safe.framed (node_safe t 61) perm0.symm
  · rw [parent6_1 t ht]
    exact Safe.framed (node_safe t 42) perm2.symm
  · rw [parent6_2 t ht]
    exact Safe.framed (node_safe t 76) perm6.symm

theorem region6_safe (t : Int) (ht : 0≤t) (i : Fin 3) :
    SafeCore t (matrix (generic param6_0 param6_1 param6_2 param6_3 i) t) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core t) (region6 t ht) (parents6_safe t ht) (0,Fin.castLE (by decide) i)

def param7_0 : P := [4]
def param7_1 : P := [47]
def param7_2 : P := [10]
def param7_3 : P := [12]
theorem domain7 (t : Int) (ht : 0≤t) : GenericStrip.Domain (eval param7_0 t) (eval param7_1 t) (eval param7_2 t) (eval param7_3 t) :=
  generic_domain param7_0 param7_1 param7_2 param7_3 t ht (by decide)

def region7 (t : Int) (ht : 0≤t) : Region := .inl (.inl ⟨eval param7_0 t,⟨eval param7_1 t,eval param7_2 t,eval param7_3 t⟩,domain7 t ht⟩)

theorem parent7_0 (t : Int) (ht : 0≤t) :
    data.parent (region7 t ht) (0 : Fin 3)=(relabel (node t 68) perm1.symm) := by
  have he := mutation_equal (generic param7_0 param7_1 param7_2 param7_3 0) (prelabel (pnode 68) perm1.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent7_1 (t : Int) (ht : 0≤t) :
    data.parent (region7 t ht) (1 : Fin 3)=(relabel (node t 54) perm3.symm) := by
  have he := mutation_equal (generic param7_0 param7_1 param7_2 param7_3 0) (prelabel (pnode 54) perm3.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent7_2 (t : Int) (ht : 0≤t) :
    data.parent (region7 t ht) (2 : Fin 3)=(relabel (node t 78) perm7.symm) := by
  have he := mutation_equal (generic param7_0 param7_1 param7_2 param7_3 2) (prelabel (pnode 78) perm7.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parents7_safe (t : Int) (ht : 0≤t) (p : Fin 3) :
    SafeCore t (data.parent (region7 t ht) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hp with rfl|rfl|rfl
  · rw [parent7_0 t ht]
    exact Safe.framed (node_safe t 68) perm1.symm
  · rw [parent7_1 t ht]
    exact Safe.framed (node_safe t 54) perm3.symm
  · rw [parent7_2 t ht]
    exact Safe.framed (node_safe t 78) perm7.symm

theorem region7_safe (t : Int) (ht : 0≤t) (i : Fin 3) :
    SafeCore t (matrix (generic param7_0 param7_1 param7_2 param7_3 i) t) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core t) (region7 t ht) (parents7_safe t ht) (0,Fin.castLE (by decide) i)

def param8_0 : P := [2]
def param8_1 : P := [23]
def param8_2 : P := [8]
def param8_3 : P := [12]
theorem domain8 (t : Int) (ht : 0≤t) : GenericStrip.Domain (eval param8_0 t) (eval param8_1 t) (eval param8_2 t) (eval param8_3 t) :=
  generic_domain param8_0 param8_1 param8_2 param8_3 t ht (by decide)

def region8 (t : Int) (ht : 0≤t) : Region := .inl (.inl ⟨eval param8_0 t,⟨eval param8_1 t,eval param8_2 t,eval param8_3 t⟩,domain8 t ht⟩)

theorem parent8_0 (t : Int) (ht : 0≤t) :
    data.parent (region8 t ht) (0 : Fin 3)=(reverse (relabel (node t 79) perm11.symm)) := by
  have he := mutation_equal (generic param8_0 param8_1 param8_2 param8_3 0) (preverse (prelabel (pnode 79) perm11.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent8_1 (t : Int) (ht : 0≤t) :
    data.parent (region8 t ht) (1 : Fin 3)=(reverse (relabel (node t 54) perm11.symm)) := by
  have he := mutation_equal (generic param8_0 param8_1 param8_2 param8_3 0) (preverse (prelabel (pnode 54) perm11.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent8_2 (t : Int) (ht : 0≤t) :
    data.parent (region8 t ht) (2 : Fin 3)=(reverse (relabel (node t 80) perm11.symm)) := by
  have he := mutation_equal (generic param8_0 param8_1 param8_2 param8_3 2) (preverse (prelabel (pnode 80) perm11.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parents8_safe (t : Int) (ht : 0≤t) (p : Fin 3) :
    SafeCore t (data.parent (region8 t ht) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hp with rfl|rfl|rfl
  · rw [parent8_0 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 79) perm11.symm)
  · rw [parent8_1 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 54) perm11.symm)
  · rw [parent8_2 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 80) perm11.symm)

theorem region8_safe (t : Int) (ht : 0≤t) (i : Fin 3) :
    SafeCore t (matrix (generic param8_0 param8_1 param8_2 param8_3 i) t) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core t) (region8 t ht) (parents8_safe t ht) (0,Fin.castLE (by decide) i)

def param9_0 : P := [4]
def param9_1 : P := [33]
def param9_2 : P := [5]
def param9_3 : P := [8]
theorem domain9 (t : Int) (ht : 0≤t) : GenericStrip.Domain (eval param9_0 t) (eval param9_1 t) (eval param9_2 t) (eval param9_3 t) :=
  generic_domain param9_0 param9_1 param9_2 param9_3 t ht (by decide)

def region9 (t : Int) (ht : 0≤t) : Region := .inl (.inl ⟨eval param9_0 t,⟨eval param9_1 t,eval param9_2 t,eval param9_3 t⟩,domain9 t ht⟩)

theorem parent9_0 (t : Int) (ht : 0≤t) :
    data.parent (region9 t ht) (0 : Fin 3)=(reverse (relabel (node t 71) perm7.symm)) := by
  have he := mutation_equal (generic param9_0 param9_1 param9_2 param9_3 0) (preverse (prelabel (pnode 71) perm7.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent9_1 (t : Int) (ht : 0≤t) :
    data.parent (region9 t ht) (1 : Fin 3)=(reverse (relabel (node t 56) perm13.symm)) := by
  have he := mutation_equal (generic param9_0 param9_1 param9_2 param9_3 0) (preverse (prelabel (pnode 56) perm13.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent9_2 (t : Int) (ht : 0≤t) :
    data.parent (region9 t ht) (2 : Fin 3)=(reverse (relabel (node t 81) perm1.symm)) := by
  have he := mutation_equal (generic param9_0 param9_1 param9_2 param9_3 2) (preverse (prelabel (pnode 81) perm1.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parents9_safe (t : Int) (ht : 0≤t) (p : Fin 3) :
    SafeCore t (data.parent (region9 t ht) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hp with rfl|rfl|rfl
  · rw [parent9_0 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 71) perm7.symm)
  · rw [parent9_1 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 56) perm13.symm)
  · rw [parent9_2 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 81) perm1.symm)

theorem region9_safe (t : Int) (ht : 0≤t) (i : Fin 3) :
    SafeCore t (matrix (generic param9_0 param9_1 param9_2 param9_3 i) t) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core t) (region9 t ht) (parents9_safe t ht) (0,Fin.castLE (by decide) i)

def param10_0 : P := [12]
def param10_1 : P := [9040]
def param10_2 : P := [691]
def param10_3 : P := [753]
theorem domain10 (t : Int) (ht : 0≤t) : GenericStrip.Domain (eval param10_0 t) (eval param10_1 t) (eval param10_2 t) (eval param10_3 t) :=
  generic_domain param10_0 param10_1 param10_2 param10_3 t ht (by decide)

def region10 (t : Int) (ht : 0≤t) : Region := .inl (.inl ⟨eval param10_0 t,⟨eval param10_1 t,eval param10_2 t,eval param10_3 t⟩,domain10 t ht⟩)

theorem parent10_0 (t : Int) (ht : 0≤t) :
    data.parent (region10 t ht) (0 : Fin 3)=(reverse (relabel (node t 77) perm6.symm)) := by
  have he := mutation_equal (generic param10_0 param10_1 param10_2 param10_3 0) (preverse (prelabel (pnode 77) perm6.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent10_1 (t : Int) (ht : 0≤t) :
    data.parent (region10 t ht) (1 : Fin 3)=(reverse (relabel (node t 59) perm0.symm)) := by
  have he := mutation_equal (generic param10_0 param10_1 param10_2 param10_3 0) (preverse (prelabel (pnode 59) perm0.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent10_2 (t : Int) (ht : 0≤t) :
    data.parent (region10 t ht) (2 : Fin 3)=(reverse (relabel (node t 82) perm0.symm)) := by
  have he := mutation_equal (generic param10_0 param10_1 param10_2 param10_3 2) (preverse (prelabel (pnode 82) perm0.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parents10_safe (t : Int) (ht : 0≤t) (p : Fin 3) :
    SafeCore t (data.parent (region10 t ht) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hp with rfl|rfl|rfl
  · rw [parent10_0 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 77) perm6.symm)
  · rw [parent10_1 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 59) perm0.symm)
  · rw [parent10_2 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 82) perm0.symm)

theorem region10_safe (t : Int) (ht : 0≤t) (i : Fin 3) :
    SafeCore t (matrix (generic param10_0 param10_1 param10_2 param10_3 i) t) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core t) (region10 t ht) (parents10_safe t ht) (0,Fin.castLE (by decide) i)

def param11_0 : P := [7]
def param11_1 : P := [4]
def param11_2 : P := [33]
def param11_3 : P := [226]
theorem domain11 (t : Int) (ht : 0≤t) : UnitZeroStrip.Domain (eval param11_0 t) (eval param11_1 t) (eval param11_2 t) (eval param11_3 t) :=
  zero_domain param11_0 param11_1 param11_2 param11_3 t ht (by decide)

def region11 (t : Int) (ht : 0≤t) : Region := .inl (.inr (.n (eval param11_0 t) ⟨eval param11_1 t,eval param11_2 t,eval param11_3 t⟩ (domain11 t ht)))

theorem parent11_0 (t : Int) (ht : 0≤t) :
    data.parent (region11 t ht) (0 : Fin 2)=(reverse (relabel (node t 7) perm0.symm)) := by
  have he := mutation_equal (zero param11_0 param11_1 param11_2 param11_3 0) (preverse (prelabel (pnode 7) perm0.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,zero_eval] at he
  exact he

theorem parent11_1 (t : Int) (ht : 0≤t) :
    data.parent (region11 t ht) (1 : Fin 2)=(reverse (relabel (node t 17) perm0.symm)) := by
  have he := mutation_equal (zero param11_0 param11_1 param11_2 param11_3 1) (preverse (prelabel (pnode 17) perm0.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,zero_eval] at he
  exact he

theorem parents11_safe (t : Int) (ht : 0≤t) (p : Fin 2) :
    SafeCore t (data.parent (region11 t ht) p) := by
  have hp : p=0 ∨ p=1 := by change p=(0 : Fin 2) ∨ p=(1 : Fin 2); omega
  rcases hp with rfl|rfl
  · rw [parent11_0 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 7) perm0.symm)
  · rw [parent11_1 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 17) perm0.symm)

theorem region11_safe (t : Int) (ht : 0≤t) (i : Fin 2) :
    SafeCore t (matrix (zero param11_0 param11_1 param11_2 param11_3 i) t) := by
  rw [zero_eval]
  exact Safe.region (D:=data) (core:=Core t) (region11 t ht) (parents11_safe t ht) (0,Fin.castLE (by decide) i)

def param12_0 : P := [2]
def param12_1 : P := [9]
def param12_2 : P := [13]
def param12_3 : P := [16]
theorem domain12 (t : Int) (ht : 0≤t) : UnitZeroStrip.Domain (eval param12_0 t) (eval param12_1 t) (eval param12_2 t) (eval param12_3 t) :=
  zero_domain param12_0 param12_1 param12_2 param12_3 t ht (by decide)

def region12 (t : Int) (ht : 0≤t) : Region := .inl (.inr (.n (eval param12_0 t) ⟨eval param12_1 t,eval param12_2 t,eval param12_3 t⟩ (domain12 t ht)))

theorem parent12_0 (t : Int) (ht : 0≤t) :
    data.parent (region12 t ht) (0 : Fin 2)=(reverse (relabel (node t 27) perm1.symm)) := by
  have he := mutation_equal (zero param12_0 param12_1 param12_2 param12_3 0) (preverse (prelabel (pnode 27) perm1.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,zero_eval] at he
  exact he

theorem parent12_1 (t : Int) (ht : 0≤t) :
    data.parent (region12 t ht) (1 : Fin 2)=(reverse (relabel (node t 30) perm20.symm)) := by
  have he := mutation_equal (zero param12_0 param12_1 param12_2 param12_3 1) (preverse (prelabel (pnode 30) perm20.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,zero_eval] at he
  exact he

theorem parents12_safe (t : Int) (ht : 0≤t) (p : Fin 2) :
    SafeCore t (data.parent (region12 t ht) p) := by
  have hp : p=0 ∨ p=1 := by change p=(0 : Fin 2) ∨ p=(1 : Fin 2); omega
  rcases hp with rfl|rfl
  · rw [parent12_0 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 27) perm1.symm)
  · rw [parent12_1 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 30) perm20.symm)

theorem region12_safe (t : Int) (ht : 0≤t) (i : Fin 2) :
    SafeCore t (matrix (zero param12_0 param12_1 param12_2 param12_3 i) t) := by
  rw [zero_eval]
  exact Safe.region (D:=data) (core:=Core t) (region12 t ht) (parents12_safe t ht) (0,Fin.castLE (by decide) i)

def param13_0 : P := [7]
def param13_1 : P := [9]
def param13_2 : P := [68]
def param13_3 : P := [466]
theorem domain13 (t : Int) (ht : 0≤t) : UnitZeroStrip.Domain (eval param13_0 t) (eval param13_1 t) (eval param13_2 t) (eval param13_3 t) :=
  zero_domain param13_0 param13_1 param13_2 param13_3 t ht (by decide)

def region13 (t : Int) (ht : 0≤t) : Region := .inl (.inr (.n (eval param13_0 t) ⟨eval param13_1 t,eval param13_2 t,eval param13_3 t⟩ (domain13 t ht)))

theorem parent13_0 (t : Int) (ht : 0≤t) :
    data.parent (region13 t ht) (0 : Fin 2)=(relabel (node t 28) perm0.symm) := by
  have he := mutation_equal (zero param13_0 param13_1 param13_2 param13_3 0) (prelabel (pnode 28) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,zero_eval] at he
  exact he

theorem parent13_1 (t : Int) (ht : 0≤t) :
    data.parent (region13 t ht) (1 : Fin 2)=(relabel (node t 32) perm21.symm) := by
  have he := mutation_equal (zero param13_0 param13_1 param13_2 param13_3 1) (prelabel (pnode 32) perm21.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,zero_eval] at he
  exact he

theorem parents13_safe (t : Int) (ht : 0≤t) (p : Fin 2) :
    SafeCore t (data.parent (region13 t ht) p) := by
  have hp : p=0 ∨ p=1 := by change p=(0 : Fin 2) ∨ p=(1 : Fin 2); omega
  rcases hp with rfl|rfl
  · rw [parent13_0 t ht]
    exact Safe.framed (node_safe t 28) perm0.symm
  · rw [parent13_1 t ht]
    exact Safe.framed (node_safe t 32) perm21.symm

theorem region13_safe (t : Int) (ht : 0≤t) (i : Fin 2) :
    SafeCore t (matrix (zero param13_0 param13_1 param13_2 param13_3 i) t) := by
  rw [zero_eval]
  exact Safe.region (D:=data) (core:=Core t) (region13 t ht) (parents13_safe t ht) (0,Fin.castLE (by decide) i)

theorem node_skew (t : Int) (i : Fin 83) : SkewSymmetric (node t i) := by
  rcases finCore i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp only [node,pnode,matrix_six] <;> exact ofSix_skew _ _ _ _ _ _

theorem cyclic0 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 0) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 0 0 2) t ht (by decide))
  have h1 := hr 2 3 (pos (pnode 0 2 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 0 3 0) t ht (by decide))
  omega

theorem cyclic1 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 1) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 1 2 (pos (pnode 1 1 2) t ht (by decide))
  have h1 := hr 2 3 (pos (pnode 1 2 3) t ht (by decide))
  have h2 := hr 3 1 (pos (pnode 1 3 1) t ht (by decide))
  omega

theorem cyclic2 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 2) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 2 0 3) t ht (by decide))
  have h1 := hr 3 2 (pos (pnode 2 3 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 2 2 0) t ht (by decide))
  omega

theorem cyclic3 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 3) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 3 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 3 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 3 1 0) t ht (by decide))
  omega

theorem cyclic4 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 4) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 4 0 1) t ht (by decide))
  have h1 := hr 1 3 (pos (pnode 4 1 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 4 3 0) t ht (by decide))
  omega

theorem cyclic5 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 5) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 1 3 (pos (pnode 5 1 3) t ht (by decide))
  have h1 := hr 3 2 (pos (pnode 5 3 2) t ht (by decide))
  have h2 := hr 2 1 (pos (pnode 5 2 1) t ht (by decide))
  omega

theorem cyclic6 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 6) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 1 2 (pos (pnode 6 1 2) t ht (by decide))
  have h1 := hr 2 3 (pos (pnode 6 2 3) t ht (by decide))
  have h2 := hr 3 1 (pos (pnode 6 3 1) t ht (by decide))
  omega

theorem cyclic7 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 7) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 7 0 2) t ht (by decide))
  have h1 := hr 2 3 (pos (pnode 7 2 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 7 3 0) t ht (by decide))
  omega

theorem cyclic8 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 8) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 8 0 1) t ht (by decide))
  have h1 := hr 1 2 (pos (pnode 8 1 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 8 2 0) t ht (by decide))
  omega

theorem cyclic9 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 9) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 9 0 1) t ht (by decide))
  have h1 := hr 1 3 (pos (pnode 9 1 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 9 3 0) t ht (by decide))
  omega

theorem cyclic10 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 10) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 10 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 10 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 10 1 0) t ht (by decide))
  omega

theorem cyclic11 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 11) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 11 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (pnode 11 3 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 11 1 0) t ht (by decide))
  omega

theorem cyclic12 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 12) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 12 0 1) t ht (by decide))
  have h1 := hr 1 3 (pos (pnode 12 1 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 12 3 0) t ht (by decide))
  omega

theorem cyclic13 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 13) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 13 0 2) t ht (by decide))
  have h1 := hr 2 3 (pos (pnode 13 2 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 13 3 0) t ht (by decide))
  omega

theorem cyclic14 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 14) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 14 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (pnode 14 3 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 14 1 0) t ht (by decide))
  omega

theorem cyclic15 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 15) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 15 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 15 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 15 1 0) t ht (by decide))
  omega

theorem cyclic16 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 16) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 16 0 1) t ht (by decide))
  have h1 := hr 1 3 (pos (pnode 16 1 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 16 3 0) t ht (by decide))
  omega

theorem cyclic17 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 17) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 1 2 (pos (pnode 17 1 2) t ht (by decide))
  have h1 := hr 2 3 (pos (pnode 17 2 3) t ht (by decide))
  have h2 := hr 3 1 (pos (pnode 17 3 1) t ht (by decide))
  omega

theorem cyclic18 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 18) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 18 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 18 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 18 1 0) t ht (by decide))
  omega

theorem cyclic19 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 19) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 19 0 1) t ht (by decide))
  have h1 := hr 1 2 (pos (pnode 19 1 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 19 2 0) t ht (by decide))
  omega

theorem cyclic20 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 20) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 20 0 2) t ht (by decide))
  have h1 := hr 2 3 (pos (pnode 20 2 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 20 3 0) t ht (by decide))
  omega

theorem cyclic21 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 21) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 21 0 1) t ht (by decide))
  have h1 := hr 1 2 (pos (pnode 21 1 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 21 2 0) t ht (by decide))
  omega

theorem cyclic22 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 22) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 22 0 1) t ht (by decide))
  have h1 := hr 1 3 (pos (pnode 22 1 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 22 3 0) t ht (by decide))
  omega

theorem cyclic23 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 23) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 23 0 1) t ht (by decide))
  have h1 := hr 1 3 (pos (pnode 23 1 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 23 3 0) t ht (by decide))
  omega

theorem cyclic24 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 24) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 24 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 24 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 24 1 0) t ht (by decide))
  omega

theorem cyclic25 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 25) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 25 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (pnode 25 3 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 25 1 0) t ht (by decide))
  omega

theorem cyclic26 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 26) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 26 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 26 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 26 1 0) t ht (by decide))
  omega

theorem cyclic27 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 27) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 27 0 3) t ht (by decide))
  have h1 := hr 3 2 (pos (pnode 27 3 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 27 2 0) t ht (by decide))
  omega

theorem cyclic28 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 28) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 28 0 3) t ht (by decide))
  have h1 := hr 3 2 (pos (pnode 28 3 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 28 2 0) t ht (by decide))
  omega

theorem cyclic29 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 29) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 29 0 3) t ht (by decide))
  have h1 := hr 3 2 (pos (pnode 29 3 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 29 2 0) t ht (by decide))
  omega

theorem cyclic30 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 30) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 30 0 1) t ht (by decide))
  have h1 := hr 1 3 (pos (pnode 30 1 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 30 3 0) t ht (by decide))
  omega

theorem cyclic31 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 31) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 31 0 2) t ht (by decide))
  have h1 := hr 2 3 (pos (pnode 31 2 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 31 3 0) t ht (by decide))
  omega

theorem cyclic32 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 32) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 32 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 32 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 32 1 0) t ht (by decide))
  omega

theorem cyclic33 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 33) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 33 0 2) t ht (by decide))
  have h1 := hr 2 3 (pos (pnode 33 2 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 33 3 0) t ht (by decide))
  omega

theorem cyclic34 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 34) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 34 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 34 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 34 1 0) t ht (by decide))
  omega

theorem cyclic35 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 35) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 35 0 1) t ht (by decide))
  have h1 := hr 1 2 (pos (pnode 35 1 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 35 2 0) t ht (by decide))
  omega

theorem cyclic36 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 36) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 36 0 1) t ht (by decide))
  have h1 := hr 1 2 (pos (pnode 36 1 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 36 2 0) t ht (by decide))
  omega

theorem cyclic37 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 37) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 37 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 37 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 37 1 0) t ht (by decide))
  omega

theorem cyclic38 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 38) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 38 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 38 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 38 1 0) t ht (by decide))
  omega

theorem cyclic39 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 39) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 39 0 1) t ht (by decide))
  have h1 := hr 1 3 (pos (pnode 39 1 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 39 3 0) t ht (by decide))
  omega

theorem cyclic40 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 40) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 40 0 1) t ht (by decide))
  have h1 := hr 1 2 (pos (pnode 40 1 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 40 2 0) t ht (by decide))
  omega

theorem cyclic41 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 41) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 41 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 41 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 41 1 0) t ht (by decide))
  omega

theorem cyclic42 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 42) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 42 0 3) t ht (by decide))
  have h1 := hr 3 2 (pos (pnode 42 3 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 42 2 0) t ht (by decide))
  omega

theorem cyclic43 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 43) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 43 0 1) t ht (by decide))
  have h1 := hr 1 2 (pos (pnode 43 1 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 43 2 0) t ht (by decide))
  omega

theorem cyclic44 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 44) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 44 0 1) t ht (by decide))
  have h1 := hr 1 3 (pos (pnode 44 1 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 44 3 0) t ht (by decide))
  omega

theorem cyclic45 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 45) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 45 0 1) t ht (by decide))
  have h1 := hr 1 3 (pos (pnode 45 1 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 45 3 0) t ht (by decide))
  omega

theorem cyclic46 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 46) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 46 0 1) t ht (by decide))
  have h1 := hr 1 3 (pos (pnode 46 1 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 46 3 0) t ht (by decide))
  omega

theorem cyclic47 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 47) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 47 0 1) t ht (by decide))
  have h1 := hr 1 3 (pos (pnode 47 1 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 47 3 0) t ht (by decide))
  omega

theorem cyclic48 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 48) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 48 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (pnode 48 3 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 48 1 0) t ht (by decide))
  omega

theorem cyclic49 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 49) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 49 0 1) t ht (by decide))
  have h1 := hr 1 2 (pos (pnode 49 1 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 49 2 0) t ht (by decide))
  omega

theorem cyclic50 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 50) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 50 0 1) t ht (by decide))
  have h1 := hr 1 2 (pos (pnode 50 1 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 50 2 0) t ht (by decide))
  omega

theorem cyclic51 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 51) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 51 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (pnode 51 3 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 51 1 0) t ht (by decide))
  omega

theorem cyclic52 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 52) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 52 0 2) t ht (by decide))
  have h1 := hr 2 3 (pos (pnode 52 2 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 52 3 0) t ht (by decide))
  omega

theorem cyclic53 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 53) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 53 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 53 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 53 1 0) t ht (by decide))
  omega

theorem cyclic54 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 54) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 54 0 1) t ht (by decide))
  have h1 := hr 1 2 (pos (pnode 54 1 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 54 2 0) t ht (by decide))
  omega

theorem cyclic55 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 55) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 55 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 55 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 55 1 0) t ht (by decide))
  omega

theorem cyclic56 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 56) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 56 0 3) t ht (by decide))
  have h1 := hr 3 2 (pos (pnode 56 3 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 56 2 0) t ht (by decide))
  omega

theorem cyclic57 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 57) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 57 0 1) t ht (by decide))
  have h1 := hr 1 2 (pos (pnode 57 1 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 57 2 0) t ht (by decide))
  omega

theorem cyclic58 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 58) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 58 0 1) t ht (by decide))
  have h1 := hr 1 2 (pos (pnode 58 1 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 58 2 0) t ht (by decide))
  omega

theorem cyclic59 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 59) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 59 0 1) t ht (by decide))
  have h1 := hr 1 3 (pos (pnode 59 1 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 59 3 0) t ht (by decide))
  omega

theorem cyclic60 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 60) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 60 0 2) t ht (by decide))
  have h1 := hr 2 3 (pos (pnode 60 2 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 60 3 0) t ht (by decide))
  omega

theorem cyclic61 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 61) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 61 0 1) t ht (by decide))
  have h1 := hr 1 2 (pos (pnode 61 1 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 61 2 0) t ht (by decide))
  omega

theorem cyclic62 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 62) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 62 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (pnode 62 3 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 62 1 0) t ht (by decide))
  omega

theorem cyclic63 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 63) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 63 0 2) t ht (by decide))
  have h1 := hr 2 3 (pos (pnode 63 2 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 63 3 0) t ht (by decide))
  omega

theorem cyclic64 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 64) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 64 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (pnode 64 3 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 64 1 0) t ht (by decide))
  omega

theorem cyclic65 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 65) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 65 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 65 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 65 1 0) t ht (by decide))
  omega

theorem cyclic66 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 66) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 66 0 1) t ht (by decide))
  have h1 := hr 1 3 (pos (pnode 66 1 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 66 3 0) t ht (by decide))
  omega

theorem cyclic67 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 67) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 67 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 67 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 67 1 0) t ht (by decide))
  omega

theorem cyclic68 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 68) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 68 0 1) t ht (by decide))
  have h1 := hr 1 3 (pos (pnode 68 1 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 68 3 0) t ht (by decide))
  omega

theorem cyclic69 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 69) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 69 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 69 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 69 1 0) t ht (by decide))
  omega

theorem cyclic70 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 70) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 70 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 70 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 70 1 0) t ht (by decide))
  omega

theorem cyclic71 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 71) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 71 0 1) t ht (by decide))
  have h1 := hr 1 3 (pos (pnode 71 1 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 71 3 0) t ht (by decide))
  omega

theorem cyclic72 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 72) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 72 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 72 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 72 1 0) t ht (by decide))
  omega

theorem cyclic73 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 73) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 73 0 2) t ht (by decide))
  have h1 := hr 2 3 (pos (pnode 73 2 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 73 3 0) t ht (by decide))
  omega

theorem cyclic74 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 74) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 74 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 74 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 74 1 0) t ht (by decide))
  omega

theorem cyclic75 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 75) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 75 0 2) t ht (by decide))
  have h1 := hr 2 3 (pos (pnode 75 2 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 75 3 0) t ht (by decide))
  omega

theorem cyclic76 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 76) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 76 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 76 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 76 1 0) t ht (by decide))
  omega

theorem cyclic77 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 77) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 77 0 1) t ht (by decide))
  have h1 := hr 1 2 (pos (pnode 77 1 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 77 2 0) t ht (by decide))
  omega

theorem cyclic78 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 78) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 78 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (pnode 78 3 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 78 1 0) t ht (by decide))
  omega

theorem cyclic79 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 79) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 79 0 3) t ht (by decide))
  have h1 := hr 3 2 (pos (pnode 79 3 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 79 2 0) t ht (by decide))
  omega

theorem cyclic80 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 80) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 80 0 1) t ht (by decide))
  have h1 := hr 1 2 (pos (pnode 80 1 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 80 2 0) t ht (by decide))
  omega

theorem cyclic81 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 81) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 81 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (pnode 81 3 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 81 1 0) t ht (by decide))
  omega

theorem cyclic82 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 82) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 82 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 82 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 82 1 0) t ht (by decide))
  omega

theorem edge0_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 0) 0) := by
  have he := mutation_equal (pnode 0) (prelabel (pnode 1) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 0) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 1) perm0.symm

theorem edge0_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 0) 1) := by
  have he := mutation_equal (pnode 0) (preverse (prelabel (pnode 1) perm0.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 0) t) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (node_safe t 1) perm0.symm)

theorem edge0_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 0) 2) := by
  have he := mutation_equal (pnode 0) (prelabel (pnode 2) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 0) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 2) perm0.symm

theorem edge0_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 0) 3) := by
  have he := mutation_equal (pnode 0) (prelabel (root [5] [19] [13] [4] [3] []) perm22.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 0) 3
  rw [show mutate (node t 0) 3=(relabel (matrix (root [5] [19] [13] [4] [3] []) t) perm22.symm) from he]
  exact IsRoot.relabelled (root_sound [5] [19] [13] [4] [3] [] t ht (by decide)) perm22.symm

theorem edge1_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 1) 0) := by
  have he := mutation_equal (pnode 1) (prelabel (pnode 0) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 1) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 0) perm0.symm

theorem edge1_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 1) 1) := by
  have he := mutation_equal (pnode 1) (preverse (prelabel (pnode 0) perm0.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 1) t) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (node_safe t 0) perm0.symm)

theorem edge1_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 1) 2) := by
  have he := mutation_equal (pnode 1) (prelabel (pnode 3) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 1) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 3) perm0.symm

theorem edge1_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 1) 3) := by
  have he := mutation_equal (pnode 1) (prelabel (pnode 4) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 1) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 4) perm0.symm

theorem edge2_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 2) 0) := by
  have he := mutation_equal (pnode 2) (prelabel (pnode 5) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 2) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 5) perm0.symm

theorem edge2_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 2) 1) := by
  have he := mutation_equal (pnode 2) (prelabel (pnode 6) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 2) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 6) perm0.symm

theorem edge2_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 2) 2) := by
  have he := mutation_equal (pnode 2) (prelabel (pnode 0) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 2) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 0) perm0.symm

theorem edge2_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 2) 3) := by
  have he := mutation_equal (pnode 2) (prelabel (pnode 7) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 2) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 7) perm0.symm

theorem edge3_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 3) 0) := by
  have he := mutation_equal (pnode 3) (prelabel (pnode 5) perm14.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 3) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 5) perm14.symm

theorem edge3_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 3) 1) := by
  have he := mutation_equal (pnode 3) (prelabel (pnode 8) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 3) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 8) perm0.symm

theorem edge3_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 3) 2) := by
  have he := mutation_equal (pnode 3) (prelabel (pnode 1) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 3) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 1) perm0.symm

theorem edge3_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 3) 3) := by
  have he := mutation_equal (pnode 3) (prelabel (pnode 9) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 3) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 9) perm0.symm

theorem edge4_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 4) 0) := by
  have he := mutation_equal (pnode 4) (prelabel (pnode 10) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 4) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 10) perm0.symm

theorem edge4_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 4) 1) := by
  have he := mutation_equal (pnode 4) (prelabel (pnode 11) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 4) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 11) perm0.symm

theorem edge4_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 4) 2) := by
  have he := mutation_equal (pnode 4) (prelabel (pnode 12) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 4) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 12) perm0.symm

theorem edge4_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 4) 3) := by
  have he := mutation_equal (pnode 4) (prelabel (pnode 1) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 4) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 1) perm0.symm

theorem edge5_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 5) 0) := by
  have he := mutation_equal (pnode 5) (prelabel (pnode 2) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 5) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 2) perm0.symm

theorem edge5_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 5) 1) := by
  have he := mutation_equal (pnode 5) (prelabel (pnode 13) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 5) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 13) perm0.symm

theorem edge5_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 5) 2) := by
  have he := mutation_equal (pnode 5) (prelabel (pnode 3) perm14.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 5) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 3) perm14.symm

theorem edge5_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 5) 3) := by
  have he := mutation_equal (pnode 5) (prelabel (pnode 14) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 5) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 14) perm0.symm

theorem edge6_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 6) 0) := by
  have he := mutation_equal (pnode 6) (prelabel (pnode 13) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 6) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 13) perm0.symm

theorem edge6_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 6) 1) := by
  have he := mutation_equal (pnode 6) (prelabel (pnode 2) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 6) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 2) perm0.symm

theorem edge6_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 6) 2) := by
  have he := mutation_equal (pnode 6) (prelabel (pnode 15) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 6) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 15) perm0.symm

theorem edge6_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 6) 3) := by
  have he := mutation_equal (pnode 6) (prelabel (pnode 16) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 6) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 16) perm0.symm

theorem edge7_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 7) 0) := by
  have he := mutation_equal (pnode 7) (prelabel (pnode 17) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 7) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 17) perm0.symm

theorem edge7_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 7) 1) := by
  have he := mutation_equal (pnode 7) (preverse (prelabel (zero param11_0 param11_1 param11_2 param11_3 0) perm0.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 7) t) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (region11_safe t ht 0) perm0.symm)

theorem edge7_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 7) 2) := by
  have he := mutation_equal (pnode 7) (preverse (prelabel (root [5] [19] [158] [4] [33] []) perm16.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 7) 2
  rw [show mutate (node t 7) 2=(reverse (relabel (matrix (root [5] [19] [158] [4] [33] []) t) perm16.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [5] [19] [158] [4] [33] [] t ht (by decide)) perm16.symm)

theorem edge7_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 7) 3) := by
  have he := mutation_equal (pnode 7) (prelabel (pnode 2) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 7) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 2) perm0.symm

theorem edge8_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 8) 0) := by
  have he := mutation_equal (pnode 8) (prelabel (root [3] [4] [5] [2] [2] [1]) perm2.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 8) 0
  rw [show mutate (node t 8) 0=(relabel (matrix (root [3] [4] [5] [2] [2] [1]) t) perm2.symm) from he]
  exact IsRoot.relabelled (root_sound [3] [4] [5] [2] [2] [1] t ht (by decide)) perm2.symm

theorem edge8_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 8) 1) := by
  have he := mutation_equal (pnode 8) (prelabel (pnode 3) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 8) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 3) perm0.symm

theorem edge8_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 8) 2) := by
  have he := mutation_equal (pnode 8) (prelabel (pnode 18) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 8) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 18) perm0.symm

theorem edge8_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 8) 3) := by
  have he := mutation_equal (pnode 8) (prelabel (pnode 19) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 8) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 19) perm0.symm

theorem edge9_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 9) 0) := by
  have he := mutation_equal (pnode 9) (preverse (prelabel (fork [4] [2] [5] [7] [19] [2]) perm4.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (node_safe t 9)
  rw [show mutate (node t 9) 0=(reverse (relabel (matrix (fork [4] [2] [5] [7] [19] [2]) t) perm4.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [4] [2] [5] [7] [19] [2] t ht (by decide)) perm4.symm)

theorem edge9_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 9) 1) := by
  have he := mutation_equal (pnode 9) (prelabel (pnode 20) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 9) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 20) perm0.symm

theorem edge9_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 9) 2) := by
  have he := mutation_equal (pnode 9) (prelabel (pnode 12) perm1.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 9) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 12) perm1.symm

theorem edge9_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 9) 3) := by
  have he := mutation_equal (pnode 9) (prelabel (pnode 3) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 9) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 3) perm0.symm

theorem edge10_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 10) 0) := by
  have he := mutation_equal (pnode 10) (prelabel (pnode 4) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 10) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 4) perm0.symm

theorem edge10_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 10) 1) := by
  have he := mutation_equal (pnode 10) (preverse (prelabel (root [12] [155] [536] [13] [45] [1]) perm6.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 10) 1
  rw [show mutate (node t 10) 1=(reverse (relabel (matrix (root [12] [155] [536] [13] [45] [1]) t) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [12] [155] [536] [13] [45] [1] t ht (by decide)) perm6.symm)

theorem edge10_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 10) 2) := by
  have he := mutation_equal (pnode 10) (prelabel (pnode 21) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 10) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 21) perm0.symm

theorem edge10_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 10) 3) := by
  have he := mutation_equal (pnode 10) (prelabel (pnode 22) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 10) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 22) perm0.symm

theorem edge11_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 11) 0) := by
  have he := mutation_equal (pnode 11) (prelabel (pnode 23) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 11) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 23) perm0.symm

theorem edge11_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 11) 1) := by
  have he := mutation_equal (pnode 11) (prelabel (pnode 4) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 11) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 4) perm0.symm

theorem edge11_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 11) 2) := by
  have he := mutation_equal (pnode 11) (prelabel (pnode 24) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 11) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 24) perm0.symm

theorem edge11_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 11) 3) := by
  have he := mutation_equal (pnode 11) (preverse (prelabel (root [3] [84] [5] [32] [2] [1]) perm20.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 11) 3
  rw [show mutate (node t 11) 3=(reverse (relabel (matrix (root [3] [84] [5] [32] [2] [1]) t) perm20.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [3] [84] [5] [32] [2] [1] t ht (by decide)) perm20.symm)

theorem edge12_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 12) 0) := by
  have he := mutation_equal (pnode 12) (prelabel (pnode 25) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 12) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 25) perm0.symm

theorem edge12_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 12) 1) := by
  have he := mutation_equal (pnode 12) (prelabel (pnode 26) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 12) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 26) perm0.symm

theorem edge12_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 12) 2) := by
  have he := mutation_equal (pnode 12) (prelabel (pnode 4) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 12) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 4) perm0.symm

theorem edge12_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 12) 3) := by
  have he := mutation_equal (pnode 12) (prelabel (pnode 9) perm1.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 12) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 9) perm1.symm

theorem edge13_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 13) 0) := by
  have he := mutation_equal (pnode 13) (prelabel (pnode 6) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 13) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 6) perm0.symm

theorem edge13_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 13) 1) := by
  have he := mutation_equal (pnode 13) (prelabel (pnode 5) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 13) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 5) perm0.symm

theorem edge13_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 13) 2) := by
  have he := mutation_equal (pnode 13) (prelabel (pnode 27) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 13) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 27) perm0.symm

theorem edge13_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 13) 3) := by
  have he := mutation_equal (pnode 13) (prelabel (pnode 28) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 13) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 28) perm0.symm

theorem edge14_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 14) 0) := by
  have he := mutation_equal (pnode 14) (prelabel (pnode 17) perm21.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 14) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 17) perm21.symm

theorem edge14_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 14) 1) := by
  have he := mutation_equal (pnode 14) (prelabel (root [7] [48] [178] [7] [26] [1]) perm10.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 14) 1
  rw [show mutate (node t 14) 1=(relabel (matrix (root [7] [48] [178] [7] [26] [1]) t) perm10.symm) from he]
  exact IsRoot.relabelled (root_sound [7] [48] [178] [7] [26] [1] t ht (by decide)) perm10.symm

theorem edge14_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 14) 2) := by
  have he := mutation_equal (pnode 14) (prelabel (pnode 29) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 14) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 29) perm0.symm

theorem edge14_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 14) 3) := by
  have he := mutation_equal (pnode 14) (prelabel (pnode 5) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 14) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 5) perm0.symm

theorem edge15_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 15) 0) := by
  have he := mutation_equal (pnode 15) (prelabel (pnode 30) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 15) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 30) perm0.symm

theorem edge15_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 15) 1) := by
  have he := mutation_equal (pnode 15) (prelabel (root [2] [3] [13] [2] [11] [1]) perm8.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 15) 1
  rw [show mutate (node t 15) 1=(relabel (matrix (root [2] [3] [13] [2] [11] [1]) t) perm8.symm) from he]
  exact IsRoot.relabelled (root_sound [2] [3] [13] [2] [11] [1] t ht (by decide)) perm8.symm

theorem edge15_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 15) 2) := by
  have he := mutation_equal (pnode 15) (prelabel (pnode 6) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 15) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 6) perm0.symm

theorem edge15_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 15) 3) := by
  have he := mutation_equal (pnode 15) (prelabel (pnode 31) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 15) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 31) perm0.symm

theorem edge16_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 16) 0) := by
  have he := mutation_equal (pnode 16) (prelabel (pnode 32) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 16) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 32) perm0.symm

theorem edge16_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 16) 1) := by
  have he := mutation_equal (pnode 16) (preverse (prelabel (root [7] [48] [418] [7] [61] [1]) perm10.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 16) 1
  rw [show mutate (node t 16) 1=(reverse (relabel (matrix (root [7] [48] [418] [7] [61] [1]) t) perm10.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [7] [48] [418] [7] [61] [1] t ht (by decide)) perm10.symm)

theorem edge16_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 16) 2) := by
  have he := mutation_equal (pnode 16) (prelabel (pnode 33) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 16) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 33) perm0.symm

theorem edge16_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 16) 3) := by
  have he := mutation_equal (pnode 16) (prelabel (pnode 6) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 16) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 6) perm0.symm

theorem edge17_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 17) 0) := by
  have he := mutation_equal (pnode 17) (prelabel (pnode 7) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 17) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 7) perm0.symm

theorem edge17_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 17) 1) := by
  have he := mutation_equal (pnode 17) (preverse (prelabel (zero param11_0 param11_1 param11_2 param11_3 1) perm0.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 17) t) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (region11_safe t ht 1) perm0.symm)

theorem edge17_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 17) 2) := by
  have he := mutation_equal (pnode 17) (prelabel (pnode 34) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 17) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 34) perm0.symm

theorem edge17_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 17) 3) := by
  have he := mutation_equal (pnode 17) (prelabel (pnode 14) perm21.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 17) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 14) perm21.symm

theorem edge18_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 18) 0) := by
  have he := mutation_equal (pnode 18) (prelabel (pnode 35) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 18) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 35) perm0.symm

theorem edge18_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 18) 1) := by
  have he := mutation_equal (pnode 18) (prelabel (pnode 36) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 18) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 36) perm0.symm

theorem edge18_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 18) 2) := by
  have he := mutation_equal (pnode 18) (prelabel (pnode 8) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 18) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 8) perm0.symm

theorem edge18_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 18) 3) := by
  have he := mutation_equal (pnode 18) (prelabel (pnode 37) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 18) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 37) perm0.symm

theorem edge19_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 19) 0) := by
  have he := mutation_equal (pnode 19) (preverse (prelabel (pnode 37) perm20.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 19) t) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (node_safe t 37) perm20.symm)

theorem edge19_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 19) 1) := by
  have he := mutation_equal (pnode 19) (prelabel (pnode 20) perm5.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 19) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 20) perm5.symm

theorem edge19_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 19) 2) := by
  have he := mutation_equal (pnode 19) (preverse (prelabel (pnode 19) perm21.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 19) t) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (node_safe t 19) perm21.symm)

theorem edge19_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 19) 3) := by
  have he := mutation_equal (pnode 19) (prelabel (pnode 8) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 19) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 8) perm0.symm

theorem edge20_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 20) 0) := by
  have he := mutation_equal (pnode 20) (preverse (prelabel (root [5] [12] [7] [2] [2] [1]) perm2.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 20) 0
  rw [show mutate (node t 20) 0=(reverse (relabel (matrix (root [5] [12] [7] [2] [2] [1]) t) perm2.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [5] [12] [7] [2] [2] [1] t ht (by decide)) perm2.symm)

theorem edge20_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 20) 1) := by
  have he := mutation_equal (pnode 20) (prelabel (pnode 9) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 20) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 9) perm0.symm

theorem edge20_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 20) 2) := by
  have he := mutation_equal (pnode 20) (prelabel (fork [3] [2] [5] [5] [13] [2]) perm17.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 2 (node_safe t 20)
  rw [show mutate (node t 20) 2=(relabel (matrix (fork [3] [2] [5] [5] [13] [2]) t) perm17.symm) from he]
  exact IsFork.relabelled (fork_sound [3] [2] [5] [5] [13] [2] t ht (by decide)) perm17.symm

theorem edge20_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 20) 3) := by
  have he := mutation_equal (pnode 20) (prelabel (pnode 19) perm5.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 20) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 19) perm5.symm

theorem edge21_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 21) 0) := by
  have he := mutation_equal (pnode 21) (prelabel (pnode 25) perm14.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 21) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 25) perm14.symm

theorem edge21_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 21) 1) := by
  have he := mutation_equal (pnode 21) (prelabel (pnode 38) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 21) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 38) perm0.symm

theorem edge21_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 21) 2) := by
  have he := mutation_equal (pnode 21) (prelabel (pnode 10) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 21) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 10) perm0.symm

theorem edge21_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 21) 3) := by
  have he := mutation_equal (pnode 21) (prelabel (pnode 39) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 21) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 39) perm0.symm

theorem edge22_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 22) 0) := by
  have he := mutation_equal (pnode 22) (preverse (prelabel (fork [4] [168] [5] [627] [19] [13]) perm4.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (node_safe t 22)
  rw [show mutate (node t 22) 0=(reverse (relabel (matrix (fork [4] [168] [5] [627] [19] [13]) t) perm4.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [4] [168] [5] [627] [19] [13] t ht (by decide)) perm4.symm)

theorem edge22_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 22) 1) := by
  have he := mutation_equal (pnode 22) (prelabel (fork [45] [168] [13] [7556] [586] [5]) perm10.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (node_safe t 22)
  rw [show mutate (node t 22) 1=(relabel (matrix (fork [45] [168] [13] [7556] [586] [5]) t) perm10.symm) from he]
  exact IsFork.relabelled (fork_sound [45] [168] [13] [7556] [586] [5] t ht (by decide)) perm10.symm

theorem edge22_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 22) 2) := by
  have he := mutation_equal (pnode 22) (prelabel (pnode 40) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 22) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 40) perm0.symm

theorem edge22_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 22) 3) := by
  have he := mutation_equal (pnode 22) (prelabel (pnode 10) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 22) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 10) perm0.symm

theorem edge23_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 23) 0) := by
  have he := mutation_equal (pnode 23) (prelabel (pnode 11) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 23) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 11) perm0.symm

theorem edge23_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 23) 1) := by
  have he := mutation_equal (pnode 23) (prelabel (pnode 41) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 23) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 41) perm0.symm

theorem edge23_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 23) 2) := by
  have he := mutation_equal (pnode 23) (prelabel (pnode 42) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 23) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 42) perm0.symm

theorem edge23_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 23) 3) := by
  have he := mutation_equal (pnode 23) (preverse (prelabel (root [32] [1087] [12180] [34] [381] [1]) perm19.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 23) 3
  rw [show mutate (node t 23) 3=(reverse (relabel (matrix (root [32] [1087] [12180] [34] [381] [1]) t) perm19.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [32] [1087] [12180] [34] [381] [1] t ht (by decide)) perm19.symm)

theorem edge24_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 24) 0) := by
  have he := mutation_equal (pnode 24) (prelabel (pnode 43) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 24) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 43) perm0.symm

theorem edge24_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 24) 1) := by
  have he := mutation_equal (pnode 24) (prelabel (pnode 26) perm2.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 24) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 26) perm2.symm

theorem edge24_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 24) 2) := by
  have he := mutation_equal (pnode 24) (prelabel (pnode 11) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 24) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 11) perm0.symm

theorem edge24_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 24) 3) := by
  have he := mutation_equal (pnode 24) (prelabel (pnode 44) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 24) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 44) perm0.symm

theorem edge25_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 25) 0) := by
  have he := mutation_equal (pnode 25) (prelabel (pnode 12) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 25) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 12) perm0.symm

theorem edge25_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 25) 1) := by
  have he := mutation_equal (pnode 25) (prelabel (pnode 45) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 25) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 45) perm0.symm

theorem edge25_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 25) 2) := by
  have he := mutation_equal (pnode 25) (prelabel (pnode 21) perm14.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 25) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 21) perm14.symm

theorem edge25_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 25) 3) := by
  have he := mutation_equal (pnode 25) (prelabel (root [5] [278] [19] [58] [4] [1]) perm18.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 25) 3
  rw [show mutate (node t 25) 3=(relabel (matrix (root [5] [278] [19] [58] [4] [1]) t) perm18.symm) from he]
  exact IsRoot.relabelled (root_sound [5] [278] [19] [58] [4] [1] t ht (by decide)) perm18.symm

theorem edge26_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 26) 0) := by
  have he := mutation_equal (pnode 26) (prelabel (root [12] [155] [226] [13] [19] [1]) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 26) 0
  rw [show mutate (node t 26) 0=(relabel (matrix (root [12] [155] [226] [13] [19] [1]) t) perm0.symm) from he]
  exact IsRoot.relabelled (root_sound [12] [155] [226] [13] [19] [1] t ht (by decide)) perm0.symm

theorem edge26_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 26) 1) := by
  have he := mutation_equal (pnode 26) (prelabel (pnode 12) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 26) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 12) perm0.symm

theorem edge26_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 26) 2) := by
  have he := mutation_equal (pnode 26) (prelabel (pnode 24) perm2.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 26) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 24) perm2.symm

theorem edge26_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 26) 3) := by
  have he := mutation_equal (pnode 26) (prelabel (pnode 46) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 26) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 46) perm0.symm

theorem edge27_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 27) 0) := by
  have he := mutation_equal (pnode 27) (prelabel (pnode 30) perm14.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 27) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 30) perm14.symm

theorem edge27_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 27) 1) := by
  have he := mutation_equal (pnode 27) (preverse (prelabel (zero param12_0 param12_1 param12_2 param12_3 0) perm1.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 27) t) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (region12_safe t ht 0) perm1.symm)

theorem edge27_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 27) 2) := by
  have he := mutation_equal (pnode 27) (prelabel (pnode 13) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 27) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 13) perm0.symm

theorem edge27_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 27) 3) := by
  have he := mutation_equal (pnode 27) (preverse (prelabel (root [10] [89] [128] [9] [13] []) perm22.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 27) 3
  rw [show mutate (node t 27) 3=(reverse (relabel (matrix (root [10] [89] [128] [9] [13] []) t) perm22.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [10] [89] [128] [9] [13] [] t ht (by decide)) perm22.symm)

theorem edge28_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 28) 0) := by
  have he := mutation_equal (pnode 28) (prelabel (pnode 32) perm21.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 28) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 32) perm21.symm

theorem edge28_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 28) 1) := by
  have he := mutation_equal (pnode 28) (prelabel (zero param13_0 param13_1 param13_2 param13_3 0) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 28) t) 1)
  rw [he]
  exact Safe.framed (region13_safe t ht 0) perm0.symm

theorem edge28_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 28) 2) := by
  have he := mutation_equal (pnode 28) (prelabel (root [10] [89] [673] [9] [68] []) perm16.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 28) 2
  rw [show mutate (node t 28) 2=(relabel (matrix (root [10] [89] [673] [9] [68] []) t) perm16.symm) from he]
  exact IsRoot.relabelled (root_sound [10] [89] [673] [9] [68] [] t ht (by decide)) perm16.symm

theorem edge28_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 28) 3) := by
  have he := mutation_equal (pnode 28) (prelabel (pnode 13) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 28) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 13) perm0.symm

theorem edge29_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 29) 0) := by
  have he := mutation_equal (pnode 29) (prelabel (pnode 47) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 29) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 47) perm0.symm

theorem edge29_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 29) 1) := by
  have he := mutation_equal (pnode 29) (preverse (prelabel (fork [26] [97] [7] [2518] [183] [5]) perm9.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (node_safe t 29)
  rw [show mutate (node t 29) 1=(reverse (relabel (matrix (fork [26] [97] [7] [2518] [183] [5]) t) perm9.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [26] [97] [7] [2518] [183] [5] t ht (by decide)) perm9.symm)

theorem edge29_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 29) 2) := by
  have he := mutation_equal (pnode 29) (prelabel (pnode 14) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 29) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 14) perm0.symm

theorem edge29_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 29) 3) := by
  have he := mutation_equal (pnode 29) (prelabel (fork [4] [97] [5] [362] [19] [7]) perm23.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 3 (node_safe t 29)
  rw [show mutate (node t 29) 3=(relabel (matrix (fork [4] [97] [5] [362] [19] [7]) t) perm23.symm) from he]
  exact IsFork.relabelled (fork_sound [4] [97] [5] [362] [19] [7] t ht (by decide)) perm23.symm

theorem edge30_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 30) 0) := by
  have he := mutation_equal (pnode 30) (prelabel (pnode 15) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 30) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 15) perm0.symm

theorem edge30_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 30) 1) := by
  have he := mutation_equal (pnode 30) (preverse (prelabel (zero param12_0 param12_1 param12_2 param12_3 1) perm15.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 30) t) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (region12_safe t ht 1) perm15.symm)

theorem edge30_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 30) 2) := by
  have he := mutation_equal (pnode 30) (prelabel (pnode 27) perm14.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 30) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 27) perm14.symm

theorem edge30_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 30) 3) := by
  have he := mutation_equal (pnode 30) (prelabel (pnode 48) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 30) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 48) perm0.symm

theorem edge31_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 31) 0) := by
  have he := mutation_equal (pnode 31) (prelabel (pnode 49) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 31) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 49) perm0.symm

theorem edge31_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 31) 1) := by
  have he := mutation_equal (pnode 31) (preverse (prelabel (fork [11] [97] [2] [1058] [23] [10]) perm11.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (node_safe t 31)
  rw [show mutate (node t 31) 1=(reverse (relabel (matrix (fork [11] [97] [2] [1058] [23] [10]) t) perm11.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [11] [97] [2] [1058] [23] [10] t ht (by decide)) perm11.symm)

theorem edge31_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 31) 2) := by
  have he := mutation_equal (pnode 31) (prelabel (fork [9] [97] [10] [862] [89] [2]) perm17.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 2 (node_safe t 31)
  rw [show mutate (node t 31) 2=(relabel (matrix (fork [9] [97] [10] [862] [89] [2]) t) perm17.symm) from he]
  exact IsFork.relabelled (fork_sound [9] [97] [10] [862] [89] [2] t ht (by decide)) perm17.symm

theorem edge31_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 31) 3) := by
  have he := mutation_equal (pnode 31) (prelabel (pnode 15) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 31) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 15) perm0.symm

theorem edge32_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 32) 0) := by
  have he := mutation_equal (pnode 32) (prelabel (pnode 16) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 32) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 16) perm0.symm

theorem edge32_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 32) 1) := by
  have he := mutation_equal (pnode 32) (prelabel (zero param13_0 param13_1 param13_2 param13_3 1) perm21.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 32) t) 1)
  rw [he]
  exact Safe.framed (region13_safe t ht 1) perm21.symm

theorem edge32_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 32) 2) := by
  have he := mutation_equal (pnode 32) (prelabel (pnode 50) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 32) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 50) perm0.symm

theorem edge32_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 32) 3) := by
  have he := mutation_equal (pnode 32) (prelabel (pnode 28) perm21.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 32) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 28) perm21.symm

theorem edge33_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 33) 0) := by
  have he := mutation_equal (pnode 33) (prelabel (pnode 51) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 33) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 51) perm0.symm

theorem edge33_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 33) 1) := by
  have he := mutation_equal (pnode 33) (prelabel (fork [61] [542] [7] [33053] [428] [10]) perm9.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (node_safe t 33)
  rw [show mutate (node t 33) 1=(relabel (matrix (fork [61] [542] [7] [33053] [428] [10]) t) perm9.symm) from he]
  exact IsFork.relabelled (fork_sound [61] [542] [7] [33053] [428] [10] t ht (by decide)) perm9.symm

theorem edge33_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 33) 2) := by
  have he := mutation_equal (pnode 33) (prelabel (pnode 16) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 33) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 16) perm0.symm

theorem edge33_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 33) 3) := by
  have he := mutation_equal (pnode 33) (preverse (prelabel (fork [9] [542] [10] [4817] [89] [7]) perm23.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 3 (node_safe t 33)
  rw [show mutate (node t 33) 3=(reverse (relabel (matrix (fork [9] [542] [10] [4817] [89] [7]) t) perm23.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [9] [542] [10] [4817] [89] [7] t ht (by decide)) perm23.symm)

theorem edge34_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 34) 0) := by
  have he := mutation_equal (pnode 34) (preverse (prelabel (generic param0_0 param0_1 param0_2 param0_3 1) perm5.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 34) t) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (region0_safe t ht 1) perm5.symm)

theorem edge34_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 34) 1) := by
  have he := mutation_equal (pnode 34) (prelabel (root [33] [4352] [857] [132] [26] [1]) perm8.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 34) 1
  rw [show mutate (node t 34) 1=(relabel (matrix (root [33] [4352] [857] [132] [26] [1]) t) perm8.symm) from he]
  exact IsRoot.relabelled (root_sound [33] [4352] [857] [132] [26] [1] t ht (by decide)) perm8.symm

theorem edge34_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 34) 2) := by
  have he := mutation_equal (pnode 34) (prelabel (pnode 17) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 34) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 17) perm0.symm

theorem edge34_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 34) 3) := by
  have he := mutation_equal (pnode 34) (prelabel (pnode 47) perm15.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 34) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 47) perm15.symm

theorem edge35_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 35) 0) := by
  have he := mutation_equal (pnode 35) (prelabel (pnode 18) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 35) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 18) perm0.symm

theorem edge35_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 35) 1) := by
  have he := mutation_equal (pnode 35) (prelabel (pnode 53) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 35) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 53) perm0.symm

theorem edge35_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 35) 2) := by
  have he := mutation_equal (pnode 35) (preverse (prelabel (root [3] [5] [26] [2] [10] [1]) perm13.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 35) 2
  rw [show mutate (node t 35) 2=(reverse (relabel (matrix (root [3] [5] [26] [2] [10] [1]) t) perm13.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [3] [5] [26] [2] [10] [1] t ht (by decide)) perm13.symm)

theorem edge35_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 35) 3) := by
  have he := mutation_equal (pnode 35) (prelabel (pnode 54) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 35) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 54) perm0.symm

theorem edge36_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 36) 0) := by
  have he := mutation_equal (pnode 36) (prelabel (pnode 55) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 36) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 55) perm0.symm

theorem edge36_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 36) 1) := by
  have he := mutation_equal (pnode 36) (prelabel (pnode 18) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 36) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 18) perm0.symm

theorem edge36_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 36) 2) := by
  have he := mutation_equal (pnode 36) (prelabel (root [2] [5] [6] [3] [5] [1]) perm15.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 36) 2
  rw [show mutate (node t 36) 2=(relabel (matrix (root [2] [5] [6] [3] [5] [1]) t) perm15.symm) from he]
  exact IsRoot.relabelled (root_sound [2] [5] [6] [3] [5] [1] t ht (by decide)) perm15.symm

theorem edge36_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 36) 3) := by
  have he := mutation_equal (pnode 36) (prelabel (pnode 56) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 36) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 56) perm0.symm

theorem edge37_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 37) 0) := by
  have he := mutation_equal (pnode 37) (prelabel (pnode 57) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 37) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 57) perm0.symm

theorem edge37_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 37) 1) := by
  have he := mutation_equal (pnode 37) (prelabel (pnode 58) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 37) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 58) perm0.symm

theorem edge37_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 37) 2) := by
  have he := mutation_equal (pnode 37) (preverse (prelabel (pnode 19) perm15.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 37) t) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (node_safe t 19) perm15.symm)

theorem edge37_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 37) 3) := by
  have he := mutation_equal (pnode 37) (prelabel (pnode 18) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 37) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 18) perm0.symm

theorem edge38_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 38) 0) := by
  have he := mutation_equal (pnode 38) (prelabel (pnode 59) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 38) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 59) perm0.symm

theorem edge38_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 38) 1) := by
  have he := mutation_equal (pnode 38) (prelabel (pnode 21) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 38) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 21) perm0.symm

theorem edge38_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 38) 2) := by
  have he := mutation_equal (pnode 38) (prelabel (fork [13] [12] [753] [155] [9731] [4]) perm14.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 2 (node_safe t 38)
  rw [show mutate (node t 38) 2=(relabel (matrix (fork [13] [12] [753] [155] [9731] [4]) t) perm14.symm) from he]
  exact IsFork.relabelled (fork_sound [13] [12] [753] [155] [9731] [4] t ht (by decide)) perm14.symm

theorem edge38_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 38) 3) := by
  have he := mutation_equal (pnode 38) (preverse (prelabel (root [753] [3024] [43661] [4] [58] [1]) perm22.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 38) 3
  rw [show mutate (node t 38) 3=(reverse (relabel (matrix (root [753] [3024] [43661] [4] [58] [1]) t) perm22.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [753] [3024] [43661] [4] [58] [1] t ht (by decide)) perm22.symm)

theorem edge39_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 39) 0) := by
  have he := mutation_equal (pnode 39) (prelabel (generic param1_0 param1_1 param1_2 param1_3 1) perm3.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 39) t) 0)
  rw [he]
  exact Safe.framed (region1_safe t ht 1) perm3.symm

theorem edge39_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 39) 1) := by
  have he := mutation_equal (pnode 39) (preverse (prelabel (root [58] [13510] [2609] [233] [45] [1]) perm10.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 39) 1
  rw [show mutate (node t 39) 1=(reverse (relabel (matrix (root [58] [13510] [2609] [233] [45] [1]) t) perm10.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [58] [13510] [2609] [233] [45] [1] t ht (by decide)) perm10.symm)

theorem edge39_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 39) 2) := by
  have he := mutation_equal (pnode 39) (prelabel (pnode 40) perm1.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 39) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 40) perm1.symm

theorem edge39_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 39) 3) := by
  have he := mutation_equal (pnode 39) (prelabel (pnode 21) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 39) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 21) perm0.symm

theorem edge40_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 40) 0) := by
  have he := mutation_equal (pnode 40) (prelabel (pnode 60) perm20.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 40) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 60) perm20.symm

theorem edge40_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 40) 1) := by
  have he := mutation_equal (pnode 40) (prelabel (root [233] [10486] [3024] [45] [13] [1]) perm7.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 40) 1
  rw [show mutate (node t 40) 1=(relabel (matrix (root [233] [10486] [3024] [45] [13] [1]) t) perm7.symm) from he]
  exact IsRoot.relabelled (root_sound [233] [10486] [3024] [45] [13] [1] t ht (by decide)) perm7.symm

theorem edge40_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 40) 2) := by
  have he := mutation_equal (pnode 40) (prelabel (pnode 22) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 40) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 22) perm0.symm

theorem edge40_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 40) 3) := by
  have he := mutation_equal (pnode 40) (prelabel (pnode 39) perm1.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 40) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 39) perm1.symm

theorem edge41_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 41) 0) := by
  have he := mutation_equal (pnode 41) (preverse (prelabel (fork [12] [4540] [13] [54099] [155] [34]) perm1.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (node_safe t 41)
  rw [show mutate (node t 41) 0=(reverse (relabel (matrix (fork [12] [4540] [13] [54099] [155] [34]) t) perm1.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [12] [4540] [13] [54099] [155] [34] t ht (by decide)) perm1.symm)

theorem edge41_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 41) 1) := by
  have he := mutation_equal (pnode 41) (prelabel (pnode 23) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 41) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 23) perm0.symm

theorem edge41_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 41) 2) := by
  have he := mutation_equal (pnode 41) (prelabel (pnode 61) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 41) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 61) perm0.symm

theorem edge41_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 41) 3) := by
  have he := mutation_equal (pnode 41) (prelabel (fork [381] [4540] [34] [1729728] [12955] [13]) perm20.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 3 (node_safe t 41)
  rw [show mutate (node t 41) 3=(relabel (matrix (fork [381] [4540] [34] [1729728] [12955] [13]) t) perm20.symm) from he]
  exact IsFork.relabelled (fork_sound [381] [4540] [34] [1729728] [12955] [13] t ht (by decide)) perm20.symm

theorem edge42_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 42) 0) := by
  have he := mutation_equal (pnode 42) (prelabel (pnode 43) perm14.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 42) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 43) perm14.symm

theorem edge42_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 42) 1) := by
  have he := mutation_equal (pnode 42) (prelabel (pnode 62) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 42) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 62) perm0.symm

theorem edge42_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 42) 2) := by
  have he := mutation_equal (pnode 42) (prelabel (pnode 23) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 42) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 23) perm0.symm

theorem edge42_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 42) 3) := by
  have he := mutation_equal (pnode 42) (prelabel (fork [34] [2] [415] [67] [14109] [12]) perm22.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 3 (node_safe t 42)
  rw [show mutate (node t 42) 3=(relabel (matrix (fork [34] [2] [415] [67] [14109] [12]) t) perm22.symm) from he]
  exact IsFork.relabelled (fork_sound [34] [2] [415] [67] [14109] [12] t ht (by decide)) perm22.symm

theorem edge43_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 43) 0) := by
  have he := mutation_equal (pnode 43) (prelabel (pnode 24) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 43) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 24) perm0.symm

theorem edge43_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 43) 1) := by
  have he := mutation_equal (pnode 43) (preverse (prelabel (fork [13] [12] [415] [155] [5363] [2]) perm6.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (node_safe t 43)
  rw [show mutate (node t 43) 1=(reverse (relabel (matrix (fork [13] [12] [415] [155] [5363] [2]) t) perm6.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [13] [12] [415] [155] [5363] [2] t ht (by decide)) perm6.symm)

theorem edge43_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 43) 2) := by
  have he := mutation_equal (pnode 43) (prelabel (pnode 42) perm14.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 43) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 42) perm14.symm

theorem edge43_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 43) 3) := by
  have he := mutation_equal (pnode 43) (prelabel (root [415] [842] [13267] [2] [32] [1]) perm21.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 43) 3
  rw [show mutate (node t 43) 3=(relabel (matrix (root [415] [842] [13267] [2] [32] [1]) t) perm21.symm) from he]
  exact IsRoot.relabelled (root_sound [415] [842] [13267] [2] [32] [1] t ht (by decide)) perm21.symm

theorem edge44_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 44) 0) := by
  have he := mutation_equal (pnode 44) (prelabel (root [32] [2078] [607] [65] [19] [1]) perm5.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 44) 0
  rw [show mutate (node t 44) 0=(relabel (matrix (root [32] [2078] [607] [65] [19] [1]) t) perm5.symm) from he]
  exact IsRoot.relabelled (root_sound [32] [2078] [607] [65] [19] [1] t ht (by decide)) perm5.symm

theorem edge44_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 44) 1) := by
  have he := mutation_equal (pnode 44) (prelabel (pnode 63) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 44) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 63) perm0.symm

theorem edge44_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 44) 2) := by
  have he := mutation_equal (pnode 44) (preverse (prelabel (generic param2_0 param2_1 param2_2 param2_3 1) perm15.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 44) t) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (region2_safe t ht 1) perm15.symm)

theorem edge44_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 44) 3) := by
  have he := mutation_equal (pnode 44) (prelabel (pnode 24) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 44) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 24) perm0.symm

theorem edge45_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 45) 0) := by
  have he := mutation_equal (pnode 45) (prelabel (pnode 65) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 45) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 65) perm0.symm

theorem edge45_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 45) 1) := by
  have he := mutation_equal (pnode 45) (prelabel (pnode 25) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 45) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 25) perm0.symm

theorem edge45_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 45) 2) := by
  have he := mutation_equal (pnode 45) (prelabel (pnode 59) perm8.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 45) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 59) perm8.symm

theorem edge45_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 45) 3) := by
  have he := mutation_equal (pnode 45) (prelabel (root [58] [3595] [40066] [62] [691] [1]) perm21.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 45) 3
  rw [show mutate (node t 45) 3=(relabel (matrix (root [58] [3595] [40066] [62] [691] [1]) t) perm21.symm) from he]
  exact IsRoot.relabelled (root_sound [58] [3595] [40066] [62] [691] [1] t ht (by decide)) perm21.symm

theorem edge46_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 46) 0) := by
  have he := mutation_equal (pnode 46) (preverse (prelabel (fork [19] [26] [13] [492] [248] [3]) perm4.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (node_safe t 46)
  rw [show mutate (node t 46) 0=(reverse (relabel (matrix (fork [19] [26] [13] [492] [248] [3]) t) perm4.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [19] [26] [13] [492] [248] [3] t ht (by decide)) perm4.symm)

theorem edge46_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 46) 1) := by
  have he := mutation_equal (pnode 46) (prelabel (fork [2] [26] [3] [33] [5] [13]) perm10.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (node_safe t 46)
  rw [show mutate (node t 46) 1=(relabel (matrix (fork [2] [26] [3] [33] [5] [13]) t) perm10.symm) from he]
  exact IsFork.relabelled (fork_sound [2] [26] [3] [33] [5] [13] t ht (by decide)) perm10.symm

theorem edge46_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 46) 2) := by
  have he := mutation_equal (pnode 46) (prelabel (pnode 63) perm4.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 46) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 63) perm4.symm

theorem edge46_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 46) 3) := by
  have he := mutation_equal (pnode 46) (prelabel (pnode 26) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 46) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 26) perm0.symm

theorem edge47_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 47) 0) := by
  have he := mutation_equal (pnode 47) (prelabel (pnode 29) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 47) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 29) perm0.symm

theorem edge47_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 47) 1) := by
  have he := mutation_equal (pnode 47) (preverse (prelabel (root [132] [3433] [919] [26] [7] [1]) perm11.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 47) 1
  rw [show mutate (node t 47) 1=(reverse (relabel (matrix (root [132] [3433] [919] [26] [7] [1]) t) perm11.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [132] [3433] [919] [26] [7] [1] t ht (by decide)) perm11.symm)

theorem edge47_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 47) 2) := by
  have he := mutation_equal (pnode 47) (prelabel (pnode 34) perm20.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 47) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 34) perm20.symm

theorem edge47_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 47) 3) := by
  have he := mutation_equal (pnode 47) (prelabel (pnode 52) perm14.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 47) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 52) perm14.symm

theorem edge48_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 48) 0) := by
  have he := mutation_equal (pnode 48) (prelabel (pnode 49) perm21.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 48) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 49) perm21.symm

theorem edge48_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 48) 1) := by
  have he := mutation_equal (pnode 48) (prelabel (root [13] [1512] [142] [117] [11] [1]) perm11.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 48) 1
  rw [show mutate (node t 48) 1=(relabel (matrix (root [13] [1512] [142] [117] [11] [1]) t) perm11.symm) from he]
  exact IsRoot.relabelled (root_sound [13] [1512] [142] [117] [11] [1] t ht (by decide)) perm11.symm

theorem edge48_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 48) 2) := by
  have he := mutation_equal (pnode 48) (preverse (prelabel (generic param3_0 param3_1 param3_2 param3_3 1) perm13.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 48) t) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (region3_safe t ht 1) perm13.symm)

theorem edge48_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 48) 3) := by
  have he := mutation_equal (pnode 48) (prelabel (pnode 30) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 48) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 30) perm0.symm

theorem edge49_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 49) 0) := by
  have he := mutation_equal (pnode 49) (prelabel (pnode 31) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 49) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 31) perm0.symm

theorem edge49_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 49) 1) := by
  have he := mutation_equal (pnode 49) (preverse (prelabel (root [117] [1288] [224] [11] [2] [1]) perm9.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 49) 1
  rw [show mutate (node t 49) 1=(reverse (relabel (matrix (root [117] [1288] [224] [11] [2] [1]) t) perm9.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [117] [1288] [224] [11] [2] [1] t ht (by decide)) perm9.symm)

theorem edge49_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 49) 2) := by
  have he := mutation_equal (pnode 49) (prelabel (pnode 66) perm15.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 49) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 66) perm15.symm

theorem edge49_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 49) 3) := by
  have he := mutation_equal (pnode 49) (prelabel (pnode 48) perm21.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 49) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 48) perm21.symm

theorem edge50_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 50) 0) := by
  have he := mutation_equal (pnode 50) (prelabel (pnode 51) perm14.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 50) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 51) perm14.symm

theorem edge50_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 50) 1) := by
  have he := mutation_equal (pnode 50) (preverse (prelabel (root [68] [41607] [4147] [612] [61] [1]) perm9.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 50) 1
  rw [show mutate (node t 50) 1=(reverse (relabel (matrix (root [68] [41607] [4147] [612] [61] [1]) t) perm9.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [68] [41607] [4147] [612] [61] [1] t ht (by decide)) perm9.symm)

theorem edge50_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 50) 2) := by
  have he := mutation_equal (pnode 50) (prelabel (pnode 32) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 50) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 32) perm0.symm

theorem edge50_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 50) 3) := by
  have he := mutation_equal (pnode 50) (prelabel (generic param4_0 param4_1 param4_2 param4_3 1) perm19.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 50) t) 3)
  rw [he]
  exact Safe.framed (region4_safe t ht 1) perm19.symm

theorem edge51_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 51) 0) := by
  have he := mutation_equal (pnode 51) (prelabel (pnode 33) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 51) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 33) perm0.symm

theorem edge51_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 51) 1) := by
  have he := mutation_equal (pnode 51) (prelabel (root [612] [37333] [4274] [61] [7] [1]) perm11.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 51) 1
  rw [show mutate (node t 51) 1=(relabel (matrix (root [612] [37333] [4274] [61] [7] [1]) t) perm11.symm) from he]
  exact IsRoot.relabelled (root_sound [612] [37333] [4274] [61] [7] [1] t ht (by decide)) perm11.symm

theorem edge51_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 51) 2) := by
  have he := mutation_equal (pnode 51) (prelabel (pnode 50) perm14.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 51) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 50) perm14.symm

theorem edge51_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 51) 3) := by
  have he := mutation_equal (pnode 51) (prelabel (pnode 67) perm20.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 51) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 67) perm20.symm

theorem edge52_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 52) 0) := by
  have he := mutation_equal (pnode 52) (preverse (prelabel (generic param0_0 param0_1 param0_2 param0_3 2) perm5.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 52) t) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (region0_safe t ht 2) perm5.symm)

theorem edge52_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 52) 1) := by
  have he := mutation_equal (pnode 52) (preverse (prelabel (root [653] [16982] [86191] [26] [132] [1]) perm8.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 52) 1
  rw [show mutate (node t 52) 1=(reverse (relabel (matrix (root [653] [16982] [86191] [26] [132] [1]) t) perm8.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [653] [16982] [86191] [26] [132] [1] t ht (by decide)) perm8.symm)

theorem edge52_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 52) 2) := by
  have he := mutation_equal (pnode 52) (prelabel (fork [5] [4] [653] [19] [3133] [26]) perm16.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 2 (node_safe t 52)
  rw [show mutate (node t 52) 2=(relabel (matrix (fork [5] [4] [653] [19] [3133] [26]) t) perm16.symm) from he]
  exact IsFork.relabelled (fork_sound [5] [4] [653] [19] [3133] [26] t ht (by decide)) perm16.symm

theorem edge52_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 52) 3) := by
  have he := mutation_equal (pnode 52) (prelabel (pnode 47) perm14.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 52) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 47) perm14.symm

theorem edge53_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 53) 0) := by
  have he := mutation_equal (pnode 53) (preverse (prelabel (fork [4] [37] [5] [138] [19] [2]) perm0.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (node_safe t 53)
  rw [show mutate (node t 53) 0=(reverse (relabel (matrix (fork [4] [37] [5] [138] [19] [2]) t) perm0.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [4] [37] [5] [138] [19] [2] t ht (by decide)) perm0.symm)

theorem edge53_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 53) 1) := by
  have he := mutation_equal (pnode 53) (prelabel (pnode 35) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 53) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 35) perm0.symm

theorem edge53_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 53) 2) := by
  have he := mutation_equal (pnode 53) (prelabel (fork [10] [37] [2] [366] [21] [5]) perm14.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 2 (node_safe t 53)
  rw [show mutate (node t 53) 2=(relabel (matrix (fork [10] [37] [2] [366] [21] [5]) t) perm14.symm) from he]
  exact IsFork.relabelled (fork_sound [10] [37] [2] [366] [21] [5] t ht (by decide)) perm14.symm

theorem edge53_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 53) 3) := by
  have he := mutation_equal (pnode 53) (prelabel (pnode 68) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 53) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 68) perm0.symm

theorem edge54_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 54) 0) := by
  have he := mutation_equal (pnode 54) (prelabel (pnode 57) perm21.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 54) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 57) perm21.symm

theorem edge54_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 54) 1) := by
  have he := mutation_equal (pnode 54) (prelabel (pnode 69) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 54) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 69) perm0.symm

theorem edge54_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 54) 2) := by
  have he := mutation_equal (pnode 54) (prelabel (pnode 70) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 54) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 70) perm0.symm

theorem edge54_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 54) 3) := by
  have he := mutation_equal (pnode 54) (prelabel (pnode 35) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 54) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 35) perm0.symm

theorem edge55_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 55) 0) := by
  have he := mutation_equal (pnode 55) (prelabel (pnode 36) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 55) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 36) perm0.symm

theorem edge55_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 55) 1) := by
  have he := mutation_equal (pnode 55) (prelabel (fork [4] [18] [5] [67] [19] [3]) perm6.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (node_safe t 55)
  rw [show mutate (node t 55) 1=(relabel (matrix (fork [4] [18] [5] [67] [19] [3]) t) perm6.symm) from he]
  exact IsFork.relabelled (fork_sound [4] [18] [5] [67] [19] [3] t ht (by decide)) perm6.symm

theorem edge55_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 55) 2) := by
  have he := mutation_equal (pnode 55) (preverse (prelabel (fork [5] [18] [3] [86] [16] [5]) perm12.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 2 (node_safe t 55)
  rw [show mutate (node t 55) 2=(reverse (relabel (matrix (fork [5] [18] [3] [86] [16] [5]) t) perm12.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [5] [18] [3] [86] [16] [5] t ht (by decide)) perm12.symm)

theorem edge55_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 55) 3) := by
  have he := mutation_equal (pnode 55) (prelabel (pnode 71) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 55) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 71) perm0.symm

theorem edge56_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 56) 0) := by
  have he := mutation_equal (pnode 56) (prelabel (pnode 72) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 56) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 72) perm0.symm

theorem edge56_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 56) 1) := by
  have he := mutation_equal (pnode 56) (prelabel (pnode 58) perm5.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 56) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 58) perm5.symm

theorem edge56_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 56) 2) := by
  have he := mutation_equal (pnode 56) (prelabel (pnode 73) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 56) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 73) perm0.symm

theorem edge56_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 56) 3) := by
  have he := mutation_equal (pnode 56) (prelabel (pnode 36) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 56) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 36) perm0.symm

theorem edge57_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 57) 0) := by
  have he := mutation_equal (pnode 57) (prelabel (pnode 37) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 57) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 37) perm0.symm

theorem edge57_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 57) 1) := by
  have he := mutation_equal (pnode 57) (prelabel (root [5] [19] [38] [4] [8] [1]) perm7.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 57) 1
  rw [show mutate (node t 57) 1=(relabel (matrix (root [5] [19] [38] [4] [8] [1]) t) perm7.symm) from he]
  exact IsRoot.relabelled (root_sound [5] [19] [38] [4] [8] [1] t ht (by decide)) perm7.symm

theorem edge57_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 57) 2) := by
  have he := mutation_equal (pnode 57) (prelabel (pnode 74) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 57) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 74) perm0.symm

theorem edge57_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 57) 3) := by
  have he := mutation_equal (pnode 57) (prelabel (pnode 54) perm21.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 57) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 54) perm21.symm

theorem edge58_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 58) 0) := by
  have he := mutation_equal (pnode 58) (preverse (prelabel (root [5] [38] [19] [8] [4] [1]) perm0.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 58) 0
  rw [show mutate (node t 58) 0=(reverse (relabel (matrix (root [5] [38] [19] [8] [4] [1]) t) perm0.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [5] [38] [19] [8] [4] [1] t ht (by decide)) perm0.symm)

theorem edge58_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 58) 1) := by
  have he := mutation_equal (pnode 58) (prelabel (pnode 37) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 58) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 37) perm0.symm

theorem edge58_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 58) 2) := by
  have he := mutation_equal (pnode 58) (prelabel (generic param5_0 param5_1 param5_2 param5_3 1) perm17.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 58) t) 2)
  rw [he]
  exact Safe.framed (region5_safe t ht 1) perm17.symm

theorem edge58_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 58) 3) := by
  have he := mutation_equal (pnode 58) (prelabel (pnode 56) perm5.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 58) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 56) perm5.symm

theorem edge59_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 59) 0) := by
  have he := mutation_equal (pnode 59) (prelabel (pnode 38) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 59) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 38) perm0.symm

theorem edge59_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 59) 1) := by
  have he := mutation_equal (pnode 59) (prelabel (pnode 45) perm12.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 59) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 45) perm12.symm

theorem edge59_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 59) 2) := by
  have he := mutation_equal (pnode 59) (prelabel (pnode 75) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 59) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 75) perm0.symm

theorem edge59_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 59) 3) := by
  have he := mutation_equal (pnode 59) (preverse (prelabel (fork [62] [4] [753] [247] [46685] [12]) perm20.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 3 (node_safe t 59)
  rw [show mutate (node t 59) 3=(reverse (relabel (matrix (fork [62] [4] [753] [247] [46685] [12]) t) perm20.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [62] [4] [753] [247] [46685] [12] t ht (by decide)) perm20.symm)

theorem edge60_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 60) 0) := by
  have he := mutation_equal (pnode 60) (prelabel (generic param1_0 param1_1 param1_2 param1_3 2) perm3.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 60) t) 0)
  rw [he]
  exact Safe.framed (region1_safe t ht 2) perm3.symm

theorem edge60_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 60) 1) := by
  have he := mutation_equal (pnode 60) (prelabel (root [1152] [51844] [268411] [45] [233] [1]) perm10.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 60) 1
  rw [show mutate (node t 60) 1=(relabel (matrix (root [1152] [51844] [268411] [45] [233] [1]) t) perm10.symm) from he]
  exact IsRoot.relabelled (root_sound [1152] [51844] [268411] [45] [233] [1] t ht (by decide)) perm10.symm

theorem edge60_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 60) 2) := by
  have he := mutation_equal (pnode 60) (prelabel (pnode 40) perm15.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 60) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 40) perm15.symm

theorem edge60_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 60) 3) := by
  have he := mutation_equal (pnode 60) (preverse (prelabel (fork [5] [4] [1152] [19] [5527] [45]) perm22.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 3 (node_safe t 60)
  rw [show mutate (node t 60) 3=(reverse (relabel (matrix (fork [5] [4] [1152] [19] [5527] [45]) t) perm22.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [5] [4] [1152] [19] [5527] [45] t ht (by decide)) perm22.symm)

theorem edge61_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 61) 0) := by
  have he := mutation_equal (pnode 61) (prelabel (pnode 76) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 61) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 76) perm0.symm

theorem edge61_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 61) 1) := by
  have he := mutation_equal (pnode 61) (prelabel (pnode 62) perm2.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 61) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 62) perm2.symm

theorem edge61_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 61) 2) := by
  have he := mutation_equal (pnode 61) (prelabel (pnode 41) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 61) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 41) perm0.symm

theorem edge61_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 61) 3) := by
  have he := mutation_equal (pnode 61) (prelabel (root [4982] [1898143] [169375] [381] [34] [1]) perm18.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 61) 3
  rw [show mutate (node t 61) 3=(relabel (matrix (root [4982] [1898143] [169375] [381] [34] [1]) t) perm18.symm) from he]
  exact IsRoot.relabelled (root_sound [4982] [1898143] [169375] [381] [34] [1] t ht (by decide)) perm18.symm

theorem edge62_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 62) 0) := by
  have he := mutation_equal (pnode 62) (prelabel (generic param6_0 param6_1 param6_2 param6_3 1) perm2.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 62) t) 0)
  rw [he]
  exact Safe.framed (region6_safe t ht 1) perm2.symm

theorem edge62_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 62) 1) := by
  have he := mutation_equal (pnode 62) (prelabel (pnode 42) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 62) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 42) perm0.symm

theorem edge62_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 62) 2) := by
  have he := mutation_equal (pnode 62) (prelabel (pnode 61) perm2.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 62) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 61) perm2.symm

theorem edge62_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 62) 3) := by
  have he := mutation_equal (pnode 62) (preverse (prelabel (root [415] [2067518] [158114] [4982] [381] [1]) perm20.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 62) 3
  rw [show mutate (node t 62) 3=(reverse (relabel (matrix (root [415] [2067518] [158114] [4982] [381] [1]) t) perm20.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [415] [2067518] [158114] [4982] [381] [1] t ht (by decide)) perm20.symm)

theorem edge63_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 63) 0) := by
  have he := mutation_equal (pnode 63) (preverse (prelabel (root [65] [1236] [842] [19] [13] [1]) perm2.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 63) 0
  rw [show mutate (node t 63) 0=(reverse (relabel (matrix (root [65] [1236] [842] [19] [13] [1]) t) perm2.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [65] [1236] [842] [19] [13] [1] t ht (by decide)) perm2.symm)

theorem edge63_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 63) 1) := by
  have he := mutation_equal (pnode 63) (prelabel (pnode 44) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 63) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 44) perm0.symm

theorem edge63_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 63) 2) := by
  have he := mutation_equal (pnode 63) (prelabel (pnode 64) perm2.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 63) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 64) perm2.symm

theorem edge63_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 63) 3) := by
  have he := mutation_equal (pnode 63) (prelabel (pnode 46) perm3.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 63) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 46) perm3.symm

theorem edge64_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 64) 0) := by
  have he := mutation_equal (pnode 64) (preverse (prelabel (root [182] [3460] [11827] [19] [65] [1]) perm5.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 64) 0
  rw [show mutate (node t 64) 0=(reverse (relabel (matrix (root [182] [3460] [11827] [19] [65] [1]) t) perm5.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [182] [3460] [11827] [19] [65] [1] t ht (by decide)) perm5.symm)

theorem edge64_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 64) 1) := by
  have he := mutation_equal (pnode 64) (prelabel (pnode 63) perm2.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 64) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 63) perm2.symm

theorem edge64_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 64) 2) := by
  have he := mutation_equal (pnode 64) (preverse (prelabel (generic param2_0 param2_1 param2_2 param2_3 2) perm15.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 64) t) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (region2_safe t ht 2) perm15.symm)

theorem edge64_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 64) 3) := by
  have he := mutation_equal (pnode 64) (prelabel (fork [3] [2] [182] [5] [481] [19]) perm21.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 3 (node_safe t 64)
  rw [show mutate (node t 64) 3=(relabel (matrix (fork [3] [2] [182] [5] [481] [19]) t) perm21.symm) from he]
  exact IsFork.relabelled (fork_sound [3] [2] [182] [5] [481] [19] t ht (by decide)) perm21.symm

theorem edge65_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 65) 0) := by
  have he := mutation_equal (pnode 65) (prelabel (pnode 45) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 65) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 45) perm0.symm

theorem edge65_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 65) 1) := by
  have he := mutation_equal (pnode 65) (prelabel (fork [12] [8234] [13] [98117] [155] [62]) perm7.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (node_safe t 65)
  rw [show mutate (node t 65) 1=(relabel (matrix (fork [12] [8234] [13] [98117] [155] [62]) t) perm7.symm) from he]
  exact IsFork.relabelled (fork_sound [12] [8234] [13] [98117] [155] [62] t ht (by decide)) perm7.symm

theorem edge65_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 65) 2) := by
  have he := mutation_equal (pnode 65) (prelabel (pnode 77) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 65) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 77) perm0.symm

theorem edge65_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 65) 3) := by
  have he := mutation_equal (pnode 65) (preverse (prelabel (fork [691] [8234] [62] [5689682] [42843] [13]) perm18.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 3 (node_safe t 65)
  rw [show mutate (node t 65) 3=(reverse (relabel (matrix (fork [691] [8234] [62] [5689682] [42843] [13]) t) perm18.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [691] [8234] [62] [5689682] [42843] [13] t ht (by decide)) perm18.symm)

theorem edge66_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 66) 0) := by
  have he := mutation_equal (pnode 66) (prelabel (pnode 49) perm20.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 66) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 49) perm20.symm

theorem edge66_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 66) 1) := by
  have he := mutation_equal (pnode 66) (preverse (prelabel (root [1168] [12857] [136646] [11] [117] [1]) perm11.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 66) 1
  rw [show mutate (node t 66) 1=(reverse (relabel (matrix (root [1168] [12857] [136646] [11] [117] [1]) t) perm11.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [1168] [12857] [136646] [11] [117] [1] t ht (by decide)) perm11.symm)

theorem edge66_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 66) 2) := by
  have he := mutation_equal (pnode 66) (preverse (prelabel (generic param3_0 param3_1 param3_2 param3_3 2) perm13.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 66) t) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (region3_safe t ht 2) perm13.symm)

theorem edge66_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 66) 3) := by
  have he := mutation_equal (pnode 66) (prelabel (fork [10] [9] [1168] [89] [11563] [11]) perm19.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 3 (node_safe t 66)
  rw [show mutate (node t 66) 3=(relabel (matrix (fork [10] [9] [1168] [89] [11563] [11]) t) perm19.symm) from he]
  exact IsFork.relabelled (fork_sound [10] [9] [1168] [89] [11563] [11] t ht (by decide)) perm19.symm

theorem edge67_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 67) 0) := by
  have he := mutation_equal (pnode 67) (prelabel (pnode 51) perm15.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 67) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 51) perm15.symm

theorem edge67_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 67) 1) := by
  have he := mutation_equal (pnode 67) (prelabel (root [6113] [372902] [3741146] [61] [612] [1]) perm9.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 67) 1
  rw [show mutate (node t 67) 1=(relabel (matrix (root [6113] [372902] [3741146] [61] [612] [1]) t) perm9.symm) from he]
  exact IsRoot.relabelled (root_sound [6113] [372902] [3741146] [61] [612] [1] t ht (by decide)) perm9.symm

theorem edge67_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 67) 2) := by
  have he := mutation_equal (pnode 67) (preverse (prelabel (fork [10] [9] [6113] [89] [60518] [61]) perm13.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 2 (node_safe t 67)
  rw [show mutate (node t 67) 2=(reverse (relabel (matrix (fork [10] [9] [6113] [89] [60518] [61]) t) perm13.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [10] [9] [6113] [89] [60518] [61] t ht (by decide)) perm13.symm)

theorem edge67_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 67) 3) := by
  have he := mutation_equal (pnode 67) (prelabel (generic param4_0 param4_1 param4_2 param4_3 2) perm19.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 67) t) 3)
  rw [he]
  exact Safe.framed (region4_safe t ht 2) perm19.symm

theorem edge68_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 68) 0) := by
  have he := mutation_equal (pnode 68) (prelabel (pnode 78) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 68) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 78) perm0.symm

theorem edge68_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 68) 1) := by
  have he := mutation_equal (pnode 68) (prelabel (pnode 69) perm5.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 68) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 69) perm5.symm

theorem edge68_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 68) 2) := by
  have he := mutation_equal (pnode 68) (prelabel (root [47] [471] [89] [10] [2] [1]) perm12.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 68) 2
  rw [show mutate (node t 68) 2=(relabel (matrix (root [47] [471] [89] [10] [2] [1]) t) perm12.symm) from he]
  exact IsRoot.relabelled (root_sound [47] [471] [89] [10] [2] [1] t ht (by decide)) perm12.symm

theorem edge68_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 68) 3) := by
  have he := mutation_equal (pnode 68) (prelabel (pnode 53) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 68) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 53) perm0.symm

theorem edge69_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 69) 0) := by
  have he := mutation_equal (pnode 69) (prelabel (generic param7_0 param7_1 param7_2 param7_3 1) perm4.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 69) t) 0)
  rw [he]
  exact Safe.framed (region7_safe t ht 1) perm4.symm

theorem edge69_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 69) 1) := by
  have he := mutation_equal (pnode 69) (prelabel (pnode 54) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 69) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 54) perm0.symm

theorem edge69_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 69) 2) := by
  have he := mutation_equal (pnode 69) (preverse (prelabel (root [12] [560] [119] [47] [10] [1]) perm14.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 69) 2
  rw [show mutate (node t 69) 2=(reverse (relabel (matrix (root [12] [560] [119] [47] [10] [1]) t) perm14.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [12] [560] [119] [47] [10] [1] t ht (by decide)) perm14.symm)

theorem edge69_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 69) 3) := by
  have he := mutation_equal (pnode 69) (prelabel (pnode 68) perm5.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 69) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 68) perm5.symm

theorem edge70_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 70) 0) := by
  have he := mutation_equal (pnode 70) (prelabel (pnode 79) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 70) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 79) perm0.symm

theorem edge70_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 70) 1) := by
  have he := mutation_equal (pnode 70) (prelabel (root [12] [274] [95] [23] [8] [1]) perm9.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 70) 1
  rw [show mutate (node t 70) 1=(relabel (matrix (root [12] [274] [95] [23] [8] [1]) t) perm9.symm) from he]
  exact IsRoot.relabelled (root_sound [12] [274] [95] [23] [8] [1] t ht (by decide)) perm9.symm

theorem edge70_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 70) 2) := by
  have he := mutation_equal (pnode 70) (prelabel (pnode 54) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 70) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 54) perm0.symm

theorem edge70_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 70) 3) := by
  have he := mutation_equal (pnode 70) (preverse (prelabel (generic param8_0 param8_1 param8_2 param8_3 1) perm19.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 70) t) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (region8_safe t ht 1) perm19.symm)

theorem edge71_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 71) 0) := by
  have he := mutation_equal (pnode 71) (prelabel (pnode 72) perm21.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 71) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 72) perm21.symm

theorem edge71_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 71) 1) := by
  have he := mutation_equal (pnode 71) (prelabel (pnode 81) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 71) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 81) perm0.symm

theorem edge71_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 71) 2) := by
  have he := mutation_equal (pnode 71) (preverse (prelabel (root [33] [166] [94] [5] [3] [1]) perm14.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 71) 2
  rw [show mutate (node t 71) 2=(reverse (relabel (matrix (root [33] [166] [94] [5] [3] [1]) t) perm14.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [33] [166] [94] [5] [3] [1] t ht (by decide)) perm14.symm)

theorem edge71_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 71) 3) := by
  have he := mutation_equal (pnode 71) (prelabel (pnode 55) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 71) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 55) perm0.symm

theorem edge72_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 72) 0) := by
  have he := mutation_equal (pnode 72) (prelabel (pnode 56) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 72) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 56) perm0.symm

theorem edge72_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 72) 1) := by
  have he := mutation_equal (pnode 72) (preverse (prelabel (generic param9_0 param9_1 param9_2 param9_3 1) perm10.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 72) t) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (region9_safe t ht 1) perm10.symm)

theorem edge72_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 72) 2) := by
  have he := mutation_equal (pnode 72) (prelabel (root [8] [260] [39] [33] [5] [1]) perm12.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 72) 2
  rw [show mutate (node t 72) 2=(relabel (matrix (root [8] [260] [39] [33] [5] [1]) t) perm12.symm) from he]
  exact IsRoot.relabelled (root_sound [8] [260] [39] [33] [5] [1] t ht (by decide)) perm12.symm

theorem edge72_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 72) 3) := by
  have he := mutation_equal (pnode 72) (prelabel (pnode 71) perm21.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 72) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 71) perm21.symm

theorem edge73_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 73) 0) := by
  have he := mutation_equal (pnode 73) (prelabel (root [23] [94] [181] [4] [8] [1]) perm4.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 73) 0
  rw [show mutate (node t 73) 0=(relabel (matrix (root [23] [94] [181] [4] [8] [1]) t) perm4.symm) from he]
  exact IsRoot.relabelled (root_sound [23] [94] [181] [4] [8] [1] t ht (by decide)) perm4.symm

theorem edge73_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 73) 1) := by
  have he := mutation_equal (pnode 73) (prelabel (generic param5_0 param5_1 param5_2 param5_3 2) perm9.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 73) t) 1)
  rw [he]
  exact Safe.framed (region5_safe t ht 2) perm9.symm

theorem edge73_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 73) 2) := by
  have he := mutation_equal (pnode 73) (prelabel (pnode 56) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 73) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 56) perm0.symm

theorem edge73_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 73) 3) := by
  have he := mutation_equal (pnode 73) (preverse (prelabel (fork [3] [2] [23] [5] [61] [4]) perm23.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 3 (node_safe t 73)
  rw [show mutate (node t 73) 3=(reverse (relabel (matrix (fork [3] [2] [23] [5] [61] [4]) t) perm23.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [3] [2] [23] [5] [61] [4] t ht (by decide)) perm23.symm)

theorem edge74_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 74) 0) := by
  have he := mutation_equal (pnode 74) (prelabel (fork [2] [11] [3] [14] [5] [4]) perm2.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (node_safe t 74)
  rw [show mutate (node t 74) 0=(relabel (matrix (fork [2] [11] [3] [14] [5] [4]) t) perm2.symm) from he]
  exact IsFork.relabelled (fork_sound [2] [11] [3] [14] [5] [4] t ht (by decide)) perm2.symm

theorem edge74_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 74) 1) := by
  have he := mutation_equal (pnode 74) (preverse (prelabel (fork [8] [11] [4] [86] [33] [3]) perm8.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (node_safe t 74)
  rw [show mutate (node t 74) 1=(reverse (relabel (matrix (fork [8] [11] [4] [86] [33] [3]) t) perm8.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [8] [11] [4] [86] [33] [3] t ht (by decide)) perm8.symm)

theorem edge74_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 74) 2) := by
  have he := mutation_equal (pnode 74) (prelabel (pnode 57) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 74) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 57) perm0.symm

theorem edge74_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 74) 3) := by
  have he := mutation_equal (pnode 74) (prelabel (pnode 79) perm15.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 74) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 79) perm15.symm

theorem edge75_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 75) 0) := by
  have he := mutation_equal (pnode 75) (preverse (prelabel (generic param10_0 param10_1 param10_2 param10_3 1) perm0.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 75) t) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (region10_safe t ht 1) perm0.symm)

theorem edge75_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 75) 1) := by
  have he := mutation_equal (pnode 75) (prelabel (pnode 77) perm6.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 75) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 77) perm6.symm

theorem edge75_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 75) 2) := by
  have he := mutation_equal (pnode 75) (prelabel (pnode 59) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 75) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 59) perm0.symm

theorem edge75_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 75) 3) := by
  have he := mutation_equal (pnode 75) (prelabel (root [753] [6807108] [520322] [9040] [691] [1]) perm22.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 75) 3
  rw [show mutate (node t 75) 3=(relabel (matrix (root [753] [6807108] [520322] [9040] [691] [1]) t) perm22.symm) from he]
  exact IsRoot.relabelled (root_sound [753] [6807108] [520322] [9040] [691] [1] t ht (by decide)) perm22.symm

theorem edge76_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 76) 0) := by
  have he := mutation_equal (pnode 76) (prelabel (pnode 61) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 76) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 61) perm0.symm

theorem edge76_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 76) 1) := by
  have he := mutation_equal (pnode 76) (prelabel (generic param6_0 param6_1 param6_2 param6_3 2) perm6.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 76) t) 1)
  rw [he]
  exact Safe.framed (region6_safe t ht 2) perm6.symm

theorem edge76_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 76) 2) := by
  have he := mutation_equal (pnode 76) (preverse (prelabel (fork [13] [12] [64732] [155] [836534] [381]) perm12.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 2 (node_safe t 76)
  rw [show mutate (node t 76) 2=(reverse (relabel (matrix (fork [13] [12] [64732] [155] [836534] [381]) t) perm12.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [13] [12] [64732] [155] [836534] [381] t ht (by decide)) perm12.symm)

theorem edge76_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 76) 3) := by
  have he := mutation_equal (pnode 76) (prelabel (root [64732] [24662904] [322494811] [381] [4982] [1]) perm23.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 76) 3
  rw [show mutate (node t 76) 3=(relabel (matrix (root [64732] [24662904] [322494811] [381] [4982] [1]) t) perm23.symm) from he]
  exact IsRoot.relabelled (root_sound [64732] [24662904] [322494811] [381] [4982] [1] t ht (by decide)) perm23.symm

theorem edge77_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 77) 0) := by
  have he := mutation_equal (pnode 77) (prelabel (pnode 75) perm6.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 77) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 75) perm6.symm

theorem edge77_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 77) 1) := by
  have he := mutation_equal (pnode 77) (prelabel (pnode 82) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 77) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 82) perm0.symm

theorem edge77_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 77) 2) := by
  have he := mutation_equal (pnode 77) (prelabel (pnode 65) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 77) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 65) perm0.symm

theorem edge77_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 77) 3) := by
  have he := mutation_equal (pnode 77) (preverse (prelabel (root [9040] [6246641] [560467] [691] [62] [1]) perm20.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 77) 3
  rw [show mutate (node t 77) 3=(reverse (relabel (matrix (root [9040] [6246641] [560467] [691] [62] [1]) t) perm20.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [9040] [6246641] [560467] [691] [62] [1] t ht (by decide)) perm20.symm)

theorem edge78_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 78) 0) := by
  have he := mutation_equal (pnode 78) (prelabel (pnode 68) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 78) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 68) perm0.symm

theorem edge78_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 78) 1) := by
  have he := mutation_equal (pnode 78) (prelabel (generic param7_0 param7_1 param7_2 param7_3 2) perm7.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 78) t) 1)
  rw [he]
  exact Safe.framed (region7_safe t ht 2) perm7.symm

theorem edge78_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 78) 2) := by
  have he := mutation_equal (pnode 78) (prelabel (root [233] [2334] [10946] [10] [47] [1]) perm17.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 78) 2
  rw [show mutate (node t 78) 2=(relabel (matrix (root [233] [2334] [10946] [10] [47] [1]) t) perm17.symm) from he]
  exact IsRoot.relabelled (root_sound [233] [2334] [10946] [10] [47] [1] t ht (by decide)) perm17.symm

theorem edge78_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 78) 3) := by
  have he := mutation_equal (pnode 78) (preverse (prelabel (fork [5] [4] [233] [19] [1118] [10]) perm18.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 3 (node_safe t 78)
  rw [show mutate (node t 78) 3=(reverse (relabel (matrix (fork [5] [4] [233] [19] [1118] [10]) t) perm18.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [5] [4] [233] [19] [1118] [10] t ht (by decide)) perm18.symm)

theorem edge79_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 79) 0) := by
  have he := mutation_equal (pnode 79) (prelabel (pnode 70) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 79) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 70) perm0.symm

theorem edge79_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 79) 1) := by
  have he := mutation_equal (pnode 79) (preverse (prelabel (root [23] [185] [89] [8] [4] [1]) perm10.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 79) 1
  rw [show mutate (node t 79) 1=(reverse (relabel (matrix (root [23] [185] [89] [8] [4] [1]) t) perm10.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [23] [185] [89] [8] [4] [1] t ht (by decide)) perm10.symm)

theorem edge79_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 79) 2) := by
  have he := mutation_equal (pnode 79) (prelabel (pnode 74) perm20.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 79) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 74) perm20.symm

theorem edge79_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 79) 3) := by
  have he := mutation_equal (pnode 79) (prelabel (pnode 80) perm21.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 79) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 80) perm21.symm

theorem edge80_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 80) 0) := by
  have he := mutation_equal (pnode 80) (prelabel (pnode 79) perm21.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 80) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 79) perm21.symm

theorem edge80_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 80) 1) := by
  have he := mutation_equal (pnode 80) (preverse (prelabel (root [65] [522] [1492] [8] [23] [1]) perm9.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 80) 1
  rw [show mutate (node t 80) 1=(reverse (relabel (matrix (root [65] [522] [1492] [8] [23] [1]) t) perm9.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [65] [522] [1492] [8] [23] [1] t ht (by decide)) perm9.symm)

theorem edge80_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 80) 2) := by
  have he := mutation_equal (pnode 80) (prelabel (fork [3] [2] [65] [5] [172] [8]) perm13.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 2 (node_safe t 80)
  rw [show mutate (node t 80) 2=(relabel (matrix (fork [3] [2] [65] [5] [172] [8]) t) perm13.symm) from he]
  exact IsFork.relabelled (fork_sound [3] [2] [65] [5] [172] [8] t ht (by decide)) perm13.symm

theorem edge80_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 80) 3) := by
  have he := mutation_equal (pnode 80) (preverse (prelabel (generic param8_0 param8_1 param8_2 param8_3 2) perm19.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 80) t) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (region8_safe t ht 2) perm19.symm)

theorem edge81_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 81) 0) := by
  have he := mutation_equal (pnode 81) (preverse (prelabel (generic param9_0 param9_1 param9_2 param9_3 2) perm1.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 81) t) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (region9_safe t ht 2) perm1.symm)

theorem edge81_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 81) 1) := by
  have he := mutation_equal (pnode 81) (prelabel (pnode 71) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 81) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 71) perm0.symm

theorem edge81_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 81) 2) := by
  have he := mutation_equal (pnode 81) (preverse (prelabel (root [162] [814] [5341] [5] [33] [1]) perm16.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 81) 2
  rw [show mutate (node t 81) 2=(reverse (relabel (matrix (root [162] [814] [5341] [5] [33] [1]) t) perm16.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [162] [814] [5341] [5] [33] [1] t ht (by decide)) perm16.symm)

theorem edge81_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 81) 3) := by
  have he := mutation_equal (pnode 81) (prelabel (fork [5] [4] [162] [19] [777] [5]) perm20.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 3 (node_safe t 81)
  rw [show mutate (node t 81) 3=(relabel (matrix (fork [5] [4] [162] [19] [777] [5]) t) perm20.symm) from he]
  exact IsFork.relabelled (fork_sound [5] [4] [162] [19] [777] [5] t ht (by decide)) perm20.symm

theorem edge82_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 82) 0) := by
  have he := mutation_equal (pnode 82) (preverse (prelabel (generic param10_0 param10_1 param10_2 param10_3 2) perm0.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 82) t) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (region10_safe t ht 2) perm0.symm)

theorem edge82_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 82) 1) := by
  have he := mutation_equal (pnode 82) (prelabel (pnode 77) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 82) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 77) perm0.symm

theorem edge82_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 82) 2) := by
  have he := mutation_equal (pnode 82) (prelabel (fork [13] [12] [117458] [155] [1517914] [691]) perm14.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 2 (node_safe t 82)
  rw [show mutate (node t 82) 2=(relabel (matrix (fork [13] [12] [117458] [155] [1517914] [691]) t) perm14.symm) from he]
  exact IsFork.relabelled (fork_sound [13] [12] [117458] [155] [1517914] [691] t ht (by decide)) perm14.symm

theorem edge82_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 82) 3) := by
  have he := mutation_equal (pnode 82) (preverse (prelabel (root [117458] [81163490] [1061820307] [691] [9040] [1]) perm22.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 82) 3
  rw [show mutate (node t 82) 3=(reverse (relabel (matrix (root [117458] [81163490] [1061820307] [691] [9040] [1]) t) perm22.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [117458] [81163490] [1061820307] [691] [9040] [1] t ht (by decide)) perm22.symm)

theorem all_cyclic (t : Int) (ht : 0≤t) (i : Fin 83) : ¬ Acyclic (node t i) := by
  rcases finCore i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact cyclic0 t ht
  · exact cyclic1 t ht
  · exact cyclic2 t ht
  · exact cyclic3 t ht
  · exact cyclic4 t ht
  · exact cyclic5 t ht
  · exact cyclic6 t ht
  · exact cyclic7 t ht
  · exact cyclic8 t ht
  · exact cyclic9 t ht
  · exact cyclic10 t ht
  · exact cyclic11 t ht
  · exact cyclic12 t ht
  · exact cyclic13 t ht
  · exact cyclic14 t ht
  · exact cyclic15 t ht
  · exact cyclic16 t ht
  · exact cyclic17 t ht
  · exact cyclic18 t ht
  · exact cyclic19 t ht
  · exact cyclic20 t ht
  · exact cyclic21 t ht
  · exact cyclic22 t ht
  · exact cyclic23 t ht
  · exact cyclic24 t ht
  · exact cyclic25 t ht
  · exact cyclic26 t ht
  · exact cyclic27 t ht
  · exact cyclic28 t ht
  · exact cyclic29 t ht
  · exact cyclic30 t ht
  · exact cyclic31 t ht
  · exact cyclic32 t ht
  · exact cyclic33 t ht
  · exact cyclic34 t ht
  · exact cyclic35 t ht
  · exact cyclic36 t ht
  · exact cyclic37 t ht
  · exact cyclic38 t ht
  · exact cyclic39 t ht
  · exact cyclic40 t ht
  · exact cyclic41 t ht
  · exact cyclic42 t ht
  · exact cyclic43 t ht
  · exact cyclic44 t ht
  · exact cyclic45 t ht
  · exact cyclic46 t ht
  · exact cyclic47 t ht
  · exact cyclic48 t ht
  · exact cyclic49 t ht
  · exact cyclic50 t ht
  · exact cyclic51 t ht
  · exact cyclic52 t ht
  · exact cyclic53 t ht
  · exact cyclic54 t ht
  · exact cyclic55 t ht
  · exact cyclic56 t ht
  · exact cyclic57 t ht
  · exact cyclic58 t ht
  · exact cyclic59 t ht
  · exact cyclic60 t ht
  · exact cyclic61 t ht
  · exact cyclic62 t ht
  · exact cyclic63 t ht
  · exact cyclic64 t ht
  · exact cyclic65 t ht
  · exact cyclic66 t ht
  · exact cyclic67 t ht
  · exact cyclic68 t ht
  · exact cyclic69 t ht
  · exact cyclic70 t ht
  · exact cyclic71 t ht
  · exact cyclic72 t ht
  · exact cyclic73 t ht
  · exact cyclic74 t ht
  · exact cyclic75 t ht
  · exact cyclic76 t ht
  · exact cyclic77 t ht
  · exact cyclic78 t ht
  · exact cyclic79 t ht
  · exact cyclic80 t ht
  · exact cyclic81 t ht
  · exact cyclic82 t ht

theorem all_edges (t : Int) (ht : 0≤t) (i : Fin 83) (k : Fin 4) : SafeCore t (mutate (node t i) k) := by
  have hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
  rcases finCore i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rcases hk with rfl|rfl|rfl|rfl
  · exact edge0_0 t ht
  · exact edge0_1 t ht
  · exact edge0_2 t ht
  · exact edge0_3 t ht
  · exact edge1_0 t ht
  · exact edge1_1 t ht
  · exact edge1_2 t ht
  · exact edge1_3 t ht
  · exact edge2_0 t ht
  · exact edge2_1 t ht
  · exact edge2_2 t ht
  · exact edge2_3 t ht
  · exact edge3_0 t ht
  · exact edge3_1 t ht
  · exact edge3_2 t ht
  · exact edge3_3 t ht
  · exact edge4_0 t ht
  · exact edge4_1 t ht
  · exact edge4_2 t ht
  · exact edge4_3 t ht
  · exact edge5_0 t ht
  · exact edge5_1 t ht
  · exact edge5_2 t ht
  · exact edge5_3 t ht
  · exact edge6_0 t ht
  · exact edge6_1 t ht
  · exact edge6_2 t ht
  · exact edge6_3 t ht
  · exact edge7_0 t ht
  · exact edge7_1 t ht
  · exact edge7_2 t ht
  · exact edge7_3 t ht
  · exact edge8_0 t ht
  · exact edge8_1 t ht
  · exact edge8_2 t ht
  · exact edge8_3 t ht
  · exact edge9_0 t ht
  · exact edge9_1 t ht
  · exact edge9_2 t ht
  · exact edge9_3 t ht
  · exact edge10_0 t ht
  · exact edge10_1 t ht
  · exact edge10_2 t ht
  · exact edge10_3 t ht
  · exact edge11_0 t ht
  · exact edge11_1 t ht
  · exact edge11_2 t ht
  · exact edge11_3 t ht
  · exact edge12_0 t ht
  · exact edge12_1 t ht
  · exact edge12_2 t ht
  · exact edge12_3 t ht
  · exact edge13_0 t ht
  · exact edge13_1 t ht
  · exact edge13_2 t ht
  · exact edge13_3 t ht
  · exact edge14_0 t ht
  · exact edge14_1 t ht
  · exact edge14_2 t ht
  · exact edge14_3 t ht
  · exact edge15_0 t ht
  · exact edge15_1 t ht
  · exact edge15_2 t ht
  · exact edge15_3 t ht
  · exact edge16_0 t ht
  · exact edge16_1 t ht
  · exact edge16_2 t ht
  · exact edge16_3 t ht
  · exact edge17_0 t ht
  · exact edge17_1 t ht
  · exact edge17_2 t ht
  · exact edge17_3 t ht
  · exact edge18_0 t ht
  · exact edge18_1 t ht
  · exact edge18_2 t ht
  · exact edge18_3 t ht
  · exact edge19_0 t ht
  · exact edge19_1 t ht
  · exact edge19_2 t ht
  · exact edge19_3 t ht
  · exact edge20_0 t ht
  · exact edge20_1 t ht
  · exact edge20_2 t ht
  · exact edge20_3 t ht
  · exact edge21_0 t ht
  · exact edge21_1 t ht
  · exact edge21_2 t ht
  · exact edge21_3 t ht
  · exact edge22_0 t ht
  · exact edge22_1 t ht
  · exact edge22_2 t ht
  · exact edge22_3 t ht
  · exact edge23_0 t ht
  · exact edge23_1 t ht
  · exact edge23_2 t ht
  · exact edge23_3 t ht
  · exact edge24_0 t ht
  · exact edge24_1 t ht
  · exact edge24_2 t ht
  · exact edge24_3 t ht
  · exact edge25_0 t ht
  · exact edge25_1 t ht
  · exact edge25_2 t ht
  · exact edge25_3 t ht
  · exact edge26_0 t ht
  · exact edge26_1 t ht
  · exact edge26_2 t ht
  · exact edge26_3 t ht
  · exact edge27_0 t ht
  · exact edge27_1 t ht
  · exact edge27_2 t ht
  · exact edge27_3 t ht
  · exact edge28_0 t ht
  · exact edge28_1 t ht
  · exact edge28_2 t ht
  · exact edge28_3 t ht
  · exact edge29_0 t ht
  · exact edge29_1 t ht
  · exact edge29_2 t ht
  · exact edge29_3 t ht
  · exact edge30_0 t ht
  · exact edge30_1 t ht
  · exact edge30_2 t ht
  · exact edge30_3 t ht
  · exact edge31_0 t ht
  · exact edge31_1 t ht
  · exact edge31_2 t ht
  · exact edge31_3 t ht
  · exact edge32_0 t ht
  · exact edge32_1 t ht
  · exact edge32_2 t ht
  · exact edge32_3 t ht
  · exact edge33_0 t ht
  · exact edge33_1 t ht
  · exact edge33_2 t ht
  · exact edge33_3 t ht
  · exact edge34_0 t ht
  · exact edge34_1 t ht
  · exact edge34_2 t ht
  · exact edge34_3 t ht
  · exact edge35_0 t ht
  · exact edge35_1 t ht
  · exact edge35_2 t ht
  · exact edge35_3 t ht
  · exact edge36_0 t ht
  · exact edge36_1 t ht
  · exact edge36_2 t ht
  · exact edge36_3 t ht
  · exact edge37_0 t ht
  · exact edge37_1 t ht
  · exact edge37_2 t ht
  · exact edge37_3 t ht
  · exact edge38_0 t ht
  · exact edge38_1 t ht
  · exact edge38_2 t ht
  · exact edge38_3 t ht
  · exact edge39_0 t ht
  · exact edge39_1 t ht
  · exact edge39_2 t ht
  · exact edge39_3 t ht
  · exact edge40_0 t ht
  · exact edge40_1 t ht
  · exact edge40_2 t ht
  · exact edge40_3 t ht
  · exact edge41_0 t ht
  · exact edge41_1 t ht
  · exact edge41_2 t ht
  · exact edge41_3 t ht
  · exact edge42_0 t ht
  · exact edge42_1 t ht
  · exact edge42_2 t ht
  · exact edge42_3 t ht
  · exact edge43_0 t ht
  · exact edge43_1 t ht
  · exact edge43_2 t ht
  · exact edge43_3 t ht
  · exact edge44_0 t ht
  · exact edge44_1 t ht
  · exact edge44_2 t ht
  · exact edge44_3 t ht
  · exact edge45_0 t ht
  · exact edge45_1 t ht
  · exact edge45_2 t ht
  · exact edge45_3 t ht
  · exact edge46_0 t ht
  · exact edge46_1 t ht
  · exact edge46_2 t ht
  · exact edge46_3 t ht
  · exact edge47_0 t ht
  · exact edge47_1 t ht
  · exact edge47_2 t ht
  · exact edge47_3 t ht
  · exact edge48_0 t ht
  · exact edge48_1 t ht
  · exact edge48_2 t ht
  · exact edge48_3 t ht
  · exact edge49_0 t ht
  · exact edge49_1 t ht
  · exact edge49_2 t ht
  · exact edge49_3 t ht
  · exact edge50_0 t ht
  · exact edge50_1 t ht
  · exact edge50_2 t ht
  · exact edge50_3 t ht
  · exact edge51_0 t ht
  · exact edge51_1 t ht
  · exact edge51_2 t ht
  · exact edge51_3 t ht
  · exact edge52_0 t ht
  · exact edge52_1 t ht
  · exact edge52_2 t ht
  · exact edge52_3 t ht
  · exact edge53_0 t ht
  · exact edge53_1 t ht
  · exact edge53_2 t ht
  · exact edge53_3 t ht
  · exact edge54_0 t ht
  · exact edge54_1 t ht
  · exact edge54_2 t ht
  · exact edge54_3 t ht
  · exact edge55_0 t ht
  · exact edge55_1 t ht
  · exact edge55_2 t ht
  · exact edge55_3 t ht
  · exact edge56_0 t ht
  · exact edge56_1 t ht
  · exact edge56_2 t ht
  · exact edge56_3 t ht
  · exact edge57_0 t ht
  · exact edge57_1 t ht
  · exact edge57_2 t ht
  · exact edge57_3 t ht
  · exact edge58_0 t ht
  · exact edge58_1 t ht
  · exact edge58_2 t ht
  · exact edge58_3 t ht
  · exact edge59_0 t ht
  · exact edge59_1 t ht
  · exact edge59_2 t ht
  · exact edge59_3 t ht
  · exact edge60_0 t ht
  · exact edge60_1 t ht
  · exact edge60_2 t ht
  · exact edge60_3 t ht
  · exact edge61_0 t ht
  · exact edge61_1 t ht
  · exact edge61_2 t ht
  · exact edge61_3 t ht
  · exact edge62_0 t ht
  · exact edge62_1 t ht
  · exact edge62_2 t ht
  · exact edge62_3 t ht
  · exact edge63_0 t ht
  · exact edge63_1 t ht
  · exact edge63_2 t ht
  · exact edge63_3 t ht
  · exact edge64_0 t ht
  · exact edge64_1 t ht
  · exact edge64_2 t ht
  · exact edge64_3 t ht
  · exact edge65_0 t ht
  · exact edge65_1 t ht
  · exact edge65_2 t ht
  · exact edge65_3 t ht
  · exact edge66_0 t ht
  · exact edge66_1 t ht
  · exact edge66_2 t ht
  · exact edge66_3 t ht
  · exact edge67_0 t ht
  · exact edge67_1 t ht
  · exact edge67_2 t ht
  · exact edge67_3 t ht
  · exact edge68_0 t ht
  · exact edge68_1 t ht
  · exact edge68_2 t ht
  · exact edge68_3 t ht
  · exact edge69_0 t ht
  · exact edge69_1 t ht
  · exact edge69_2 t ht
  · exact edge69_3 t ht
  · exact edge70_0 t ht
  · exact edge70_1 t ht
  · exact edge70_2 t ht
  · exact edge70_3 t ht
  · exact edge71_0 t ht
  · exact edge71_1 t ht
  · exact edge71_2 t ht
  · exact edge71_3 t ht
  · exact edge72_0 t ht
  · exact edge72_1 t ht
  · exact edge72_2 t ht
  · exact edge72_3 t ht
  · exact edge73_0 t ht
  · exact edge73_1 t ht
  · exact edge73_2 t ht
  · exact edge73_3 t ht
  · exact edge74_0 t ht
  · exact edge74_1 t ht
  · exact edge74_2 t ht
  · exact edge74_3 t ht
  · exact edge75_0 t ht
  · exact edge75_1 t ht
  · exact edge75_2 t ht
  · exact edge75_3 t ht
  · exact edge76_0 t ht
  · exact edge76_1 t ht
  · exact edge76_2 t ht
  · exact edge76_3 t ht
  · exact edge77_0 t ht
  · exact edge77_1 t ht
  · exact edge77_2 t ht
  · exact edge77_3 t ht
  · exact edge78_0 t ht
  · exact edge78_1 t ht
  · exact edge78_2 t ht
  · exact edge78_3 t ht
  · exact edge79_0 t ht
  · exact edge79_1 t ht
  · exact edge79_2 t ht
  · exact edge79_3 t ht
  · exact edge80_0 t ht
  · exact edge80_1 t ht
  · exact edge80_2 t ht
  · exact edge80_3 t ht
  · exact edge81_0 t ht
  · exact edge81_1 t ht
  · exact edge81_2 t ht
  · exact edge81_3 t ht
  · exact edge82_0 t ht
  · exact edge82_1 t ht
  · exact edge82_2 t ht
  · exact edge82_3 t ht

theorem NMA (t : Int) (ht : 0≤t) : ¬ MutationAcyclic (node t 0) := by
  apply safe_NMA data rules (Core t)
  · rintro B ⟨i,rfl⟩; exact node_skew t i
  · rintro B ⟨i,rfl⟩; exact all_cyclic t ht i
  · rintro B ⟨i,rfl⟩ k; exact all_edges t ht i k
  · exact node_safe t 0
end Boundary3
namespace HalfLine
private theorem finCore (i : Fin 49) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 ∨ i=15 ∨ i=16 ∨ i=17 ∨ i=18 ∨ i=19 ∨ i=20 ∨ i=21 ∨ i=22 ∨ i=23 ∨ i=24 ∨ i=25 ∨ i=26 ∨ i=27 ∨ i=28 ∨ i=29 ∨ i=30 ∨ i=31 ∨ i=32 ∨ i=33 ∨ i=34 ∨ i=35 ∨ i=36 ∨ i=37 ∨ i=38 ∨ i=39 ∨ i=40 ∨ i=41 ∨ i=42 ∨ i=43 ∨ i=44 ∨ i=45 ∨ i=46 ∨ i=47 ∨ i=48 := by omega

def pnode (i : Fin 49) : PMatrix := match i.val with
  | 0 => six [] [1] [-6,-2] [2] [-4,-1] [7,2]
  | 1 => six [] [-1] [6,2] [2] [-4,-1] [1]
  | 2 => six [] [-1] [1] [-2] [10,3] [-7,-2]
  | 3 => six [-2] [1] [6,2] [-2] [-2,-1] [-1]
  | 4 => six [24,14,2] [-1] [-6,-2] [-2,-1] [4,1] [-1]
  | 5 => six [] [1] [-1] [-2] [10,3] [-6,-2]
  | 6 => six [] [-1] [1] [2] [-10,-3] [13,4]
  | 7 => six [] [6,2] [-1] [68,41,6] [-10,-3] [7,2]
  | 8 => six [2] [-3] [2] [2] [2,1] [-1]
  | 9 => six [10,10,2] [7,2] [-6,-2] [-2] [2,1] [1]
  | 10 => six [-24,-14,-2] [1] [6,2] [-26,-15,-2] [-140,-131,-40,-4] [-1]
  | 11 => six [24,14,2] [1] [-7,-2] [2,1] [2] [1]
  | 12 => six [] [1] [-1] [2] [-10,-3] [14,4]
  | 13 => six [-10,-3] [1] [1] [58,38,6] [-10,-3] [6,2]
  | 14 => six [-2] [1] [1] [-2] [16,5] [-13,-4]
  | 15 => six [10,3] [-1] [-1] [-128,-79,-12] [10,3] [-13,-4]
  | 16 => six [] [-6,-2] [1] [68,41,6] [-10,-3] [1]
  | 17 => six [-4] [3] [-1] [-2] [2,1] [1]
  | 18 => six [2] [-1] [-2] [4,1] [-2,-1] [1]
  | 19 => six [2,1] [-1] [6,2] [26,15,2] [-166,-146,-42,-4] [1]
  | 20 => six [816,1052,500,104,8] [7,2] [-6,-2] [-26,-15,-2] [140,131,40,4] [1]
  | 21 => six [-24,-14,-2] [-1] [7,2] [2,1] [-166,-146,-42,-4] [-6,-2]
  | 22 => six [] [-1] [13,4] [-2] [18,5] [-14,-4]
  | 23 => six [] [-13,-4] [1] [-138,-82,-12] [10,3] [-14,-4]
  | 24 => six [-10,-3] [-1] [7,2] [-58,-38,-6] [338,341,112,12] [-6,-2]
  | 25 => six [2] [-1] [-1] [] [18,5] [-13,-4]
  | 26 => six [-2] [14,4] [-1] [206,129,20] [-16,-5] [13,4]
  | 27 => six [-10,-3] [1] [1] [-138,-82,-12] [] [-13,-4]
  | 28 => six [10,3] [1] [-14,-4] [128,79,12] [-1654,-1536,-472,-48] [13,4]
  | 29 => six [-408,-382,-118,-12] [6,2] [1] [-68,-41,-6] [58,38,6] [-1]
  | 30 => six [4] [-3] [1] [10] [2,1] [-2]
  | 31 => six [-6,-1] [2] [1] [-2] [-2,-1] [-1]
  | 32 => six [998,1209,544,108,8] [-1] [-6,-2] [-140,-131,-40,-4] [166,146,42,4] [-1]
  | 33 => six [998,1209,544,108,8] [-7,-2] [1] [26,15,2] [140,131,40,4] [-1]
  | 34 => six [10,3] [1] [-7,-2] [-58,-38,-6] [408,382,118,12] [1]
  | 35 => six [-16,-5] [-1] [1] [234,137,20] [-18,-5] [13,4]
  | 36 => six [2] [-14,-4] [1] [234,137,20] [-16,-5] [-1]
  | 37 => six [128,79,12] [-1] [1] [138,82,12] [-1794,-1618,-484,-48] [13,4]
  | 38 => six [-10,-3] [-1] [14,4] [128,79,12] [-1794,-1618,-484,-48] [-1]
  | 39 => six [58,38,6] [6,2] [-1] [2846,3487,1590,320,24] [-408,-382,-118,-12] [7,2]
  | 40 => six [4] [-1] [-1] [14,2] [-2,-1] [2]
  | 41 => six [6,1] [-2] [-1] [10,2] [4] [-1]
  | 42 => six [-140,-131,-40,-4] [1] [-6,-2] [998,1209,544,108,8] [-6960,-10444,-6224,-1844,-272,-16] [7,2]
  | 43 => six [234,137,20] [1] [-14,-4] [-16,-5] [3274,2854,828,80] [13,4]
  | 44 => six [-1794,-1618,-484,-48] [14,4] [-1] [-25106,-29825,-13248,-2608,-192] [128,79,12] [13,4]
  | 45 => six [-10,-2] [1] [-1] [-14,-2] [26,3] [-2]
  | 46 => six [-14,-3] [2] [-3] [-10,-2] [4] [1]
  | 47 => six [10,2] [-1] [1] [-4] [26,3] [-3]
  | _ => six [26,3] [-3] [1] [74,9] [-10,-2] [-2]

def node (t : Int) (i : Fin 49) : Matrix 4 := matrix (pnode i) t
def Core (t : Int) (B : Matrix 4) : Prop := ∃ i, B=node t i
abbrev SafeCore (t : Int) := Safe data (Core t)
theorem node_safe (t : Int) (i : Fin 49) : SafeCore t (node t i) := Safe.central ⟨i,rfl⟩

def param0_0 : P := [6,2]
def param0_1 : P := [408,382,118,12]
def param0_2 : P := [58,38,6]
def param0_3 : P := [68,41,6]
theorem domain0 (t : Int) (ht : 0≤t) : GenericStrip.Domain (eval param0_0 t) (eval param0_1 t) (eval param0_2 t) (eval param0_3 t) :=
  generic_domain param0_0 param0_1 param0_2 param0_3 t ht (by decide)

def region0 (t : Int) (ht : 0≤t) : Region := .inl (.inl ⟨eval param0_0 t,⟨eval param0_1 t,eval param0_2 t,eval param0_3 t⟩,domain0 t ht⟩)

theorem parent0_0 (t : Int) (ht : 0≤t) :
    data.parent (region0 t ht) (0 : Fin 3)=(reverse (relabel (node t 34) perm17.symm)) := by
  have he := mutation_equal (generic param0_0 param0_1 param0_2 param0_3 0) (preverse (prelabel (pnode 34) perm17.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent0_1 (t : Int) (ht : 0≤t) :
    data.parent (region0 t ht) (1 : Fin 3)=(reverse (relabel (node t 16) perm5.symm)) := by
  have he := mutation_equal (generic param0_0 param0_1 param0_2 param0_3 0) (preverse (prelabel (pnode 16) perm5.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent0_2 (t : Int) (ht : 0≤t) :
    data.parent (region0 t ht) (2 : Fin 3)=(reverse (relabel (node t 39) perm5.symm)) := by
  have he := mutation_equal (generic param0_0 param0_1 param0_2 param0_3 2) (preverse (prelabel (pnode 39) perm5.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parents0_safe (t : Int) (ht : 0≤t) (p : Fin 3) :
    SafeCore t (data.parent (region0 t ht) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hp with rfl|rfl|rfl
  · rw [parent0_0 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 34) perm17.symm)
  · rw [parent0_1 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 16) perm5.symm)
  · rw [parent0_2 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 39) perm5.symm)

theorem region0_safe (t : Int) (ht : 0≤t) (i : Fin 3) :
    SafeCore t (matrix (generic param0_0 param0_1 param0_2 param0_3 i) t) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core t) (region0 t ht) (parents0_safe t ht) (0,Fin.castLE (by decide) i)

def param1_0 : P := [6,2]
def param1_1 : P := [998,1209,544,108,8]
def param1_2 : P := [140,131,40,4]
def param1_3 : P := [166,146,42,4]
theorem domain1 (t : Int) (ht : 0≤t) : GenericStrip.Domain (eval param1_0 t) (eval param1_1 t) (eval param1_2 t) (eval param1_3 t) :=
  generic_domain param1_0 param1_1 param1_2 param1_3 t ht (by decide)

def region1 (t : Int) (ht : 0≤t) : Region := .inl (.inl ⟨eval param1_0 t,⟨eval param1_1 t,eval param1_2 t,eval param1_3 t⟩,domain1 t ht⟩)

theorem parent1_0 (t : Int) (ht : 0≤t) :
    data.parent (region1 t ht) (0 : Fin 3)=(relabel (node t 33) perm5.symm) := by
  have he := mutation_equal (generic param1_0 param1_1 param1_2 param1_3 0) (prelabel (pnode 33) perm5.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent1_1 (t : Int) (ht : 0≤t) :
    data.parent (region1 t ht) (1 : Fin 3)=(relabel (node t 19) perm4.symm) := by
  have he := mutation_equal (generic param1_0 param1_1 param1_2 param1_3 0) (prelabel (pnode 19) perm4.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent1_2 (t : Int) (ht : 0≤t) :
    data.parent (region1 t ht) (2 : Fin 3)=(relabel (node t 42) perm4.symm) := by
  have he := mutation_equal (generic param1_0 param1_1 param1_2 param1_3 2) (prelabel (pnode 42) perm4.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parents1_safe (t : Int) (ht : 0≤t) (p : Fin 3) :
    SafeCore t (data.parent (region1 t ht) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hp with rfl|rfl|rfl
  · rw [parent1_0 t ht]
    exact Safe.framed (node_safe t 33) perm5.symm
  · rw [parent1_1 t ht]
    exact Safe.framed (node_safe t 19) perm4.symm
  · rw [parent1_2 t ht]
    exact Safe.framed (node_safe t 42) perm4.symm

theorem region1_safe (t : Int) (ht : 0≤t) (i : Fin 3) :
    SafeCore t (matrix (generic param1_0 param1_1 param1_2 param1_3 i) t) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core t) (region1 t ht) (parents1_safe t ht) (0,Fin.castLE (by decide) i)

def param2_0 : P := [13,4]
def param2_1 : P := [234,137,20]
def param2_2 : P := [16,5]
def param2_3 : P := [18,5]
theorem domain2 (t : Int) (ht : 0≤t) : GenericStrip.Domain (eval param2_0 t) (eval param2_1 t) (eval param2_2 t) (eval param2_3 t) :=
  generic_domain param2_0 param2_1 param2_2 param2_3 t ht (by decide)

def region2 (t : Int) (ht : 0≤t) : Region := .inl (.inl ⟨eval param2_0 t,⟨eval param2_1 t,eval param2_2 t,eval param2_3 t⟩,domain2 t ht⟩)

theorem parent2_0 (t : Int) (ht : 0≤t) :
    data.parent (region2 t ht) (0 : Fin 3)=(reverse (relabel (node t 36) perm16.symm)) := by
  have he := mutation_equal (generic param2_0 param2_1 param2_2 param2_3 0) (preverse (prelabel (pnode 36) perm16.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent2_1 (t : Int) (ht : 0≤t) :
    data.parent (region2 t ht) (1 : Fin 3)=(reverse (relabel (node t 25) perm10.symm)) := by
  have he := mutation_equal (generic param2_0 param2_1 param2_2 param2_3 0) (preverse (prelabel (pnode 25) perm10.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent2_2 (t : Int) (ht : 0≤t) :
    data.parent (region2 t ht) (2 : Fin 3)=(reverse (relabel (node t 43) perm10.symm)) := by
  have he := mutation_equal (generic param2_0 param2_1 param2_2 param2_3 2) (preverse (prelabel (pnode 43) perm10.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parents2_safe (t : Int) (ht : 0≤t) (p : Fin 3) :
    SafeCore t (data.parent (region2 t ht) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hp with rfl|rfl|rfl
  · rw [parent2_0 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 36) perm16.symm)
  · rw [parent2_1 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 25) perm10.symm)
  · rw [parent2_2 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 43) perm10.symm)

theorem region2_safe (t : Int) (ht : 0≤t) (i : Fin 3) :
    SafeCore t (matrix (generic param2_0 param2_1 param2_2 param2_3 i) t) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core t) (region2 t ht) (parents2_safe t ht) (0,Fin.castLE (by decide) i)

def param3_0 : P := [13,4]
def param3_1 : P := [1794,1618,484,48]
def param3_2 : P := [128,79,12]
def param3_3 : P := [138,82,12]
theorem domain3 (t : Int) (ht : 0≤t) : GenericStrip.Domain (eval param3_0 t) (eval param3_1 t) (eval param3_2 t) (eval param3_3 t) :=
  generic_domain param3_0 param3_1 param3_2 param3_3 t ht (by decide)

def region3 (t : Int) (ht : 0≤t) : Region := .inl (.inl ⟨eval param3_0 t,⟨eval param3_1 t,eval param3_2 t,eval param3_3 t⟩,domain3 t ht⟩)

theorem parent3_0 (t : Int) (ht : 0≤t) :
    data.parent (region3 t ht) (0 : Fin 3)=(relabel (node t 38) perm17.symm) := by
  have he := mutation_equal (generic param3_0 param3_1 param3_2 param3_3 0) (prelabel (pnode 38) perm17.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent3_1 (t : Int) (ht : 0≤t) :
    data.parent (region3 t ht) (1 : Fin 3)=(relabel (node t 27) perm11.symm) := by
  have he := mutation_equal (generic param3_0 param3_1 param3_2 param3_3 0) (prelabel (pnode 27) perm11.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent3_2 (t : Int) (ht : 0≤t) :
    data.parent (region3 t ht) (2 : Fin 3)=(relabel (node t 44) perm11.symm) := by
  have he := mutation_equal (generic param3_0 param3_1 param3_2 param3_3 2) (prelabel (pnode 44) perm11.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parents3_safe (t : Int) (ht : 0≤t) (p : Fin 3) :
    SafeCore t (data.parent (region3 t ht) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hp with rfl|rfl|rfl
  · rw [parent3_0 t ht]
    exact Safe.framed (node_safe t 38) perm17.symm
  · rw [parent3_1 t ht]
    exact Safe.framed (node_safe t 27) perm11.symm
  · rw [parent3_2 t ht]
    exact Safe.framed (node_safe t 44) perm11.symm

theorem region3_safe (t : Int) (ht : 0≤t) (i : Fin 3) :
    SafeCore t (matrix (generic param3_0 param3_1 param3_2 param3_3 i) t) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core t) (region3 t ht) (parents3_safe t ht) (0,Fin.castLE (by decide) i)

def param4_0 : P := [2]
def param4_1 : P := [26,3]
def param4_2 : P := [10,2]
def param4_3 : P := [14,2]
theorem domain4 (t : Int) (ht : 0≤t) : GenericStrip.Domain (eval param4_0 t) (eval param4_1 t) (eval param4_2 t) (eval param4_3 t) :=
  generic_domain param4_0 param4_1 param4_2 param4_3 t ht (by decide)

def region4 (t : Int) (ht : 0≤t) : Region := .inl (.inl ⟨eval param4_0 t,⟨eval param4_1 t,eval param4_2 t,eval param4_3 t⟩,domain4 t ht⟩)

theorem parent4_0 (t : Int) (ht : 0≤t) :
    data.parent (region4 t ht) (0 : Fin 3)=(reverse (relabel (node t 47) perm11.symm)) := by
  have he := mutation_equal (generic param4_0 param4_1 param4_2 param4_3 0) (preverse (prelabel (pnode 47) perm11.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent4_1 (t : Int) (ht : 0≤t) :
    data.parent (region4 t ht) (1 : Fin 3)=(reverse (relabel (node t 40) perm11.symm)) := by
  have he := mutation_equal (generic param4_0 param4_1 param4_2 param4_3 0) (preverse (prelabel (pnode 40) perm11.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent4_2 (t : Int) (ht : 0≤t) :
    data.parent (region4 t ht) (2 : Fin 3)=(reverse (relabel (node t 48) perm11.symm)) := by
  have he := mutation_equal (generic param4_0 param4_1 param4_2 param4_3 2) (preverse (prelabel (pnode 48) perm11.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parents4_safe (t : Int) (ht : 0≤t) (p : Fin 3) :
    SafeCore t (data.parent (region4 t ht) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hp with rfl|rfl|rfl
  · rw [parent4_0 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 47) perm11.symm)
  · rw [parent4_1 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 40) perm11.symm)
  · rw [parent4_2 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 48) perm11.symm)

theorem region4_safe (t : Int) (ht : 0≤t) (i : Fin 3) :
    SafeCore t (matrix (generic param4_0 param4_1 param4_2 param4_3 i) t) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core t) (region4 t ht) (parents4_safe t ht) (0,Fin.castLE (by decide) i)

def param5_0 : P := [10,3]
def param5_1 : P := [6,2]
def param5_2 : P := [68,41,6]
def param5_3 : P := [673,612,183,18]
theorem domain5 (t : Int) (ht : 0≤t) : UnitZeroStrip.Domain (eval param5_0 t) (eval param5_1 t) (eval param5_2 t) (eval param5_3 t) :=
  zero_domain param5_0 param5_1 param5_2 param5_3 t ht (by decide)

def region5 (t : Int) (ht : 0≤t) : Region := .inl (.inr (.n (eval param5_0 t) ⟨eval param5_1 t,eval param5_2 t,eval param5_3 t⟩ (domain5 t ht)))

theorem parent5_0 (t : Int) (ht : 0≤t) :
    data.parent (region5 t ht) (0 : Fin 2)=(reverse (relabel (node t 7) perm0.symm)) := by
  have he := mutation_equal (zero param5_0 param5_1 param5_2 param5_3 0) (preverse (prelabel (pnode 7) perm0.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,zero_eval] at he
  exact he

theorem parent5_1 (t : Int) (ht : 0≤t) :
    data.parent (region5 t ht) (1 : Fin 2)=(reverse (relabel (node t 16) perm0.symm)) := by
  have he := mutation_equal (zero param5_0 param5_1 param5_2 param5_3 1) (preverse (prelabel (pnode 16) perm0.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,zero_eval] at he
  exact he

theorem parents5_safe (t : Int) (ht : 0≤t) (p : Fin 2) :
    SafeCore t (data.parent (region5 t ht) p) := by
  have hp : p=0 ∨ p=1 := by change p=(0 : Fin 2) ∨ p=(1 : Fin 2); omega
  rcases hp with rfl|rfl
  · rw [parent5_0 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 7) perm0.symm)
  · rw [parent5_1 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 16) perm0.symm)

theorem region5_safe (t : Int) (ht : 0≤t) (i : Fin 2) :
    SafeCore t (matrix (zero param5_0 param5_1 param5_2 param5_3 i) t) := by
  rw [zero_eval]
  exact Safe.region (D:=data) (core:=Core t) (region5 t ht) (parents5_safe t ht) (0,Fin.castLE (by decide) i)

def param6_0 : P := [2]
def param6_1 : P := [13,4]
def param6_2 : P := [18,5]
def param6_3 : P := [22,6]
theorem domain6 (t : Int) (ht : 0≤t) : UnitZeroStrip.Domain (eval param6_0 t) (eval param6_1 t) (eval param6_2 t) (eval param6_3 t) :=
  zero_domain param6_0 param6_1 param6_2 param6_3 t ht (by decide)

def region6 (t : Int) (ht : 0≤t) : Region := .inl (.inr (.n (eval param6_0 t) ⟨eval param6_1 t,eval param6_2 t,eval param6_3 t⟩ (domain6 t ht)))

theorem parent6_0 (t : Int) (ht : 0≤t) :
    data.parent (region6 t ht) (0 : Fin 2)=(reverse (relabel (node t 22) perm1.symm)) := by
  have he := mutation_equal (zero param6_0 param6_1 param6_2 param6_3 0) (preverse (prelabel (pnode 22) perm1.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,zero_eval] at he
  exact he

theorem parent6_1 (t : Int) (ht : 0≤t) :
    data.parent (region6 t ht) (1 : Fin 2)=(reverse (relabel (node t 25) perm20.symm)) := by
  have he := mutation_equal (zero param6_0 param6_1 param6_2 param6_3 1) (preverse (prelabel (pnode 25) perm20.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,zero_eval] at he
  exact he

theorem parents6_safe (t : Int) (ht : 0≤t) (p : Fin 2) :
    SafeCore t (data.parent (region6 t ht) p) := by
  have hp : p=0 ∨ p=1 := by change p=(0 : Fin 2) ∨ p=(1 : Fin 2); omega
  rcases hp with rfl|rfl
  · rw [parent6_0 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 22) perm1.symm)
  · rw [parent6_1 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 25) perm20.symm)

theorem region6_safe (t : Int) (ht : 0≤t) (i : Fin 2) :
    SafeCore t (matrix (zero param6_0 param6_1 param6_2 param6_3 i) t) := by
  rw [zero_eval]
  exact Safe.region (D:=data) (core:=Core t) (region6 t ht) (parents6_safe t ht) (0,Fin.castLE (by decide) i)

def param7_0 : P := [10,3]
def param7_1 : P := [13,4]
def param7_2 : P := [138,82,12]
def param7_3 : P := [1366,1230,366,36]
theorem domain7 (t : Int) (ht : 0≤t) : UnitZeroStrip.Domain (eval param7_0 t) (eval param7_1 t) (eval param7_2 t) (eval param7_3 t) :=
  zero_domain param7_0 param7_1 param7_2 param7_3 t ht (by decide)

def region7 (t : Int) (ht : 0≤t) : Region := .inl (.inr (.n (eval param7_0 t) ⟨eval param7_1 t,eval param7_2 t,eval param7_3 t⟩ (domain7 t ht)))

theorem parent7_0 (t : Int) (ht : 0≤t) :
    data.parent (region7 t ht) (0 : Fin 2)=(relabel (node t 23) perm0.symm) := by
  have he := mutation_equal (zero param7_0 param7_1 param7_2 param7_3 0) (prelabel (pnode 23) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,zero_eval] at he
  exact he

theorem parent7_1 (t : Int) (ht : 0≤t) :
    data.parent (region7 t ht) (1 : Fin 2)=(relabel (node t 27) perm21.symm) := by
  have he := mutation_equal (zero param7_0 param7_1 param7_2 param7_3 1) (prelabel (pnode 27) perm21.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,zero_eval] at he
  exact he

theorem parents7_safe (t : Int) (ht : 0≤t) (p : Fin 2) :
    SafeCore t (data.parent (region7 t ht) p) := by
  have hp : p=0 ∨ p=1 := by change p=(0 : Fin 2) ∨ p=(1 : Fin 2); omega
  rcases hp with rfl|rfl
  · rw [parent7_0 t ht]
    exact Safe.framed (node_safe t 23) perm0.symm
  · rw [parent7_1 t ht]
    exact Safe.framed (node_safe t 27) perm21.symm

theorem region7_safe (t : Int) (ht : 0≤t) (i : Fin 2) :
    SafeCore t (matrix (zero param7_0 param7_1 param7_2 param7_3 i) t) := by
  rw [zero_eval]
  exact Safe.region (D:=data) (core:=Core t) (region7 t ht) (parents7_safe t ht) (0,Fin.castLE (by decide) i)

theorem node_skew (t : Int) (i : Fin 49) : SkewSymmetric (node t i) := by
  rcases finCore i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp only [node,pnode,matrix_six] <;> exact ofSix_skew _ _ _ _ _ _

theorem cyclic0 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 0) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 0 0 2) t ht (by decide))
  have h1 := hr 2 3 (pos (pnode 0 2 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 0 3 0) t ht (by decide))
  omega

theorem cyclic1 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 1) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 1 2 (pos (pnode 1 1 2) t ht (by decide))
  have h1 := hr 2 3 (pos (pnode 1 2 3) t ht (by decide))
  have h2 := hr 3 1 (pos (pnode 1 3 1) t ht (by decide))
  omega

theorem cyclic2 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 2) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 2 0 3) t ht (by decide))
  have h1 := hr 3 2 (pos (pnode 2 3 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 2 2 0) t ht (by decide))
  omega

theorem cyclic3 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 3) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 3 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 3 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 3 1 0) t ht (by decide))
  omega

theorem cyclic4 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 4) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 4 0 1) t ht (by decide))
  have h1 := hr 1 3 (pos (pnode 4 1 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 4 3 0) t ht (by decide))
  omega

theorem cyclic5 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 5) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 1 3 (pos (pnode 5 1 3) t ht (by decide))
  have h1 := hr 3 2 (pos (pnode 5 3 2) t ht (by decide))
  have h2 := hr 2 1 (pos (pnode 5 2 1) t ht (by decide))
  omega

theorem cyclic6 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 6) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 1 2 (pos (pnode 6 1 2) t ht (by decide))
  have h1 := hr 2 3 (pos (pnode 6 2 3) t ht (by decide))
  have h2 := hr 3 1 (pos (pnode 6 3 1) t ht (by decide))
  omega

theorem cyclic7 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 7) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 7 0 2) t ht (by decide))
  have h1 := hr 2 3 (pos (pnode 7 2 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 7 3 0) t ht (by decide))
  omega

theorem cyclic8 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 8) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 8 0 1) t ht (by decide))
  have h1 := hr 1 2 (pos (pnode 8 1 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 8 2 0) t ht (by decide))
  omega

theorem cyclic9 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 9) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 9 0 1) t ht (by decide))
  have h1 := hr 1 3 (pos (pnode 9 1 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 9 3 0) t ht (by decide))
  omega

theorem cyclic10 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 10) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 10 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 10 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 10 1 0) t ht (by decide))
  omega

theorem cyclic11 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 11) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 11 0 1) t ht (by decide))
  have h1 := hr 1 3 (pos (pnode 11 1 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 11 3 0) t ht (by decide))
  omega

theorem cyclic12 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 12) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 12 0 2) t ht (by decide))
  have h1 := hr 2 3 (pos (pnode 12 2 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 12 3 0) t ht (by decide))
  omega

theorem cyclic13 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 13) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 13 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (pnode 13 3 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 13 1 0) t ht (by decide))
  omega

theorem cyclic14 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 14) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 14 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 14 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 14 1 0) t ht (by decide))
  omega

theorem cyclic15 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 15) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 15 0 1) t ht (by decide))
  have h1 := hr 1 3 (pos (pnode 15 1 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 15 3 0) t ht (by decide))
  omega

theorem cyclic16 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 16) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 1 2 (pos (pnode 16 1 2) t ht (by decide))
  have h1 := hr 2 3 (pos (pnode 16 2 3) t ht (by decide))
  have h2 := hr 3 1 (pos (pnode 16 3 1) t ht (by decide))
  omega

theorem cyclic17 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 17) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 17 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 17 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 17 1 0) t ht (by decide))
  omega

theorem cyclic18 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 18) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 18 0 1) t ht (by decide))
  have h1 := hr 1 2 (pos (pnode 18 1 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 18 2 0) t ht (by decide))
  omega

theorem cyclic19 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 19) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 19 0 1) t ht (by decide))
  have h1 := hr 1 2 (pos (pnode 19 1 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 19 2 0) t ht (by decide))
  omega

theorem cyclic20 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 20) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 20 0 1) t ht (by decide))
  have h1 := hr 1 3 (pos (pnode 20 1 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 20 3 0) t ht (by decide))
  omega

theorem cyclic21 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 21) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 21 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (pnode 21 3 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 21 1 0) t ht (by decide))
  omega

theorem cyclic22 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 22) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 22 0 3) t ht (by decide))
  have h1 := hr 3 2 (pos (pnode 22 3 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 22 2 0) t ht (by decide))
  omega

theorem cyclic23 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 23) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 23 0 3) t ht (by decide))
  have h1 := hr 3 2 (pos (pnode 23 3 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 23 2 0) t ht (by decide))
  omega

theorem cyclic24 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 24) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 24 0 3) t ht (by decide))
  have h1 := hr 3 2 (pos (pnode 24 3 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 24 2 0) t ht (by decide))
  omega

theorem cyclic25 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 25) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 25 0 1) t ht (by decide))
  have h1 := hr 1 3 (pos (pnode 25 1 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 25 3 0) t ht (by decide))
  omega

theorem cyclic26 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 26) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 26 0 2) t ht (by decide))
  have h1 := hr 2 3 (pos (pnode 26 2 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 26 3 0) t ht (by decide))
  omega

theorem cyclic27 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 27) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 27 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 27 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 27 1 0) t ht (by decide))
  omega

theorem cyclic28 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 28) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 28 0 2) t ht (by decide))
  have h1 := hr 2 3 (pos (pnode 28 2 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 28 3 0) t ht (by decide))
  omega

theorem cyclic29 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 29) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 29 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 29 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 29 1 0) t ht (by decide))
  omega

theorem cyclic30 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 30) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 30 0 1) t ht (by decide))
  have h1 := hr 1 2 (pos (pnode 30 1 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 30 2 0) t ht (by decide))
  omega

theorem cyclic31 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 31) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 31 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 31 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 31 1 0) t ht (by decide))
  omega

theorem cyclic32 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 32) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 32 0 1) t ht (by decide))
  have h1 := hr 1 3 (pos (pnode 32 1 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 32 3 0) t ht (by decide))
  omega

theorem cyclic33 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 33) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 33 0 1) t ht (by decide))
  have h1 := hr 1 2 (pos (pnode 33 1 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 33 2 0) t ht (by decide))
  omega

theorem cyclic34 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 34) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 34 0 1) t ht (by decide))
  have h1 := hr 1 3 (pos (pnode 34 1 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 34 3 0) t ht (by decide))
  omega

theorem cyclic35 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 35) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 35 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (pnode 35 3 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 35 1 0) t ht (by decide))
  omega

theorem cyclic36 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 36) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 36 0 1) t ht (by decide))
  have h1 := hr 1 2 (pos (pnode 36 1 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 36 2 0) t ht (by decide))
  omega

theorem cyclic37 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 37) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 37 0 1) t ht (by decide))
  have h1 := hr 1 2 (pos (pnode 37 1 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 37 2 0) t ht (by decide))
  omega

theorem cyclic38 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 38) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 38 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (pnode 38 3 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 38 1 0) t ht (by decide))
  omega

theorem cyclic39 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 39) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 39 0 2) t ht (by decide))
  have h1 := hr 2 3 (pos (pnode 39 2 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 39 3 0) t ht (by decide))
  omega

theorem cyclic40 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 40) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 40 0 1) t ht (by decide))
  have h1 := hr 1 2 (pos (pnode 40 1 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 40 2 0) t ht (by decide))
  omega

theorem cyclic41 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 41) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 41 0 1) t ht (by decide))
  have h1 := hr 1 2 (pos (pnode 41 1 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 41 2 0) t ht (by decide))
  omega

theorem cyclic42 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 42) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 42 0 2) t ht (by decide))
  have h1 := hr 2 3 (pos (pnode 42 2 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 42 3 0) t ht (by decide))
  omega

theorem cyclic43 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 43) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 43 0 1) t ht (by decide))
  have h1 := hr 1 3 (pos (pnode 43 1 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 43 3 0) t ht (by decide))
  omega

theorem cyclic44 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 44) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 44 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 44 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 44 1 0) t ht (by decide))
  omega

theorem cyclic45 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 45) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 45 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 45 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 45 1 0) t ht (by decide))
  omega

theorem cyclic46 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 46) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 46 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 46 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 46 1 0) t ht (by decide))
  omega

theorem cyclic47 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 47) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 47 0 3) t ht (by decide))
  have h1 := hr 3 2 (pos (pnode 47 3 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 47 2 0) t ht (by decide))
  omega

theorem cyclic48 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 48) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 48 0 1) t ht (by decide))
  have h1 := hr 1 2 (pos (pnode 48 1 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 48 2 0) t ht (by decide))
  omega

theorem edge0_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 0) 0) := by
  have he := mutation_equal (pnode 0) (prelabel (pnode 1) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 0) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 1) perm0.symm

theorem edge0_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 0) 1) := by
  have he := mutation_equal (pnode 0) (preverse (prelabel (pnode 1) perm0.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 0) t) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (node_safe t 1) perm0.symm)

theorem edge0_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 0) 2) := by
  have he := mutation_equal (pnode 0) (prelabel (pnode 2) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 0) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 2) perm0.symm

theorem edge0_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 0) 3) := by
  have he := mutation_equal (pnode 0) (prelabel (root [7,2] [41,26,4] [26,15,2] [6,2] [4,1] []) perm22.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 0) 3
  rw [show mutate (node t 0) 3=(relabel (matrix (root [7,2] [41,26,4] [26,15,2] [6,2] [4,1] []) t) perm22.symm) from he]
  exact IsRoot.relabelled (root_sound [7,2] [41,26,4] [26,15,2] [6,2] [4,1] [] t ht (by decide)) perm22.symm

theorem edge1_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 1) 0) := by
  have he := mutation_equal (pnode 1) (prelabel (pnode 0) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 1) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 0) perm0.symm

theorem edge1_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 1) 1) := by
  have he := mutation_equal (pnode 1) (preverse (prelabel (pnode 0) perm0.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 1) t) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (node_safe t 0) perm0.symm)

theorem edge1_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 1) 2) := by
  have he := mutation_equal (pnode 1) (prelabel (pnode 3) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 1) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 3) perm0.symm

theorem edge1_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 1) 3) := by
  have he := mutation_equal (pnode 1) (prelabel (pnode 4) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 1) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 4) perm0.symm

theorem edge2_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 2) 0) := by
  have he := mutation_equal (pnode 2) (prelabel (pnode 5) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 2) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 5) perm0.symm

theorem edge2_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 2) 1) := by
  have he := mutation_equal (pnode 2) (prelabel (pnode 6) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 2) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 6) perm0.symm

theorem edge2_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 2) 2) := by
  have he := mutation_equal (pnode 2) (prelabel (pnode 0) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 2) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 0) perm0.symm

theorem edge2_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 2) 3) := by
  have he := mutation_equal (pnode 2) (prelabel (pnode 7) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 2) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 7) perm0.symm

theorem edge3_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 3) 0) := by
  have he := mutation_equal (pnode 3) (prelabel (pnode 5) perm14.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 3) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 5) perm14.symm

theorem edge3_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 3) 1) := by
  have he := mutation_equal (pnode 3) (prelabel (pnode 8) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 3) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 8) perm0.symm

theorem edge3_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 3) 2) := by
  have he := mutation_equal (pnode 3) (prelabel (pnode 1) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 3) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 1) perm0.symm

theorem edge3_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 3) 3) := by
  have he := mutation_equal (pnode 3) (prelabel (pnode 9) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 3) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 9) perm0.symm

theorem edge4_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 4) 0) := by
  have he := mutation_equal (pnode 4) (prelabel (pnode 10) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 4) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 10) perm0.symm

theorem edge4_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 4) 1) := by
  have he := mutation_equal (pnode 4) (preverse (prelabel (root [4,1] [90,78,22,2] [7,6,1] [24,14,2] [2,1] [1]) perm10.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 4) 1
  rw [show mutate (node t 4) 1=(reverse (relabel (matrix (root [4,1] [90,78,22,2] [7,6,1] [24,14,2] [2,1] [1]) t) perm10.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [4,1] [90,78,22,2] [7,6,1] [24,14,2] [2,1] [1] t ht (by decide)) perm10.symm)

theorem edge4_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 4) 2) := by
  have he := mutation_equal (pnode 4) (prelabel (pnode 11) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 4) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 11) perm0.symm

theorem edge4_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 4) 3) := by
  have he := mutation_equal (pnode 4) (prelabel (pnode 1) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 4) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 1) perm0.symm

theorem edge5_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 5) 0) := by
  have he := mutation_equal (pnode 5) (prelabel (pnode 2) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 5) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 2) perm0.symm

theorem edge5_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 5) 1) := by
  have he := mutation_equal (pnode 5) (prelabel (pnode 12) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 5) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 12) perm0.symm

theorem edge5_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 5) 2) := by
  have he := mutation_equal (pnode 5) (prelabel (pnode 3) perm14.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 5) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 3) perm14.symm

theorem edge5_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 5) 3) := by
  have he := mutation_equal (pnode 5) (prelabel (pnode 13) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 5) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 13) perm0.symm

theorem edge6_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 6) 0) := by
  have he := mutation_equal (pnode 6) (prelabel (pnode 12) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 6) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 12) perm0.symm

theorem edge6_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 6) 1) := by
  have he := mutation_equal (pnode 6) (prelabel (pnode 2) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 6) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 2) perm0.symm

theorem edge6_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 6) 2) := by
  have he := mutation_equal (pnode 6) (prelabel (pnode 14) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 6) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 14) perm0.symm

theorem edge6_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 6) 3) := by
  have he := mutation_equal (pnode 6) (prelabel (pnode 15) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 6) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 15) perm0.symm

theorem edge7_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 7) 0) := by
  have he := mutation_equal (pnode 7) (prelabel (pnode 16) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 7) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 16) perm0.symm

theorem edge7_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 7) 1) := by
  have he := mutation_equal (pnode 7) (preverse (prelabel (zero param5_0 param5_1 param5_2 param5_3 0) perm0.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 7) t) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (region5_safe t ht 0) perm0.symm)

theorem edge7_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 7) 2) := by
  have he := mutation_equal (pnode 7) (preverse (prelabel (root [7,2] [41,26,4] [466,420,124,12] [6,2] [68,41,6] []) perm16.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 7) 2
  rw [show mutate (node t 7) 2=(reverse (relabel (matrix (root [7,2] [41,26,4] [466,420,124,12] [6,2] [68,41,6] []) t) perm16.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [7,2] [41,26,4] [466,420,124,12] [6,2] [68,41,6] [] t ht (by decide)) perm16.symm)

theorem edge7_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 7) 3) := by
  have he := mutation_equal (pnode 7) (prelabel (pnode 2) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 7) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 2) perm0.symm

theorem edge8_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 8) 0) := by
  have he := mutation_equal (pnode 8) (preverse (prelabel (fork [3] [2] [2] [5] [4] [2,1]) perm3.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (node_safe t 8)
  rw [show mutate (node t 8) 0=(reverse (relabel (matrix (fork [3] [2] [2] [5] [4] [2,1]) t) perm3.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [3] [2] [2] [5] [4] [2,1] t ht (by decide)) perm3.symm)

theorem edge8_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 8) 1) := by
  have he := mutation_equal (pnode 8) (prelabel (pnode 3) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 8) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 3) perm0.symm

theorem edge8_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 8) 2) := by
  have he := mutation_equal (pnode 8) (prelabel (pnode 17) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 8) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 17) perm0.symm

theorem edge8_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 8) 3) := by
  have he := mutation_equal (pnode 8) (prelabel (pnode 18) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 8) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 18) perm0.symm

theorem edge9_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 9) 0) := by
  have he := mutation_equal (pnode 9) (preverse (prelabel (fork [6,2] [10,10,2] [7,2] [58,79,32,4] [41,26,4] [2]) perm4.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (node_safe t 9)
  rw [show mutate (node t 9) 0=(reverse (relabel (matrix (fork [6,2] [10,10,2] [7,2] [58,79,32,4] [41,26,4] [2]) t) perm4.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [6,2] [10,10,2] [7,2] [58,79,32,4] [41,26,4] [2] t ht (by decide)) perm4.symm)

theorem edge9_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 9) 1) := by
  have he := mutation_equal (pnode 9) (prelabel (fork [2,1] [10,10,2] [2] [14,28,14,2] [5,2] [7,2]) perm10.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (node_safe t 9)
  rw [show mutate (node t 9) 1=(relabel (matrix (fork [2,1] [10,10,2] [2] [14,28,14,2] [5,2] [7,2]) t) perm10.symm) from he]
  exact IsFork.relabelled (fork_sound [2,1] [10,10,2] [2] [14,28,14,2] [5,2] [7,2] t ht (by decide)) perm10.symm

theorem edge9_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 9) 2) := by
  have he := mutation_equal (pnode 9) (prelabel (pnode 11) perm1.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 9) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 11) perm1.symm

theorem edge9_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 9) 3) := by
  have he := mutation_equal (pnode 9) (prelabel (pnode 3) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 9) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 3) perm0.symm

theorem edge10_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 10) 0) := by
  have he := mutation_equal (pnode 10) (prelabel (pnode 4) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 10) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 4) perm0.symm

theorem edge10_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 10) 1) := by
  have he := mutation_equal (pnode 10) (preverse (prelabel (root [24,14,2] [623,724,310,58,4] [3354,5102,3074,918,136,8] [26,15,2] [140,131,40,4] [1]) perm6.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 10) 1
  rw [show mutate (node t 10) 1=(reverse (relabel (matrix (root [24,14,2] [623,724,310,58,4] [3354,5102,3074,918,136,8] [26,15,2] [140,131,40,4] [1]) t) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [24,14,2] [623,724,310,58,4] [3354,5102,3074,918,136,8] [26,15,2] [140,131,40,4] [1] t ht (by decide)) perm6.symm)

theorem edge10_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 10) 2) := by
  have he := mutation_equal (pnode 10) (prelabel (pnode 19) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 10) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 19) perm0.symm

theorem edge10_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 10) 3) := by
  have he := mutation_equal (pnode 10) (prelabel (pnode 20) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 10) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 20) perm0.symm

theorem edge11_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 11) 0) := by
  have he := mutation_equal (pnode 11) (prelabel (pnode 21) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 11) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 21) perm0.symm

theorem edge11_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 11) 1) := by
  have he := mutation_equal (pnode 11) (prelabel (root [24,14,2] [49,52,18,2] [41,26,4] [2,1] [2] [1]) perm6.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 11) 1
  rw [show mutate (node t 11) 1=(relabel (matrix (root [24,14,2] [49,52,18,2] [41,26,4] [2,1] [2] [1]) t) perm6.symm) from he]
  exact IsRoot.relabelled (root_sound [24,14,2] [49,52,18,2] [41,26,4] [2,1] [2] [1] t ht (by decide)) perm6.symm

theorem edge11_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 11) 2) := by
  have he := mutation_equal (pnode 11) (prelabel (pnode 4) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 11) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 4) perm0.symm

theorem edge11_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 11) 3) := by
  have he := mutation_equal (pnode 11) (prelabel (pnode 9) perm1.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 11) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 9) perm1.symm

theorem edge12_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 12) 0) := by
  have he := mutation_equal (pnode 12) (prelabel (pnode 6) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 12) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 6) perm0.symm

theorem edge12_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 12) 1) := by
  have he := mutation_equal (pnode 12) (prelabel (pnode 5) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 12) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 5) perm0.symm

theorem edge12_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 12) 2) := by
  have he := mutation_equal (pnode 12) (prelabel (pnode 22) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 12) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 22) perm0.symm

theorem edge12_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 12) 3) := by
  have he := mutation_equal (pnode 12) (prelabel (pnode 23) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 12) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 23) perm0.symm

theorem edge13_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 13) 0) := by
  have he := mutation_equal (pnode 13) (prelabel (pnode 16) perm21.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 13) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 16) perm21.symm

theorem edge13_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 13) 1) := by
  have he := mutation_equal (pnode 13) (prelabel (root [10,3] [99,60,9] [574,552,174,18] [10,3] [58,38,6] [1]) perm10.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 13) 1
  rw [show mutate (node t 13) 1=(relabel (matrix (root [10,3] [99,60,9] [574,552,174,18] [10,3] [58,38,6] [1]) t) perm10.symm) from he]
  exact IsRoot.relabelled (root_sound [10,3] [99,60,9] [574,552,174,18] [10,3] [58,38,6] [1] t ht (by decide)) perm10.symm

theorem edge13_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 13) 2) := by
  have he := mutation_equal (pnode 13) (prelabel (pnode 24) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 13) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 24) perm0.symm

theorem edge13_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 13) 3) := by
  have he := mutation_equal (pnode 13) (prelabel (pnode 5) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 13) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 5) perm0.symm

theorem edge14_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 14) 0) := by
  have he := mutation_equal (pnode 14) (prelabel (pnode 25) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 14) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 25) perm0.symm

theorem edge14_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 14) 1) := by
  have he := mutation_equal (pnode 14) (prelabel (root [2] [3] [19,6] [2] [16,5] [1]) perm8.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 14) 1
  rw [show mutate (node t 14) 1=(relabel (matrix (root [2] [3] [19,6] [2] [16,5] [1]) t) perm8.symm) from he]
  exact IsRoot.relabelled (root_sound [2] [3] [19,6] [2] [16,5] [1] t ht (by decide)) perm8.symm

theorem edge14_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 14) 2) := by
  have he := mutation_equal (pnode 14) (prelabel (pnode 6) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 14) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 6) perm0.symm

theorem edge14_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 14) 3) := by
  have he := mutation_equal (pnode 14) (prelabel (pnode 26) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 14) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 26) perm0.symm

theorem edge15_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 15) 0) := by
  have he := mutation_equal (pnode 15) (prelabel (pnode 27) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 15) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 27) perm0.symm

theorem edge15_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 15) 1) := by
  have he := mutation_equal (pnode 15) (preverse (prelabel (root [10,3] [99,60,9] [1267,1170,357,36] [10,3] [128,79,12] [1]) perm10.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 15) 1
  rw [show mutate (node t 15) 1=(reverse (relabel (matrix (root [10,3] [99,60,9] [1267,1170,357,36] [10,3] [128,79,12] [1]) t) perm10.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [10,3] [99,60,9] [1267,1170,357,36] [10,3] [128,79,12] [1] t ht (by decide)) perm10.symm)

theorem edge15_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 15) 2) := by
  have he := mutation_equal (pnode 15) (prelabel (pnode 28) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 15) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 28) perm0.symm

theorem edge15_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 15) 3) := by
  have he := mutation_equal (pnode 15) (prelabel (pnode 6) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 15) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 6) perm0.symm

theorem edge16_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 16) 0) := by
  have he := mutation_equal (pnode 16) (prelabel (pnode 7) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 16) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 7) perm0.symm

theorem edge16_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 16) 1) := by
  have he := mutation_equal (pnode 16) (preverse (prelabel (zero param5_0 param5_1 param5_2 param5_3 1) perm0.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 16) t) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (region5_safe t ht 1) perm0.symm)

theorem edge16_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 16) 2) := by
  have he := mutation_equal (pnode 16) (prelabel (pnode 29) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 16) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 29) perm0.symm

theorem edge16_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 16) 3) := by
  have he := mutation_equal (pnode 16) (prelabel (pnode 13) perm21.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 16) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 13) perm21.symm

theorem edge17_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 17) 0) := by
  have he := mutation_equal (pnode 17) (prelabel (pnode 30) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 17) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 30) perm0.symm

theorem edge17_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 17) 1) := by
  have he := mutation_equal (pnode 17) (prelabel (root [2] [5,2] [5] [2,1] [4] [1]) perm9.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 17) 1
  rw [show mutate (node t 17) 1=(relabel (matrix (root [2] [5,2] [5] [2,1] [4] [1]) t) perm9.symm) from he]
  exact IsRoot.relabelled (root_sound [2] [5,2] [5] [2,1] [4] [1] t ht (by decide)) perm9.symm

theorem edge17_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 17) 2) := by
  have he := mutation_equal (pnode 17) (prelabel (pnode 8) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 17) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 8) perm0.symm

theorem edge17_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 17) 3) := by
  have he := mutation_equal (pnode 17) (prelabel (pnode 31) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 17) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 31) perm0.symm

theorem edge18_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 18) 0) := by
  have he := mutation_equal (pnode 18) (preverse (prelabel (pnode 31) perm20.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 18) t) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (node_safe t 31) perm20.symm)

theorem edge18_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 18) 1) := by
  have he := mutation_equal (pnode 18) (prelabel (fork [4,1] [2,1] [2] [7,6,1] [7,2] [2]) perm9.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (node_safe t 18)
  rw [show mutate (node t 18) 1=(relabel (matrix (fork [4,1] [2,1] [2] [7,6,1] [7,2] [2]) t) perm9.symm) from he]
  exact IsFork.relabelled (fork_sound [4,1] [2,1] [2] [7,6,1] [7,2] [2] t ht (by decide)) perm9.symm

theorem edge18_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 18) 2) := by
  have he := mutation_equal (pnode 18) (preverse (prelabel (pnode 18) perm21.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 18) t) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (node_safe t 18) perm21.symm)

theorem edge18_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 18) 3) := by
  have he := mutation_equal (pnode 18) (prelabel (pnode 8) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 18) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 8) perm0.symm

theorem edge19_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 19) 0) := by
  have he := mutation_equal (pnode 19) (prelabel (pnode 21) perm14.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 19) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 21) perm14.symm

theorem edge19_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 19) 1) := by
  have he := mutation_equal (pnode 19) (prelabel (fork [26,15,2] [2,1] [166,146,42,4] [51,56,19,2] [4315,6286,3614,1026,144,8] [6,2]) perm8.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (node_safe t 19)
  rw [show mutate (node t 19) 1=(relabel (matrix (fork [26,15,2] [2,1] [166,146,42,4] [51,56,19,2] [4315,6286,3614,1026,144,8] [6,2]) t) perm8.symm) from he]
  exact IsFork.relabelled (fork_sound [26,15,2] [2,1] [166,146,42,4] [51,56,19,2] [4315,6286,3614,1026,144,8] [6,2] t ht (by decide)) perm8.symm

theorem edge19_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 19) 2) := by
  have he := mutation_equal (pnode 19) (prelabel (pnode 10) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 19) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 10) perm0.symm

theorem edge19_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 19) 3) := by
  have he := mutation_equal (pnode 19) (prelabel (pnode 32) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 19) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 32) perm0.symm

theorem edge20_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 20) 0) := by
  have he := mutation_equal (pnode 20) (preverse (prelabel (fork [6,2] [816,1052,500,104,8] [7,2] [4756,7813,5064,1620,256,16] [41,26,4] [26,15,2]) perm4.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (node_safe t 20)
  rw [show mutate (node t 20) 0=(reverse (relabel (matrix (fork [6,2] [816,1052,500,104,8] [7,2] [4756,7813,5064,1620,256,16] [41,26,4] [26,15,2]) t) perm4.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [6,2] [816,1052,500,104,8] [7,2] [4756,7813,5064,1620,256,16] [41,26,4] [26,15,2] t ht (by decide)) perm4.symm)

theorem edge20_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 20) 1) := by
  have he := mutation_equal (pnode 20) (prelabel (fork [140,131,40,4] [816,1052,500,104,8] [26,15,2] [114234,254174,240452,125404,38952,7208,736,32] [3641,5506,3285,966,140,8] [7,2]) perm10.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (node_safe t 20)
  rw [show mutate (node t 20) 1=(relabel (matrix (fork [140,131,40,4] [816,1052,500,104,8] [26,15,2] [114234,254174,240452,125404,38952,7208,736,32] [3641,5506,3285,966,140,8] [7,2]) t) perm10.symm) from he]
  exact IsFork.relabelled (fork_sound [140,131,40,4] [816,1052,500,104,8] [26,15,2] [114234,254174,240452,125404,38952,7208,736,32] [3641,5506,3285,966,140,8] [7,2] t ht (by decide)) perm10.symm

theorem edge20_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 20) 2) := by
  have he := mutation_equal (pnode 20) (prelabel (pnode 33) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 20) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 33) perm0.symm

theorem edge20_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 20) 3) := by
  have he := mutation_equal (pnode 20) (prelabel (pnode 10) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 20) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 10) perm0.symm

theorem edge21_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 21) 0) := by
  have he := mutation_equal (pnode 21) (prelabel (pnode 11) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 21) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 11) perm0.symm

theorem edge21_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 21) 1) := by
  have he := mutation_equal (pnode 21) (prelabel (root [166,146,42,4] [338,460,230,50,4] [3977,5826,3384,976,140,8] [2,1] [24,14,2] [1]) perm11.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 21) 1
  rw [show mutate (node t 21) 1=(relabel (matrix (root [166,146,42,4] [338,460,230,50,4] [3977,5826,3384,976,140,8] [2,1] [24,14,2] [1]) t) perm11.symm) from he]
  exact IsRoot.relabelled (root_sound [166,146,42,4] [338,460,230,50,4] [3977,5826,3384,976,140,8] [2,1] [24,14,2] [1] t ht (by decide)) perm11.symm

theorem edge21_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 21) 2) := by
  have he := mutation_equal (pnode 21) (prelabel (pnode 19) perm14.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 21) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 19) perm14.symm

theorem edge21_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 21) 3) := by
  have he := mutation_equal (pnode 21) (preverse (prelabel (fork [7,2] [6,2] [166,146,42,4] [41,26,4] [1138,1340,584,112,8] [2,1]) perm19.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 3 (node_safe t 21)
  rw [show mutate (node t 21) 3=(reverse (relabel (matrix (fork [7,2] [6,2] [166,146,42,4] [41,26,4] [1138,1340,584,112,8] [2,1]) t) perm19.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [7,2] [6,2] [166,146,42,4] [41,26,4] [1138,1340,584,112,8] [2,1] t ht (by decide)) perm19.symm)

theorem edge22_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 22) 0) := by
  have he := mutation_equal (pnode 22) (prelabel (pnode 25) perm14.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 22) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 25) perm14.symm

theorem edge22_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 22) 1) := by
  have he := mutation_equal (pnode 22) (preverse (prelabel (zero param6_0 param6_1 param6_2 param6_3 0) perm1.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 22) t) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (region6_safe t ht 0) perm1.symm)

theorem edge22_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 22) 2) := by
  have he := mutation_equal (pnode 22) (prelabel (pnode 12) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 22) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 12) perm0.symm

theorem edge22_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 22) 3) := by
  have he := mutation_equal (pnode 22) (preverse (prelabel (root [14,4] [181,108,16] [250,142,20] [13,4] [18,5] []) perm22.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 22) 3
  rw [show mutate (node t 22) 3=(reverse (relabel (matrix (root [14,4] [181,108,16] [250,142,20] [13,4] [18,5] []) t) perm22.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [14,4] [181,108,16] [250,142,20] [13,4] [18,5] [] t ht (by decide)) perm22.symm)

theorem edge23_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 23) 0) := by
  have he := mutation_equal (pnode 23) (prelabel (pnode 27) perm21.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 23) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 27) perm21.symm

theorem edge23_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 23) 1) := by
  have he := mutation_equal (pnode 23) (prelabel (zero param7_0 param7_1 param7_2 param7_3 0) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 23) t) 1)
  rw [he]
  exact Safe.framed (region7_safe t ht 0) perm0.symm

theorem edge23_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 23) 2) := by
  have he := mutation_equal (pnode 23) (prelabel (root [14,4] [181,108,16] [1922,1697,496,48] [13,4] [138,82,12] []) perm16.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 23) 2
  rw [show mutate (node t 23) 2=(relabel (matrix (root [14,4] [181,108,16] [1922,1697,496,48] [13,4] [138,82,12] []) t) perm16.symm) from he]
  exact IsRoot.relabelled (root_sound [14,4] [181,108,16] [1922,1697,496,48] [13,4] [138,82,12] [] t ht (by decide)) perm16.symm

theorem edge23_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 23) 3) := by
  have he := mutation_equal (pnode 23) (prelabel (pnode 12) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 23) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 12) perm0.symm

theorem edge24_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 24) 0) := by
  have he := mutation_equal (pnode 24) (prelabel (pnode 34) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 24) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 34) perm0.symm

theorem edge24_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 24) 1) := by
  have he := mutation_equal (pnode 24) (preverse (prelabel (fork [58,38,6] [338,341,112,12] [10,3] [19598,32620,21482,6998,1128,72] [581,554,174,18] [7,2]) perm9.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (node_safe t 24)
  rw [show mutate (node t 24) 1=(reverse (relabel (matrix (fork [58,38,6] [338,341,112,12] [10,3] [19598,32620,21482,6998,1128,72] [581,554,174,18] [7,2]) t) perm9.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [58,38,6] [338,341,112,12] [10,3] [19598,32620,21482,6998,1128,72] [581,554,174,18] [7,2] t ht (by decide)) perm9.symm)

theorem edge24_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 24) 2) := by
  have he := mutation_equal (pnode 24) (prelabel (pnode 13) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 24) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 13) perm0.symm

theorem edge24_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 24) 3) := by
  have he := mutation_equal (pnode 24) (prelabel (fork [6,2] [338,341,112,12] [7,2] [1970,2684,1348,296,24] [41,26,4] [10,3]) perm23.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 3 (node_safe t 24)
  rw [show mutate (node t 24) 3=(relabel (matrix (fork [6,2] [338,341,112,12] [7,2] [1970,2684,1348,296,24] [41,26,4] [10,3]) t) perm23.symm) from he]
  exact IsFork.relabelled (fork_sound [6,2] [338,341,112,12] [7,2] [1970,2684,1348,296,24] [41,26,4] [10,3] t ht (by decide)) perm23.symm

theorem edge25_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 25) 0) := by
  have he := mutation_equal (pnode 25) (prelabel (pnode 14) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 25) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 14) perm0.symm

theorem edge25_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 25) 1) := by
  have he := mutation_equal (pnode 25) (preverse (prelabel (zero param6_0 param6_1 param6_2 param6_3 1) perm15.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 25) t) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (region6_safe t ht 1) perm15.symm)

theorem edge25_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 25) 2) := by
  have he := mutation_equal (pnode 25) (prelabel (pnode 22) perm14.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 25) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 22) perm14.symm

theorem edge25_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 25) 3) := by
  have he := mutation_equal (pnode 25) (prelabel (pnode 35) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 25) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 35) perm0.symm

theorem edge26_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 26) 0) := by
  have he := mutation_equal (pnode 26) (prelabel (pnode 36) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 26) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 36) perm0.symm

theorem edge26_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 26) 1) := by
  have he := mutation_equal (pnode 26) (preverse (prelabel (fork [16,5] [206,129,20] [2] [3283,3090,965,100] [33,10] [14,4]) perm11.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (node_safe t 26)
  rw [show mutate (node t 26) 1=(reverse (relabel (matrix (fork [16,5] [206,129,20] [2] [3283,3090,965,100] [33,10] [14,4]) t) perm11.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [16,5] [206,129,20] [2] [3283,3090,965,100] [33,10] [14,4] t ht (by decide)) perm11.symm)

theorem edge26_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 26) 2) := by
  have he := mutation_equal (pnode 26) (prelabel (fork [13,4] [206,129,20] [14,4] [2662,2496,776,80] [181,108,16] [2]) perm17.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 2 (node_safe t 26)
  rw [show mutate (node t 26) 2=(relabel (matrix (fork [13,4] [206,129,20] [14,4] [2662,2496,776,80] [181,108,16] [2]) t) perm17.symm) from he]
  exact IsFork.relabelled (fork_sound [13,4] [206,129,20] [14,4] [2662,2496,776,80] [181,108,16] [2] t ht (by decide)) perm17.symm

theorem edge26_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 26) 3) := by
  have he := mutation_equal (pnode 26) (prelabel (pnode 14) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 26) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 14) perm0.symm

theorem edge27_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 27) 0) := by
  have he := mutation_equal (pnode 27) (prelabel (pnode 15) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 27) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 15) perm0.symm

theorem edge27_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 27) 1) := by
  have he := mutation_equal (pnode 27) (prelabel (zero param7_0 param7_1 param7_2 param7_3 1) perm21.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 27) t) 1)
  rw [he]
  exact Safe.framed (region7_safe t ht 1) perm21.symm

theorem edge27_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 27) 2) := by
  have he := mutation_equal (pnode 27) (prelabel (pnode 37) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 27) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 37) perm0.symm

theorem edge27_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 27) 3) := by
  have he := mutation_equal (pnode 27) (prelabel (pnode 23) perm21.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 27) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 23) perm21.symm

theorem edge28_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 28) 0) := by
  have he := mutation_equal (pnode 28) (prelabel (pnode 38) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 28) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 38) perm0.symm

theorem edge28_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 28) 1) := by
  have he := mutation_equal (pnode 28) (prelabel (fork [128,79,12] [1654,1536,472,48] [10,3] [211699,327270,201608,61864,9456,576] [1281,1174,357,36] [14,4]) perm9.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (node_safe t 28)
  rw [show mutate (node t 28) 1=(relabel (matrix (fork [128,79,12] [1654,1536,472,48] [10,3] [211699,327270,201608,61864,9456,576] [1281,1174,357,36] [14,4]) t) perm9.symm) from he]
  exact IsFork.relabelled (fork_sound [128,79,12] [1654,1536,472,48] [10,3] [211699,327270,201608,61864,9456,576] [1281,1174,357,36] [14,4] t ht (by decide)) perm9.symm

theorem edge28_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 28) 2) := by
  have he := mutation_equal (pnode 28) (prelabel (pnode 15) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 28) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 15) perm0.symm

theorem edge28_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 28) 3) := by
  have he := mutation_equal (pnode 28) (preverse (prelabel (fork [13,4] [1654,1536,472,48] [14,4] [21374,26505,12268,2512,192] [181,108,16] [10,3]) perm23.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 3 (node_safe t 28)
  rw [show mutate (node t 28) 3=(reverse (relabel (matrix (fork [13,4] [1654,1536,472,48] [14,4] [21374,26505,12268,2512,192] [181,108,16] [10,3]) t) perm23.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [13,4] [1654,1536,472,48] [14,4] [21374,26505,12268,2512,192] [181,108,16] [10,3] t ht (by decide)) perm23.symm)

theorem edge29_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 29) 0) := by
  have he := mutation_equal (pnode 29) (preverse (prelabel (generic param0_0 param0_1 param0_2 param0_3 1) perm5.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 29) t) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (region0_safe t ht 1) perm5.symm)

theorem edge29_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 29) 1) := by
  have he := mutation_equal (pnode 29) (prelabel (root [68,41,6] [27738,42702,26134,7946,1200,72] [3943,4962,2314,474,36] [408,382,118,12] [58,38,6] [1]) perm8.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 29) 1
  rw [show mutate (node t 29) 1=(relabel (matrix (root [68,41,6] [27738,42702,26134,7946,1200,72] [3943,4962,2314,474,36] [408,382,118,12] [58,38,6] [1]) t) perm8.symm) from he]
  exact IsRoot.relabelled (root_sound [68,41,6] [27738,42702,26134,7946,1200,72] [3943,4962,2314,474,36] [408,382,118,12] [58,38,6] [1] t ht (by decide)) perm8.symm

theorem edge29_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 29) 2) := by
  have he := mutation_equal (pnode 29) (prelabel (pnode 16) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 29) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 16) perm0.symm

theorem edge29_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 29) 3) := by
  have he := mutation_equal (pnode 29) (prelabel (pnode 34) perm15.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 29) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 34) perm15.symm

theorem edge30_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 30) 0) := by
  have he := mutation_equal (pnode 30) (prelabel (pnode 17) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 30) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 17) perm0.symm

theorem edge30_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 30) 1) := by
  have he := mutation_equal (pnode 30) (preverse (prelabel (fork [4] [10] [2,1] [37] [9,4] [2]) perm6.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (node_safe t 30)
  rw [show mutate (node t 30) 1=(reverse (relabel (matrix (fork [4] [10] [2,1] [37] [9,4] [2]) t) perm6.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [4] [10] [2,1] [37] [9,4] [2] t ht (by decide)) perm6.symm)

theorem edge30_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 30) 2) := by
  have he := mutation_equal (pnode 30) (prelabel (fork [3] [10] [2] [26] [5] [2,1]) perm12.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 2 (node_safe t 30)
  rw [show mutate (node t 30) 2=(relabel (matrix (fork [3] [10] [2] [26] [5] [2,1]) t) perm12.symm) from he]
  exact IsFork.relabelled (fork_sound [3] [10] [2] [26] [5] [2,1] t ht (by decide)) perm12.symm

theorem edge30_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 30) 3) := by
  have he := mutation_equal (pnode 30) (prelabel (pnode 40) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 30) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 40) perm0.symm

theorem edge31_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 31) 0) := by
  have he := mutation_equal (pnode 31) (prelabel (pnode 41) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 31) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 41) perm0.symm

theorem edge31_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 31) 1) := by
  have he := mutation_equal (pnode 31) (preverse (prelabel (root [6,1] [10,2] [11,8,1] [2] [2,1] [1]) perm6.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 31) 1
  rw [show mutate (node t 31) 1=(reverse (relabel (matrix (root [6,1] [10,2] [11,8,1] [2] [2,1] [1]) t) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [6,1] [10,2] [11,8,1] [2] [2,1] [1] t ht (by decide)) perm6.symm)

theorem edge31_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 31) 2) := by
  have he := mutation_equal (pnode 31) (preverse (prelabel (pnode 18) perm15.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 31) t) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (node_safe t 18) perm15.symm)

theorem edge31_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 31) 3) := by
  have he := mutation_equal (pnode 31) (prelabel (pnode 17) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 31) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 17) perm0.symm

theorem edge32_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 32) 0) := by
  have he := mutation_equal (pnode 32) (prelabel (generic param1_0 param1_1 param1_2 param1_3 1) perm3.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 32) t) 0)
  rw [he]
  exact Safe.framed (region1_safe t ht 1) perm3.symm

theorem edge32_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 32) 1) := by
  have he := mutation_equal (pnode 32) (preverse (prelabel (root [166,146,42,4] [165662,346400,308734,152122,44780,7880,768,32] [23239,42186,31646,12566,2788,328,16] [998,1209,544,108,8] [140,131,40,4] [1]) perm10.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 32) 1
  rw [show mutate (node t 32) 1=(reverse (relabel (matrix (root [166,146,42,4] [165662,346400,308734,152122,44780,7880,768,32] [23239,42186,31646,12566,2788,328,16] [998,1209,544,108,8] [140,131,40,4] [1]) t) perm10.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [166,146,42,4] [165662,346400,308734,152122,44780,7880,768,32] [23239,42186,31646,12566,2788,328,16] [998,1209,544,108,8] [140,131,40,4] [1] t ht (by decide)) perm10.symm)

theorem edge32_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 32) 2) := by
  have he := mutation_equal (pnode 32) (prelabel (pnode 33) perm1.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 32) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 33) perm1.symm

theorem edge32_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 32) 3) := by
  have he := mutation_equal (pnode 32) (prelabel (pnode 19) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 32) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 19) perm0.symm

theorem edge33_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 33) 0) := by
  have he := mutation_equal (pnode 33) (prelabel (pnode 42) perm20.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 33) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 42) perm20.symm

theorem edge33_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 33) 1) := by
  have he := mutation_equal (pnode 33) (prelabel (root [998,1209,544,108,8] [139721,299998,274459,138736,41864,7544,752,32] [25941,46402,34275,13386,2916,336,16] [140,131,40,4] [26,15,2] [1]) perm7.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 33) 1
  rw [show mutate (node t 33) 1=(relabel (matrix (root [998,1209,544,108,8] [139721,299998,274459,138736,41864,7544,752,32] [25941,46402,34275,13386,2916,336,16] [140,131,40,4] [26,15,2] [1]) t) perm7.symm) from he]
  exact IsRoot.relabelled (root_sound [998,1209,544,108,8] [139721,299998,274459,138736,41864,7544,752,32] [25941,46402,34275,13386,2916,336,16] [140,131,40,4] [26,15,2] [1] t ht (by decide)) perm7.symm

theorem edge33_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 33) 2) := by
  have he := mutation_equal (pnode 33) (prelabel (pnode 20) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 33) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 20) perm0.symm

theorem edge33_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 33) 3) := by
  have he := mutation_equal (pnode 33) (prelabel (pnode 32) perm1.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 33) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 32) perm1.symm

theorem edge34_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 34) 0) := by
  have he := mutation_equal (pnode 34) (prelabel (pnode 24) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 34) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 24) perm0.symm

theorem edge34_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 34) 1) := by
  have he := mutation_equal (pnode 34) (preverse (prelabel (root [408,382,118,12] [23665,37660,23808,7472,1164,72] [4073,5042,2326,474,36] [58,38,6] [10,3] [1]) perm11.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 34) 1
  rw [show mutate (node t 34) 1=(reverse (relabel (matrix (root [408,382,118,12] [23665,37660,23808,7472,1164,72] [4073,5042,2326,474,36] [58,38,6] [10,3] [1]) t) perm11.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [408,382,118,12] [23665,37660,23808,7472,1164,72] [4073,5042,2326,474,36] [58,38,6] [10,3] [1] t ht (by decide)) perm11.symm)

theorem edge34_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 34) 2) := by
  have he := mutation_equal (pnode 34) (prelabel (pnode 29) perm20.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 34) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 29) perm20.symm

theorem edge34_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 34) 3) := by
  have he := mutation_equal (pnode 34) (prelabel (pnode 39) perm14.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 34) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 39) perm14.symm

theorem edge35_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 35) 0) := by
  have he := mutation_equal (pnode 35) (prelabel (pnode 36) perm21.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 35) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 36) perm21.symm

theorem edge35_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 35) 1) := by
  have he := mutation_equal (pnode 35) (prelabel (root [18,5] [4199,3632,1045,100] [287,170,25] [234,137,20] [16,5] [1]) perm11.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 35) 1
  rw [show mutate (node t 35) 1=(relabel (matrix (root [18,5] [4199,3632,1045,100] [287,170,25] [234,137,20] [16,5] [1]) t) perm11.symm) from he]
  exact IsRoot.relabelled (root_sound [18,5] [4199,3632,1045,100] [287,170,25] [234,137,20] [16,5] [1] t ht (by decide)) perm11.symm

theorem edge35_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 35) 2) := by
  have he := mutation_equal (pnode 35) (preverse (prelabel (generic param2_0 param2_1 param2_2 param2_3 1) perm13.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 35) t) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (region2_safe t ht 1) perm13.symm)

theorem edge35_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 35) 3) := by
  have he := mutation_equal (pnode 35) (prelabel (pnode 25) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 35) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 25) perm0.symm

theorem edge36_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 36) 0) := by
  have he := mutation_equal (pnode 36) (prelabel (pnode 26) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 36) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 26) perm0.symm

theorem edge36_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 36) 1) := by
  have he := mutation_equal (pnode 36) (preverse (prelabel (root [234,137,20] [3745,3362,1005,100] [454,270,40] [16,5] [2] [1]) perm9.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 36) 1
  rw [show mutate (node t 36) 1=(reverse (relabel (matrix (root [234,137,20] [3745,3362,1005,100] [454,270,40] [16,5] [2] [1]) t) perm9.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [234,137,20] [3745,3362,1005,100] [454,270,40] [16,5] [2] [1] t ht (by decide)) perm9.symm)

theorem edge36_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 36) 2) := by
  have he := mutation_equal (pnode 36) (prelabel (pnode 43) perm15.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 36) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 43) perm15.symm

theorem edge36_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 36) 3) := by
  have he := mutation_equal (pnode 36) (prelabel (pnode 35) perm21.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 36) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 35) perm21.symm

theorem edge37_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 37) 0) := by
  have he := mutation_equal (pnode 37) (prelabel (pnode 38) perm14.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 37) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 38) perm14.symm

theorem edge37_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 37) 1) := by
  have he := mutation_equal (pnode 37) (preverse (prelabel (root [138,82,12] [247559,370388,220996,65728,9744,576] [17663,21398,9670,1932,144] [1794,1618,484,48] [128,79,12] [1]) perm9.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 37) 1
  rw [show mutate (node t 37) 1=(reverse (relabel (matrix (root [138,82,12] [247559,370388,220996,65728,9744,576] [17663,21398,9670,1932,144] [1794,1618,484,48] [128,79,12] [1]) t) perm9.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [138,82,12] [247559,370388,220996,65728,9744,576] [17663,21398,9670,1932,144] [1794,1618,484,48] [128,79,12] [1] t ht (by decide)) perm9.symm)

theorem edge37_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 37) 2) := by
  have he := mutation_equal (pnode 37) (prelabel (pnode 27) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 37) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 27) perm0.symm

theorem edge37_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 37) 3) := by
  have he := mutation_equal (pnode 37) (prelabel (generic param3_0 param3_1 param3_2 param3_3 1) perm19.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 37) t) 3)
  rw [he]
  exact Safe.framed (region3_safe t ht 1) perm19.symm

theorem edge38_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 38) 0) := by
  have he := mutation_equal (pnode 38) (prelabel (pnode 28) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 38) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 28) perm0.symm

theorem edge38_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 38) 1) := by
  have he := mutation_equal (pnode 38) (prelabel (root [1794,1618,484,48] [229633,348830,211302,63796,9600,576] [17926,21558,9694,1932,144] [128,79,12] [10,3] [1]) perm11.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 38) 1
  rw [show mutate (node t 38) 1=(relabel (matrix (root [1794,1618,484,48] [229633,348830,211302,63796,9600,576] [17926,21558,9694,1932,144] [128,79,12] [10,3] [1]) t) perm11.symm) from he]
  exact IsRoot.relabelled (root_sound [1794,1618,484,48] [229633,348830,211302,63796,9600,576] [17926,21558,9694,1932,144] [128,79,12] [10,3] [1] t ht (by decide)) perm11.symm

theorem edge38_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 38) 2) := by
  have he := mutation_equal (pnode 38) (prelabel (pnode 37) perm14.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 38) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 37) perm14.symm

theorem edge38_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 38) 3) := by
  have he := mutation_equal (pnode 38) (prelabel (pnode 44) perm20.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 38) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 44) perm20.symm

theorem edge39_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 39) 0) := by
  have he := mutation_equal (pnode 39) (preverse (prelabel (generic param0_0 param0_1 param0_2 param0_3 2) perm5.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 39) t) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (region0_safe t ht 2) perm5.symm)

theorem edge39_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 39) 1) := by
  have he := mutation_equal (pnode 39) (preverse (prelabel (root [2846,3487,1590,320,24] [165074,310396,241802,99902,23092,2832,144] [1161161,2509866,2316582,1183558,361496,66008,6672,288] [58,38,6] [408,382,118,12] [1]) perm8.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 39) 1
  rw [show mutate (node t 39) 1=(reverse (relabel (matrix (root [2846,3487,1590,320,24] [165074,310396,241802,99902,23092,2832,144] [1161161,2509866,2316582,1183558,361496,66008,6672,288] [58,38,6] [408,382,118,12] [1]) t) perm8.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [2846,3487,1590,320,24] [165074,310396,241802,99902,23092,2832,144] [1161161,2509866,2316582,1183558,361496,66008,6672,288] [58,38,6] [408,382,118,12] [1] t ht (by decide)) perm8.symm)

theorem edge39_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 39) 2) := by
  have he := mutation_equal (pnode 39) (prelabel (fork [7,2] [6,2] [2846,3487,1590,320,24] [41,26,4] [19514,29719,17986,5408,808,48] [58,38,6]) perm16.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 2 (node_safe t 39)
  rw [show mutate (node t 39) 2=(relabel (matrix (fork [7,2] [6,2] [2846,3487,1590,320,24] [41,26,4] [19514,29719,17986,5408,808,48] [58,38,6]) t) perm16.symm) from he]
  exact IsFork.relabelled (fork_sound [7,2] [6,2] [2846,3487,1590,320,24] [41,26,4] [19514,29719,17986,5408,808,48] [58,38,6] t ht (by decide)) perm16.symm

theorem edge39_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 39) 3) := by
  have he := mutation_equal (pnode 39) (prelabel (pnode 34) perm14.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 39) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 34) perm14.symm

theorem edge40_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 40) 0) := by
  have he := mutation_equal (pnode 40) (prelabel (pnode 41) perm21.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 40) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 41) perm21.symm

theorem edge40_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 40) 1) := by
  have he := mutation_equal (pnode 40) (preverse (prelabel (root [14,2] [55,8] [26,18,2] [4] [2,1] [1]) perm8.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 40) 1
  rw [show mutate (node t 40) 1=(reverse (relabel (matrix (root [14,2] [55,8] [26,18,2] [4] [2,1] [1]) t) perm8.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [14,2] [55,8] [26,18,2] [4] [2,1] [1] t ht (by decide)) perm8.symm)

theorem edge40_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 40) 2) := by
  have he := mutation_equal (pnode 40) (prelabel (pnode 45) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 40) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 45) perm0.symm

theorem edge40_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 40) 3) := by
  have he := mutation_equal (pnode 40) (prelabel (pnode 30) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 40) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 30) perm0.symm

theorem edge41_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 41) 0) := by
  have he := mutation_equal (pnode 41) (prelabel (pnode 31) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 41) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 31) perm0.symm

theorem edge41_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 41) 1) := by
  have he := mutation_equal (pnode 41) (prelabel (root [6,1] [23,4] [58,22,2] [4] [10,2] [1]) perm7.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 41) 1
  rw [show mutate (node t 41) 1=(relabel (matrix (root [6,1] [23,4] [58,22,2] [4] [10,2] [1]) t) perm7.symm) from he]
  exact IsRoot.relabelled (root_sound [6,1] [23,4] [58,22,2] [4] [10,2] [1] t ht (by decide)) perm7.symm

theorem edge41_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 41) 2) := by
  have he := mutation_equal (pnode 41) (prelabel (pnode 46) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 41) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 46) perm0.symm

theorem edge41_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 41) 3) := by
  have he := mutation_equal (pnode 41) (prelabel (pnode 40) perm21.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 41) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 40) perm21.symm

theorem edge42_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 42) 0) := by
  have he := mutation_equal (pnode 42) (prelabel (generic param1_0 param1_1 param1_2 param1_3 2) perm3.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 42) t) 0)
  rw [he]
  exact Safe.framed (region1_safe t ht 2) perm3.symm

theorem edge42_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 42) 1) := by
  have he := mutation_equal (pnode 42) (prelabel (root [6960,10444,6224,1844,272,16] [974406,2373922,2517924,1519104,570380,136528,20352,1728,64] [6946073,18837750,22624588,15798344,7070340,2103696,416256,52832,3904,128] [140,131,40,4] [998,1209,544,108,8] [1]) perm10.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 42) 1
  rw [show mutate (node t 42) 1=(relabel (matrix (root [6960,10444,6224,1844,272,16] [974406,2373922,2517924,1519104,570380,136528,20352,1728,64] [6946073,18837750,22624588,15798344,7070340,2103696,416256,52832,3904,128] [140,131,40,4] [998,1209,544,108,8] [1]) t) perm10.symm) from he]
  exact IsRoot.relabelled (root_sound [6960,10444,6224,1844,272,16] [974406,2373922,2517924,1519104,570380,136528,20352,1728,64] [6946073,18837750,22624588,15798344,7070340,2103696,416256,52832,3904,128] [140,131,40,4] [998,1209,544,108,8] [1] t ht (by decide)) perm10.symm

theorem edge42_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 42) 2) := by
  have he := mutation_equal (pnode 42) (prelabel (pnode 33) perm15.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 42) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 33) perm15.symm

theorem edge42_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 42) 3) := by
  have he := mutation_equal (pnode 42) (preverse (prelabel (fork [7,2] [6,2] [6960,10444,6224,1844,272,16] [41,26,4] [47722,85819,63912,25248,5584,656,32] [140,131,40,4]) perm22.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 3 (node_safe t 42)
  rw [show mutate (node t 42) 3=(reverse (relabel (matrix (fork [7,2] [6,2] [6960,10444,6224,1844,272,16] [41,26,4] [47722,85819,63912,25248,5584,656,32] [140,131,40,4]) t) perm22.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [7,2] [6,2] [6960,10444,6224,1844,272,16] [41,26,4] [47722,85819,63912,25248,5584,656,32] [140,131,40,4] t ht (by decide)) perm22.symm)

theorem edge43_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 43) 0) := by
  have he := mutation_equal (pnode 43) (prelabel (pnode 36) perm20.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 43) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 36) perm20.symm

theorem edge43_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 43) 1) := by
  have he := mutation_equal (pnode 43) (preverse (prelabel (root [3274,2854,828,80] [52397,62038,27518,5420,400] [766102,1116370,650230,189236,27520,1600] [16,5] [234,137,20] [1]) perm11.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 43) 1
  rw [show mutate (node t 43) 1=(reverse (relabel (matrix (root [3274,2854,828,80] [52397,62038,27518,5420,400] [766102,1116370,650230,189236,27520,1600] [16,5] [234,137,20] [1]) t) perm11.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [3274,2854,828,80] [52397,62038,27518,5420,400] [766102,1116370,650230,189236,27520,1600] [16,5] [234,137,20] [1] t ht (by decide)) perm11.symm)

theorem edge43_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 43) 2) := by
  have he := mutation_equal (pnode 43) (preverse (prelabel (generic param2_0 param2_1 param2_2 param2_3 2) perm13.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 43) t) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (region2_safe t ht 2) perm13.symm)

theorem edge43_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 43) 3) := by
  have he := mutation_equal (pnode 43) (prelabel (fork [14,4] [13,4] [3274,2854,828,80] [181,108,16] [45602,52915,22988,4432,320] [16,5]) perm19.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 3 (node_safe t 43)
  rw [show mutate (node t 43) 3=(relabel (matrix (fork [14,4] [13,4] [3274,2854,828,80] [181,108,16] [45602,52915,22988,4432,320] [16,5]) t) perm19.symm) from he]
  exact IsFork.relabelled (fork_sound [14,4] [13,4] [3274,2854,828,80] [181,108,16] [45602,52915,22988,4432,320] [16,5] t ht (by decide)) perm19.symm

theorem edge44_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 44) 0) := by
  have he := mutation_equal (pnode 44) (prelabel (pnode 38) perm15.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 44) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 38) perm15.symm

theorem edge44_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 44) 1) := by
  have he := mutation_equal (pnode 44) (prelabel (root [25106,29825,13248,2608,192] [3213581,5800978,4353191,1738316,389584,46464,2304] [45040150,94127554,84175066,41754404,12407824,2208832,218112,9216] [128,79,12] [1794,1618,484,48] [1]) perm9.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 44) 1
  rw [show mutate (node t 44) 1=(relabel (matrix (root [25106,29825,13248,2608,192] [3213581,5800978,4353191,1738316,389584,46464,2304] [45040150,94127554,84175066,41754404,12407824,2208832,218112,9216] [128,79,12] [1794,1618,484,48] [1]) t) perm9.symm) from he]
  exact IsRoot.relabelled (root_sound [25106,29825,13248,2608,192] [3213581,5800978,4353191,1738316,389584,46464,2304] [45040150,94127554,84175066,41754404,12407824,2208832,218112,9216] [128,79,12] [1794,1618,484,48] [1] t ht (by decide)) perm9.symm

theorem edge44_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 44) 2) := by
  have he := mutation_equal (pnode 44) (preverse (prelabel (fork [14,4] [13,4] [25106,29825,13248,2608,192] [181,108,16] [349690,516356,304288,89456,13120,768] [128,79,12]) perm13.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 2 (node_safe t 44)
  rw [show mutate (node t 44) 2=(reverse (relabel (matrix (fork [14,4] [13,4] [25106,29825,13248,2608,192] [181,108,16] [349690,516356,304288,89456,13120,768] [128,79,12]) t) perm13.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [14,4] [13,4] [25106,29825,13248,2608,192] [181,108,16] [349690,516356,304288,89456,13120,768] [128,79,12] t ht (by decide)) perm13.symm)

theorem edge44_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 44) 3) := by
  have he := mutation_equal (pnode 44) (prelabel (generic param3_0 param3_1 param3_2 param3_3 2) perm19.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 44) t) 3)
  rw [he]
  exact Safe.framed (region3_safe t ht 2) perm19.symm

theorem edge45_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 45) 0) := by
  have he := mutation_equal (pnode 45) (prelabel (pnode 47) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 45) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 47) perm0.symm

theorem edge45_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 45) 1) := by
  have he := mutation_equal (pnode 45) (prelabel (root [14,2] [362,94,6] [139,48,4] [26,3] [10,2] [1]) perm9.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 45) 1
  rw [show mutate (node t 45) 1=(relabel (matrix (root [14,2] [362,94,6] [139,48,4] [26,3] [10,2] [1]) t) perm9.symm) from he]
  exact IsRoot.relabelled (root_sound [14,2] [362,94,6] [139,48,4] [26,3] [10,2] [1] t ht (by decide)) perm9.symm

theorem edge45_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 45) 2) := by
  have he := mutation_equal (pnode 45) (prelabel (pnode 40) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 45) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 40) perm0.symm

theorem edge45_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 45) 3) := by
  have he := mutation_equal (pnode 45) (preverse (prelabel (generic param4_0 param4_1 param4_2 param4_3 1) perm19.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 45) t) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (region4_safe t ht 1) perm19.symm)

theorem edge46_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 46) 0) := by
  have he := mutation_equal (pnode 46) (prelabel (fork [2] [14,3] [3] [18,4] [5] [4]) perm2.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (node_safe t 46)
  rw [show mutate (node t 46) 0=(relabel (matrix (fork [2] [14,3] [3] [18,4] [5] [4]) t) perm2.symm) from he]
  exact IsFork.relabelled (fork_sound [2] [14,3] [3] [18,4] [5] [4] t ht (by decide)) perm2.symm

theorem edge46_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 46) 1) := by
  have he := mutation_equal (pnode 46) (preverse (prelabel (fork [10,2] [14,3] [4] [138,58,6] [41,8] [3]) perm8.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (node_safe t 46)
  rw [show mutate (node t 46) 1=(reverse (relabel (matrix (fork [10,2] [14,3] [4] [138,58,6] [41,8] [3]) t) perm8.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [10,2] [14,3] [4] [138,58,6] [41,8] [3] t ht (by decide)) perm8.symm)

theorem edge46_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 46) 2) := by
  have he := mutation_equal (pnode 46) (prelabel (pnode 41) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 46) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 41) perm0.symm

theorem edge46_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 46) 3) := by
  have he := mutation_equal (pnode 46) (prelabel (pnode 47) perm15.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 46) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 47) perm15.symm

theorem edge47_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 47) 0) := by
  have he := mutation_equal (pnode 47) (prelabel (pnode 45) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 47) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 45) perm0.symm

theorem edge47_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 47) 1) := by
  have he := mutation_equal (pnode 47) (preverse (prelabel (root [26,3] [261,82,6] [101,12] [10,2] [4] [1]) perm10.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 47) 1
  rw [show mutate (node t 47) 1=(reverse (relabel (matrix (root [26,3] [261,82,6] [101,12] [10,2] [4] [1]) t) perm10.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [26,3] [261,82,6] [101,12] [10,2] [4] [1] t ht (by decide)) perm10.symm)

theorem edge47_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 47) 2) := by
  have he := mutation_equal (pnode 47) (prelabel (pnode 46) perm20.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 47) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 46) perm20.symm

theorem edge47_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 47) 3) := by
  have he := mutation_equal (pnode 47) (prelabel (pnode 48) perm21.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 47) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 48) perm21.symm

theorem edge48_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 48) 0) := by
  have he := mutation_equal (pnode 48) (prelabel (pnode 47) perm21.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 48) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 47) perm21.symm

theorem edge48_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 48) 1) := by
  have he := mutation_equal (pnode 48) (preverse (prelabel (root [74,9] [742,238,18] [1921,456,27] [10,2] [26,3] [1]) perm9.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 48) 1
  rw [show mutate (node t 48) 1=(reverse (relabel (matrix (root [74,9] [742,238,18] [1921,456,27] [10,2] [26,3] [1]) t) perm9.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [74,9] [742,238,18] [1921,456,27] [10,2] [26,3] [1] t ht (by decide)) perm9.symm)

theorem edge48_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 48) 2) := by
  have he := mutation_equal (pnode 48) (prelabel (fork [3] [2] [74,9] [5] [196,24] [10,2]) perm13.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 2 (node_safe t 48)
  rw [show mutate (node t 48) 2=(relabel (matrix (fork [3] [2] [74,9] [5] [196,24] [10,2]) t) perm13.symm) from he]
  exact IsFork.relabelled (fork_sound [3] [2] [74,9] [5] [196,24] [10,2] t ht (by decide)) perm13.symm

theorem edge48_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 48) 3) := by
  have he := mutation_equal (pnode 48) (preverse (prelabel (generic param4_0 param4_1 param4_2 param4_3 2) perm19.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 48) t) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (region4_safe t ht 2) perm19.symm)

theorem all_cyclic (t : Int) (ht : 0≤t) (i : Fin 49) : ¬ Acyclic (node t i) := by
  rcases finCore i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact cyclic0 t ht
  · exact cyclic1 t ht
  · exact cyclic2 t ht
  · exact cyclic3 t ht
  · exact cyclic4 t ht
  · exact cyclic5 t ht
  · exact cyclic6 t ht
  · exact cyclic7 t ht
  · exact cyclic8 t ht
  · exact cyclic9 t ht
  · exact cyclic10 t ht
  · exact cyclic11 t ht
  · exact cyclic12 t ht
  · exact cyclic13 t ht
  · exact cyclic14 t ht
  · exact cyclic15 t ht
  · exact cyclic16 t ht
  · exact cyclic17 t ht
  · exact cyclic18 t ht
  · exact cyclic19 t ht
  · exact cyclic20 t ht
  · exact cyclic21 t ht
  · exact cyclic22 t ht
  · exact cyclic23 t ht
  · exact cyclic24 t ht
  · exact cyclic25 t ht
  · exact cyclic26 t ht
  · exact cyclic27 t ht
  · exact cyclic28 t ht
  · exact cyclic29 t ht
  · exact cyclic30 t ht
  · exact cyclic31 t ht
  · exact cyclic32 t ht
  · exact cyclic33 t ht
  · exact cyclic34 t ht
  · exact cyclic35 t ht
  · exact cyclic36 t ht
  · exact cyclic37 t ht
  · exact cyclic38 t ht
  · exact cyclic39 t ht
  · exact cyclic40 t ht
  · exact cyclic41 t ht
  · exact cyclic42 t ht
  · exact cyclic43 t ht
  · exact cyclic44 t ht
  · exact cyclic45 t ht
  · exact cyclic46 t ht
  · exact cyclic47 t ht
  · exact cyclic48 t ht

theorem all_edges (t : Int) (ht : 0≤t) (i : Fin 49) (k : Fin 4) : SafeCore t (mutate (node t i) k) := by
  have hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
  rcases finCore i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rcases hk with rfl|rfl|rfl|rfl
  · exact edge0_0 t ht
  · exact edge0_1 t ht
  · exact edge0_2 t ht
  · exact edge0_3 t ht
  · exact edge1_0 t ht
  · exact edge1_1 t ht
  · exact edge1_2 t ht
  · exact edge1_3 t ht
  · exact edge2_0 t ht
  · exact edge2_1 t ht
  · exact edge2_2 t ht
  · exact edge2_3 t ht
  · exact edge3_0 t ht
  · exact edge3_1 t ht
  · exact edge3_2 t ht
  · exact edge3_3 t ht
  · exact edge4_0 t ht
  · exact edge4_1 t ht
  · exact edge4_2 t ht
  · exact edge4_3 t ht
  · exact edge5_0 t ht
  · exact edge5_1 t ht
  · exact edge5_2 t ht
  · exact edge5_3 t ht
  · exact edge6_0 t ht
  · exact edge6_1 t ht
  · exact edge6_2 t ht
  · exact edge6_3 t ht
  · exact edge7_0 t ht
  · exact edge7_1 t ht
  · exact edge7_2 t ht
  · exact edge7_3 t ht
  · exact edge8_0 t ht
  · exact edge8_1 t ht
  · exact edge8_2 t ht
  · exact edge8_3 t ht
  · exact edge9_0 t ht
  · exact edge9_1 t ht
  · exact edge9_2 t ht
  · exact edge9_3 t ht
  · exact edge10_0 t ht
  · exact edge10_1 t ht
  · exact edge10_2 t ht
  · exact edge10_3 t ht
  · exact edge11_0 t ht
  · exact edge11_1 t ht
  · exact edge11_2 t ht
  · exact edge11_3 t ht
  · exact edge12_0 t ht
  · exact edge12_1 t ht
  · exact edge12_2 t ht
  · exact edge12_3 t ht
  · exact edge13_0 t ht
  · exact edge13_1 t ht
  · exact edge13_2 t ht
  · exact edge13_3 t ht
  · exact edge14_0 t ht
  · exact edge14_1 t ht
  · exact edge14_2 t ht
  · exact edge14_3 t ht
  · exact edge15_0 t ht
  · exact edge15_1 t ht
  · exact edge15_2 t ht
  · exact edge15_3 t ht
  · exact edge16_0 t ht
  · exact edge16_1 t ht
  · exact edge16_2 t ht
  · exact edge16_3 t ht
  · exact edge17_0 t ht
  · exact edge17_1 t ht
  · exact edge17_2 t ht
  · exact edge17_3 t ht
  · exact edge18_0 t ht
  · exact edge18_1 t ht
  · exact edge18_2 t ht
  · exact edge18_3 t ht
  · exact edge19_0 t ht
  · exact edge19_1 t ht
  · exact edge19_2 t ht
  · exact edge19_3 t ht
  · exact edge20_0 t ht
  · exact edge20_1 t ht
  · exact edge20_2 t ht
  · exact edge20_3 t ht
  · exact edge21_0 t ht
  · exact edge21_1 t ht
  · exact edge21_2 t ht
  · exact edge21_3 t ht
  · exact edge22_0 t ht
  · exact edge22_1 t ht
  · exact edge22_2 t ht
  · exact edge22_3 t ht
  · exact edge23_0 t ht
  · exact edge23_1 t ht
  · exact edge23_2 t ht
  · exact edge23_3 t ht
  · exact edge24_0 t ht
  · exact edge24_1 t ht
  · exact edge24_2 t ht
  · exact edge24_3 t ht
  · exact edge25_0 t ht
  · exact edge25_1 t ht
  · exact edge25_2 t ht
  · exact edge25_3 t ht
  · exact edge26_0 t ht
  · exact edge26_1 t ht
  · exact edge26_2 t ht
  · exact edge26_3 t ht
  · exact edge27_0 t ht
  · exact edge27_1 t ht
  · exact edge27_2 t ht
  · exact edge27_3 t ht
  · exact edge28_0 t ht
  · exact edge28_1 t ht
  · exact edge28_2 t ht
  · exact edge28_3 t ht
  · exact edge29_0 t ht
  · exact edge29_1 t ht
  · exact edge29_2 t ht
  · exact edge29_3 t ht
  · exact edge30_0 t ht
  · exact edge30_1 t ht
  · exact edge30_2 t ht
  · exact edge30_3 t ht
  · exact edge31_0 t ht
  · exact edge31_1 t ht
  · exact edge31_2 t ht
  · exact edge31_3 t ht
  · exact edge32_0 t ht
  · exact edge32_1 t ht
  · exact edge32_2 t ht
  · exact edge32_3 t ht
  · exact edge33_0 t ht
  · exact edge33_1 t ht
  · exact edge33_2 t ht
  · exact edge33_3 t ht
  · exact edge34_0 t ht
  · exact edge34_1 t ht
  · exact edge34_2 t ht
  · exact edge34_3 t ht
  · exact edge35_0 t ht
  · exact edge35_1 t ht
  · exact edge35_2 t ht
  · exact edge35_3 t ht
  · exact edge36_0 t ht
  · exact edge36_1 t ht
  · exact edge36_2 t ht
  · exact edge36_3 t ht
  · exact edge37_0 t ht
  · exact edge37_1 t ht
  · exact edge37_2 t ht
  · exact edge37_3 t ht
  · exact edge38_0 t ht
  · exact edge38_1 t ht
  · exact edge38_2 t ht
  · exact edge38_3 t ht
  · exact edge39_0 t ht
  · exact edge39_1 t ht
  · exact edge39_2 t ht
  · exact edge39_3 t ht
  · exact edge40_0 t ht
  · exact edge40_1 t ht
  · exact edge40_2 t ht
  · exact edge40_3 t ht
  · exact edge41_0 t ht
  · exact edge41_1 t ht
  · exact edge41_2 t ht
  · exact edge41_3 t ht
  · exact edge42_0 t ht
  · exact edge42_1 t ht
  · exact edge42_2 t ht
  · exact edge42_3 t ht
  · exact edge43_0 t ht
  · exact edge43_1 t ht
  · exact edge43_2 t ht
  · exact edge43_3 t ht
  · exact edge44_0 t ht
  · exact edge44_1 t ht
  · exact edge44_2 t ht
  · exact edge44_3 t ht
  · exact edge45_0 t ht
  · exact edge45_1 t ht
  · exact edge45_2 t ht
  · exact edge45_3 t ht
  · exact edge46_0 t ht
  · exact edge46_1 t ht
  · exact edge46_2 t ht
  · exact edge46_3 t ht
  · exact edge47_0 t ht
  · exact edge47_1 t ht
  · exact edge47_2 t ht
  · exact edge47_3 t ht
  · exact edge48_0 t ht
  · exact edge48_1 t ht
  · exact edge48_2 t ht
  · exact edge48_3 t ht

theorem NMA (t : Int) (ht : 0≤t) : ¬ MutationAcyclic (node t 0) := by
  apply safe_NMA data rules (Core t)
  · rintro B ⟨i,rfl⟩; exact node_skew t i
  · rintro B ⟨i,rfl⟩; exact all_cyclic t ht i
  · rintro B ⟨i,rfl⟩ k; exact all_edges t ht i k
  · exact node_safe t 0
end HalfLine
end QuiverProofs.Rank4StructureRound2.RFamily
