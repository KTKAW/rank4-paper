import QuiverProofs.QFamilyPolynomialInterfaces
namespace QuiverProofs.Rank4StructureRound2.PFamily
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

namespace Boundary
private theorem finCore (i : Fin 87) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 ∨ i=15 ∨ i=16 ∨ i=17 ∨ i=18 ∨ i=19 ∨ i=20 ∨ i=21 ∨ i=22 ∨ i=23 ∨ i=24 ∨ i=25 ∨ i=26 ∨ i=27 ∨ i=28 ∨ i=29 ∨ i=30 ∨ i=31 ∨ i=32 ∨ i=33 ∨ i=34 ∨ i=35 ∨ i=36 ∨ i=37 ∨ i=38 ∨ i=39 ∨ i=40 ∨ i=41 ∨ i=42 ∨ i=43 ∨ i=44 ∨ i=45 ∨ i=46 ∨ i=47 ∨ i=48 ∨ i=49 ∨ i=50 ∨ i=51 ∨ i=52 ∨ i=53 ∨ i=54 ∨ i=55 ∨ i=56 ∨ i=57 ∨ i=58 ∨ i=59 ∨ i=60 ∨ i=61 ∨ i=62 ∨ i=63 ∨ i=64 ∨ i=65 ∨ i=66 ∨ i=67 ∨ i=68 ∨ i=69 ∨ i=70 ∨ i=71 ∨ i=72 ∨ i=73 ∨ i=74 ∨ i=75 ∨ i=76 ∨ i=77 ∨ i=78 ∨ i=79 ∨ i=80 ∨ i=81 ∨ i=82 ∨ i=83 ∨ i=84 ∨ i=85 ∨ i=86 := by omega

def pnode (i : Fin 87) : PMatrix := match i.val with
  | 0 => six [2] [1] [-1] [1] [-1] [4]
  | 1 => six [-2] [-1] [1] [1] [-3] [3]
  | 2 => six [2] [-1] [3] [-1] [3] [-4]
  | 3 => six [2] [-1] [-5] [-1] [3] []
  | 4 => six [-3] [1] [1] [-1] [] [-3]
  | 5 => six [1] [-1] [-1] [-8] [3] [-3]
  | 6 => six [-2] [1] [-3] [-3] [3] [-1]
  | 7 => six [-2] [-1] [9] [1] [-3] [-1]
  | 8 => six [-2] [1] [5] [-3] [-7] []
  | 9 => six [2] [1] [-5] [1] [3] []
  | 10 => six [-13] [-1] [5] [-1] [-3] []
  | 11 => six [3] [-2] [1] [1] [] [-3]
  | 12 => six [-3] [4] [-1] [-1] [] [3]
  | 13 => six [-1] [-1] [2] [8] [-3] [21]
  | 14 => six [1] [1] [-4] [8] [-21] [3]
  | 15 => six [-11] [1] [3] [] [-3] [1]
  | 16 => six [2] [1] [-9] [1] [15] [8]
  | 17 => six [25] [8] [-9] [1] [3] [1]
  | 18 => six [1] [-1] [5] [3] [-7] []
  | 19 => six [-2] [-1] [5] [1] [-7] [-5]
  | 20 => six [-13] [1] [5] [1] [-3] []
  | 21 => six [13] [1] [-5] [-1] [62] [5]
  | 22 => six [13] [-14] [-34] [1] [3] []
  | 23 => six [3] [-4] [1] [11] [] [-1]
  | 24 => six [1] [1] [-2] [8] [-1] [23]
  | 25 => six [-9] [1] [2] [-8] [165] [-21]
  | 26 => six [-1] [-1] [4] [8] [-25] [-1]
  | 27 => six [-1] [9] [-4] [-8] [21] [-165]
  | 28 => six [11] [-1] [-3] [11] [30] [1]
  | 29 => six [11] [1] [-30] [] [3] [1]
  | 30 => six [-2] [3] [21] [-1] [-15] [8]
  | 31 => six [-8] [-25] [99] [-1] [3] [-4]
  | 32 => six [-1] [2] [5] [-3] [7] [-21]
  | 33 => six [2] [-1] [-9] [-1] [7] [-12]
  | 34 => six [13] [-1] [-5] [14] [62] []
  | 35 => six [13] [1] [-34] [-1] [3] [-3]
  | 36 => six [-13] [1] [801] [1] [-62] [67]
  | 37 => six [14] [-1] [] [1] [62] [-5]
  | 38 => six [-1] [14] [-34] [-1] [3] []
  | 39 => six [-3] [29] [1] [-11] [] [-1]
  | 40 => six [-41] [4] [-3] [-11] [] [1]
  | 41 => six [1] [-1] [21] [-8] [183] [-23]
  | 42 => six [1] [-45] [2] [-15] [1] [-23]
  | 43 => six [9] [-1] [-2] [1] [183] [-21]
  | 44 => six [1] [-1] [-21] [-8] [25] [-201]
  | 45 => six [1] [-9] [4] [1] [21] [-201]
  | 46 => six [] [1] [-3] [-11] [41] [-1]
  | 47 => six [-79] [-4] [3] [11] [-30] [-1]
  | 48 => six [-11] [-1] [30] [] [-327] [-29]
  | 49 => six [-79] [-29] [30] [] [-3] [-1]
  | 50 => six [1] [-3] [45] [1] [-15] [-8]
  | 51 => six [1] [-2] [-5] [-1] [12] [-21]
  | 52 => six [-2] [1] [9] [-3] [-11] [-12]
  | 53 => six [-13] [-1] [34] [-1] [-439] [-37]
  | 54 => six [13] [-1] [-801] [14] [10351] [67]
  | 55 => six [-13] [-1] [868] [-1] [5] [-67]
  | 56 => six [-14] [13] [868] [-1] [-62] [-5]
  | 57 => six [1] [-14] [34] [13] [3] [-476]
  | 58 => six [3] [-29] [-1] [76] [3] [-1]
  | 59 => six [316] [-29] [1] [11] [-11] [1]
  | 60 => six [-1] [9] [-183] [-8] [-21] [1645]
  | 61 => six [-1] [15] [2] [45] [-3] [127]
  | 62 => six [-9] [1] [201] [-8] [-1805] [21]
  | 63 => six [-123] [1] [3] [30] [-41] [1]
  | 64 => six [-123] [4] [-1] [-11] [-30] [1]
  | 65 => six [-11] [1] [1] [] [-327] [29]
  | 66 => six [-79] [29] [1] [] [-3] [1]
  | 67 => six [1] [2] [-47] [1] [-9] [21]
  | 68 => six [1] [-1] [9] [3] [-47] [12]
  | 69 => six [13] [-14] [-5673] [1] [439] [-37]
  | 70 => six [-13] [1] [-3] [1] [-476] [37]
  | 71 => six [-1] [1] [-801] [-14] [11289] [-67]
  | 72 => six [13] [1] [-868] [-1] [11289] [801]
  | 73 => six [-2201] [29] [-30] [-76] [3] [1]
  | 74 => six [-316] [29] [-1] [-9153] [-11] [30]
  | 75 => six [30] [-1] [3] [-123] [481] [-4]
  | 76 => six [316] [1] [-1] [-9483] [327] [-29]
  | 77 => six [79] [-29] [-1] [2291] [76] [1]
  | 78 => six [-1] [2] [9] [-3] [47] [-129]
  | 79 => six [-1] [14] [-6191] [-1] [439] [37]
  | 80 => six [13] [1] [-6191] [-1] [476] [-439]
  | 81 => six [1] [-13] [-801] [14] [-11289] [157979]
  | 82 => six [-2291] [-1] [30] [-76] [-3] [-1]
  | 83 => six [-316] [-1] [1] [-9483] [11] [-30]
  | 84 => six [-9483] [-1] [30] [316] [-284479] [-29]
  | 85 => six [-68727] [-29] [30] [-76] [-2291] [-1]
  | _ => six [1] [-14] [6191] [13] [439] [-86637]

def node (t : Int) (i : Fin 87) : Matrix 4 := matrix (pnode i) t
def Core (t : Int) (B : Matrix 4) : Prop := ∃ i, B=node t i
abbrev SafeCore (t : Int) := Safe data (Core t)
theorem node_safe (t : Int) (i : Fin 87) : SafeCore t (node t i) := Safe.central ⟨i,rfl⟩

def param0_0 : P := [3]
def param0_1 : P := [25]
def param0_2 : P := [8]
def param0_3 : P := [9]
theorem domain0 (t : Int) (ht : 0≤t) : GenericStrip.Domain (eval param0_0 t) (eval param0_1 t) (eval param0_2 t) (eval param0_3 t) :=
  generic_domain param0_0 param0_1 param0_2 param0_3 t ht (by decide)

def region0 (t : Int) (ht : 0≤t) : Region := .inl (.inl ⟨eval param0_0 t,⟨eval param0_1 t,eval param0_2 t,eval param0_3 t⟩,domain0 t ht⟩)

theorem parent0_0 (t : Int) (ht : 0≤t) :
    data.parent (region0 t ht) (0 : Fin 3)=(relabel (node t 26) perm17.symm) := by
  have he := mutation_equal (generic param0_0 param0_1 param0_2 param0_3 0) (prelabel (pnode 26) perm17.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent0_1 (t : Int) (ht : 0≤t) :
    data.parent (region0 t ht) (1 : Fin 3)=(reverse (relabel (node t 7) perm18.symm)) := by
  have he := mutation_equal (generic param0_0 param0_1 param0_2 param0_3 0) (preverse (prelabel (pnode 7) perm18.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent0_2 (t : Int) (ht : 0≤t) :
    data.parent (region0 t ht) (2 : Fin 3)=(reverse (relabel (node t 31) perm18.symm)) := by
  have he := mutation_equal (generic param0_0 param0_1 param0_2 param0_3 2) (preverse (prelabel (pnode 31) perm18.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parents0_safe (t : Int) (ht : 0≤t) (p : Fin 3) :
    SafeCore t (data.parent (region0 t ht) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hp with rfl|rfl|rfl
  · rw [parent0_0 t ht]
    exact Safe.framed (node_safe t 26) perm17.symm
  · rw [parent0_1 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 7) perm18.symm)
  · rw [parent0_2 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 31) perm18.symm)

theorem region0_safe (t : Int) (ht : 0≤t) (i : Fin 3) :
    SafeCore t (matrix (generic param0_0 param0_1 param0_2 param0_3 i) t) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core t) (region0 t ht) (parents0_safe t ht) (0,Fin.castLE (by decide) i)

def param1_0 : P := [8]
def param1_1 : P := [183]
def param1_2 : P := [21]
def param1_3 : P := [23]
theorem domain1 (t : Int) (ht : 0≤t) : GenericStrip.Domain (eval param1_0 t) (eval param1_1 t) (eval param1_2 t) (eval param1_3 t) :=
  generic_domain param1_0 param1_1 param1_2 param1_3 t ht (by decide)

def region1 (t : Int) (ht : 0≤t) : Region := .inl (.inl ⟨eval param1_0 t,⟨eval param1_1 t,eval param1_2 t,eval param1_3 t⟩,domain1 t ht⟩)

theorem parent1_0 (t : Int) (ht : 0≤t) :
    data.parent (region1 t ht) (0 : Fin 3)=(relabel (node t 43) perm12.symm) := by
  have he := mutation_equal (generic param1_0 param1_1 param1_2 param1_3 0) (prelabel (pnode 43) perm12.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent1_1 (t : Int) (ht : 0≤t) :
    data.parent (region1 t ht) (1 : Fin 3)=(relabel (node t 24) perm6.symm) := by
  have he := mutation_equal (generic param1_0 param1_1 param1_2 param1_3 0) (prelabel (pnode 24) perm6.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent1_2 (t : Int) (ht : 0≤t) :
    data.parent (region1 t ht) (2 : Fin 3)=(relabel (node t 60) perm6.symm) := by
  have he := mutation_equal (generic param1_0 param1_1 param1_2 param1_3 2) (prelabel (pnode 60) perm6.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parents1_safe (t : Int) (ht : 0≤t) (p : Fin 3) :
    SafeCore t (data.parent (region1 t ht) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hp with rfl|rfl|rfl
  · rw [parent1_0 t ht]
    exact Safe.framed (node_safe t 43) perm12.symm
  · rw [parent1_1 t ht]
    exact Safe.framed (node_safe t 24) perm6.symm
  · rw [parent1_2 t ht]
    exact Safe.framed (node_safe t 60) perm6.symm

theorem region1_safe (t : Int) (ht : 0≤t) (i : Fin 3) :
    SafeCore t (matrix (generic param1_0 param1_1 param1_2 param1_3 i) t) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core t) (region1 t ht) (parents1_safe t ht) (0,Fin.castLE (by decide) i)

def param2_0 : P := [2]
def param2_1 : P := [45]
def param2_2 : P := [15]
def param2_3 : P := [23]
theorem domain2 (t : Int) (ht : 0≤t) : GenericStrip.Domain (eval param2_0 t) (eval param2_1 t) (eval param2_2 t) (eval param2_3 t) :=
  generic_domain param2_0 param2_1 param2_2 param2_3 t ht (by decide)

def region2 (t : Int) (ht : 0≤t) : Region := .inl (.inl ⟨eval param2_0 t,⟨eval param2_1 t,eval param2_2 t,eval param2_3 t⟩,domain2 t ht⟩)

theorem parent2_0 (t : Int) (ht : 0≤t) :
    data.parent (region2 t ht) (0 : Fin 3)=(relabel (node t 50) perm0.symm) := by
  have he := mutation_equal (generic param2_0 param2_1 param2_2 param2_3 0) (prelabel (pnode 50) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent2_1 (t : Int) (ht : 0≤t) :
    data.parent (region2 t ht) (1 : Fin 3)=(reverse (relabel (node t 24) perm1.symm)) := by
  have he := mutation_equal (generic param2_0 param2_1 param2_2 param2_3 0) (preverse (prelabel (pnode 24) perm1.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent2_2 (t : Int) (ht : 0≤t) :
    data.parent (region2 t ht) (2 : Fin 3)=(reverse (relabel (node t 61) perm1.symm)) := by
  have he := mutation_equal (generic param2_0 param2_1 param2_2 param2_3 2) (preverse (prelabel (pnode 61) perm1.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parents2_safe (t : Int) (ht : 0≤t) (p : Fin 3) :
    SafeCore t (data.parent (region2 t ht) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hp with rfl|rfl|rfl
  · rw [parent2_0 t ht]
    exact Safe.framed (node_safe t 50) perm0.symm
  · rw [parent2_1 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 24) perm1.symm)
  · rw [parent2_2 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 61) perm1.symm)

theorem region2_safe (t : Int) (ht : 0≤t) (i : Fin 3) :
    SafeCore t (matrix (generic param2_0 param2_1 param2_2 param2_3 i) t) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core t) (region2 t ht) (parents2_safe t ht) (0,Fin.castLE (by decide) i)

def param3_0 : P := [8]
def param3_1 : P := [201]
def param3_2 : P := [21]
def param3_3 : P := [25]
theorem domain3 (t : Int) (ht : 0≤t) : GenericStrip.Domain (eval param3_0 t) (eval param3_1 t) (eval param3_2 t) (eval param3_3 t) :=
  generic_domain param3_0 param3_1 param3_2 param3_3 t ht (by decide)

def region3 (t : Int) (ht : 0≤t) : Region := .inl (.inl ⟨eval param3_0 t,⟨eval param3_1 t,eval param3_2 t,eval param3_3 t⟩,domain3 t ht⟩)

theorem parent3_0 (t : Int) (ht : 0≤t) :
    data.parent (region3 t ht) (0 : Fin 3)=(reverse (relabel (node t 45) perm14.symm)) := by
  have he := mutation_equal (generic param3_0 param3_1 param3_2 param3_3 0) (preverse (prelabel (pnode 45) perm14.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent3_1 (t : Int) (ht : 0≤t) :
    data.parent (region3 t ht) (1 : Fin 3)=(reverse (relabel (node t 26) perm8.symm)) := by
  have he := mutation_equal (generic param3_0 param3_1 param3_2 param3_3 0) (preverse (prelabel (pnode 26) perm8.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent3_2 (t : Int) (ht : 0≤t) :
    data.parent (region3 t ht) (2 : Fin 3)=(reverse (relabel (node t 62) perm8.symm)) := by
  have he := mutation_equal (generic param3_0 param3_1 param3_2 param3_3 2) (preverse (prelabel (pnode 62) perm8.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parents3_safe (t : Int) (ht : 0≤t) (p : Fin 3) :
    SafeCore t (data.parent (region3 t ht) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hp with rfl|rfl|rfl
  · rw [parent3_0 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 45) perm14.symm)
  · rw [parent3_1 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 26) perm8.symm)
  · rw [parent3_2 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 62) perm8.symm)

theorem region3_safe (t : Int) (ht : 0≤t) (i : Fin 3) :
    SafeCore t (matrix (generic param3_0 param3_1 param3_2 param3_3 i) t) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core t) (region3 t ht) (parents3_safe t ht) (0,Fin.castLE (by decide) i)

def param4_0 : P := [3]
def param4_1 : P := [123]
def param4_2 : P := [30]
def param4_3 : P := [41]
theorem domain4 (t : Int) (ht : 0≤t) : GenericStrip.Domain (eval param4_0 t) (eval param4_1 t) (eval param4_2 t) (eval param4_3 t) :=
  generic_domain param4_0 param4_1 param4_2 param4_3 t ht (by decide)

def region4 (t : Int) (ht : 0≤t) : Region := .inl (.inl ⟨eval param4_0 t,⟨eval param4_1 t,eval param4_2 t,eval param4_3 t⟩,domain4 t ht⟩)

theorem parent4_0 (t : Int) (ht : 0≤t) :
    data.parent (region4 t ht) (0 : Fin 3)=(reverse (relabel (node t 64) perm5.symm)) := by
  have he := mutation_equal (generic param4_0 param4_1 param4_2 param4_3 0) (preverse (prelabel (pnode 64) perm5.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent4_1 (t : Int) (ht : 0≤t) :
    data.parent (region4 t ht) (1 : Fin 3)=(reverse (relabel (node t 46) perm4.symm)) := by
  have he := mutation_equal (generic param4_0 param4_1 param4_2 param4_3 0) (preverse (prelabel (pnode 46) perm4.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent4_2 (t : Int) (ht : 0≤t) :
    data.parent (region4 t ht) (2 : Fin 3)=(reverse (relabel (node t 75) perm4.symm)) := by
  have he := mutation_equal (generic param4_0 param4_1 param4_2 param4_3 2) (preverse (prelabel (pnode 75) perm4.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parents4_safe (t : Int) (ht : 0≤t) (p : Fin 3) :
    SafeCore t (data.parent (region4 t ht) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hp with rfl|rfl|rfl
  · rw [parent4_0 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 64) perm5.symm)
  · rw [parent4_1 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 46) perm4.symm)
  · rw [parent4_2 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 75) perm4.symm)

theorem region4_safe (t : Int) (ht : 0≤t) (i : Fin 3) :
    SafeCore t (matrix (generic param4_0 param4_1 param4_2 param4_3 i) t) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core t) (region4 t ht) (parents4_safe t ht) (0,Fin.castLE (by decide) i)

def param5_0 : P := [2]
def param5_1 : P := [47]
def param5_2 : P := [9]
def param5_3 : P := [21]
theorem domain5 (t : Int) (ht : 0≤t) : GenericStrip.Domain (eval param5_0 t) (eval param5_1 t) (eval param5_2 t) (eval param5_3 t) :=
  generic_domain param5_0 param5_1 param5_2 param5_3 t ht (by decide)

def region5 (t : Int) (ht : 0≤t) : Region := .inl (.inl ⟨eval param5_0 t,⟨eval param5_1 t,eval param5_2 t,eval param5_3 t⟩,domain5 t ht⟩)

theorem parent5_0 (t : Int) (ht : 0≤t) :
    data.parent (region5 t ht) (0 : Fin 3)=(reverse (relabel (node t 68) perm6.symm)) := by
  have he := mutation_equal (generic param5_0 param5_1 param5_2 param5_3 0) (preverse (prelabel (pnode 68) perm6.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent5_1 (t : Int) (ht : 0≤t) :
    data.parent (region5 t ht) (1 : Fin 3)=(reverse (relabel (node t 51) perm0.symm)) := by
  have he := mutation_equal (generic param5_0 param5_1 param5_2 param5_3 0) (preverse (prelabel (pnode 51) perm0.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent5_2 (t : Int) (ht : 0≤t) :
    data.parent (region5 t ht) (2 : Fin 3)=(reverse (relabel (node t 78) perm0.symm)) := by
  have he := mutation_equal (generic param5_0 param5_1 param5_2 param5_3 2) (preverse (prelabel (pnode 78) perm0.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parents5_safe (t : Int) (ht : 0≤t) (p : Fin 3) :
    SafeCore t (data.parent (region5 t ht) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hp with rfl|rfl|rfl
  · rw [parent5_0 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 68) perm6.symm)
  · rw [parent5_1 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 51) perm0.symm)
  · rw [parent5_2 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 78) perm0.symm)

theorem region5_safe (t : Int) (ht : 0≤t) (i : Fin 3) :
    SafeCore t (matrix (generic param5_0 param5_1 param5_2 param5_3 i) t) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core t) (region5 t ht) (parents5_safe t ht) (0,Fin.castLE (by decide) i)

def param6_0 : P := [13]
def param6_1 : P := [11289]
def param6_2 : P := [801]
def param6_3 : P := [868]
theorem domain6 (t : Int) (ht : 0≤t) : GenericStrip.Domain (eval param6_0 t) (eval param6_1 t) (eval param6_2 t) (eval param6_3 t) :=
  generic_domain param6_0 param6_1 param6_2 param6_3 t ht (by decide)

def region6 (t : Int) (ht : 0≤t) : Region := .inl (.inl ⟨eval param6_0 t,⟨eval param6_1 t,eval param6_2 t,eval param6_3 t⟩,domain6 t ht⟩)

theorem parent6_0 (t : Int) (ht : 0≤t) :
    data.parent (region6 t ht) (0 : Fin 3)=(relabel (node t 71) perm6.symm) := by
  have he := mutation_equal (generic param6_0 param6_1 param6_2 param6_3 0) (prelabel (pnode 71) perm6.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent6_1 (t : Int) (ht : 0≤t) :
    data.parent (region6 t ht) (1 : Fin 3)=(relabel (node t 55) perm12.symm) := by
  have he := mutation_equal (generic param6_0 param6_1 param6_2 param6_3 0) (prelabel (pnode 55) perm12.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent6_2 (t : Int) (ht : 0≤t) :
    data.parent (region6 t ht) (2 : Fin 3)=(relabel (node t 81) perm0.symm) := by
  have he := mutation_equal (generic param6_0 param6_1 param6_2 param6_3 2) (prelabel (pnode 81) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parents6_safe (t : Int) (ht : 0≤t) (p : Fin 3) :
    SafeCore t (data.parent (region6 t ht) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hp with rfl|rfl|rfl
  · rw [parent6_0 t ht]
    exact Safe.framed (node_safe t 71) perm6.symm
  · rw [parent6_1 t ht]
    exact Safe.framed (node_safe t 55) perm12.symm
  · rw [parent6_2 t ht]
    exact Safe.framed (node_safe t 81) perm0.symm

theorem region6_safe (t : Int) (ht : 0≤t) (i : Fin 3) :
    SafeCore t (matrix (generic param6_0 param6_1 param6_2 param6_3 i) t) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core t) (region6 t ht) (parents6_safe t ht) (0,Fin.castLE (by decide) i)

def param7_0 : P := [29]
def param7_1 : P := [9483]
def param7_2 : P := [316]
def param7_3 : P := [327]
theorem domain7 (t : Int) (ht : 0≤t) : GenericStrip.Domain (eval param7_0 t) (eval param7_1 t) (eval param7_2 t) (eval param7_3 t) :=
  generic_domain param7_0 param7_1 param7_2 param7_3 t ht (by decide)

def region7 (t : Int) (ht : 0≤t) : Region := .inl (.inl ⟨eval param7_0 t,⟨eval param7_1 t,eval param7_2 t,eval param7_3 t⟩,domain7 t ht⟩)

theorem parent7_0 (t : Int) (ht : 0≤t) :
    data.parent (region7 t ht) (0 : Fin 3)=(relabel (node t 83) perm10.symm) := by
  have he := mutation_equal (generic param7_0 param7_1 param7_2 param7_3 0) (prelabel (pnode 83) perm10.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent7_1 (t : Int) (ht : 0≤t) :
    data.parent (region7 t ht) (1 : Fin 3)=(relabel (node t 65) perm10.symm) := by
  have he := mutation_equal (generic param7_0 param7_1 param7_2 param7_3 0) (prelabel (pnode 65) perm10.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent7_2 (t : Int) (ht : 0≤t) :
    data.parent (region7 t ht) (2 : Fin 3)=(relabel (node t 84) perm10.symm) := by
  have he := mutation_equal (generic param7_0 param7_1 param7_2 param7_3 2) (prelabel (pnode 84) perm10.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parents7_safe (t : Int) (ht : 0≤t) (p : Fin 3) :
    SafeCore t (data.parent (region7 t ht) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hp with rfl|rfl|rfl
  · rw [parent7_0 t ht]
    exact Safe.framed (node_safe t 83) perm10.symm
  · rw [parent7_1 t ht]
    exact Safe.framed (node_safe t 65) perm10.symm
  · rw [parent7_2 t ht]
    exact Safe.framed (node_safe t 84) perm10.symm

theorem region7_safe (t : Int) (ht : 0≤t) (i : Fin 3) :
    SafeCore t (matrix (generic param7_0 param7_1 param7_2 param7_3 i) t) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core t) (region7 t ht) (parents7_safe t ht) (0,Fin.castLE (by decide) i)

def param8_0 : P := [29]
def param8_1 : P := [2291]
def param8_2 : P := [76]
def param8_3 : P := [79]
theorem domain8 (t : Int) (ht : 0≤t) : GenericStrip.Domain (eval param8_0 t) (eval param8_1 t) (eval param8_2 t) (eval param8_3 t) :=
  generic_domain param8_0 param8_1 param8_2 param8_3 t ht (by decide)

def region8 (t : Int) (ht : 0≤t) : Region := .inl (.inl ⟨eval param8_0 t,⟨eval param8_1 t,eval param8_2 t,eval param8_3 t⟩,domain8 t ht⟩)

theorem parent8_0 (t : Int) (ht : 0≤t) :
    data.parent (region8 t ht) (0 : Fin 3)=(reverse (relabel (node t 82) perm4.symm)) := by
  have he := mutation_equal (generic param8_0 param8_1 param8_2 param8_3 0) (preverse (prelabel (pnode 82) perm4.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent8_1 (t : Int) (ht : 0≤t) :
    data.parent (region8 t ht) (1 : Fin 3)=(reverse (relabel (node t 66) perm16.symm)) := by
  have he := mutation_equal (generic param8_0 param8_1 param8_2 param8_3 0) (preverse (prelabel (pnode 66) perm16.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent8_2 (t : Int) (ht : 0≤t) :
    data.parent (region8 t ht) (2 : Fin 3)=(reverse (relabel (node t 85) perm16.symm)) := by
  have he := mutation_equal (generic param8_0 param8_1 param8_2 param8_3 2) (preverse (prelabel (pnode 85) perm16.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parents8_safe (t : Int) (ht : 0≤t) (p : Fin 3) :
    SafeCore t (data.parent (region8 t ht) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hp with rfl|rfl|rfl
  · rw [parent8_0 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 82) perm4.symm)
  · rw [parent8_1 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 66) perm16.symm)
  · rw [parent8_2 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 85) perm16.symm)

theorem region8_safe (t : Int) (ht : 0≤t) (i : Fin 3) :
    SafeCore t (matrix (generic param8_0 param8_1 param8_2 param8_3 i) t) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core t) (region8 t ht) (parents8_safe t ht) (0,Fin.castLE (by decide) i)

def param9_0 : P := [13]
def param9_1 : P := [6191]
def param9_2 : P := [439]
def param9_3 : P := [476]
theorem domain9 (t : Int) (ht : 0≤t) : GenericStrip.Domain (eval param9_0 t) (eval param9_1 t) (eval param9_2 t) (eval param9_3 t) :=
  generic_domain param9_0 param9_1 param9_2 param9_3 t ht (by decide)

def region9 (t : Int) (ht : 0≤t) : Region := .inl (.inl ⟨eval param9_0 t,⟨eval param9_1 t,eval param9_2 t,eval param9_3 t⟩,domain9 t ht⟩)

theorem parent9_0 (t : Int) (ht : 0≤t) :
    data.parent (region9 t ht) (0 : Fin 3)=(reverse (relabel (node t 79) perm0.symm)) := by
  have he := mutation_equal (generic param9_0 param9_1 param9_2 param9_3 0) (preverse (prelabel (pnode 79) perm0.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent9_1 (t : Int) (ht : 0≤t) :
    data.parent (region9 t ht) (1 : Fin 3)=(reverse (relabel (node t 70) perm2.symm)) := by
  have he := mutation_equal (generic param9_0 param9_1 param9_2 param9_3 0) (preverse (prelabel (pnode 70) perm2.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent9_2 (t : Int) (ht : 0≤t) :
    data.parent (region9 t ht) (2 : Fin 3)=(reverse (relabel (node t 86) perm6.symm)) := by
  have he := mutation_equal (generic param9_0 param9_1 param9_2 param9_3 2) (preverse (prelabel (pnode 86) perm6.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parents9_safe (t : Int) (ht : 0≤t) (p : Fin 3) :
    SafeCore t (data.parent (region9 t ht) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hp with rfl|rfl|rfl
  · rw [parent9_0 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 79) perm0.symm)
  · rw [parent9_1 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 70) perm2.symm)
  · rw [parent9_2 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 86) perm6.symm)

theorem region9_safe (t : Int) (ht : 0≤t) (i : Fin 3) :
    SafeCore t (matrix (generic param9_0 param9_1 param9_2 param9_3 i) t) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core t) (region9 t ht) (parents9_safe t ht) (0,Fin.castLE (by decide) i)

def param10_0 : P := [5]
def param10_1 : P := [3]
def param10_2 : P := [7]
def param10_3 : P := [33]
theorem domain10 (t : Int) (ht : 0≤t) : UnitZeroStrip.Domain (eval param10_0 t) (eval param10_1 t) (eval param10_2 t) (eval param10_3 t) :=
  zero_domain param10_0 param10_1 param10_2 param10_3 t ht (by decide)

def region10 (t : Int) (ht : 0≤t) : Region := .inl (.inr (.n (eval param10_0 t) ⟨eval param10_1 t,eval param10_2 t,eval param10_3 t⟩ (domain10 t ht)))

theorem parent10_0 (t : Int) (ht : 0≤t) :
    data.parent (region10 t ht) (0 : Fin 2)=(reverse (relabel (node t 8) perm22.symm)) := by
  have he := mutation_equal (zero param10_0 param10_1 param10_2 param10_3 0) (preverse (prelabel (pnode 8) perm22.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,zero_eval] at he
  exact he

theorem parent10_1 (t : Int) (ht : 0≤t) :
    data.parent (region10 t ht) (1 : Fin 2)=(reverse (relabel (node t 18) perm22.symm)) := by
  have he := mutation_equal (zero param10_0 param10_1 param10_2 param10_3 1) (preverse (prelabel (pnode 18) perm22.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,zero_eval] at he
  exact he

theorem parents10_safe (t : Int) (ht : 0≤t) (p : Fin 2) :
    SafeCore t (data.parent (region10 t ht) p) := by
  have hp : p=0 ∨ p=1 := by change p=(0 : Fin 2) ∨ p=(1 : Fin 2); omega
  rcases hp with rfl|rfl
  · rw [parent10_0 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 8) perm22.symm)
  · rw [parent10_1 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 18) perm22.symm)

theorem region10_safe (t : Int) (ht : 0≤t) (i : Fin 2) :
    SafeCore t (matrix (zero param10_0 param10_1 param10_2 param10_3 i) t) := by
  rw [zero_eval]
  exact Safe.region (D:=data) (core:=Core t) (region10 t ht) (parents10_safe t ht) (0,Fin.castLE (by decide) i)

def param11_0 : P := [3]
def param11_1 : P := [14]
def param11_2 : P := [34]
def param11_3 : P := [89]
theorem domain11 (t : Int) (ht : 0≤t) : UnitZeroStrip.Domain (eval param11_0 t) (eval param11_1 t) (eval param11_2 t) (eval param11_3 t) :=
  zero_domain param11_0 param11_1 param11_2 param11_3 t ht (by decide)

def region11 (t : Int) (ht : 0≤t) : Region := .inl (.inr (.n (eval param11_0 t) ⟨eval param11_1 t,eval param11_2 t,eval param11_3 t⟩ (domain11 t ht)))

theorem parent11_0 (t : Int) (ht : 0≤t) :
    data.parent (region11 t ht) (0 : Fin 2)=(reverse (relabel (node t 22) perm16.symm)) := by
  have he := mutation_equal (zero param11_0 param11_1 param11_2 param11_3 0) (preverse (prelabel (pnode 22) perm16.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,zero_eval] at he
  exact he

theorem parent11_1 (t : Int) (ht : 0≤t) :
    data.parent (region11 t ht) (1 : Fin 2)=(reverse (relabel (node t 38) perm16.symm)) := by
  have he := mutation_equal (zero param11_0 param11_1 param11_2 param11_3 1) (preverse (prelabel (pnode 38) perm16.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,zero_eval] at he
  exact he

theorem parents11_safe (t : Int) (ht : 0≤t) (p : Fin 2) :
    SafeCore t (data.parent (region11 t ht) p) := by
  have hp : p=0 ∨ p=1 := by change p=(0 : Fin 2) ∨ p=(1 : Fin 2); omega
  rcases hp with rfl|rfl
  · rw [parent11_0 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 22) perm16.symm)
  · rw [parent11_1 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 38) perm16.symm)

theorem region11_safe (t : Int) (ht : 0≤t) (i : Fin 2) :
    SafeCore t (matrix (zero param11_0 param11_1 param11_2 param11_3 i) t) := by
  rw [zero_eval]
  exact Safe.region (D:=data) (core:=Core t) (region11 t ht) (parents11_safe t ht) (0,Fin.castLE (by decide) i)

def param12_0 : P := [5]
def param12_1 : P := [14]
def param12_2 : P := [62]
def param12_3 : P := [297]
theorem domain12 (t : Int) (ht : 0≤t) : UnitZeroStrip.Domain (eval param12_0 t) (eval param12_1 t) (eval param12_2 t) (eval param12_3 t) :=
  zero_domain param12_0 param12_1 param12_2 param12_3 t ht (by decide)

def region12 (t : Int) (ht : 0≤t) : Region := .inl (.inr (.n (eval param12_0 t) ⟨eval param12_1 t,eval param12_2 t,eval param12_3 t⟩ (domain12 t ht)))

theorem parent12_0 (t : Int) (ht : 0≤t) :
    data.parent (region12 t ht) (0 : Fin 2)=(relabel (node t 34) perm22.symm) := by
  have he := mutation_equal (zero param12_0 param12_1 param12_2 param12_3 0) (prelabel (pnode 34) perm22.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,zero_eval] at he
  exact he

theorem parent12_1 (t : Int) (ht : 0≤t) :
    data.parent (region12 t ht) (1 : Fin 2)=(relabel (node t 37) perm3.symm) := by
  have he := mutation_equal (zero param12_0 param12_1 param12_2 param12_3 1) (prelabel (pnode 37) perm3.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,zero_eval] at he
  exact he

theorem parents12_safe (t : Int) (ht : 0≤t) (p : Fin 2) :
    SafeCore t (data.parent (region12 t ht) p) := by
  have hp : p=0 ∨ p=1 := by change p=(0 : Fin 2) ∨ p=(1 : Fin 2); omega
  rcases hp with rfl|rfl
  · rw [parent12_0 t ht]
    exact Safe.framed (node_safe t 34) perm22.symm
  · rw [parent12_1 t ht]
    exact Safe.framed (node_safe t 37) perm3.symm

theorem region12_safe (t : Int) (ht : 0≤t) (i : Fin 2) :
    SafeCore t (matrix (zero param12_0 param12_1 param12_2 param12_3 i) t) := by
  rw [zero_eval]
  exact Safe.region (D:=data) (core:=Core t) (region12 t ht) (parents12_safe t ht) (0,Fin.castLE (by decide) i)

def param13_0 : P := [11]
def param13_1 : P := [3]
def param13_2 : P := [41]
def param13_3 : P := [447]
theorem domain13 (t : Int) (ht : 0≤t) : UnitZeroStrip.Domain (eval param13_0 t) (eval param13_1 t) (eval param13_2 t) (eval param13_3 t) :=
  zero_domain param13_0 param13_1 param13_2 param13_3 t ht (by decide)

def region13 (t : Int) (ht : 0≤t) : Region := .inl (.inr (.n (eval param13_0 t) ⟨eval param13_1 t,eval param13_2 t,eval param13_3 t⟩ (domain13 t ht)))

theorem parent13_0 (t : Int) (ht : 0≤t) :
    data.parent (region13 t ht) (0 : Fin 2)=(reverse (relabel (node t 40) perm15.symm)) := by
  have he := mutation_equal (zero param13_0 param13_1 param13_2 param13_3 0) (preverse (prelabel (pnode 40) perm15.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,zero_eval] at he
  exact he

theorem parent13_1 (t : Int) (ht : 0≤t) :
    data.parent (region13 t ht) (1 : Fin 2)=(reverse (relabel (node t 46) perm1.symm)) := by
  have he := mutation_equal (zero param13_0 param13_1 param13_2 param13_3 1) (preverse (prelabel (pnode 46) perm1.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,zero_eval] at he
  exact he

theorem parents13_safe (t : Int) (ht : 0≤t) (p : Fin 2) :
    SafeCore t (data.parent (region13 t ht) p) := by
  have hp : p=0 ∨ p=1 := by change p=(0 : Fin 2) ∨ p=(1 : Fin 2); omega
  rcases hp with rfl|rfl
  · rw [parent13_0 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 40) perm15.symm)
  · rw [parent13_1 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 46) perm1.symm)

theorem region13_safe (t : Int) (ht : 0≤t) (i : Fin 2) :
    SafeCore t (matrix (zero param13_0 param13_1 param13_2 param13_3 i) t) := by
  rw [zero_eval]
  exact Safe.region (D:=data) (core:=Core t) (region13 t ht) (parents13_safe t ht) (0,Fin.castLE (by decide) i)

def param14_0 : P := [11]
def param14_1 : P := [29]
def param14_2 : P := [327]
def param14_3 : P := [3567]
theorem domain14 (t : Int) (ht : 0≤t) : UnitZeroStrip.Domain (eval param14_0 t) (eval param14_1 t) (eval param14_2 t) (eval param14_3 t) :=
  zero_domain param14_0 param14_1 param14_2 param14_3 t ht (by decide)

def region14 (t : Int) (ht : 0≤t) : Region := .inl (.inr (.n (eval param14_0 t) ⟨eval param14_1 t,eval param14_2 t,eval param14_3 t⟩ (domain14 t ht)))

theorem parent14_0 (t : Int) (ht : 0≤t) :
    data.parent (region14 t ht) (0 : Fin 2)=(relabel (node t 48) perm20.symm) := by
  have he := mutation_equal (zero param14_0 param14_1 param14_2 param14_3 0) (prelabel (pnode 48) perm20.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,zero_eval] at he
  exact he

theorem parent14_1 (t : Int) (ht : 0≤t) :
    data.parent (region14 t ht) (1 : Fin 2)=(relabel (node t 65) perm20.symm) := by
  have he := mutation_equal (zero param14_0 param14_1 param14_2 param14_3 1) (prelabel (pnode 65) perm20.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,zero_eval] at he
  exact he

theorem parents14_safe (t : Int) (ht : 0≤t) (p : Fin 2) :
    SafeCore t (data.parent (region14 t ht) p) := by
  have hp : p=0 ∨ p=1 := by change p=(0 : Fin 2) ∨ p=(1 : Fin 2); omega
  rcases hp with rfl|rfl
  · rw [parent14_0 t ht]
    exact Safe.framed (node_safe t 48) perm20.symm
  · rw [parent14_1 t ht]
    exact Safe.framed (node_safe t 65) perm20.symm

theorem region14_safe (t : Int) (ht : 0≤t) (i : Fin 2) :
    SafeCore t (matrix (zero param14_0 param14_1 param14_2 param14_3 i) t) := by
  rw [zero_eval]
  exact Safe.region (D:=data) (core:=Core t) (region14 t ht) (parents14_safe t ht) (0,Fin.castLE (by decide) i)

def param15_0 : P := [3]
def param15_1 : P := [29]
def param15_2 : P := [79]
def param15_3 : P := [207]
theorem domain15 (t : Int) (ht : 0≤t) : UnitZeroStrip.Domain (eval param15_0 t) (eval param15_1 t) (eval param15_2 t) (eval param15_3 t) :=
  zero_domain param15_0 param15_1 param15_2 param15_3 t ht (by decide)

def region15 (t : Int) (ht : 0≤t) : Region := .inl (.inr (.n (eval param15_0 t) ⟨eval param15_1 t,eval param15_2 t,eval param15_3 t⟩ (domain15 t ht)))

theorem parent15_0 (t : Int) (ht : 0≤t) :
    data.parent (region15 t ht) (0 : Fin 2)=(reverse (relabel (node t 49) perm14.symm)) := by
  have he := mutation_equal (zero param15_0 param15_1 param15_2 param15_3 0) (preverse (prelabel (pnode 49) perm14.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,zero_eval] at he
  exact he

theorem parent15_1 (t : Int) (ht : 0≤t) :
    data.parent (region15 t ht) (1 : Fin 2)=(reverse (relabel (node t 66) perm14.symm)) := by
  have he := mutation_equal (zero param15_0 param15_1 param15_2 param15_3 1) (preverse (prelabel (pnode 66) perm14.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,zero_eval] at he
  exact he

theorem parents15_safe (t : Int) (ht : 0≤t) (p : Fin 2) :
    SafeCore t (data.parent (region15 t ht) p) := by
  have hp : p=0 ∨ p=1 := by change p=(0 : Fin 2) ∨ p=(1 : Fin 2); omega
  rcases hp with rfl|rfl
  · rw [parent15_0 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 49) perm14.symm)
  · rw [parent15_1 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 66) perm14.symm)

theorem region15_safe (t : Int) (ht : 0≤t) (i : Fin 2) :
    SafeCore t (matrix (zero param15_0 param15_1 param15_2 param15_3 i) t) := by
  rw [zero_eval]
  exact Safe.region (D:=data) (core:=Core t) (region15 t ht) (parents15_safe t ht) (0,Fin.castLE (by decide) i)

theorem node_skew (t : Int) (i : Fin 87) : SkewSymmetric (node t i) := by
  rcases finCore i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp only [node,pnode,matrix_six] <;> exact ofSix_skew _ _ _ _ _ _

theorem cyclic0 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 0) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 0 0 2) t ht (by decide))
  have h1 := hr 2 3 (pos (pnode 0 2 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 0 3 0) t ht (by decide))
  omega

theorem cyclic1 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 1) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 1 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (pnode 1 3 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 1 1 0) t ht (by decide))
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
  have h0 := hr 0 2 (pos (pnode 4 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 4 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 4 1 0) t ht (by decide))
  omega

theorem cyclic5 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 5) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 5 0 1) t ht (by decide))
  have h1 := hr 1 3 (pos (pnode 5 1 3) t ht (by decide))
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
  have h0 := hr 0 3 (pos (pnode 10 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (pnode 10 3 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 10 1 0) t ht (by decide))
  omega

theorem cyclic11 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 11) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 11 0 1) t ht (by decide))
  have h1 := hr 1 2 (pos (pnode 11 1 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 11 2 0) t ht (by decide))
  omega

theorem cyclic12 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 12) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 12 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 12 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 12 1 0) t ht (by decide))
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
  have h1 := hr 2 3 (pos (pnode 14 2 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 14 3 0) t ht (by decide))
  omega

theorem cyclic15 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 15) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 15 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (pnode 15 3 1) t ht (by decide))
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
  have h0 := hr 0 1 (pos (pnode 17 0 1) t ht (by decide))
  have h1 := hr 1 3 (pos (pnode 17 1 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 17 3 0) t ht (by decide))
  omega

theorem cyclic18 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 18) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 18 0 1) t ht (by decide))
  have h1 := hr 1 2 (pos (pnode 18 1 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 18 2 0) t ht (by decide))
  omega

theorem cyclic19 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 19) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 19 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (pnode 19 3 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 19 1 0) t ht (by decide))
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
  have h1 := hr 1 3 (pos (pnode 21 1 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 21 3 0) t ht (by decide))
  omega

theorem cyclic22 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 22) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 22 0 1) t ht (by decide))
  have h1 := hr 1 2 (pos (pnode 22 1 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 22 2 0) t ht (by decide))
  omega

theorem cyclic23 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 23) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 23 0 1) t ht (by decide))
  have h1 := hr 1 2 (pos (pnode 23 1 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 23 2 0) t ht (by decide))
  omega

theorem cyclic24 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 24) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 24 0 2) t ht (by decide))
  have h1 := hr 2 3 (pos (pnode 24 2 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 24 3 0) t ht (by decide))
  omega

theorem cyclic25 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 25) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 25 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 25 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 25 1 0) t ht (by decide))
  omega

theorem cyclic26 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 26) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 26 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (pnode 26 3 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 26 1 0) t ht (by decide))
  omega

theorem cyclic27 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 27) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 27 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 27 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 27 1 0) t ht (by decide))
  omega

theorem cyclic28 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 28) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 28 0 1) t ht (by decide))
  have h1 := hr 1 2 (pos (pnode 28 1 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 28 2 0) t ht (by decide))
  omega

theorem cyclic29 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 29) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 29 0 1) t ht (by decide))
  have h1 := hr 1 3 (pos (pnode 29 1 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 29 3 0) t ht (by decide))
  omega

theorem cyclic30 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 30) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 30 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 30 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 30 1 0) t ht (by decide))
  omega

theorem cyclic31 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 31) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 31 0 3) t ht (by decide))
  have h1 := hr 3 2 (pos (pnode 31 3 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 31 2 0) t ht (by decide))
  omega

theorem cyclic32 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 32) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 32 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 32 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 32 1 0) t ht (by decide))
  omega

theorem cyclic33 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 33) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 33 0 1) t ht (by decide))
  have h1 := hr 1 3 (pos (pnode 33 1 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 33 3 0) t ht (by decide))
  omega

theorem cyclic34 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 34) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 34 0 1) t ht (by decide))
  have h1 := hr 1 2 (pos (pnode 34 1 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 34 2 0) t ht (by decide))
  omega

theorem cyclic35 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 35) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 35 0 1) t ht (by decide))
  have h1 := hr 1 3 (pos (pnode 35 1 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 35 3 0) t ht (by decide))
  omega

theorem cyclic36 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 36) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 36 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (pnode 36 3 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 36 1 0) t ht (by decide))
  omega

theorem cyclic37 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 37) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 37 0 1) t ht (by decide))
  have h1 := hr 1 2 (pos (pnode 37 1 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 37 2 0) t ht (by decide))
  omega

theorem cyclic38 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 38) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 38 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 38 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 38 1 0) t ht (by decide))
  omega

theorem cyclic39 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 39) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 39 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 39 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 39 1 0) t ht (by decide))
  omega

theorem cyclic40 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 40) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 40 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 40 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 40 1 0) t ht (by decide))
  omega

theorem cyclic41 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 41) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 41 0 3) t ht (by decide))
  have h1 := hr 3 2 (pos (pnode 41 3 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 41 2 0) t ht (by decide))
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
  have h1 := hr 1 2 (pos (pnode 45 1 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 45 2 0) t ht (by decide))
  omega

theorem cyclic46 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 46) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 1 3 (pos (pnode 46 1 3) t ht (by decide))
  have h1 := hr 3 2 (pos (pnode 46 3 2) t ht (by decide))
  have h2 := hr 2 1 (pos (pnode 46 2 1) t ht (by decide))
  omega

theorem cyclic47 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 47) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 47 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (pnode 47 3 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 47 1 0) t ht (by decide))
  omega

theorem cyclic48 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 48) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 48 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (pnode 48 3 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 48 1 0) t ht (by decide))
  omega

theorem cyclic49 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 49) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 49 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (pnode 49 3 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 49 1 0) t ht (by decide))
  omega

theorem cyclic50 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 50) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 50 0 1) t ht (by decide))
  have h1 := hr 1 2 (pos (pnode 50 1 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 50 2 0) t ht (by decide))
  omega

theorem cyclic51 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 51) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 51 0 1) t ht (by decide))
  have h1 := hr 1 3 (pos (pnode 51 1 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 51 3 0) t ht (by decide))
  omega

theorem cyclic52 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 52) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 52 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 52 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 52 1 0) t ht (by decide))
  omega

theorem cyclic53 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 53) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 53 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (pnode 53 3 1) t ht (by decide))
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
  have h0 := hr 0 3 (pos (pnode 55 0 3) t ht (by decide))
  have h1 := hr 3 2 (pos (pnode 55 3 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 55 2 0) t ht (by decide))
  omega

theorem cyclic56 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 56) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 56 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 56 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 56 1 0) t ht (by decide))
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
  have h1 := hr 1 2 (pos (pnode 59 1 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 59 2 0) t ht (by decide))
  omega

theorem cyclic60 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 60) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 60 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 60 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 60 1 0) t ht (by decide))
  omega

theorem cyclic61 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 61) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 61 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (pnode 61 3 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 61 1 0) t ht (by decide))
  omega

theorem cyclic62 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 62) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 62 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 62 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 62 1 0) t ht (by decide))
  omega

theorem cyclic63 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 63) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 63 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (pnode 63 3 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 63 1 0) t ht (by decide))
  omega

theorem cyclic64 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 64) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 64 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 64 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 64 1 0) t ht (by decide))
  omega

theorem cyclic65 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 65) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 65 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (pnode 65 3 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 65 1 0) t ht (by decide))
  omega

theorem cyclic66 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 66) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 66 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (pnode 66 3 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 66 1 0) t ht (by decide))
  omega

theorem cyclic67 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 67) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 67 0 2) t ht (by decide))
  have h1 := hr 2 3 (pos (pnode 67 2 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 67 3 0) t ht (by decide))
  omega

theorem cyclic68 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 68) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 68 0 1) t ht (by decide))
  have h1 := hr 1 2 (pos (pnode 68 1 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 68 2 0) t ht (by decide))
  omega

theorem cyclic69 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 69) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 69 0 1) t ht (by decide))
  have h1 := hr 1 2 (pos (pnode 69 1 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 69 2 0) t ht (by decide))
  omega

theorem cyclic70 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 70) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 70 0 2) t ht (by decide))
  have h1 := hr 2 3 (pos (pnode 70 2 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 70 3 0) t ht (by decide))
  omega

theorem cyclic71 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 71) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 71 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 71 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 71 1 0) t ht (by decide))
  omega

theorem cyclic72 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 72) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 72 0 1) t ht (by decide))
  have h1 := hr 1 3 (pos (pnode 72 1 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 72 3 0) t ht (by decide))
  omega

theorem cyclic73 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 73) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 73 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 73 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 73 1 0) t ht (by decide))
  omega

theorem cyclic74 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 74) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 74 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 74 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 74 1 0) t ht (by decide))
  omega

theorem cyclic75 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 75) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 75 0 3) t ht (by decide))
  have h1 := hr 3 2 (pos (pnode 75 3 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 75 2 0) t ht (by decide))
  omega

theorem cyclic76 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 76) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 76 0 1) t ht (by decide))
  have h1 := hr 1 3 (pos (pnode 76 1 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 76 3 0) t ht (by decide))
  omega

theorem cyclic77 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 77) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 77 0 1) t ht (by decide))
  have h1 := hr 1 2 (pos (pnode 77 1 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 77 2 0) t ht (by decide))
  omega

theorem cyclic78 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 78) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 78 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 78 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 78 1 0) t ht (by decide))
  omega

theorem cyclic79 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 79) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 79 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 79 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 79 1 0) t ht (by decide))
  omega

theorem cyclic80 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 80) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 80 0 1) t ht (by decide))
  have h1 := hr 1 3 (pos (pnode 80 1 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 80 3 0) t ht (by decide))
  omega

theorem cyclic81 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 81) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 81 0 1) t ht (by decide))
  have h1 := hr 1 2 (pos (pnode 81 1 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 81 2 0) t ht (by decide))
  omega

theorem cyclic82 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 82) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 82 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (pnode 82 3 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 82 1 0) t ht (by decide))
  omega

theorem cyclic83 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 83) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 83 0 3) t ht (by decide))
  have h1 := hr 3 2 (pos (pnode 83 3 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 83 2 0) t ht (by decide))
  omega

theorem cyclic84 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 84) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 84 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (pnode 84 3 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 84 1 0) t ht (by decide))
  omega

theorem cyclic85 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 85) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 85 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (pnode 85 3 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 85 1 0) t ht (by decide))
  omega

theorem cyclic86 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 86) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 86 0 1) t ht (by decide))
  have h1 := hr 1 2 (pos (pnode 86 1 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 86 2 0) t ht (by decide))
  omega

theorem edge0_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 0) 0) := by
  have he := mutation_equal (pnode 0) (prelabel (pnode 1) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 0) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 1) perm0.symm

theorem edge0_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 0) 1) := by
  have he := mutation_equal (pnode 0) (preverse (prelabel (pnode 1) perm7.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 0) t) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (node_safe t 1) perm7.symm)

theorem edge0_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 0) 2) := by
  have he := mutation_equal (pnode 0) (prelabel (pnode 2) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 0) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 2) perm0.symm

theorem edge0_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 0) 3) := by
  have he := mutation_equal (pnode 0) (preverse (prelabel (pnode 2) perm7.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 0) t) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (node_safe t 2) perm7.symm)

theorem edge1_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 1) 0) := by
  have he := mutation_equal (pnode 1) (prelabel (pnode 0) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 1) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 0) perm0.symm

theorem edge1_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 1) 1) := by
  have he := mutation_equal (pnode 1) (prelabel (pnode 3) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 1) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 3) perm0.symm

theorem edge1_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 1) 2) := by
  have he := mutation_equal (pnode 1) (prelabel (pnode 4) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 1) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 4) perm0.symm

theorem edge1_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 1) 3) := by
  have he := mutation_equal (pnode 1) (prelabel (pnode 5) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 1) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 5) perm0.symm

theorem edge2_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 2) 0) := by
  have he := mutation_equal (pnode 2) (prelabel (pnode 6) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 2) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 6) perm0.symm

theorem edge2_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 2) 1) := by
  have he := mutation_equal (pnode 2) (prelabel (pnode 7) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 2) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 7) perm0.symm

theorem edge2_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 2) 2) := by
  have he := mutation_equal (pnode 2) (prelabel (pnode 0) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 2) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 0) perm0.symm

theorem edge2_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 2) 3) := by
  have he := mutation_equal (pnode 2) (prelabel (fork [4] [3] [3] [11] [11] [2]) perm22.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 3 (node_safe t 2)
  rw [show mutate (node t 2) 3=(relabel (matrix (fork [4] [3] [3] [11] [11] [2]) t) perm22.symm) from he]
  exact IsFork.relabelled (fork_sound [4] [3] [3] [11] [11] [2] t ht (by decide)) perm22.symm

theorem edge3_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 3) 0) := by
  have he := mutation_equal (pnode 3) (prelabel (pnode 8) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 3) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 8) perm0.symm

theorem edge3_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 3) 1) := by
  have he := mutation_equal (pnode 3) (prelabel (pnode 1) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 3) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 1) perm0.symm

theorem edge3_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 3) 2) := by
  have he := mutation_equal (pnode 3) (prelabel (pnode 9) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 3) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 9) perm0.symm

theorem edge3_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 3) 3) := by
  have he := mutation_equal (pnode 3) (prelabel (pnode 10) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 3) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 10) perm0.symm

theorem edge4_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 4) 0) := by
  have he := mutation_equal (pnode 4) (prelabel (pnode 6) perm14.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 4) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 6) perm14.symm

theorem edge4_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 4) 1) := by
  have he := mutation_equal (pnode 4) (prelabel (pnode 11) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 4) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 11) perm0.symm

theorem edge4_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 4) 2) := by
  have he := mutation_equal (pnode 4) (prelabel (pnode 1) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 4) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 1) perm0.symm

theorem edge4_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 4) 3) := by
  have he := mutation_equal (pnode 4) (prelabel (pnode 12) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 4) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 12) perm0.symm

theorem edge5_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 5) 0) := by
  have he := mutation_equal (pnode 5) (preverse (prelabel (pnode 7) perm10.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 5) t) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (node_safe t 7) perm10.symm)

theorem edge5_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 5) 1) := by
  have he := mutation_equal (pnode 5) (prelabel (pnode 13) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 5) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 13) perm0.symm

theorem edge5_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 5) 2) := by
  have he := mutation_equal (pnode 5) (prelabel (pnode 14) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 5) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 14) perm0.symm

theorem edge5_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 5) 3) := by
  have he := mutation_equal (pnode 5) (prelabel (pnode 1) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 5) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 1) perm0.symm

theorem edge6_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 6) 0) := by
  have he := mutation_equal (pnode 6) (prelabel (pnode 2) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 6) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 2) perm0.symm

theorem edge6_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 6) 1) := by
  have he := mutation_equal (pnode 6) (preverse (prelabel (fork [3] [2] [3] [5] [8] [3]) perm8.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (node_safe t 6)
  rw [show mutate (node t 6) 1=(reverse (relabel (matrix (fork [3] [2] [3] [5] [8] [3]) t) perm8.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [3] [2] [3] [5] [8] [3] t ht (by decide)) perm8.symm)

theorem edge6_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 6) 2) := by
  have he := mutation_equal (pnode 6) (prelabel (pnode 4) perm14.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 6) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 4) perm14.symm

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
  have he := mutation_equal (pnode 7) (prelabel (pnode 2) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 7) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 2) perm0.symm

theorem edge7_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 7) 2) := by
  have he := mutation_equal (pnode 7) (preverse (prelabel (pnode 5) perm13.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 7) t) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (node_safe t 5) perm13.symm)

theorem edge7_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 7) 3) := by
  have he := mutation_equal (pnode 7) (prelabel (pnode 17) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 7) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 17) perm0.symm

theorem edge8_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 8) 0) := by
  have he := mutation_equal (pnode 8) (prelabel (pnode 3) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 8) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 3) perm0.symm

theorem edge8_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 8) 1) := by
  have he := mutation_equal (pnode 8) (preverse (prelabel (root [2] [5] [9] [3] [7] []) perm6.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 8) 1
  rw [show mutate (node t 8) 1=(reverse (relabel (matrix (root [2] [5] [9] [3] [7] []) t) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [2] [5] [9] [3] [7] [] t ht (by decide)) perm6.symm)

theorem edge8_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 8) 2) := by
  have he := mutation_equal (pnode 8) (prelabel (pnode 18) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 8) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 18) perm0.symm

theorem edge8_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 8) 3) := by
  have he := mutation_equal (pnode 8) (preverse (prelabel (zero param10_0 param10_1 param10_2 param10_3 0) perm17.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 8) t) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (region10_safe t ht 0) perm17.symm)

theorem edge9_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 9) 0) := by
  have he := mutation_equal (pnode 9) (prelabel (pnode 19) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 9) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 19) perm0.symm

theorem edge9_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 9) 1) := by
  have he := mutation_equal (pnode 9) (prelabel (pnode 11) perm2.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 9) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 11) perm2.symm

theorem edge9_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 9) 2) := by
  have he := mutation_equal (pnode 9) (prelabel (pnode 3) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 9) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 3) perm0.symm

theorem edge9_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 9) 3) := by
  have he := mutation_equal (pnode 9) (prelabel (pnode 20) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 9) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 20) perm0.symm

theorem edge10_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 10) 0) := by
  have he := mutation_equal (pnode 10) (prelabel (pnode 21) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 10) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 21) perm0.symm

theorem edge10_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 10) 1) := by
  have he := mutation_equal (pnode 10) (prelabel (pnode 22) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 10) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 22) perm0.symm

theorem edge10_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 10) 2) := by
  have he := mutation_equal (pnode 10) (prelabel (pnode 20) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 10) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 20) perm0.symm

theorem edge10_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 10) 3) := by
  have he := mutation_equal (pnode 10) (prelabel (pnode 3) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 10) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 3) perm0.symm

theorem edge11_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 11) 0) := by
  have he := mutation_equal (pnode 11) (preverse (prelabel (pnode 9) perm13.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 11) t) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (node_safe t 9) perm13.symm)

theorem edge11_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 11) 1) := by
  have he := mutation_equal (pnode 11) (prelabel (pnode 4) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 11) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 4) perm0.symm

theorem edge11_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 11) 2) := by
  have he := mutation_equal (pnode 11) (prelabel (pnode 9) perm2.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 11) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 9) perm2.symm

theorem edge11_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 11) 3) := by
  have he := mutation_equal (pnode 11) (preverse (prelabel (pnode 4) perm16.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 11) t) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (node_safe t 4) perm16.symm)

theorem edge12_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 12) 0) := by
  have he := mutation_equal (pnode 12) (prelabel (pnode 23) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 12) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 23) perm0.symm

theorem edge12_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 12) 1) := by
  have he := mutation_equal (pnode 12) (preverse (prelabel (pnode 4) perm16.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 12) t) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (node_safe t 4) perm16.symm)

theorem edge12_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 12) 2) := by
  have he := mutation_equal (pnode 12) (preverse (prelabel (pnode 23) perm16.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 12) t) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (node_safe t 23) perm16.symm)

theorem edge12_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 12) 3) := by
  have he := mutation_equal (pnode 12) (prelabel (pnode 4) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 12) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 4) perm0.symm

theorem edge13_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 13) 0) := by
  have he := mutation_equal (pnode 13) (prelabel (pnode 24) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 13) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 24) perm0.symm

theorem edge13_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 13) 1) := by
  have he := mutation_equal (pnode 13) (prelabel (pnode 5) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 13) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 5) perm0.symm

theorem edge13_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 13) 2) := by
  have he := mutation_equal (pnode 13) (prelabel (pnode 25) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 13) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 25) perm0.symm

theorem edge13_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 13) 3) := by
  have he := mutation_equal (pnode 13) (preverse (prelabel (root [3] [5] [55] [2] [21] [1]) perm20.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 13) 3
  rw [show mutate (node t 13) 3=(reverse (relabel (matrix (root [3] [5] [55] [2] [21] [1]) t) perm20.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [3] [5] [55] [2] [21] [1] t ht (by decide)) perm20.symm)

theorem edge14_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 14) 0) := by
  have he := mutation_equal (pnode 14) (prelabel (pnode 26) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 14) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 26) perm0.symm

theorem edge14_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 14) 1) := by
  have he := mutation_equal (pnode 14) (prelabel (pnode 27) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 14) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 27) perm0.symm

theorem edge14_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 14) 2) := by
  have he := mutation_equal (pnode 14) (prelabel (pnode 5) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 14) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 5) perm0.symm

theorem edge14_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 14) 3) := by
  have he := mutation_equal (pnode 14) (prelabel (root [3] [11] [55] [4] [21] [1]) perm22.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 14) 3
  rw [show mutate (node t 14) 3=(relabel (matrix (root [3] [11] [55] [4] [21] [1]) t) perm22.symm) from he]
  exact IsRoot.relabelled (root_sound [3] [11] [55] [4] [21] [1] t ht (by decide)) perm22.symm

theorem edge15_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 15) 0) := by
  have he := mutation_equal (pnode 15) (prelabel (pnode 28) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 15) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 28) perm0.symm

theorem edge15_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 15) 1) := by
  have he := mutation_equal (pnode 15) (prelabel (pnode 29) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 15) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 29) perm0.symm

theorem edge15_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 15) 2) := by
  have he := mutation_equal (pnode 15) (prelabel (pnode 23) perm20.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 15) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 23) perm20.symm

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
  have he := mutation_equal (pnode 16) (prelabel (pnode 30) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 16) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 30) perm0.symm

theorem edge16_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 16) 2) := by
  have he := mutation_equal (pnode 16) (preverse (prelabel (pnode 24) perm3.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 16) t) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (node_safe t 24) perm3.symm)

theorem edge16_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 16) 3) := by
  have he := mutation_equal (pnode 16) (preverse (prelabel (root [9] [71] [133] [8] [15] [1]) perm19.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 16) 3
  rw [show mutate (node t 16) 3=(reverse (relabel (matrix (root [9] [71] [133] [8] [15] [1]) t) perm19.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [9] [71] [133] [8] [15] [1] t ht (by decide)) perm19.symm)

theorem edge17_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 17) 0) := by
  have he := mutation_equal (pnode 17) (prelabel (root [9] [222] [71] [25] [8] [1]) perm4.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 17) 0
  rw [show mutate (node t 17) 0=(relabel (matrix (root [9] [222] [71] [25] [8] [1]) t) perm4.symm) from he]
  exact IsRoot.relabelled (root_sound [9] [222] [71] [25] [8] [1] t ht (by decide)) perm4.symm

theorem edge17_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 17) 1) := by
  have he := mutation_equal (pnode 17) (preverse (prelabel (generic param0_0 param0_1 param0_2 param0_3 1) perm9.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 17) t) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (region0_safe t ht 1) perm9.symm)

theorem edge17_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 17) 2) := by
  have he := mutation_equal (pnode 17) (preverse (prelabel (pnode 26) perm19.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 17) t) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (node_safe t 26) perm19.symm)

theorem edge17_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 17) 3) := by
  have he := mutation_equal (pnode 17) (prelabel (pnode 7) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 17) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 7) perm0.symm

theorem edge18_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 18) 0) := by
  have he := mutation_equal (pnode 18) (prelabel (pnode 19) perm14.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 18) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 19) perm14.symm

theorem edge18_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 18) 1) := by
  have he := mutation_equal (pnode 18) (prelabel (pnode 32) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 18) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 32) perm0.symm

theorem edge18_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 18) 2) := by
  have he := mutation_equal (pnode 18) (prelabel (pnode 8) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 18) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 8) perm0.symm

theorem edge18_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 18) 3) := by
  have he := mutation_equal (pnode 18) (preverse (prelabel (zero param10_0 param10_1 param10_2 param10_3 1) perm17.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 18) t) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (region10_safe t ht 1) perm17.symm)

theorem edge19_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 19) 0) := by
  have he := mutation_equal (pnode 19) (prelabel (pnode 9) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 19) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 9) perm0.symm

theorem edge19_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 19) 1) := by
  have he := mutation_equal (pnode 19) (prelabel (pnode 33) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 19) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 33) perm0.symm

theorem edge19_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 19) 2) := by
  have he := mutation_equal (pnode 19) (prelabel (pnode 18) perm14.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 19) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 18) perm14.symm

theorem edge19_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 19) 3) := by
  have he := mutation_equal (pnode 19) (prelabel (root [5] [33] [24] [7] [5] [1]) perm18.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 19) 3
  rw [show mutate (node t 19) 3=(relabel (matrix (root [5] [33] [24] [7] [5] [1]) t) perm18.symm) from he]
  exact IsRoot.relabelled (root_sound [5] [33] [24] [7] [5] [1] t ht (by decide)) perm18.symm

theorem edge20_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 20) 0) := by
  have he := mutation_equal (pnode 20) (prelabel (pnode 34) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 20) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 34) perm0.symm

theorem edge20_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 20) 1) := by
  have he := mutation_equal (pnode 20) (prelabel (pnode 35) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 20) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 35) perm0.symm

theorem edge20_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 20) 2) := by
  have he := mutation_equal (pnode 20) (prelabel (pnode 10) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 20) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 10) perm0.symm

theorem edge20_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 20) 3) := by
  have he := mutation_equal (pnode 20) (prelabel (pnode 9) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 20) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 9) perm0.symm

theorem edge21_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 21) 0) := by
  have he := mutation_equal (pnode 21) (prelabel (pnode 10) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 21) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 10) perm0.symm

theorem edge21_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 21) 1) := by
  have he := mutation_equal (pnode 21) (prelabel (pnode 36) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 21) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 36) perm0.symm

theorem edge21_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 21) 2) := by
  have he := mutation_equal (pnode 21) (prelabel (pnode 37) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 21) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 37) perm0.symm

theorem edge21_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 21) 3) := by
  have he := mutation_equal (pnode 21) (preverse (prelabel (root [5] [297] [24] [62] [5] [1]) perm18.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 21) 3
  rw [show mutate (node t 21) 3=(reverse (relabel (matrix (root [5] [297] [24] [62] [5] [1]) t) perm18.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [5] [297] [24] [62] [5] [1] t ht (by decide)) perm18.symm)

theorem edge22_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 22) 0) := by
  have he := mutation_equal (pnode 22) (preverse (prelabel (root [13] [181] [439] [14] [34] []) perm0.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 22) 0
  rw [show mutate (node t 22) 0=(reverse (relabel (matrix (root [13] [181] [439] [14] [34] []) t) perm0.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [13] [181] [439] [14] [34] [] t ht (by decide)) perm0.symm)

theorem edge22_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 22) 1) := by
  have he := mutation_equal (pnode 22) (prelabel (pnode 10) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 22) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 10) perm0.symm

theorem edge22_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 22) 2) := by
  have he := mutation_equal (pnode 22) (prelabel (pnode 38) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 22) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 38) perm0.symm

theorem edge22_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 22) 3) := by
  have he := mutation_equal (pnode 22) (preverse (prelabel (zero param11_0 param11_1 param11_2 param11_3 0) perm16.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 22) t) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (region11_safe t ht 0) perm16.symm)

theorem edge23_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 23) 0) := by
  have he := mutation_equal (pnode 23) (prelabel (pnode 12) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 23) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 12) perm0.symm

theorem edge23_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 23) 1) := by
  have he := mutation_equal (pnode 23) (prelabel (pnode 39) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 23) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 39) perm0.symm

theorem edge23_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 23) 2) := by
  have he := mutation_equal (pnode 23) (prelabel (pnode 40) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 23) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 40) perm0.symm

theorem edge23_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 23) 3) := by
  have he := mutation_equal (pnode 23) (prelabel (pnode 15) perm15.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 23) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 15) perm15.symm

theorem edge24_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 24) 0) := by
  have he := mutation_equal (pnode 24) (prelabel (pnode 13) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 24) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 13) perm0.symm

theorem edge24_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 24) 1) := by
  have he := mutation_equal (pnode 24) (preverse (prelabel (pnode 16) perm4.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 24) t) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (node_safe t 16) perm4.symm)

theorem edge24_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 24) 2) := by
  have he := mutation_equal (pnode 24) (prelabel (pnode 41) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 24) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 41) perm0.symm

theorem edge24_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 24) 3) := by
  have he := mutation_equal (pnode 24) (prelabel (pnode 42) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 24) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 42) perm0.symm

theorem edge25_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 25) 0) := by
  have he := mutation_equal (pnode 25) (prelabel (pnode 43) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 25) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 43) perm0.symm

theorem edge25_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 25) 1) := by
  have he := mutation_equal (pnode 25) (preverse (prelabel (fork [8] [165] [9] [1299] [71] [2]) perm9.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (node_safe t 25)
  rw [show mutate (node t 25) 1=(reverse (relabel (matrix (fork [8] [165] [9] [1299] [71] [2]) t) perm9.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [8] [165] [9] [1299] [71] [2] t ht (by decide)) perm9.symm)

theorem edge25_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 25) 2) := by
  have he := mutation_equal (pnode 25) (prelabel (pnode 13) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 25) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 13) perm0.symm

theorem edge25_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 25) 3) := by
  have he := mutation_equal (pnode 25) (prelabel (fork [21] [165] [2] [3457] [43] [9]) perm23.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 3 (node_safe t 25)
  rw [show mutate (node t 25) 3=(relabel (matrix (fork [21] [165] [2] [3457] [43] [9]) t) perm23.symm) from he]
  exact IsFork.relabelled (fork_sound [21] [165] [2] [3457] [43] [9] t ht (by decide)) perm23.symm

theorem edge26_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 26) 0) := by
  have he := mutation_equal (pnode 26) (prelabel (pnode 14) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 26) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 14) perm0.symm

theorem edge26_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 26) 1) := by
  have he := mutation_equal (pnode 26) (prelabel (pnode 44) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 26) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 44) perm0.symm

theorem edge26_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 26) 2) := by
  have he := mutation_equal (pnode 26) (preverse (prelabel (pnode 17) perm11.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 26) t) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (node_safe t 17) perm11.symm)

theorem edge26_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 26) 3) := by
  have he := mutation_equal (pnode 26) (preverse (prelabel (pnode 31) perm9.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 26) t) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (node_safe t 31) perm9.symm)

theorem edge27_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 27) 0) := by
  have he := mutation_equal (pnode 27) (prelabel (pnode 45) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 27) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 45) perm0.symm

theorem edge27_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 27) 1) := by
  have he := mutation_equal (pnode 27) (prelabel (pnode 14) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 27) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 14) perm0.symm

theorem edge27_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 27) 2) := by
  have he := mutation_equal (pnode 27) (prelabel (fork [8] [165] [9] [1299] [71] [4]) perm15.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 2 (node_safe t 27)
  rw [show mutate (node t 27) 2=(relabel (matrix (fork [8] [165] [9] [1299] [71] [4]) t) perm15.symm) from he]
  exact IsFork.relabelled (fork_sound [8] [165] [9] [1299] [71] [4] t ht (by decide)) perm15.symm

theorem edge27_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 27) 3) := by
  have he := mutation_equal (pnode 27) (preverse (prelabel (fork [21] [165] [4] [3457] [85] [9]) perm21.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 3 (node_safe t 27)
  rw [show mutate (node t 27) 3=(reverse (relabel (matrix (fork [21] [165] [4] [3457] [85] [9]) t) perm21.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [21] [165] [4] [3457] [85] [9] t ht (by decide)) perm21.symm)

theorem edge28_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 28) 0) := by
  have he := mutation_equal (pnode 28) (prelabel (pnode 15) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 28) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 15) perm0.symm

theorem edge28_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 28) 1) := by
  have he := mutation_equal (pnode 28) (prelabel (root [11] [120] [327] [11] [30] [1]) perm6.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 28) 1
  rw [show mutate (node t 28) 1=(relabel (matrix (root [11] [120] [327] [11] [30] [1]) t) perm6.symm) from he]
  exact IsRoot.relabelled (root_sound [11] [120] [327] [11] [30] [1] t ht (by decide)) perm6.symm

theorem edge28_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 28) 2) := by
  have he := mutation_equal (pnode 28) (prelabel (pnode 46) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 28) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 46) perm0.symm

theorem edge28_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 28) 3) := by
  have he := mutation_equal (pnode 28) (prelabel (pnode 47) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 28) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 47) perm0.symm

theorem edge29_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 29) 0) := by
  have he := mutation_equal (pnode 29) (prelabel (pnode 48) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 29) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 48) perm0.symm

theorem edge29_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 29) 1) := by
  have he := mutation_equal (pnode 29) (prelabel (pnode 15) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 29) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 15) perm0.symm

theorem edge29_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 29) 2) := by
  have he := mutation_equal (pnode 29) (prelabel (pnode 39) perm20.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 29) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 39) perm20.symm

theorem edge29_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 29) 3) := by
  have he := mutation_equal (pnode 29) (prelabel (pnode 49) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 29) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 49) perm0.symm

theorem edge30_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 30) 0) := by
  have he := mutation_equal (pnode 30) (preverse (prelabel (fork [2] [21] [3] [27] [5] [8]) perm1.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (node_safe t 30)
  rw [show mutate (node t 30) 0=(reverse (relabel (matrix (fork [2] [21] [3] [27] [5] [8]) t) perm1.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [2] [21] [3] [27] [5] [8] t ht (by decide)) perm1.symm)

theorem edge30_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 30) 1) := by
  have he := mutation_equal (pnode 30) (prelabel (pnode 16) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 30) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 16) perm0.symm

theorem edge30_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 30) 2) := by
  have he := mutation_equal (pnode 30) (prelabel (pnode 50) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 30) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 50) perm0.symm

theorem edge30_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 30) 3) := by
  have he := mutation_equal (pnode 30) (prelabel (fork [15] [21] [8] [313] [121] [3]) perm20.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 3 (node_safe t 30)
  rw [show mutate (node t 30) 3=(relabel (matrix (fork [15] [21] [8] [313] [121] [3]) t) perm20.symm) from he]
  exact IsFork.relabelled (fork_sound [15] [21] [8] [313] [121] [3] t ht (by decide)) perm20.symm

theorem edge31_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 31) 0) := by
  have he := mutation_equal (pnode 31) (preverse (prelabel (root [99] [795] [2471] [8] [25] [1]) perm4.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 31) 0
  rw [show mutate (node t 31) 0=(reverse (relabel (matrix (root [99] [795] [2471] [8] [25] [1]) t) perm4.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [99] [795] [2471] [8] [25] [1] t ht (by decide)) perm4.symm)

theorem edge31_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 31) 1) := by
  have he := mutation_equal (pnode 31) (preverse (prelabel (generic param0_0 param0_1 param0_2 param0_3 2) perm9.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 31) t) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (region0_safe t ht 2) perm9.symm)

theorem edge31_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 31) 2) := by
  have he := mutation_equal (pnode 31) (preverse (prelabel (pnode 26) perm18.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 31) t) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (node_safe t 26) perm18.symm)

theorem edge31_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 31) 3) := by
  have he := mutation_equal (pnode 31) (prelabel (fork [4] [3] [99] [11] [371] [8]) perm23.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 3 (node_safe t 31)
  rw [show mutate (node t 31) 3=(relabel (matrix (fork [4] [3] [99] [11] [371] [8]) t) perm23.symm) from he]
  exact IsFork.relabelled (fork_sound [4] [3] [99] [11] [371] [8] t ht (by decide)) perm23.symm

theorem edge32_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 32) 0) := by
  have he := mutation_equal (pnode 32) (prelabel (pnode 51) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 32) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 51) perm0.symm

theorem edge32_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 32) 1) := by
  have he := mutation_equal (pnode 32) (prelabel (pnode 18) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 32) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 18) perm0.symm

theorem edge32_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 32) 2) := by
  have he := mutation_equal (pnode 32) (prelabel (fork [3] [2] [21] [5] [56] [5]) perm14.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 2 (node_safe t 32)
  rw [show mutate (node t 32) 2=(relabel (matrix (fork [3] [2] [21] [5] [56] [5]) t) perm14.symm) from he]
  exact IsFork.relabelled (fork_sound [3] [2] [21] [5] [56] [5] t ht (by decide)) perm14.symm

theorem edge32_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 32) 3) := by
  have he := mutation_equal (pnode 32) (preverse (prelabel (root [21] [107] [144] [5] [7] [1]) perm22.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 32) 3
  rw [show mutate (node t 32) 3=(reverse (relabel (matrix (root [21] [107] [144] [5] [7] [1]) t) perm22.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [21] [107] [144] [5] [7] [1] t ht (by decide)) perm22.symm)

theorem edge33_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 33) 0) := by
  have he := mutation_equal (pnode 33) (prelabel (pnode 52) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 33) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 52) perm0.symm

theorem edge33_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 33) 1) := by
  have he := mutation_equal (pnode 33) (prelabel (pnode 19) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 33) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 19) perm0.symm

theorem edge33_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 33) 2) := by
  have he := mutation_equal (pnode 33) (prelabel (pnode 51) perm8.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 33) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 51) perm8.symm

theorem edge33_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 33) 3) := by
  have he := mutation_equal (pnode 33) (prelabel (root [7] [83] [61] [12] [9] [1]) perm21.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 33) 3
  rw [show mutate (node t 33) 3=(relabel (matrix (root [7] [83] [61] [12] [9] [1]) t) perm21.symm) from he]
  exact IsRoot.relabelled (root_sound [7] [83] [61] [12] [9] [1] t ht (by decide)) perm21.symm

theorem edge34_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 34) 0) := by
  have he := mutation_equal (pnode 34) (prelabel (pnode 20) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 34) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 20) perm0.symm

theorem edge34_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 34) 1) := by
  have he := mutation_equal (pnode 34) (prelabel (root [13] [181] [801] [14] [62] []) perm6.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 34) 1
  rw [show mutate (node t 34) 1=(relabel (matrix (root [13] [181] [801] [14] [62] []) t) perm6.symm) from he]
  exact IsRoot.relabelled (root_sound [13] [181] [801] [14] [62] [] t ht (by decide)) perm6.symm

theorem edge34_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 34) 2) := by
  have he := mutation_equal (pnode 34) (prelabel (pnode 37) perm14.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 34) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 37) perm14.symm

theorem edge34_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 34) 3) := by
  have he := mutation_equal (pnode 34) (prelabel (zero param12_0 param12_1 param12_2 param12_3 0) perm17.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 34) t) 3)
  rw [he]
  exact Safe.framed (region12_safe t ht 0) perm17.symm

theorem edge35_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 35) 0) := by
  have he := mutation_equal (pnode 35) (prelabel (pnode 53) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 35) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 53) perm0.symm

theorem edge35_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 35) 1) := by
  have he := mutation_equal (pnode 35) (prelabel (pnode 20) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 35) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 20) perm0.symm

theorem edge35_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 35) 2) := by
  have he := mutation_equal (pnode 35) (prelabel (pnode 38) perm2.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 35) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 38) perm2.symm

theorem edge35_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 35) 3) := by
  have he := mutation_equal (pnode 35) (prelabel (root [3] [89] [8] [34] [3] [1]) perm20.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 35) 3
  rw [show mutate (node t 35) 3=(relabel (matrix (root [3] [89] [8] [34] [3] [1]) t) perm20.symm) from he]
  exact IsRoot.relabelled (root_sound [3] [89] [8] [34] [3] [1] t ht (by decide)) perm20.symm

theorem edge36_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 36) 0) := by
  have he := mutation_equal (pnode 36) (prelabel (pnode 54) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 36) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 54) perm0.symm

theorem edge36_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 36) 1) := by
  have he := mutation_equal (pnode 36) (prelabel (pnode 21) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 36) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 21) perm0.symm

theorem edge36_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 36) 2) := by
  have he := mutation_equal (pnode 36) (prelabel (pnode 55) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 36) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 55) perm0.symm

theorem edge36_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 36) 3) := by
  have he := mutation_equal (pnode 36) (preverse (prelabel (root [62] [4153] [49649] [67] [801] [1]) perm21.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 36) 3
  rw [show mutate (node t 36) 3=(reverse (relabel (matrix (root [62] [4153] [49649] [67] [801] [1]) t) perm21.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [62] [4153] [49649] [67] [801] [1] t ht (by decide)) perm21.symm)

theorem edge37_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 37) 0) := by
  have he := mutation_equal (pnode 37) (prelabel (pnode 34) perm14.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 37) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 34) perm14.symm

theorem edge37_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 37) 1) := by
  have he := mutation_equal (pnode 37) (prelabel (pnode 56) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 37) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 56) perm0.symm

theorem edge37_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 37) 2) := by
  have he := mutation_equal (pnode 37) (prelabel (pnode 21) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 37) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 21) perm0.symm

theorem edge37_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 37) 3) := by
  have he := mutation_equal (pnode 37) (prelabel (zero param12_0 param12_1 param12_2 param12_3 1) perm4.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 37) t) 3)
  rw [he]
  exact Safe.framed (region12_safe t ht 1) perm4.symm

theorem edge38_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 38) 0) := by
  have he := mutation_equal (pnode 38) (prelabel (pnode 57) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 38) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 57) perm0.symm

theorem edge38_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 38) 1) := by
  have he := mutation_equal (pnode 38) (prelabel (pnode 35) perm2.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 38) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 35) perm2.symm

theorem edge38_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 38) 2) := by
  have he := mutation_equal (pnode 38) (prelabel (pnode 22) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 38) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 22) perm0.symm

theorem edge38_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 38) 3) := by
  have he := mutation_equal (pnode 38) (preverse (prelabel (zero param11_0 param11_1 param11_2 param11_3 1) perm16.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 38) t) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (region11_safe t ht 1) perm16.symm)

theorem edge39_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 39) 0) := by
  have he := mutation_equal (pnode 39) (prelabel (pnode 58) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 39) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 58) perm0.symm

theorem edge39_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 39) 1) := by
  have he := mutation_equal (pnode 39) (prelabel (pnode 23) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 39) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 23) perm0.symm

theorem edge39_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 39) 2) := by
  have he := mutation_equal (pnode 39) (prelabel (pnode 59) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 39) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 59) perm0.symm

theorem edge39_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 39) 3) := by
  have he := mutation_equal (pnode 39) (prelabel (pnode 29) perm15.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 39) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 29) perm15.symm

theorem edge40_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 40) 0) := by
  have he := mutation_equal (pnode 40) (preverse (prelabel (root [4] [153] [11] [41] [3] []) perm2.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 40) 0
  rw [show mutate (node t 40) 0=(reverse (relabel (matrix (root [4] [153] [11] [41] [3] []) t) perm2.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [4] [153] [11] [41] [3] [] t ht (by decide)) perm2.symm)

theorem edge40_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 40) 1) := by
  have he := mutation_equal (pnode 40) (preverse (prelabel (zero param13_0 param13_1 param13_2 param13_3 0) perm20.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 40) t) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (region13_safe t ht 0) perm20.symm)

theorem edge40_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 40) 2) := by
  have he := mutation_equal (pnode 40) (prelabel (pnode 23) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 40) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 23) perm0.symm

theorem edge40_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 40) 3) := by
  have he := mutation_equal (pnode 40) (prelabel (pnode 46) perm21.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 40) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 46) perm21.symm

theorem edge41_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 41) 0) := by
  have he := mutation_equal (pnode 41) (prelabel (pnode 43) perm14.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 41) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 43) perm14.symm

theorem edge41_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 41) 1) := by
  have he := mutation_equal (pnode 41) (prelabel (generic param1_0 param1_1 param1_2 param1_3 1) perm6.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 41) t) 1)
  rw [he]
  exact Safe.framed (region1_safe t ht 1) perm6.symm

theorem edge41_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 41) 2) := by
  have he := mutation_equal (pnode 41) (prelabel (pnode 24) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 41) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 24) perm0.symm

theorem edge41_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 41) 3) := by
  have he := mutation_equal (pnode 41) (preverse (prelabel (root [23] [4201] [482] [183] [21] [1]) perm23.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 41) 3
  rw [show mutate (node t 41) 3=(reverse (relabel (matrix (root [23] [4201] [482] [183] [21] [1]) t) perm23.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [23] [4201] [482] [183] [21] [1] t ht (by decide)) perm23.symm)

theorem edge42_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 42) 0) := by
  have he := mutation_equal (pnode 42) (preverse (prelabel (generic param2_0 param2_1 param2_2 param2_3 1) perm1.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 42) t) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (region2_safe t ht 1) perm1.symm)

theorem edge42_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 42) 1) := by
  have he := mutation_equal (pnode 42) (preverse (prelabel (pnode 50) perm1.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 42) t) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (node_safe t 50) perm1.symm)

theorem edge42_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 42) 2) := by
  have he := mutation_equal (pnode 42) (prelabel (root [23] [1033] [344] [45] [15] [1]) perm16.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 42) 2
  rw [show mutate (node t 42) 2=(relabel (matrix (root [23] [1033] [344] [45] [15] [1]) t) perm16.symm) from he]
  exact IsRoot.relabelled (root_sound [23] [1033] [344] [45] [15] [1] t ht (by decide)) perm16.symm

theorem edge42_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 42) 3) := by
  have he := mutation_equal (pnode 42) (prelabel (pnode 24) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 42) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 24) perm0.symm

theorem edge43_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 43) 0) := by
  have he := mutation_equal (pnode 43) (prelabel (pnode 25) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 43) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 25) perm0.symm

theorem edge43_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 43) 1) := by
  have he := mutation_equal (pnode 43) (prelabel (pnode 60) perm8.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 43) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 60) perm8.symm

theorem edge43_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 43) 2) := by
  have he := mutation_equal (pnode 43) (prelabel (pnode 41) perm14.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 43) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 41) perm14.symm

theorem edge43_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 43) 3) := by
  have he := mutation_equal (pnode 43) (prelabel (root [183] [3844] [357] [21] [2] [1]) perm21.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 43) 3
  rw [show mutate (node t 43) 3=(relabel (matrix (root [183] [3844] [357] [21] [2] [1]) t) perm21.symm) from he]
  exact IsRoot.relabelled (root_sound [183] [3844] [357] [21] [2] [1] t ht (by decide)) perm21.symm

theorem edge44_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 44) 0) := by
  have he := mutation_equal (pnode 44) (prelabel (pnode 45) perm6.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 44) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 45) perm6.symm

theorem edge44_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 44) 1) := by
  have he := mutation_equal (pnode 44) (prelabel (pnode 26) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 44) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 26) perm0.symm

theorem edge44_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 44) 2) := by
  have he := mutation_equal (pnode 44) (preverse (prelabel (generic param3_0 param3_1 param3_2 param3_3 1) perm12.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 44) t) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (region3_safe t ht 1) perm12.symm)

theorem edge44_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 44) 3) := by
  have he := mutation_equal (pnode 44) (prelabel (root [25] [5017] [524] [201] [21] [1]) perm21.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 44) 3
  rw [show mutate (node t 44) 3=(relabel (matrix (root [25] [5017] [524] [201] [21] [1]) t) perm21.symm) from he]
  exact IsRoot.relabelled (root_sound [25] [5017] [524] [201] [21] [1] t ht (by decide)) perm21.symm

theorem edge45_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 45) 0) := by
  have he := mutation_equal (pnode 45) (prelabel (pnode 27) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 45) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 27) perm0.symm

theorem edge45_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 45) 1) := by
  have he := mutation_equal (pnode 45) (prelabel (pnode 44) perm6.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 45) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 44) perm6.symm

theorem edge45_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 45) 2) := by
  have he := mutation_equal (pnode 45) (prelabel (pnode 62) perm12.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 45) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 62) perm12.symm

theorem edge45_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 45) 3) := by
  have he := mutation_equal (pnode 45) (preverse (prelabel (root [201] [4222] [795] [21] [4] [1]) perm23.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 45) 3
  rw [show mutate (node t 45) 3=(reverse (relabel (matrix (root [201] [4222] [795] [21] [4] [1]) t) perm23.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [201] [4222] [795] [21] [4] [1] t ht (by decide)) perm23.symm)

theorem edge46_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 46) 0) := by
  have he := mutation_equal (pnode 46) (prelabel (pnode 40) perm21.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 46) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 40) perm21.symm

theorem edge46_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 46) 1) := by
  have he := mutation_equal (pnode 46) (preverse (prelabel (zero param13_0 param13_1 param13_2 param13_3 1) perm1.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 46) t) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (region13_safe t ht 1) perm1.symm)

theorem edge46_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 46) 2) := by
  have he := mutation_equal (pnode 46) (prelabel (pnode 28) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 46) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 28) perm0.symm

theorem edge46_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 46) 3) := by
  have he := mutation_equal (pnode 46) (prelabel (pnode 63) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 46) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 63) perm0.symm

theorem edge47_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 47) 0) := by
  have he := mutation_equal (pnode 47) (prelabel (fork [3] [79] [4] [207] [11] [11]) perm4.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (node_safe t 47)
  rw [show mutate (node t 47) 0=(relabel (matrix (fork [3] [79] [4] [207] [11] [11]) t) perm4.symm) from he]
  exact IsFork.relabelled (fork_sound [3] [79] [4] [207] [11] [11] t ht (by decide)) perm4.symm

theorem edge47_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 47) 1) := by
  have he := mutation_equal (pnode 47) (preverse (prelabel (fork [30] [79] [11] [2367] [331] [4]) perm10.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (node_safe t 47)
  rw [show mutate (node t 47) 1=(reverse (relabel (matrix (fork [30] [79] [11] [2367] [331] [4]) t) perm10.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [30] [79] [11] [2367] [331] [4] t ht (by decide)) perm10.symm)

theorem edge47_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 47) 2) := by
  have he := mutation_equal (pnode 47) (prelabel (pnode 64) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 47) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 64) perm0.symm

theorem edge47_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 47) 3) := by
  have he := mutation_equal (pnode 47) (prelabel (pnode 28) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 47) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 28) perm0.symm

theorem edge48_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 48) 0) := by
  have he := mutation_equal (pnode 48) (prelabel (pnode 29) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 48) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 29) perm0.symm

theorem edge48_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 48) 1) := by
  have he := mutation_equal (pnode 48) (prelabel (zero param14_0 param14_1 param14_2 param14_3 0) perm15.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 48) t) 1)
  rw [he]
  exact Safe.framed (region14_safe t ht 0) perm15.symm

theorem edge48_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 48) 2) := by
  have he := mutation_equal (pnode 48) (prelabel (pnode 65) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 48) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 65) perm0.symm

theorem edge48_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 48) 3) := by
  have he := mutation_equal (pnode 48) (prelabel (root [30] [9799] [869] [327] [29] []) perm18.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 48) 3
  rw [show mutate (node t 48) 3=(relabel (matrix (root [30] [9799] [869] [327] [29] []) t) perm18.symm) from he]
  exact IsRoot.relabelled (root_sound [30] [9799] [869] [327] [29] [] t ht (by decide)) perm18.symm

theorem edge49_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 49) 0) := by
  have he := mutation_equal (pnode 49) (preverse (prelabel (root [30] [2367] [869] [79] [29] []) perm4.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 49) 0
  rw [show mutate (node t 49) 0=(reverse (relabel (matrix (root [30] [2367] [869] [79] [29] []) t) perm4.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [30] [2367] [869] [79] [29] [] t ht (by decide)) perm4.symm)

theorem edge49_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 49) 1) := by
  have he := mutation_equal (pnode 49) (preverse (prelabel (zero param15_0 param15_1 param15_2 param15_3 0) perm14.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 49) t) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (region15_safe t ht 0) perm14.symm)

theorem edge49_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 49) 2) := by
  have he := mutation_equal (pnode 49) (prelabel (pnode 66) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 49) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 66) perm0.symm

theorem edge49_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 49) 3) := by
  have he := mutation_equal (pnode 49) (prelabel (pnode 29) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 49) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 29) perm0.symm

theorem edge50_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 50) 0) := by
  have he := mutation_equal (pnode 50) (preverse (prelabel (pnode 61) perm7.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 50) t) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (node_safe t 61) perm7.symm)

theorem edge50_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 50) 1) := by
  have he := mutation_equal (pnode 50) (preverse (prelabel (pnode 42) perm1.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 50) t) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (node_safe t 42) perm1.symm)

theorem edge50_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 50) 2) := by
  have he := mutation_equal (pnode 50) (prelabel (pnode 30) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 50) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 30) perm0.symm

theorem edge50_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 50) 3) := by
  have he := mutation_equal (pnode 50) (prelabel (root [45] [676] [357] [15] [8] [1]) perm18.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 50) 3
  rw [show mutate (node t 50) 3=(relabel (matrix (root [45] [676] [357] [15] [8] [1]) t) perm18.symm) from he]
  exact IsRoot.relabelled (root_sound [45] [676] [357] [15] [8] [1] t ht (by decide)) perm18.symm

theorem edge51_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 51) 0) := by
  have he := mutation_equal (pnode 51) (prelabel (pnode 32) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 51) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 32) perm0.symm

theorem edge51_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 51) 1) := by
  have he := mutation_equal (pnode 51) (prelabel (pnode 33) perm12.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 51) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 33) perm12.symm

theorem edge51_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 51) 2) := by
  have he := mutation_equal (pnode 51) (prelabel (pnode 67) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 51) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 67) perm0.symm

theorem edge51_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 51) 3) := by
  have he := mutation_equal (pnode 51) (preverse (prelabel (fork [12] [5] [21] [59] [251] [2]) perm20.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 3 (node_safe t 51)
  rw [show mutate (node t 51) 3=(reverse (relabel (matrix (fork [12] [5] [21] [59] [251] [2]) t) perm20.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [12] [5] [21] [59] [251] [2] t ht (by decide)) perm20.symm)

theorem edge52_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 52) 0) := by
  have he := mutation_equal (pnode 52) (prelabel (pnode 33) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 52) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 33) perm0.symm

theorem edge52_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 52) 1) := by
  have he := mutation_equal (pnode 52) (prelabel (fork [2] [11] [3] [13] [5] [12]) perm7.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (node_safe t 52)
  rw [show mutate (node t 52) 1=(relabel (matrix (fork [2] [11] [3] [13] [5] [12]) t) perm7.symm) from he]
  exact IsFork.relabelled (fork_sound [2] [11] [3] [13] [5] [12] t ht (by decide)) perm7.symm

theorem edge52_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 52) 2) := by
  have he := mutation_equal (pnode 52) (prelabel (pnode 68) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 52) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 68) perm0.symm

theorem edge52_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 52) 3) := by
  have he := mutation_equal (pnode 52) (preverse (prelabel (fork [9] [11] [12] [97] [109] [3]) perm18.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 3 (node_safe t 52)
  rw [show mutate (node t 52) 3=(reverse (relabel (matrix (fork [9] [11] [12] [97] [109] [3]) t) perm18.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [9] [11] [12] [97] [109] [3] t ht (by decide)) perm18.symm)

theorem edge53_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 53) 0) := by
  have he := mutation_equal (pnode 53) (prelabel (pnode 35) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 53) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 35) perm0.symm

theorem edge53_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 53) 1) := by
  have he := mutation_equal (pnode 53) (prelabel (pnode 69) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 53) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 69) perm0.symm

theorem edge53_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 53) 2) := by
  have he := mutation_equal (pnode 53) (prelabel (pnode 70) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 53) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 70) perm0.symm

theorem edge53_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 53) 3) := by
  have he := mutation_equal (pnode 53) (prelabel (root [34] [1257] [14913] [37] [439] [1]) perm19.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 53) 3
  rw [show mutate (node t 53) 3=(relabel (matrix (root [34] [1257] [14913] [37] [439] [1]) t) perm19.symm) from he]
  exact IsRoot.relabelled (root_sound [34] [1257] [14913] [37] [439] [1] t ht (by decide)) perm19.symm

theorem edge54_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 54) 0) := by
  have he := mutation_equal (pnode 54) (prelabel (pnode 36) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 54) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 36) perm0.symm

theorem edge54_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 54) 1) := by
  have he := mutation_equal (pnode 54) (preverse (prelabel (fork [13] [10351] [14] [133762] [181] [67]) perm7.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (node_safe t 54)
  rw [show mutate (node t 54) 1=(reverse (relabel (matrix (fork [13] [10351] [14] [133762] [181] [67]) t) perm7.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [13] [10351] [14] [133762] [181] [67] t ht (by decide)) perm7.symm)

theorem edge54_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 54) 2) := by
  have he := mutation_equal (pnode 54) (prelabel (pnode 71) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 54) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 71) perm0.symm

theorem edge54_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 54) 3) := by
  have he := mutation_equal (pnode 54) (prelabel (fork [801] [10351] [67] [8291138] [53668] [14]) perm18.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 3 (node_safe t 54)
  rw [show mutate (node t 54) 3=(relabel (matrix (fork [801] [10351] [67] [8291138] [53668] [14]) t) perm18.symm) from he]
  exact IsFork.relabelled (fork_sound [801] [10351] [67] [8291138] [53668] [14] t ht (by decide)) perm18.symm

theorem edge55_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 55) 0) := by
  have he := mutation_equal (pnode 55) (prelabel (pnode 72) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 55) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 72) perm0.symm

theorem edge55_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 55) 1) := by
  have he := mutation_equal (pnode 55) (prelabel (pnode 56) perm2.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 55) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 56) perm2.symm

theorem edge55_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 55) 2) := by
  have he := mutation_equal (pnode 55) (prelabel (pnode 36) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 55) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 36) perm0.symm

theorem edge55_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 55) 3) := by
  have he := mutation_equal (pnode 55) (prelabel (fork [67] [5] [868] [334] [58155] [13]) perm23.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 3 (node_safe t 55)
  rw [show mutate (node t 55) 3=(relabel (matrix (fork [67] [5] [868] [334] [58155] [13]) t) perm23.symm) from he]
  exact IsFork.relabelled (fork_sound [67] [5] [868] [334] [58155] [13] t ht (by decide)) perm23.symm

theorem edge56_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 56) 0) := by
  have he := mutation_equal (pnode 56) (preverse (prelabel (fork [14] [13] [868] [181] [12090] [5]) perm0.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (node_safe t 56)
  rw [show mutate (node t 56) 0=(reverse (relabel (matrix (fork [14] [13] [868] [181] [12090] [5]) t) perm0.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [14] [13] [868] [181] [12090] [5] t ht (by decide)) perm0.symm)

theorem edge56_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 56) 1) := by
  have he := mutation_equal (pnode 56) (prelabel (pnode 37) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 56) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 37) perm0.symm

theorem edge56_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 56) 2) := by
  have he := mutation_equal (pnode 56) (prelabel (pnode 55) perm2.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 56) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 55) perm2.symm

theorem edge56_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 56) 3) := by
  have he := mutation_equal (pnode 56) (prelabel (root [868] [4353] [53802] [5] [62] [1]) perm19.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 56) 3
  rw [show mutate (node t 56) 3=(relabel (matrix (root [868] [4353] [53802] [5] [62] [1]) t) perm19.symm) from he]
  exact IsRoot.relabelled (root_sound [868] [4353] [53802] [5] [62] [1] t ht (by decide)) perm19.symm

theorem edge57_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 57) 0) := by
  have he := mutation_equal (pnode 57) (prelabel (pnode 38) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 57) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 38) perm0.symm

theorem edge57_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 57) 1) := by
  have he := mutation_equal (pnode 57) (prelabel (pnode 70) perm8.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 57) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 70) perm8.symm

theorem edge57_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 57) 2) := by
  have he := mutation_equal (pnode 57) (prelabel (fork [14] [13] [476] [181] [6630] [3]) perm12.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 2 (node_safe t 57)
  rw [show mutate (node t 57) 2=(relabel (matrix (fork [14] [13] [476] [181] [6630] [3]) t) perm12.symm) from he]
  exact IsFork.relabelled (fork_sound [14] [13] [476] [181] [6630] [3] t ht (by decide)) perm12.symm

theorem edge57_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 57) 3) := by
  have he := mutation_equal (pnode 57) (preverse (prelabel (root [476] [1441] [16170] [3] [34] [1]) perm23.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 57) 3
  rw [show mutate (node t 57) 3=(reverse (relabel (matrix (root [476] [1441] [16170] [3] [34] [1]) t) perm23.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [476] [1441] [16170] [3] [34] [1] t ht (by decide)) perm23.symm)

theorem edge58_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 58) 0) := by
  have he := mutation_equal (pnode 58) (prelabel (pnode 39) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 58) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 39) perm0.symm

theorem edge58_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 58) 1) := by
  have he := mutation_equal (pnode 58) (prelabel (root [3] [8] [199] [3] [76] [1]) perm7.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 58) 1
  rw [show mutate (node t 58) 1=(relabel (matrix (root [3] [8] [199] [3] [76] [1]) t) perm7.symm) from he]
  exact IsRoot.relabelled (root_sound [3] [8] [199] [3] [76] [1] t ht (by decide)) perm7.symm

theorem edge58_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 58) 2) := by
  have he := mutation_equal (pnode 58) (prelabel (pnode 73) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 58) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 73) perm0.symm

theorem edge58_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 58) 3) := by
  have he := mutation_equal (pnode 58) (prelabel (pnode 66) perm14.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 58) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 66) perm14.symm

theorem edge59_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 59) 0) := by
  have he := mutation_equal (pnode 59) (prelabel (pnode 74) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 59) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 74) perm0.symm

theorem edge59_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 59) 1) := by
  have he := mutation_equal (pnode 59) (preverse (prelabel (root [11] [120] [3447] [11] [316] [1]) perm9.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 59) 1
  rw [show mutate (node t 59) 1=(reverse (relabel (matrix (root [11] [120] [3447] [11] [316] [1]) t) perm9.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [11] [120] [3447] [11] [316] [1] t ht (by decide)) perm9.symm)

theorem edge59_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 59) 2) := by
  have he := mutation_equal (pnode 59) (prelabel (pnode 39) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 59) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 39) perm0.symm

theorem edge59_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 59) 3) := by
  have he := mutation_equal (pnode 59) (prelabel (pnode 65) perm21.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 59) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 65) perm21.symm

theorem edge60_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 60) 0) := by
  have he := mutation_equal (pnode 60) (prelabel (pnode 43) perm12.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 60) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 43) perm12.symm

theorem edge60_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 60) 1) := by
  have he := mutation_equal (pnode 60) (prelabel (generic param1_0 param1_1 param1_2 param1_3 2) perm6.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 60) t) 1)
  rw [he]
  exact Safe.framed (region1_safe t ht 2) perm6.symm

theorem edge60_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 60) 2) := by
  have he := mutation_equal (pnode 60) (preverse (prelabel (fork [9] [8] [1645] [71] [14622] [21]) perm12.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 2 (node_safe t 60)
  rw [show mutate (node t 60) 2=(reverse (relabel (matrix (fork [9] [8] [1645] [71] [14622] [21]) t) perm12.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [9] [8] [1645] [71] [14622] [21] t ht (by decide)) perm12.symm)

theorem edge60_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 60) 3) := by
  have he := mutation_equal (pnode 60) (prelabel (root [1645] [34553] [301026] [21] [183] [1]) perm23.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 60) 3
  rw [show mutate (node t 60) 3=(relabel (matrix (root [1645] [34553] [301026] [21] [183] [1]) t) perm23.symm) from he]
  exact IsRoot.relabelled (root_sound [1645] [34553] [301026] [21] [183] [1] t ht (by decide)) perm23.symm

theorem edge61_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 61) 0) := by
  have he := mutation_equal (pnode 61) (preverse (prelabel (generic param2_0 param2_1 param2_2 param2_3 2) perm1.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 61) t) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (region2_safe t ht 2) perm1.symm)

theorem edge61_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 61) 1) := by
  have he := mutation_equal (pnode 61) (preverse (prelabel (pnode 50) perm7.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 61) t) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (node_safe t 50) perm7.symm)

theorem edge61_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 61) 2) := by
  have he := mutation_equal (pnode 61) (preverse (prelabel (root [127] [1907] [5712] [15] [45] [1]) perm16.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 61) 2
  rw [show mutate (node t 61) 2=(reverse (relabel (matrix (root [127] [1907] [5712] [15] [45] [1]) t) perm16.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [127] [1907] [5712] [15] [45] [1] t ht (by decide)) perm16.symm)

theorem edge61_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 61) 3) := by
  have he := mutation_equal (pnode 61) (prelabel (fork [3] [2] [127] [5] [336] [15]) perm20.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 3 (node_safe t 61)
  rw [show mutate (node t 61) 3=(relabel (matrix (fork [3] [2] [127] [5] [336] [15]) t) perm20.symm) from he]
  exact IsFork.relabelled (fork_sound [3] [2] [127] [5] [336] [15] t ht (by decide)) perm20.symm

theorem edge62_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 62) 0) := by
  have he := mutation_equal (pnode 62) (prelabel (pnode 45) perm8.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 62) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 45) perm8.symm

theorem edge62_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 62) 1) := by
  have he := mutation_equal (pnode 62) (prelabel (fork [9] [8] [1805] [71] [16044] [21]) perm6.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (node_safe t 62)
  rw [show mutate (node t 62) 1=(relabel (matrix (fork [9] [8] [1805] [71] [16044] [21]) t) perm6.symm) from he]
  exact IsFork.relabelled (fork_sound [9] [8] [1805] [71] [16044] [21] t ht (by decide)) perm6.symm

theorem edge62_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 62) 2) := by
  have he := mutation_equal (pnode 62) (preverse (prelabel (generic param3_0 param3_1 param3_2 param3_3 2) perm12.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 62) t) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (region3_safe t ht 2) perm12.symm)

theorem edge62_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 62) 3) := by
  have he := mutation_equal (pnode 62) (preverse (prelabel (root [1805] [37913] [362796] [21] [201] [1]) perm21.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 62) 3
  rw [show mutate (node t 62) 3=(reverse (relabel (matrix (root [1805] [37913] [362796] [21] [201] [1]) t) perm21.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [1805] [37913] [362796] [21] [201] [1] t ht (by decide)) perm21.symm)

theorem edge63_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 63) 0) := by
  have he := mutation_equal (pnode 63) (preverse (prelabel (generic param4_0 param4_1 param4_2 param4_3 1) perm3.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 63) t) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (region4_safe t ht 1) perm3.symm)

theorem edge63_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 63) 1) := by
  have he := mutation_equal (pnode 63) (prelabel (root [41] [5040] [1229] [123] [30] [1]) perm10.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 63) 1
  rw [show mutate (node t 63) 1=(relabel (matrix (root [41] [5040] [1229] [123] [30] [1]) t) perm10.symm) from he]
  exact IsRoot.relabelled (root_sound [41] [5040] [1229] [123] [30] [1] t ht (by decide)) perm10.symm

theorem edge63_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 63) 2) := by
  have he := mutation_equal (pnode 63) (prelabel (pnode 64) perm1.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 63) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 64) perm1.symm

theorem edge63_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 63) 3) := by
  have he := mutation_equal (pnode 63) (prelabel (pnode 46) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 63) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 46) perm0.symm

theorem edge64_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 64) 0) := by
  have he := mutation_equal (pnode 64) (prelabel (pnode 75) perm20.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 64) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 75) perm20.symm

theorem edge64_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 64) 1) := by
  have he := mutation_equal (pnode 64) (preverse (prelabel (root [123] [3691] [1349] [30] [11] [1]) perm7.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 64) 1
  rw [show mutate (node t 64) 1=(reverse (relabel (matrix (root [123] [3691] [1349] [30] [11] [1]) t) perm7.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [123] [3691] [1349] [30] [11] [1] t ht (by decide)) perm7.symm)

theorem edge64_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 64) 2) := by
  have he := mutation_equal (pnode 64) (prelabel (pnode 47) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 64) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 47) perm0.symm

theorem edge64_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 64) 3) := by
  have he := mutation_equal (pnode 64) (prelabel (pnode 63) perm1.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 64) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 63) perm1.symm

theorem edge65_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 65) 0) := by
  have he := mutation_equal (pnode 65) (prelabel (pnode 59) perm21.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 65) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 59) perm21.symm

theorem edge65_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 65) 1) := by
  have he := mutation_equal (pnode 65) (prelabel (zero param14_0 param14_1 param14_2 param14_3 1) perm15.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 65) t) 1)
  rw [he]
  exact Safe.framed (region14_safe t ht 1) perm15.symm

theorem edge65_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 65) 2) := by
  have he := mutation_equal (pnode 65) (prelabel (pnode 48) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 65) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 48) perm0.symm

theorem edge65_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 65) 3) := by
  have he := mutation_equal (pnode 65) (prelabel (pnode 76) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 65) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 76) perm0.symm

theorem edge66_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 66) 0) := by
  have he := mutation_equal (pnode 66) (prelabel (pnode 77) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 66) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 77) perm0.symm

theorem edge66_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 66) 1) := by
  have he := mutation_equal (pnode 66) (preverse (prelabel (zero param15_0 param15_1 param15_2 param15_3 1) perm14.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 66) t) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (region15_safe t ht 1) perm14.symm)

theorem edge66_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 66) 2) := by
  have he := mutation_equal (pnode 66) (prelabel (pnode 49) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 66) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 49) perm0.symm

theorem edge66_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 66) 3) := by
  have he := mutation_equal (pnode 66) (prelabel (pnode 58) perm14.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 66) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 58) perm14.symm

theorem edge67_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 67) 0) := by
  have he := mutation_equal (pnode 67) (preverse (prelabel (generic param5_0 param5_1 param5_2 param5_3 1) perm0.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 67) t) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (region5_safe t ht 1) perm0.symm)

theorem edge67_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 67) 1) := by
  have he := mutation_equal (pnode 67) (prelabel (pnode 68) perm6.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 67) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 68) perm6.symm

theorem edge67_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 67) 2) := by
  have he := mutation_equal (pnode 67) (prelabel (pnode 51) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 67) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 51) perm0.symm

theorem edge67_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 67) 3) := by
  have he := mutation_equal (pnode 67) (prelabel (root [21] [985] [188] [47] [9] [1]) perm22.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 67) 3
  rw [show mutate (node t 67) 3=(relabel (matrix (root [21] [985] [188] [47] [9] [1]) t) perm22.symm) from he]
  exact IsRoot.relabelled (root_sound [21] [985] [188] [47] [9] [1] t ht (by decide)) perm22.symm

theorem edge68_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 68) 0) := by
  have he := mutation_equal (pnode 68) (prelabel (pnode 67) perm6.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 68) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 67) perm6.symm

theorem edge68_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 68) 1) := by
  have he := mutation_equal (pnode 68) (prelabel (pnode 78) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 68) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 78) perm0.symm

theorem edge68_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 68) 2) := by
  have he := mutation_equal (pnode 68) (prelabel (pnode 52) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 68) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 52) perm0.symm

theorem edge68_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 68) 3) := by
  have he := mutation_equal (pnode 68) (preverse (prelabel (root [47] [424] [561] [9] [12] [1]) perm20.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 68) 3
  rw [show mutate (node t 68) 3=(reverse (relabel (matrix (root [47] [424] [561] [9] [12] [1]) t) perm20.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [47] [424] [561] [9] [12] [1] t ht (by decide)) perm20.symm)

theorem edge69_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 69) 0) := by
  have he := mutation_equal (pnode 69) (prelabel (fork [13] [5673] [14] [73310] [181] [37]) perm1.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (node_safe t 69)
  rw [show mutate (node t 69) 0=(relabel (matrix (fork [13] [5673] [14] [73310] [181] [37]) t) perm1.symm) from he]
  exact IsFork.relabelled (fork_sound [13] [5673] [14] [73310] [181] [37] t ht (by decide)) perm1.symm

theorem edge69_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 69) 1) := by
  have he := mutation_equal (pnode 69) (prelabel (pnode 53) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 69) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 53) perm0.symm

theorem edge69_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 69) 2) := by
  have he := mutation_equal (pnode 69) (prelabel (pnode 79) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 69) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 79) perm0.symm

theorem edge69_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 69) 3) := by
  have he := mutation_equal (pnode 69) (preverse (prelabel (fork [439] [5673] [37] [2490434] [16244] [14]) perm20.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 3 (node_safe t 69)
  rw [show mutate (node t 69) 3=(reverse (relabel (matrix (fork [439] [5673] [37] [2490434] [16244] [14]) t) perm20.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [439] [5673] [37] [2490434] [16244] [14] t ht (by decide)) perm20.symm)

theorem edge70_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 70) 0) := by
  have he := mutation_equal (pnode 70) (prelabel (pnode 57) perm12.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 70) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 57) perm12.symm

theorem edge70_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 70) 1) := by
  have he := mutation_equal (pnode 70) (prelabel (pnode 80) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 70) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 80) perm0.symm

theorem edge70_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 70) 2) := by
  have he := mutation_equal (pnode 70) (prelabel (pnode 53) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 70) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 53) perm0.symm

theorem edge70_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 70) 3) := by
  have he := mutation_equal (pnode 70) (preverse (prelabel (fork [37] [3] [476] [110] [17611] [13]) perm22.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 3 (node_safe t 70)
  rw [show mutate (node t 70) 3=(reverse (relabel (matrix (fork [37] [3] [476] [110] [17611] [13]) t) perm22.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [37] [3] [476] [110] [17611] [13] t ht (by decide)) perm22.symm)

theorem edge71_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 71) 0) := by
  have he := mutation_equal (pnode 71) (prelabel (pnode 72) perm14.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 71) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 72) perm14.symm

theorem edge71_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 71) 1) := by
  have he := mutation_equal (pnode 71) (prelabel (pnode 81) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 71) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 81) perm0.symm

theorem edge71_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 71) 2) := by
  have he := mutation_equal (pnode 71) (prelabel (pnode 54) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 71) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 54) perm0.symm

theorem edge71_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 71) 3) := by
  have he := mutation_equal (pnode 71) (prelabel (root [11289] [9042490] [756349] [801] [67] [1]) perm20.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 71) 3
  rw [show mutate (node t 71) 3=(relabel (matrix (root [11289] [9042490] [756349] [801] [67] [1]) t) perm20.symm) from he]
  exact IsRoot.relabelled (root_sound [11289] [9042490] [756349] [801] [67] [1] t ht (by decide)) perm20.symm

theorem edge72_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 72) 0) := by
  have he := mutation_equal (pnode 72) (prelabel (pnode 55) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 72) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 55) perm0.symm

theorem edge72_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 72) 1) := by
  have he := mutation_equal (pnode 72) (prelabel (generic param6_0 param6_1 param6_2 param6_3 1) perm8.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 72) t) 1)
  rw [he]
  exact Safe.framed (region6_safe t ht 1) perm8.symm

theorem edge72_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 72) 2) := by
  have he := mutation_equal (pnode 72) (prelabel (pnode 71) perm14.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 72) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 71) perm14.symm

theorem edge72_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 72) 3) := by
  have he := mutation_equal (pnode 72) (preverse (prelabel (root [868] [9798839] [695267] [11289] [801] [1]) perm18.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 72) 3
  rw [show mutate (node t 72) 3=(reverse (relabel (matrix (root [868] [9798839] [695267] [11289] [801] [1]) t) perm18.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [868] [9798839] [695267] [11289] [801] [1] t ht (by decide)) perm18.symm)

theorem edge73_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 73) 0) := by
  have he := mutation_equal (pnode 73) (prelabel (fork [29] [2201] [30] [63753] [869] [3]) perm2.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (node_safe t 73)
  rw [show mutate (node t 73) 0=(relabel (matrix (fork [29] [2201] [30] [63753] [869] [3]) t) perm2.symm) from he]
  exact IsFork.relabelled (fork_sound [29] [2201] [30] [63753] [869] [3] t ht (by decide)) perm2.symm

theorem edge73_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 73) 1) := by
  have he := mutation_equal (pnode 73) (preverse (prelabel (fork [76] [2201] [3] [167247] [229] [30]) perm8.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (node_safe t 73)
  rw [show mutate (node t 73) 1=(reverse (relabel (matrix (fork [76] [2201] [3] [167247] [229] [30]) t) perm8.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [76] [2201] [3] [167247] [229] [30] t ht (by decide)) perm8.symm)

theorem edge73_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 73) 2) := by
  have he := mutation_equal (pnode 73) (prelabel (pnode 58) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 73) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 58) perm0.symm

theorem edge73_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 73) 3) := by
  have he := mutation_equal (pnode 73) (prelabel (pnode 82) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 73) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 82) perm0.symm

theorem edge74_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 74) 0) := by
  have he := mutation_equal (pnode 74) (prelabel (pnode 59) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 74) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 59) perm0.symm

theorem edge74_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 74) 1) := by
  have he := mutation_equal (pnode 74) (prelabel (fork [316] [9153] [11] [2892319] [3477] [30]) perm6.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (node_safe t 74)
  rw [show mutate (node t 74) 1=(relabel (matrix (fork [316] [9153] [11] [2892319] [3477] [30]) t) perm6.symm) from he]
  exact IsFork.relabelled (fork_sound [316] [9153] [11] [2892319] [3477] [30] t ht (by decide)) perm6.symm

theorem edge74_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 74) 2) := by
  have he := mutation_equal (pnode 74) (preverse (prelabel (fork [29] [9153] [30] [265121] [869] [11]) perm12.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 2 (node_safe t 74)
  rw [show mutate (node t 74) 2=(reverse (relabel (matrix (fork [29] [9153] [30] [265121] [869] [11]) t) perm12.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [29] [9153] [30] [265121] [869] [11] t ht (by decide)) perm12.symm)

theorem edge74_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 74) 3) := by
  have he := mutation_equal (pnode 74) (prelabel (pnode 83) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 74) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 83) perm0.symm

theorem edge75_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 75) 0) := by
  have he := mutation_equal (pnode 75) (preverse (prelabel (generic param4_0 param4_1 param4_2 param4_3 2) perm3.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 75) t) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (region4_safe t ht 2) perm3.symm)

theorem edge75_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 75) 1) := by
  have he := mutation_equal (pnode 75) (preverse (prelabel (root [481] [14433] [59159] [30] [123] [1]) perm10.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 75) 1
  rw [show mutate (node t 75) 1=(reverse (relabel (matrix (root [481] [14433] [59159] [30] [123] [1]) t) perm10.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [481] [14433] [59159] [30] [123] [1] t ht (by decide)) perm10.symm)

theorem edge75_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 75) 2) := by
  have he := mutation_equal (pnode 75) (prelabel (pnode 64) perm15.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 75) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 64) perm15.symm

theorem edge75_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 75) 3) := by
  have he := mutation_equal (pnode 75) (prelabel (fork [4] [3] [481] [11] [1801] [30]) perm22.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 3 (node_safe t 75)
  rw [show mutate (node t 75) 3=(relabel (matrix (fork [4] [3] [481] [11] [1801] [30]) t) perm22.symm) from he]
  exact IsFork.relabelled (fork_sound [4] [3] [481] [11] [1801] [30] t ht (by decide)) perm22.symm

theorem edge76_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 76) 0) := by
  have he := mutation_equal (pnode 76) (prelabel (pnode 83) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 76) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 83) perm0.symm

theorem edge76_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 76) 1) := by
  have he := mutation_equal (pnode 76) (preverse (prelabel (root [327] [3100912] [103331] [9483] [316] [1]) perm11.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 76) 1
  rw [show mutate (node t 76) 1=(reverse (relabel (matrix (root [327] [3100912] [103331] [9483] [316] [1]) t) perm11.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [327] [3100912] [103331] [9483] [316] [1] t ht (by decide)) perm11.symm)

theorem edge76_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 76) 2) := by
  have he := mutation_equal (pnode 76) (prelabel (generic param7_0 param7_1 param7_2 param7_3 1) perm13.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 76) t) 2)
  rw [he]
  exact Safe.framed (region7_safe t ht 1) perm13.symm

theorem edge76_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 76) 3) := by
  have he := mutation_equal (pnode 76) (prelabel (pnode 65) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 76) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 65) perm0.symm

theorem edge77_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 77) 0) := by
  have he := mutation_equal (pnode 77) (prelabel (pnode 66) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 77) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 66) perm0.symm

theorem edge77_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 77) 1) := by
  have he := mutation_equal (pnode 77) (prelabel (root [79] [180960] [6003] [2291] [76] [1]) perm6.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 77) 1
  rw [show mutate (node t 77) 1=(relabel (matrix (root [79] [180960] [6003] [2291] [76] [1]) t) perm6.symm) from he]
  exact IsRoot.relabelled (root_sound [79] [180960] [6003] [2291] [76] [1] t ht (by decide)) perm6.symm

theorem edge77_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 77) 2) := by
  have he := mutation_equal (pnode 77) (preverse (prelabel (generic param8_0 param8_1 param8_2 param8_3 1) perm16.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 77) t) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (region8_safe t ht 1) perm16.symm)

theorem edge77_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 77) 3) := by
  have he := mutation_equal (pnode 77) (prelabel (pnode 82) perm15.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 77) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 82) perm15.symm

theorem edge78_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 78) 0) := by
  have he := mutation_equal (pnode 78) (preverse (prelabel (generic param5_0 param5_1 param5_2 param5_3 2) perm0.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 78) t) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (region5_safe t ht 2) perm0.symm)

theorem edge78_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 78) 1) := by
  have he := mutation_equal (pnode 78) (prelabel (pnode 68) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 78) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 68) perm0.symm

theorem edge78_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 78) 2) := by
  have he := mutation_equal (pnode 78) (prelabel (fork [3] [2] [129] [5] [340] [9]) perm14.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 2 (node_safe t 78)
  rw [show mutate (node t 78) 2=(relabel (matrix (fork [3] [2] [129] [5] [340] [9]) t) perm14.symm) from he]
  exact IsFork.relabelled (fork_sound [3] [2] [129] [5] [340] [9] t ht (by decide)) perm14.symm

theorem edge78_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 78) 3) := by
  have he := mutation_equal (pnode 78) (preverse (prelabel (root [129] [1163] [6060] [9] [47] [1]) perm22.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 78) 3
  rw [show mutate (node t 78) 3=(reverse (relabel (matrix (root [129] [1163] [6060] [9] [47] [1]) t) perm22.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [129] [1163] [6060] [9] [47] [1] t ht (by decide)) perm22.symm)

theorem edge79_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 79) 0) := by
  have he := mutation_equal (pnode 79) (prelabel (pnode 86) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 79) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 86) perm0.symm

theorem edge79_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 79) 1) := by
  have he := mutation_equal (pnode 79) (prelabel (pnode 80) perm2.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 79) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 80) perm2.symm

theorem edge79_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 79) 2) := by
  have he := mutation_equal (pnode 79) (prelabel (pnode 69) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 79) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 69) perm0.symm

theorem edge79_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 79) 3) := by
  have he := mutation_equal (pnode 79) (preverse (prelabel (root [6191] [2717850] [229053] [439] [37] [1]) perm18.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 79) 3
  rw [show mutate (node t 79) 3=(reverse (relabel (matrix (root [6191] [2717850] [229053] [439] [37] [1]) t) perm18.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [6191] [2717850] [229053] [439] [37] [1] t ht (by decide)) perm18.symm)

theorem edge80_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 80) 0) := by
  have he := mutation_equal (pnode 80) (preverse (prelabel (generic param9_0 param9_1 param9_2 param9_3 1) perm2.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 80) t) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (region9_safe t ht 1) perm2.symm)

theorem edge80_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 80) 1) := by
  have he := mutation_equal (pnode 80) (prelabel (pnode 70) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 80) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 70) perm0.symm

theorem edge80_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 80) 2) := by
  have he := mutation_equal (pnode 80) (prelabel (pnode 79) perm2.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 80) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 79) perm2.symm

theorem edge80_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 80) 3) := by
  have he := mutation_equal (pnode 80) (prelabel (root [476] [2946903] [208963] [6191] [439] [1]) perm20.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 80) 3
  rw [show mutate (node t 80) 3=(relabel (matrix (root [476] [2946903] [208963] [6191] [439] [1]) t) perm20.symm) from he]
  exact IsRoot.relabelled (root_sound [476] [2946903] [208963] [6191] [439] [1] t ht (by decide)) perm20.symm

theorem edge81_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 81) 0) := by
  have he := mutation_equal (pnode 81) (prelabel (generic param6_0 param6_1 param6_2 param6_3 2) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 81) t) 0)
  rw [he]
  exact Safe.framed (region6_safe t ht 2) perm0.symm

theorem edge81_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 81) 1) := by
  have he := mutation_equal (pnode 81) (prelabel (pnode 71) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 81) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 71) perm0.symm

theorem edge81_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 81) 2) := by
  have he := mutation_equal (pnode 81) (preverse (prelabel (fork [14] [13] [157979] [181] [2200417] [801]) perm14.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 2 (node_safe t 81)
  rw [show mutate (node t 81) 2=(reverse (relabel (matrix (fork [14] [13] [157979] [181] [2200417] [801]) t) perm14.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [14] [13] [157979] [181] [2200417] [801] t ht (by decide)) perm14.symm)

theorem edge81_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 81) 3) := by
  have he := mutation_equal (pnode 81) (prelabel (root [157979] [126541192] [1783424917] [801] [11289] [1]) perm22.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 81) 3
  rw [show mutate (node t 81) 3=(relabel (matrix (root [157979] [126541192] [1783424917] [801] [11289] [1]) t) perm22.symm) from he]
  exact IsRoot.relabelled (root_sound [157979] [126541192] [1783424917] [801] [11289] [1] t ht (by decide)) perm22.symm

theorem edge82_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 82) 0) := by
  have he := mutation_equal (pnode 82) (prelabel (pnode 85) perm21.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 82) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 85) perm21.symm

theorem edge82_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 82) 1) := by
  have he := mutation_equal (pnode 82) (preverse (prelabel (root [2291] [174117] [6843] [76] [3] [1]) perm6.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 82) 1
  rw [show mutate (node t 82) 1=(reverse (relabel (matrix (root [2291] [174117] [6843] [76] [3] [1]) t) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [2291] [174117] [6843] [76] [3] [1] t ht (by decide)) perm6.symm)

theorem edge82_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 82) 2) := by
  have he := mutation_equal (pnode 82) (prelabel (pnode 77) perm20.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 82) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 77) perm20.symm

theorem edge82_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 82) 3) := by
  have he := mutation_equal (pnode 82) (prelabel (pnode 73) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 82) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 73) perm0.symm

theorem edge83_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 83) 0) := by
  have he := mutation_equal (pnode 83) (prelabel (pnode 76) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 83) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 76) perm0.symm

theorem edge83_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 83) 1) := by
  have he := mutation_equal (pnode 83) (prelabel (root [9483] [2996629] [104283] [316] [11] [1]) perm8.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 83) 1
  rw [show mutate (node t 83) 1=(relabel (matrix (root [9483] [2996629] [104283] [316] [11] [1]) t) perm8.symm) from he]
  exact IsRoot.relabelled (root_sound [9483] [2996629] [104283] [316] [11] [1] t ht (by decide)) perm8.symm

theorem edge83_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 83) 2) := by
  have he := mutation_equal (pnode 83) (prelabel (pnode 84) perm14.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 83) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 84) perm14.symm

theorem edge83_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 83) 3) := by
  have he := mutation_equal (pnode 83) (prelabel (pnode 74) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 83) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 74) perm0.symm

theorem edge84_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 84) 0) := by
  have he := mutation_equal (pnode 84) (prelabel (pnode 83) perm14.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 84) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 83) perm14.symm

theorem edge84_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 84) 1) := by
  have he := mutation_equal (pnode 84) (prelabel (root [284479] [89895393] [2697714327] [316] [9483] [1]) perm11.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 84) 1
  rw [show mutate (node t 84) 1=(relabel (matrix (root [284479] [89895393] [2697714327] [316] [9483] [1]) t) perm11.symm) from he]
  exact IsRoot.relabelled (root_sound [284479] [89895393] [2697714327] [316] [9483] [1] t ht (by decide)) perm11.symm

theorem edge84_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 84) 2) := by
  have he := mutation_equal (pnode 84) (prelabel (generic param7_0 param7_1 param7_2 param7_3 2) perm13.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 84) t) 2)
  rw [he]
  exact Safe.framed (region7_safe t ht 2) perm13.symm

theorem edge84_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 84) 3) := by
  have he := mutation_equal (pnode 84) (preverse (prelabel (fork [30] [29] [284479] [869] [8524887] [316]) perm19.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 3 (node_safe t 84)
  rw [show mutate (node t 84) 3=(reverse (relabel (matrix (fork [30] [29] [284479] [869] [8524887] [316]) t) perm19.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [30] [29] [284479] [869] [8524887] [316] t ht (by decide)) perm19.symm)

theorem edge85_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 85) 0) := by
  have he := mutation_equal (pnode 85) (prelabel (fork [30] [29] [68727] [869] [2059519] [76]) perm5.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (node_safe t 85)
  rw [show mutate (node t 85) 0=(relabel (matrix (fork [30] [29] [68727] [869] [2059519] [76]) t) perm5.symm) from he]
  exact IsFork.relabelled (fork_sound [30] [29] [68727] [869] [2059519] [76] t ht (by decide)) perm5.symm

theorem edge85_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 85) 1) := by
  have he := mutation_equal (pnode 85) (preverse (prelabel (root [68727] [5223281] [157453527] [76] [2291] [1]) perm6.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 85) 1
  rw [show mutate (node t 85) 1=(reverse (relabel (matrix (root [68727] [5223281] [157453527] [76] [2291] [1]) t) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [68727] [5223281] [157453527] [76] [2291] [1] t ht (by decide)) perm6.symm)

theorem edge85_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 85) 2) := by
  have he := mutation_equal (pnode 85) (preverse (prelabel (generic param8_0 param8_1 param8_2 param8_3 2) perm16.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 85) t) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (region8_safe t ht 2) perm16.symm)

theorem edge85_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 85) 3) := by
  have he := mutation_equal (pnode 85) (prelabel (pnode 82) perm21.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 85) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 82) perm21.symm

theorem edge86_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 86) 0) := by
  have he := mutation_equal (pnode 86) (prelabel (pnode 79) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 86) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 79) perm0.symm

theorem edge86_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 86) 1) := by
  have he := mutation_equal (pnode 86) (preverse (prelabel (generic param9_0 param9_1 param9_2 param9_3 2) perm6.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 86) t) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (region9_safe t ht 2) perm6.symm)

theorem edge86_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 86) 2) := by
  have he := mutation_equal (pnode 86) (prelabel (fork [14] [13] [86637] [181] [1206727] [439]) perm12.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 2 (node_safe t 86)
  rw [show mutate (node t 86) 2=(relabel (matrix (fork [14] [13] [86637] [181] [1206727] [439]) t) perm12.symm) from he]
  exact IsFork.relabelled (fork_sound [14] [13] [86637] [181] [1206727] [439] t ht (by decide)) perm12.symm

theorem edge86_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 86) 3) := by
  have he := mutation_equal (pnode 86) (preverse (prelabel (root [86637] [38033656] [536369653] [439] [6191] [1]) perm23.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 86) 3
  rw [show mutate (node t 86) 3=(reverse (relabel (matrix (root [86637] [38033656] [536369653] [439] [6191] [1]) t) perm23.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [86637] [38033656] [536369653] [439] [6191] [1] t ht (by decide)) perm23.symm)

theorem all_cyclic (t : Int) (ht : 0≤t) (i : Fin 87) : ¬ Acyclic (node t i) := by
  rcases finCore i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
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
  · exact cyclic83 t ht
  · exact cyclic84 t ht
  · exact cyclic85 t ht
  · exact cyclic86 t ht

theorem all_edges (t : Int) (ht : 0≤t) (i : Fin 87) (k : Fin 4) : SafeCore t (mutate (node t i) k) := by
  have hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
  rcases finCore i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rcases hk with rfl|rfl|rfl|rfl
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
  · exact edge83_0 t ht
  · exact edge83_1 t ht
  · exact edge83_2 t ht
  · exact edge83_3 t ht
  · exact edge84_0 t ht
  · exact edge84_1 t ht
  · exact edge84_2 t ht
  · exact edge84_3 t ht
  · exact edge85_0 t ht
  · exact edge85_1 t ht
  · exact edge85_2 t ht
  · exact edge85_3 t ht
  · exact edge86_0 t ht
  · exact edge86_1 t ht
  · exact edge86_2 t ht
  · exact edge86_3 t ht

theorem NMA (t : Int) (ht : 0≤t) : ¬ MutationAcyclic (node t 0) := by
  apply safe_NMA data rules (Core t)
  · rintro B ⟨i,rfl⟩; exact node_skew t i
  · rintro B ⟨i,rfl⟩; exact all_cyclic t ht i
  · rintro B ⟨i,rfl⟩ k; exact all_edges t ht i k
  · exact node_safe t 0
end Boundary
namespace HalfLine
private theorem finCore (i : Fin 94) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 ∨ i=15 ∨ i=16 ∨ i=17 ∨ i=18 ∨ i=19 ∨ i=20 ∨ i=21 ∨ i=22 ∨ i=23 ∨ i=24 ∨ i=25 ∨ i=26 ∨ i=27 ∨ i=28 ∨ i=29 ∨ i=30 ∨ i=31 ∨ i=32 ∨ i=33 ∨ i=34 ∨ i=35 ∨ i=36 ∨ i=37 ∨ i=38 ∨ i=39 ∨ i=40 ∨ i=41 ∨ i=42 ∨ i=43 ∨ i=44 ∨ i=45 ∨ i=46 ∨ i=47 ∨ i=48 ∨ i=49 ∨ i=50 ∨ i=51 ∨ i=52 ∨ i=53 ∨ i=54 ∨ i=55 ∨ i=56 ∨ i=57 ∨ i=58 ∨ i=59 ∨ i=60 ∨ i=61 ∨ i=62 ∨ i=63 ∨ i=64 ∨ i=65 ∨ i=66 ∨ i=67 ∨ i=68 ∨ i=69 ∨ i=70 ∨ i=71 ∨ i=72 ∨ i=73 ∨ i=74 ∨ i=75 ∨ i=76 ∨ i=77 ∨ i=78 ∨ i=79 ∨ i=80 ∨ i=81 ∨ i=82 ∨ i=83 ∨ i=84 ∨ i=85 ∨ i=86 ∨ i=87 ∨ i=88 ∨ i=89 ∨ i=90 ∨ i=91 ∨ i=92 ∨ i=93 := by omega

def pnode (i : Fin 94) : PMatrix := match i.val with
  | 0 => six [2] [2,1] [-1] [1] [-1] [5,1]
  | 1 => six [-2] [-2,-1] [1] [1] [-3] [3]
  | 2 => six [-2] [4,1] [-1] [-1] [1] [4,1]
  | 3 => six [2] [-2,-1] [9,7,1] [-1] [4,1] [-5,-1]
  | 4 => six [2] [-3] [1] [-4,-1] [1] [-5,-1]
  | 5 => six [2] [-2,-1] [-5] [-1] [3] []
  | 6 => six [-4,-1] [2,1] [1] [-1] [] [-3]
  | 7 => six [1] [-2,-1] [-1] [-8] [3] [-3]
  | 8 => six [2] [-4,-1] [1] [7,2] [1] []
  | 9 => six [2,1] [-4,-1] [15,8,1] [1] [1] [-4,-1]
  | 10 => six [-3] [] [1] [-1] [-1] [-4,-1]
  | 11 => six [-2] [-2,-1] [17,9,1] [1] [-4,-1] [-1]
  | 12 => six [-2] [3] [-1] [-10,-1] [1] [-2,-1]
  | 13 => six [-2] [-3] [3] [4,1] [-1] [-1]
  | 14 => six [2] [2,1] [-5] [1] [3] []
  | 15 => six [-13] [-2,-1] [5] [-1] [-3] []
  | 16 => six [4,1] [-2,-1] [-1] [7,6,1] [4,1] [-3]
  | 17 => six [4,1] [-2] [1] [1] [] [-3]
  | 18 => six [-4,-1] [5,1] [-1] [-1] [] [3]
  | 19 => six [-1] [-2,-1] [2] [8] [-3] [21]
  | 20 => six [-2] [10,3] [3] [-7,-2] [-1] []
  | 21 => six [-26,-15,-2] [4,1] [1] [-7,-2] [1] []
  | 22 => six [2] [-4,-1] [-1] [7,2] [-1] []
  | 23 => six [2,1] [56,46,12,1] [-15,-8,-1] [5,1] [-1] [4,1]
  | 24 => six [66,53,13,1] [15,8,1] [-17,-9,-1] [1] [4,1] [1]
  | 25 => six [2] [-17,-2] [-1] [10,1] [-1] [8]
  | 26 => six [-14,-3] [3] [] [-4,-1] [-1] [1]
  | 27 => six [-13] [2,1] [5] [1] [-3] []
  | 28 => six [13] [-15,-1] [-34] [1] [3] []
  | 29 => six [] [-2,-1] [1] [19,9,1] [-4,-1] [3]
  | 30 => six [4,1] [-5,-1] [1] [19,9,1] [] [-2,-1]
  | 31 => six [1] [-5,-1] [14,3] [1] [] [-3]
  | 32 => six [1] [2,1] [-2] [8] [-1] [25,2]
  | 33 => six [1] [10,3] [-3] [-7,-2] [1] []
  | 34 => six [26,15,2] [-4,-1] [-1] [97,84,23,2] [27,15,2] []
  | 35 => six [26,15,2] [-178,-156,-44,-4] [1] [7,2] [-1] [7,2]
  | 36 => six [-26,-15,-2] [4,1] [-1] [-7,-2] [-1] []
  | 37 => six [-2] [10,3] [-1] [-7,-2] [1] [-7,-2]
  | 38 => six [-2,-1] [66,53,13,1] [-15,-8,-1] [-5,-1] [1] [-1]
  | 39 => six [-15,-8,-1] [-66,-53,-13,-1] [328,330,118,18,1] [-1] [4,1] [-5,-1]
  | 40 => six [-2] [17,2] [1] [-24,-3] [-3] [8]
  | 41 => six [14,3] [-3] [] [38,8] [-1] [1]
  | 42 => six [14,3] [-53,-26,-3] [-14,-3] [4,1] [1] [1]
  | 43 => six [13] [2,1] [-34] [-1] [3] [-3]
  | 44 => six [-2,-1] [15,1] [-34] [-1] [3] []
  | 45 => six [-1] [5,1] [-14,-3] [-4,-1] [] [67,29,3]
  | 46 => six [1] [37,8] [-14,-3] [1] [] [3]
  | 47 => six [1] [-48,-3] [2] [-17,-2] [1] [-25,-2]
  | 48 => six [-1] [-10,-3] [3] [-7,-2] [-2] [-30,-9]
  | 49 => six [-1] [-4,-1] [1] [97,84,23,2] [-27,-15,-2] []
  | 50 => six [-26,-15,-2] [178,156,44,4] [-1] [-4621,-6724,-3840,-1076,-148,-8] [-1] [185,158,44,4]
  | 51 => six [27,15,2] [-178,-156,-44,-4] [-1] [] [1] [-7,-2]
  | 52 => six [26,15,2] [-4,-1] [1] [97,84,23,2] [-1] [-4,-1]
  | 53 => six [26,15,2] [-178,-156,-44,-4] [-27,-15,-2] [7,2] [1] []
  | 54 => six [2] [-10,-3] [1] [13,4] [1] [-17,-5]
  | 55 => six [1] [17,2] [-1] [-48,-3] [3] [-8]
  | 56 => six [-14,-3] [529,226,24] [] [-38,-8] [1] [-37,-8]
  | 57 => six [-100,-21] [3] [] [-38,-8] [37,8] [-1]
  | 58 => six [-198,-154,-38,-3] [53,26,3] [-14,-3] [-4,-1] [5,1] [-1]
  | 59 => six [] [-67,-29,-3] [14,3] [4,1] [-1] [-1]
  | 60 => six [-1] [-37,-8] [14,3] [1] [-14,-3] [-515,-223,-24]
  | 61 => six [1] [-37,-8] [97,21] [-1] [3] [-3]
  | 62 => six [-1] [17,2] [2] [48,3] [-3] [136,9]
  | 63 => six [1] [-17,-5] [1] [7,2] [2] [-30,-9]
  | 64 => six [1] [-4,-1] [-26,-15,-2] [-97,-84,-23,-2] [27,15,2] [-2619,-3723,-2075,-567,-76,-4]
  | 65 => six [26,15,2] [-119968,-243983,-209898,-99020,-27668,-4580,-416,-16] [-27,-15,-2] [4621,6724,3840,1076,148,8] [1] [185,158,44,4]
  | 66 => six [-26,-15,-2] [-7,-2] [1] [-4806,-6882,-3884,-1080,-148,-8] [1] [-185,-158,-44,-4]
  | 67 => six [-27,-15,-2] [178,156,44,4] [1] [-4806,-6882,-3884,-1080,-148,-8] [-26,-15,-2] [-7,-2]
  | 68 => six [-26,-15,-2] [2518,3638,2052,565,76,4] [1] [-97,-84,-23,-2] [1] [-101,-85,-23,-2]
  | 69 => six [-2] [16,5] [3] [-13,-4] [-1] [-17,-5]
  | 70 => six [-14,-3] [529,226,24] [] [-1] [-1] [37,8]
  | 71 => six [-100,-21] [3] [] [-1] [-37,-8] [1]
  | 72 => six [-268,-183,-41,-3] [53,26,3] [14,3] [1] [-5,-1] [1]
  | 73 => six [-268,-183,-41,-3] [67,29,3] [-53,-26,-3] [-4,-1] [-1] [1]
  | 74 => six [-38,-8] [37,8] [-19041,-12368,-2672,-192] [-1] [-14,-3] [515,223,24]
  | 75 => six [-1] [37,8] [-97,-21] [-38,-8] [3] [3586,1553,168]
  | 76 => six [1] [13,4] [-1] [67,20] [-2] [30,9]
  | 77 => six [-1] [4,1] [26,15,2] [-101,-85,-23,-2] [1] [-2619,-3723,-2075,-567,-76,-4]
  | 78 => six [-1] [-124963,-251024,-213826,-100104,-27816,-4588,-416,-16] [27,15,2] [4621,6724,3840,1076,148,8] [-1] [-185,-158,-44,-4]
  | 79 => six [26,15,2] [-124963,-251024,-213826,-100104,-27816,-4588,-416,-16] [1] [4806,6882,3884,1080,148,8] [-1] [4621,6724,3840,1076,148,8]
  | 80 => six [26,15,2] [-2518,-3638,-2052,-565,-76,-4] [-1] [65371,132274,112935,52744,14555,2374,212,8] [27,15,2] [-101,-85,-23,-2]
  | 81 => six [1] [67,20] [-3] [-13,-4] [1] [17,5]
  | 82 => six [515,223,24] [-529,-226,-24] [19573,12594,2696,192] [1] [-1] [-37,-8]
  | 83 => six [100,21] [-97,-21] [-3700,-1577,-168] [1] [37,8] [1]
  | 84 => six [268,183,41,3] [53,26,3] [-1326,-1180,-388,-56,-3] [-1] [5,1] [-4,-1]
  | 85 => six [38,8] [-1] [-19573,-12594,-2696,-192] [1] [14,3] [515,223,24]
  | 86 => six [1] [-1] [-97,-21] [38,8] [-3] [3700,1577,168]
  | 87 => six [-1] [-67,-20] [3] [-13,-4] [-2] [-184,-55]
  | 88 => six [-1] [68098,136084,115033,53313,14631,2378,212,8] [-26,-15,-2] [2518,3638,2052,565,76,4] [-1] [2619,3723,2075,567,76,4]
  | 89 => six [1] [124963,251024,213826,100104,27816,4588,416,16] [-27,-15,-2] [4621,6724,3840,1076,148,8] [26,15,2] [3373816,8651935,9788544,6412242,2680244,741324,135684,15848,1072,32]
  | 90 => six [-1] [-2518,-3638,-2052,-565,-76,-4] [1] [68098,136084,115033,53313,14631,2378,212,8] [-27,-15,-2] [101,85,23,2]
  | 91 => six [-19573,-12594,-2696,-192] [743760,635153,203200,28864,1536] [-515,-223,-24] [-38,-8] [1] [-37,-8]
  | 92 => six [-140597,-89526,-19000,-1344] [3700,1577,168] [97,21] [-38,-8] [37,8] [-1]
  | _ => six [1] [-2518,-3638,-2052,-565,-76,-4] [-26,-15,-2] [-68098,-136084,-115033,-53313,-14631,-2378,-212,-8] [27,15,2] [-1838545,-4695653,-5283324,-3437112,-1424798,-390297,-70656,-8152,-544,-16]

def node (t : Int) (i : Fin 94) : Matrix 4 := matrix (pnode i) t
def Core (t : Int) (B : Matrix 4) : Prop := ∃ i, B=node t i
abbrev SafeCore (t : Int) := Safe data (Core t)
theorem node_safe (t : Int) (i : Fin 94) : SafeCore t (node t i) := Safe.central ⟨i,rfl⟩

def param0_0 : P := [4,1]
def param0_1 : P := [66,53,13,1]
def param0_2 : P := [15,8,1]
def param0_3 : P := [17,9,1]
theorem domain0 (t : Int) (ht : 0≤t) : GenericStrip.Domain (eval param0_0 t) (eval param0_1 t) (eval param0_2 t) (eval param0_3 t) :=
  generic_domain param0_0 param0_1 param0_2 param0_3 t ht (by decide)

def region0 (t : Int) (ht : 0≤t) : Region := .inl (.inl ⟨eval param0_0 t,⟨eval param0_1 t,eval param0_2 t,eval param0_3 t⟩,domain0 t ht⟩)

theorem parent0_0 (t : Int) (ht : 0≤t) :
    data.parent (region0 t ht) (0 : Fin 3)=(reverse (relabel (node t 38) perm22.symm)) := by
  have he := mutation_equal (generic param0_0 param0_1 param0_2 param0_3 0) (preverse (prelabel (pnode 38) perm22.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent0_1 (t : Int) (ht : 0≤t) :
    data.parent (region0 t ht) (1 : Fin 3)=(reverse (relabel (node t 11) perm18.symm)) := by
  have he := mutation_equal (generic param0_0 param0_1 param0_2 param0_3 0) (preverse (prelabel (pnode 11) perm18.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent0_2 (t : Int) (ht : 0≤t) :
    data.parent (region0 t ht) (2 : Fin 3)=(reverse (relabel (node t 39) perm18.symm)) := by
  have he := mutation_equal (generic param0_0 param0_1 param0_2 param0_3 2) (preverse (prelabel (pnode 39) perm18.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parents0_safe (t : Int) (ht : 0≤t) (p : Fin 3) :
    SafeCore t (data.parent (region0 t ht) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hp with rfl|rfl|rfl
  · rw [parent0_0 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 38) perm22.symm)
  · rw [parent0_1 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 11) perm18.symm)
  · rw [parent0_2 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 39) perm18.symm)

theorem region0_safe (t : Int) (ht : 0≤t) (i : Fin 3) :
    SafeCore t (matrix (generic param0_0 param0_1 param0_2 param0_3 i) t) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core t) (region0 t ht) (parents0_safe t ht) (0,Fin.castLE (by decide) i)

def param1_0 : P := [2]
def param1_1 : P := [48,3]
def param1_2 : P := [17,2]
def param1_3 : P := [25,2]
theorem domain1 (t : Int) (ht : 0≤t) : GenericStrip.Domain (eval param1_0 t) (eval param1_1 t) (eval param1_2 t) (eval param1_3 t) :=
  generic_domain param1_0 param1_1 param1_2 param1_3 t ht (by decide)

def region1 (t : Int) (ht : 0≤t) : Region := .inl (.inl ⟨eval param1_0 t,⟨eval param1_1 t,eval param1_2 t,eval param1_3 t⟩,domain1 t ht⟩)

theorem parent1_0 (t : Int) (ht : 0≤t) :
    data.parent (region1 t ht) (0 : Fin 3)=(reverse (relabel (node t 55) perm7.symm)) := by
  have he := mutation_equal (generic param1_0 param1_1 param1_2 param1_3 0) (preverse (prelabel (pnode 55) perm7.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent1_1 (t : Int) (ht : 0≤t) :
    data.parent (region1 t ht) (1 : Fin 3)=(reverse (relabel (node t 32) perm1.symm)) := by
  have he := mutation_equal (generic param1_0 param1_1 param1_2 param1_3 0) (preverse (prelabel (pnode 32) perm1.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent1_2 (t : Int) (ht : 0≤t) :
    data.parent (region1 t ht) (2 : Fin 3)=(reverse (relabel (node t 62) perm1.symm)) := by
  have he := mutation_equal (generic param1_0 param1_1 param1_2 param1_3 2) (preverse (prelabel (pnode 62) perm1.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parents1_safe (t : Int) (ht : 0≤t) (p : Fin 3) :
    SafeCore t (data.parent (region1 t ht) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hp with rfl|rfl|rfl
  · rw [parent1_0 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 55) perm7.symm)
  · rw [parent1_1 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 32) perm1.symm)
  · rw [parent1_2 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 62) perm1.symm)

theorem region1_safe (t : Int) (ht : 0≤t) (i : Fin 3) :
    SafeCore t (matrix (generic param1_0 param1_1 param1_2 param1_3 i) t) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core t) (region1 t ht) (parents1_safe t ht) (0,Fin.castLE (by decide) i)

def param2_0 : P := [4,1]
def param2_1 : P := [268,183,41,3]
def param2_2 : P := [53,26,3]
def param2_3 : P := [67,29,3]
theorem domain2 (t : Int) (ht : 0≤t) : GenericStrip.Domain (eval param2_0 t) (eval param2_1 t) (eval param2_2 t) (eval param2_3 t) :=
  generic_domain param2_0 param2_1 param2_2 param2_3 t ht (by decide)

def region2 (t : Int) (ht : 0≤t) : Region := .inl (.inl ⟨eval param2_0 t,⟨eval param2_1 t,eval param2_2 t,eval param2_3 t⟩,domain2 t ht⟩)

theorem parent2_0 (t : Int) (ht : 0≤t) :
    data.parent (region2 t ht) (0 : Fin 3)=(relabel (node t 72) perm18.symm) := by
  have he := mutation_equal (generic param2_0 param2_1 param2_2 param2_3 0) (prelabel (pnode 72) perm18.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent2_1 (t : Int) (ht : 0≤t) :
    data.parent (region2 t ht) (1 : Fin 3)=(relabel (node t 59) perm19.symm) := by
  have he := mutation_equal (generic param2_0 param2_1 param2_2 param2_3 0) (prelabel (pnode 59) perm19.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent2_2 (t : Int) (ht : 0≤t) :
    data.parent (region2 t ht) (2 : Fin 3)=(relabel (node t 84) perm20.symm) := by
  have he := mutation_equal (generic param2_0 param2_1 param2_2 param2_3 2) (prelabel (pnode 84) perm20.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parents2_safe (t : Int) (ht : 0≤t) (p : Fin 3) :
    SafeCore t (data.parent (region2 t ht) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hp with rfl|rfl|rfl
  · rw [parent2_0 t ht]
    exact Safe.framed (node_safe t 72) perm18.symm
  · rw [parent2_1 t ht]
    exact Safe.framed (node_safe t 59) perm19.symm
  · rw [parent2_2 t ht]
    exact Safe.framed (node_safe t 84) perm20.symm

theorem region2_safe (t : Int) (ht : 0≤t) (i : Fin 3) :
    SafeCore t (matrix (generic param2_0 param2_1 param2_2 param2_3 i) t) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core t) (region2 t ht) (parents2_safe t ht) (0,Fin.castLE (by decide) i)

def param3_0 : P := [2]
def param3_1 : P := [67,20]
def param3_2 : P := [13,4]
def param3_3 : P := [30,9]
theorem domain3 (t : Int) (ht : 0≤t) : GenericStrip.Domain (eval param3_0 t) (eval param3_1 t) (eval param3_2 t) (eval param3_3 t) :=
  generic_domain param3_0 param3_1 param3_2 param3_3 t ht (by decide)

def region3 (t : Int) (ht : 0≤t) : Region := .inl (.inl ⟨eval param3_0 t,⟨eval param3_1 t,eval param3_2 t,eval param3_3 t⟩,domain3 t ht⟩)

theorem parent3_0 (t : Int) (ht : 0≤t) :
    data.parent (region3 t ht) (0 : Fin 3)=(relabel (node t 81) perm1.symm) := by
  have he := mutation_equal (generic param3_0 param3_1 param3_2 param3_3 0) (prelabel (pnode 81) perm1.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent3_1 (t : Int) (ht : 0≤t) :
    data.parent (region3 t ht) (1 : Fin 3)=(relabel (node t 63) perm7.symm) := by
  have he := mutation_equal (generic param3_0 param3_1 param3_2 param3_3 0) (prelabel (pnode 63) perm7.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent3_2 (t : Int) (ht : 0≤t) :
    data.parent (region3 t ht) (2 : Fin 3)=(relabel (node t 87) perm7.symm) := by
  have he := mutation_equal (generic param3_0 param3_1 param3_2 param3_3 2) (prelabel (pnode 87) perm7.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parents3_safe (t : Int) (ht : 0≤t) (p : Fin 3) :
    SafeCore t (data.parent (region3 t ht) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hp with rfl|rfl|rfl
  · rw [parent3_0 t ht]
    exact Safe.framed (node_safe t 81) perm1.symm
  · rw [parent3_1 t ht]
    exact Safe.framed (node_safe t 63) perm7.symm
  · rw [parent3_2 t ht]
    exact Safe.framed (node_safe t 87) perm7.symm

theorem region3_safe (t : Int) (ht : 0≤t) (i : Fin 3) :
    SafeCore t (matrix (generic param3_0 param3_1 param3_2 param3_3 i) t) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core t) (region3 t ht) (parents3_safe t ht) (0,Fin.castLE (by decide) i)

def param4_0 : P := [26,15,2]
def param4_1 : P := [124963,251024,213826,100104,27816,4588,416,16]
def param4_2 : P := [4621,6724,3840,1076,148,8]
def param4_3 : P := [4806,6882,3884,1080,148,8]
theorem domain4 (t : Int) (ht : 0≤t) : GenericStrip.Domain (eval param4_0 t) (eval param4_1 t) (eval param4_2 t) (eval param4_3 t) :=
  generic_domain param4_0 param4_1 param4_2 param4_3 t ht (by decide)

def region4 (t : Int) (ht : 0≤t) : Region := .inl (.inl ⟨eval param4_0 t,⟨eval param4_1 t,eval param4_2 t,eval param4_3 t⟩,domain4 t ht⟩)

theorem parent4_0 (t : Int) (ht : 0≤t) :
    data.parent (region4 t ht) (0 : Fin 3)=(reverse (relabel (node t 78) perm1.symm)) := by
  have he := mutation_equal (generic param4_0 param4_1 param4_2 param4_3 0) (preverse (prelabel (pnode 78) perm1.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent4_1 (t : Int) (ht : 0≤t) :
    data.parent (region4 t ht) (1 : Fin 3)=(reverse (relabel (node t 66) perm3.symm)) := by
  have he := mutation_equal (generic param4_0 param4_1 param4_2 param4_3 0) (preverse (prelabel (pnode 66) perm3.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent4_2 (t : Int) (ht : 0≤t) :
    data.parent (region4 t ht) (2 : Fin 3)=(reverse (relabel (node t 89) perm7.symm)) := by
  have he := mutation_equal (generic param4_0 param4_1 param4_2 param4_3 2) (preverse (prelabel (pnode 89) perm7.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parents4_safe (t : Int) (ht : 0≤t) (p : Fin 3) :
    SafeCore t (data.parent (region4 t ht) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hp with rfl|rfl|rfl
  · rw [parent4_0 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 78) perm1.symm)
  · rw [parent4_1 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 66) perm3.symm)
  · rw [parent4_2 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 89) perm7.symm)

theorem region4_safe (t : Int) (ht : 0≤t) (i : Fin 3) :
    SafeCore t (matrix (generic param4_0 param4_1 param4_2 param4_3 i) t) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core t) (region4 t ht) (parents4_safe t ht) (0,Fin.castLE (by decide) i)

def param5_0 : P := [37,8]
def param5_1 : P := [19573,12594,2696,192]
def param5_2 : P := [515,223,24]
def param5_3 : P := [529,226,24]
theorem domain5 (t : Int) (ht : 0≤t) : GenericStrip.Domain (eval param5_0 t) (eval param5_1 t) (eval param5_2 t) (eval param5_3 t) :=
  generic_domain param5_0 param5_1 param5_2 param5_3 t ht (by decide)

def region5 (t : Int) (ht : 0≤t) : Region := .inl (.inl ⟨eval param5_0 t,⟨eval param5_1 t,eval param5_2 t,eval param5_3 t⟩,domain5 t ht⟩)

theorem parent5_0 (t : Int) (ht : 0≤t) :
    data.parent (region5 t ht) (0 : Fin 3)=(reverse (relabel (node t 85) perm2.symm)) := by
  have he := mutation_equal (generic param5_0 param5_1 param5_2 param5_3 0) (preverse (prelabel (pnode 85) perm2.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent5_1 (t : Int) (ht : 0≤t) :
    data.parent (region5 t ht) (1 : Fin 3)=(reverse (relabel (node t 70) perm21.symm)) := by
  have he := mutation_equal (generic param5_0 param5_1 param5_2 param5_3 0) (preverse (prelabel (pnode 70) perm21.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent5_2 (t : Int) (ht : 0≤t) :
    data.parent (region5 t ht) (2 : Fin 3)=(reverse (relabel (node t 91) perm21.symm)) := by
  have he := mutation_equal (generic param5_0 param5_1 param5_2 param5_3 2) (preverse (prelabel (pnode 91) perm21.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parents5_safe (t : Int) (ht : 0≤t) (p : Fin 3) :
    SafeCore t (data.parent (region5 t ht) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hp with rfl|rfl|rfl
  · rw [parent5_0 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 85) perm2.symm)
  · rw [parent5_1 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 70) perm21.symm)
  · rw [parent5_2 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 91) perm21.symm)

theorem region5_safe (t : Int) (ht : 0≤t) (i : Fin 3) :
    SafeCore t (matrix (generic param5_0 param5_1 param5_2 param5_3 i) t) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core t) (region5 t ht) (parents5_safe t ht) (0,Fin.castLE (by decide) i)

def param6_0 : P := [37,8]
def param6_1 : P := [3700,1577,168]
def param6_2 : P := [97,21]
def param6_3 : P := [100,21]
theorem domain6 (t : Int) (ht : 0≤t) : GenericStrip.Domain (eval param6_0 t) (eval param6_1 t) (eval param6_2 t) (eval param6_3 t) :=
  generic_domain param6_0 param6_1 param6_2 param6_3 t ht (by decide)

def region6 (t : Int) (ht : 0≤t) : Region := .inl (.inl ⟨eval param6_0 t,⟨eval param6_1 t,eval param6_2 t,eval param6_3 t⟩,domain6 t ht⟩)

theorem parent6_0 (t : Int) (ht : 0≤t) :
    data.parent (region6 t ht) (0 : Fin 3)=(relabel (node t 86) perm8.symm) := by
  have he := mutation_equal (generic param6_0 param6_1 param6_2 param6_3 0) (prelabel (pnode 86) perm8.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent6_1 (t : Int) (ht : 0≤t) :
    data.parent (region6 t ht) (1 : Fin 3)=(relabel (node t 71) perm23.symm) := by
  have he := mutation_equal (generic param6_0 param6_1 param6_2 param6_3 0) (prelabel (pnode 71) perm23.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent6_2 (t : Int) (ht : 0≤t) :
    data.parent (region6 t ht) (2 : Fin 3)=(relabel (node t 92) perm23.symm) := by
  have he := mutation_equal (generic param6_0 param6_1 param6_2 param6_3 2) (prelabel (pnode 92) perm23.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parents6_safe (t : Int) (ht : 0≤t) (p : Fin 3) :
    SafeCore t (data.parent (region6 t ht) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hp with rfl|rfl|rfl
  · rw [parent6_0 t ht]
    exact Safe.framed (node_safe t 86) perm8.symm
  · rw [parent6_1 t ht]
    exact Safe.framed (node_safe t 71) perm23.symm
  · rw [parent6_2 t ht]
    exact Safe.framed (node_safe t 92) perm23.symm

theorem region6_safe (t : Int) (ht : 0≤t) (i : Fin 3) :
    SafeCore t (matrix (generic param6_0 param6_1 param6_2 param6_3 i) t) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core t) (region6 t ht) (parents6_safe t ht) (0,Fin.castLE (by decide) i)

def param7_0 : P := [26,15,2]
def param7_1 : P := [68098,136084,115033,53313,14631,2378,212,8]
def param7_2 : P := [2518,3638,2052,565,76,4]
def param7_3 : P := [2619,3723,2075,567,76,4]
theorem domain7 (t : Int) (ht : 0≤t) : GenericStrip.Domain (eval param7_0 t) (eval param7_1 t) (eval param7_2 t) (eval param7_3 t) :=
  generic_domain param7_0 param7_1 param7_2 param7_3 t ht (by decide)

def region7 (t : Int) (ht : 0≤t) : Region := .inl (.inl ⟨eval param7_0 t,⟨eval param7_1 t,eval param7_2 t,eval param7_3 t⟩,domain7 t ht⟩)

theorem parent7_0 (t : Int) (ht : 0≤t) :
    data.parent (region7 t ht) (0 : Fin 3)=(relabel (node t 90) perm7.symm) := by
  have he := mutation_equal (generic param7_0 param7_1 param7_2 param7_3 0) (prelabel (pnode 90) perm7.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent7_1 (t : Int) (ht : 0≤t) :
    data.parent (region7 t ht) (1 : Fin 3)=(relabel (node t 77) perm1.symm) := by
  have he := mutation_equal (generic param7_0 param7_1 param7_2 param7_3 0) (prelabel (pnode 77) perm1.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parent7_2 (t : Int) (ht : 0≤t) :
    data.parent (region7 t ht) (2 : Fin 3)=(relabel (node t 93) perm1.symm) := by
  have he := mutation_equal (generic param7_0 param7_1 param7_2 param7_3 2) (prelabel (pnode 93) perm1.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem parents7_safe (t : Int) (ht : 0≤t) (p : Fin 3) :
    SafeCore t (data.parent (region7 t ht) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hp with rfl|rfl|rfl
  · rw [parent7_0 t ht]
    exact Safe.framed (node_safe t 90) perm7.symm
  · rw [parent7_1 t ht]
    exact Safe.framed (node_safe t 77) perm1.symm
  · rw [parent7_2 t ht]
    exact Safe.framed (node_safe t 93) perm1.symm

theorem region7_safe (t : Int) (ht : 0≤t) (i : Fin 3) :
    SafeCore t (matrix (generic param7_0 param7_1 param7_2 param7_3 i) t) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core t) (region7 t ht) (parents7_safe t ht) (0,Fin.castLE (by decide) i)

def param8_0 : P := [7,2]
def param8_1 : P := [3]
def param8_2 : P := [10,3]
def param8_3 : P := [68,41,6]
theorem domain8 (t : Int) (ht : 0≤t) : UnitZeroStrip.Domain (eval param8_0 t) (eval param8_1 t) (eval param8_2 t) (eval param8_3 t) :=
  zero_domain param8_0 param8_1 param8_2 param8_3 t ht (by decide)

def region8 (t : Int) (ht : 0≤t) : Region := .inl (.inr (.n (eval param8_0 t) ⟨eval param8_1 t,eval param8_2 t,eval param8_3 t⟩ (domain8 t ht)))

theorem parent8_0 (t : Int) (ht : 0≤t) :
    data.parent (region8 t ht) (0 : Fin 2)=(relabel (node t 20) perm17.symm) := by
  have he := mutation_equal (zero param8_0 param8_1 param8_2 param8_3 0) (prelabel (pnode 20) perm17.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,zero_eval] at he
  exact he

theorem parent8_1 (t : Int) (ht : 0≤t) :
    data.parent (region8 t ht) (1 : Fin 2)=(relabel (node t 33) perm17.symm) := by
  have he := mutation_equal (zero param8_0 param8_1 param8_2 param8_3 1) (prelabel (pnode 33) perm17.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,zero_eval] at he
  exact he

theorem parents8_safe (t : Int) (ht : 0≤t) (p : Fin 2) :
    SafeCore t (data.parent (region8 t ht) p) := by
  have hp : p=0 ∨ p=1 := by change p=(0 : Fin 2) ∨ p=(1 : Fin 2); omega
  rcases hp with rfl|rfl
  · rw [parent8_0 t ht]
    exact Safe.framed (node_safe t 20) perm17.symm
  · rw [parent8_1 t ht]
    exact Safe.framed (node_safe t 33) perm17.symm

theorem region8_safe (t : Int) (ht : 0≤t) (i : Fin 2) :
    SafeCore t (matrix (zero param8_0 param8_1 param8_2 param8_3 i) t) := by
  rw [zero_eval]
  exact Safe.region (D:=data) (core:=Core t) (region8 t ht) (parents8_safe t ht) (0,Fin.castLE (by decide) i)

def param9_0 : P := [3]
def param9_1 : P := [15,1]
def param9_2 : P := [34]
def param9_3 : P := [89]
theorem domain9 (t : Int) (ht : 0≤t) : UnitZeroStrip.Domain (eval param9_0 t) (eval param9_1 t) (eval param9_2 t) (eval param9_3 t) :=
  zero_domain param9_0 param9_1 param9_2 param9_3 t ht (by decide)

def region9 (t : Int) (ht : 0≤t) : Region := .inl (.inr (.n (eval param9_0 t) ⟨eval param9_1 t,eval param9_2 t,eval param9_3 t⟩ (domain9 t ht)))

theorem parent9_0 (t : Int) (ht : 0≤t) :
    data.parent (region9 t ht) (0 : Fin 2)=(reverse (relabel (node t 28) perm16.symm)) := by
  have he := mutation_equal (zero param9_0 param9_1 param9_2 param9_3 0) (preverse (prelabel (pnode 28) perm16.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,zero_eval] at he
  exact he

theorem parent9_1 (t : Int) (ht : 0≤t) :
    data.parent (region9 t ht) (1 : Fin 2)=(reverse (relabel (node t 44) perm16.symm)) := by
  have he := mutation_equal (zero param9_0 param9_1 param9_2 param9_3 1) (preverse (prelabel (pnode 44) perm16.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,zero_eval] at he
  exact he

theorem parents9_safe (t : Int) (ht : 0≤t) (p : Fin 2) :
    SafeCore t (data.parent (region9 t ht) p) := by
  have hp : p=0 ∨ p=1 := by change p=(0 : Fin 2) ∨ p=(1 : Fin 2); omega
  rcases hp with rfl|rfl
  · rw [parent9_0 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 28) perm16.symm)
  · rw [parent9_1 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 44) perm16.symm)

theorem region9_safe (t : Int) (ht : 0≤t) (i : Fin 2) :
    SafeCore t (matrix (zero param9_0 param9_1 param9_2 param9_3 i) t) := by
  rw [zero_eval]
  exact Safe.region (D:=data) (core:=Core t) (region9 t ht) (parents9_safe t ht) (0,Fin.castLE (by decide) i)

def param10_0 : P := [4,1]
def param10_1 : P := [2,1]
def param10_2 : P := [19,9,1]
def param10_3 : P := [71,54,13,1]
theorem domain10 (t : Int) (ht : 0≤t) : UnitZeroStrip.Domain (eval param10_0 t) (eval param10_1 t) (eval param10_2 t) (eval param10_3 t) :=
  zero_domain param10_0 param10_1 param10_2 param10_3 t ht (by decide)

def region10 (t : Int) (ht : 0≤t) : Region := .inl (.inr (.n (eval param10_0 t) ⟨eval param10_1 t,eval param10_2 t,eval param10_3 t⟩ (domain10 t ht)))

theorem parent10_0 (t : Int) (ht : 0≤t) :
    data.parent (region10 t ht) (0 : Fin 2)=(reverse (relabel (node t 30) perm21.symm)) := by
  have he := mutation_equal (zero param10_0 param10_1 param10_2 param10_3 0) (preverse (prelabel (pnode 30) perm21.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,zero_eval] at he
  exact he

theorem parent10_1 (t : Int) (ht : 0≤t) :
    data.parent (region10 t ht) (1 : Fin 2)=(reverse (relabel (node t 29) perm0.symm)) := by
  have he := mutation_equal (zero param10_0 param10_1 param10_2 param10_3 1) (preverse (prelabel (pnode 29) perm0.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,zero_eval] at he
  exact he

theorem parents10_safe (t : Int) (ht : 0≤t) (p : Fin 2) :
    SafeCore t (data.parent (region10 t ht) p) := by
  have hp : p=0 ∨ p=1 := by change p=(0 : Fin 2) ∨ p=(1 : Fin 2); omega
  rcases hp with rfl|rfl
  · rw [parent10_0 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 30) perm21.symm)
  · rw [parent10_1 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 29) perm0.symm)

theorem region10_safe (t : Int) (ht : 0≤t) (i : Fin 2) :
    SafeCore t (matrix (zero param10_0 param10_1 param10_2 param10_3 i) t) := by
  rw [zero_eval]
  exact Safe.region (D:=data) (core:=Core t) (region10 t ht) (parents10_safe t ht) (0,Fin.castLE (by decide) i)

def param11_0 : P := [4,1]
def param11_1 : P := [27,15,2]
def param11_2 : P := [97,84,23,2]
def param11_3 : P := [362,418,174,31,2]
theorem domain11 (t : Int) (ht : 0≤t) : UnitZeroStrip.Domain (eval param11_0 t) (eval param11_1 t) (eval param11_2 t) (eval param11_3 t) :=
  zero_domain param11_0 param11_1 param11_2 param11_3 t ht (by decide)

def region11 (t : Int) (ht : 0≤t) : Region := .inl (.inr (.n (eval param11_0 t) ⟨eval param11_1 t,eval param11_2 t,eval param11_3 t⟩ (domain11 t ht)))

theorem parent11_0 (t : Int) (ht : 0≤t) :
    data.parent (region11 t ht) (0 : Fin 2)=(relabel (node t 34) perm23.symm) := by
  have he := mutation_equal (zero param11_0 param11_1 param11_2 param11_3 0) (prelabel (pnode 34) perm23.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,zero_eval] at he
  exact he

theorem parent11_1 (t : Int) (ht : 0≤t) :
    data.parent (region11 t ht) (1 : Fin 2)=(relabel (node t 49) perm23.symm) := by
  have he := mutation_equal (zero param11_0 param11_1 param11_2 param11_3 1) (prelabel (pnode 49) perm23.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,zero_eval] at he
  exact he

theorem parents11_safe (t : Int) (ht : 0≤t) (p : Fin 2) :
    SafeCore t (data.parent (region11 t ht) p) := by
  have hp : p=0 ∨ p=1 := by change p=(0 : Fin 2) ∨ p=(1 : Fin 2); omega
  rcases hp with rfl|rfl
  · rw [parent11_0 t ht]
    exact Safe.framed (node_safe t 34) perm23.symm
  · rw [parent11_1 t ht]
    exact Safe.framed (node_safe t 49) perm23.symm

theorem region11_safe (t : Int) (ht : 0≤t) (i : Fin 2) :
    SafeCore t (matrix (zero param11_0 param11_1 param11_2 param11_3 i) t) := by
  rw [zero_eval]
  exact Safe.region (D:=data) (core:=Core t) (region11 t ht) (parents11_safe t ht) (0,Fin.castLE (by decide) i)

def param12_0 : P := [14,3]
def param12_1 : P := [4,1]
def param12_2 : P := [67,29,3]
def param12_3 : P := [933,606,129,9]
theorem domain12 (t : Int) (ht : 0≤t) : UnitZeroStrip.Domain (eval param12_0 t) (eval param12_1 t) (eval param12_2 t) (eval param12_3 t) :=
  zero_domain param12_0 param12_1 param12_2 param12_3 t ht (by decide)

def region12 (t : Int) (ht : 0≤t) : Region := .inl (.inr (.n (eval param12_0 t) ⟨eval param12_1 t,eval param12_2 t,eval param12_3 t⟩ (domain12 t ht)))

theorem parent12_0 (t : Int) (ht : 0≤t) :
    data.parent (region12 t ht) (0 : Fin 2)=(relabel (node t 45) perm19.symm) := by
  have he := mutation_equal (zero param12_0 param12_1 param12_2 param12_3 0) (prelabel (pnode 45) perm19.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,zero_eval] at he
  exact he

theorem parent12_1 (t : Int) (ht : 0≤t) :
    data.parent (region12 t ht) (1 : Fin 2)=(relabel (node t 59) perm6.symm) := by
  have he := mutation_equal (zero param12_0 param12_1 param12_2 param12_3 1) (prelabel (pnode 59) perm6.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,zero_eval] at he
  exact he

theorem parents12_safe (t : Int) (ht : 0≤t) (p : Fin 2) :
    SafeCore t (data.parent (region12 t ht) p) := by
  have hp : p=0 ∨ p=1 := by change p=(0 : Fin 2) ∨ p=(1 : Fin 2); omega
  rcases hp with rfl|rfl
  · rw [parent12_0 t ht]
    exact Safe.framed (node_safe t 45) perm19.symm
  · rw [parent12_1 t ht]
    exact Safe.framed (node_safe t 59) perm6.symm

theorem region12_safe (t : Int) (ht : 0≤t) (i : Fin 2) :
    SafeCore t (matrix (zero param12_0 param12_1 param12_2 param12_3 i) t) := by
  rw [zero_eval]
  exact Safe.region (D:=data) (core:=Core t) (region12 t ht) (parents12_safe t ht) (0,Fin.castLE (by decide) i)

def param13_0 : P := [7,2]
def param13_1 : P := [27,15,2]
def param13_2 : P := [178,156,44,4]
def param13_3 : P := [1220,1433,618,116,8]
theorem domain13 (t : Int) (ht : 0≤t) : UnitZeroStrip.Domain (eval param13_0 t) (eval param13_1 t) (eval param13_2 t) (eval param13_3 t) :=
  zero_domain param13_0 param13_1 param13_2 param13_3 t ht (by decide)

def region13 (t : Int) (ht : 0≤t) : Region := .inl (.inr (.n (eval param13_0 t) ⟨eval param13_1 t,eval param13_2 t,eval param13_3 t⟩ (domain13 t ht)))

theorem parent13_0 (t : Int) (ht : 0≤t) :
    data.parent (region13 t ht) (0 : Fin 2)=(reverse (relabel (node t 53) perm17.symm)) := by
  have he := mutation_equal (zero param13_0 param13_1 param13_2 param13_3 0) (preverse (prelabel (pnode 53) perm17.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,zero_eval] at he
  exact he

theorem parent13_1 (t : Int) (ht : 0≤t) :
    data.parent (region13 t ht) (1 : Fin 2)=(reverse (relabel (node t 51) perm12.symm)) := by
  have he := mutation_equal (zero param13_0 param13_1 param13_2 param13_3 1) (preverse (prelabel (pnode 51) perm12.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,zero_eval] at he
  exact he

theorem parents13_safe (t : Int) (ht : 0≤t) (p : Fin 2) :
    SafeCore t (data.parent (region13 t ht) p) := by
  have hp : p=0 ∨ p=1 := by change p=(0 : Fin 2) ∨ p=(1 : Fin 2); omega
  rcases hp with rfl|rfl
  · rw [parent13_0 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 53) perm17.symm)
  · rw [parent13_1 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 51) perm12.symm)

theorem region13_safe (t : Int) (ht : 0≤t) (i : Fin 2) :
    SafeCore t (matrix (zero param13_0 param13_1 param13_2 param13_3 i) t) := by
  rw [zero_eval]
  exact Safe.region (D:=data) (core:=Core t) (region13 t ht) (parents13_safe t ht) (0,Fin.castLE (by decide) i)

def param14_0 : P := [14,3]
def param14_1 : P := [37,8]
def param14_2 : P := [529,226,24]
def param14_3 : P := [7368,4743,1014,72]
theorem domain14 (t : Int) (ht : 0≤t) : UnitZeroStrip.Domain (eval param14_0 t) (eval param14_1 t) (eval param14_2 t) (eval param14_3 t) :=
  zero_domain param14_0 param14_1 param14_2 param14_3 t ht (by decide)

def region14 (t : Int) (ht : 0≤t) : Region := .inl (.inr (.n (eval param14_0 t) ⟨eval param14_1 t,eval param14_2 t,eval param14_3 t⟩ (domain14 t ht)))

theorem parent14_0 (t : Int) (ht : 0≤t) :
    data.parent (region14 t ht) (0 : Fin 2)=(reverse (relabel (node t 56) perm11.symm)) := by
  have he := mutation_equal (zero param14_0 param14_1 param14_2 param14_3 0) (preverse (prelabel (pnode 56) perm11.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,zero_eval] at he
  exact he

theorem parent14_1 (t : Int) (ht : 0≤t) :
    data.parent (region14 t ht) (1 : Fin 2)=(reverse (relabel (node t 70) perm11.symm)) := by
  have he := mutation_equal (zero param14_0 param14_1 param14_2 param14_3 1) (preverse (prelabel (pnode 70) perm11.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,zero_eval] at he
  exact he

theorem parents14_safe (t : Int) (ht : 0≤t) (p : Fin 2) :
    SafeCore t (data.parent (region14 t ht) p) := by
  have hp : p=0 ∨ p=1 := by change p=(0 : Fin 2) ∨ p=(1 : Fin 2); omega
  rcases hp with rfl|rfl
  · rw [parent14_0 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 56) perm11.symm)
  · rw [parent14_1 t ht]
    exact Safe.reversed (Safe.framed (node_safe t 70) perm11.symm)

theorem region14_safe (t : Int) (ht : 0≤t) (i : Fin 2) :
    SafeCore t (matrix (zero param14_0 param14_1 param14_2 param14_3 i) t) := by
  rw [zero_eval]
  exact Safe.region (D:=data) (core:=Core t) (region14 t ht) (parents14_safe t ht) (0,Fin.castLE (by decide) i)

def param15_0 : P := [3]
def param15_1 : P := [37,8]
def param15_2 : P := [100,21]
def param15_3 : P := [262,55]
theorem domain15 (t : Int) (ht : 0≤t) : UnitZeroStrip.Domain (eval param15_0 t) (eval param15_1 t) (eval param15_2 t) (eval param15_3 t) :=
  zero_domain param15_0 param15_1 param15_2 param15_3 t ht (by decide)

def region15 (t : Int) (ht : 0≤t) : Region := .inl (.inr (.n (eval param15_0 t) ⟨eval param15_1 t,eval param15_2 t,eval param15_3 t⟩ (domain15 t ht)))

theorem parent15_0 (t : Int) (ht : 0≤t) :
    data.parent (region15 t ht) (0 : Fin 2)=(relabel (node t 57) perm9.symm) := by
  have he := mutation_equal (zero param15_0 param15_1 param15_2 param15_3 0) (prelabel (pnode 57) perm9.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,zero_eval] at he
  exact he

theorem parent15_1 (t : Int) (ht : 0≤t) :
    data.parent (region15 t ht) (1 : Fin 2)=(relabel (node t 71) perm9.symm) := by
  have he := mutation_equal (zero param15_0 param15_1 param15_2 param15_3 1) (prelabel (pnode 71) perm9.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,zero_eval] at he
  exact he

theorem parents15_safe (t : Int) (ht : 0≤t) (p : Fin 2) :
    SafeCore t (data.parent (region15 t ht) p) := by
  have hp : p=0 ∨ p=1 := by change p=(0 : Fin 2) ∨ p=(1 : Fin 2); omega
  rcases hp with rfl|rfl
  · rw [parent15_0 t ht]
    exact Safe.framed (node_safe t 57) perm9.symm
  · rw [parent15_1 t ht]
    exact Safe.framed (node_safe t 71) perm9.symm

theorem region15_safe (t : Int) (ht : 0≤t) (i : Fin 2) :
    SafeCore t (matrix (zero param15_0 param15_1 param15_2 param15_3 i) t) := by
  rw [zero_eval]
  exact Safe.region (D:=data) (core:=Core t) (region15 t ht) (parents15_safe t ht) (0,Fin.castLE (by decide) i)

theorem node_skew (t : Int) (i : Fin 94) : SkewSymmetric (node t i) := by
  rcases finCore i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp only [node,pnode,matrix_six] <;> exact ofSix_skew _ _ _ _ _ _

theorem cyclic0 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 0) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 0 0 2) t ht (by decide))
  have h1 := hr 2 3 (pos (pnode 0 2 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 0 3 0) t ht (by decide))
  omega

theorem cyclic1 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 1) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 1 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (pnode 1 3 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 1 1 0) t ht (by decide))
  omega

theorem cyclic2 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 2) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 2 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 2 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 2 1 0) t ht (by decide))
  omega

theorem cyclic3 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 3) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 3 0 3) t ht (by decide))
  have h1 := hr 3 2 (pos (pnode 3 3 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 3 2 0) t ht (by decide))
  omega

theorem cyclic4 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 4) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 4 0 3) t ht (by decide))
  have h1 := hr 3 2 (pos (pnode 4 3 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 4 2 0) t ht (by decide))
  omega

theorem cyclic5 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 5) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 5 0 1) t ht (by decide))
  have h1 := hr 1 3 (pos (pnode 5 1 3) t ht (by decide))
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
  have h0 := hr 0 1 (pos (pnode 7 0 1) t ht (by decide))
  have h1 := hr 1 3 (pos (pnode 7 1 3) t ht (by decide))
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
  have h1 := hr 1 2 (pos (pnode 9 1 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 9 2 0) t ht (by decide))
  omega

theorem cyclic10 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 10) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 10 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (pnode 10 3 1) t ht (by decide))
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
  have h0 := hr 0 2 (pos (pnode 12 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 12 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 12 1 0) t ht (by decide))
  omega

theorem cyclic13 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 13) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 13 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (pnode 13 3 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 13 1 0) t ht (by decide))
  omega

theorem cyclic14 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 14) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 14 0 1) t ht (by decide))
  have h1 := hr 1 3 (pos (pnode 14 1 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 14 3 0) t ht (by decide))
  omega

theorem cyclic15 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 15) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 15 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (pnode 15 3 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 15 1 0) t ht (by decide))
  omega

theorem cyclic16 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 16) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 16 0 1) t ht (by decide))
  have h1 := hr 1 2 (pos (pnode 16 1 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 16 2 0) t ht (by decide))
  omega

theorem cyclic17 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 17) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 17 0 1) t ht (by decide))
  have h1 := hr 1 2 (pos (pnode 17 1 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 17 2 0) t ht (by decide))
  omega

theorem cyclic18 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 18) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 18 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 18 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 18 1 0) t ht (by decide))
  omega

theorem cyclic19 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 19) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 19 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (pnode 19 3 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 19 1 0) t ht (by decide))
  omega

theorem cyclic20 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 20) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 20 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 20 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 20 1 0) t ht (by decide))
  omega

theorem cyclic21 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 21) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 21 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 21 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 21 1 0) t ht (by decide))
  omega

theorem cyclic22 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 22) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 22 0 1) t ht (by decide))
  have h1 := hr 1 2 (pos (pnode 22 1 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 22 2 0) t ht (by decide))
  omega

theorem cyclic23 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 23) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 23 0 2) t ht (by decide))
  have h1 := hr 2 3 (pos (pnode 23 2 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 23 3 0) t ht (by decide))
  omega

theorem cyclic24 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 24) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 24 0 1) t ht (by decide))
  have h1 := hr 1 3 (pos (pnode 24 1 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 24 3 0) t ht (by decide))
  omega

theorem cyclic25 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 25) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 25 0 1) t ht (by decide))
  have h1 := hr 1 2 (pos (pnode 25 1 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 25 2 0) t ht (by decide))
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
  have h1 := hr 3 1 (pos (pnode 27 3 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 27 1 0) t ht (by decide))
  omega

theorem cyclic28 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 28) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 28 0 1) t ht (by decide))
  have h1 := hr 1 2 (pos (pnode 28 1 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 28 2 0) t ht (by decide))
  omega

theorem cyclic29 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 29) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 1 2 (pos (pnode 29 1 2) t ht (by decide))
  have h1 := hr 2 3 (pos (pnode 29 2 3) t ht (by decide))
  have h2 := hr 3 1 (pos (pnode 29 3 1) t ht (by decide))
  omega

theorem cyclic30 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 30) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 30 0 1) t ht (by decide))
  have h1 := hr 1 2 (pos (pnode 30 1 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 30 2 0) t ht (by decide))
  omega

theorem cyclic31 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 31) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 31 0 1) t ht (by decide))
  have h1 := hr 1 2 (pos (pnode 31 1 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 31 2 0) t ht (by decide))
  omega

theorem cyclic32 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 32) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 32 0 2) t ht (by decide))
  have h1 := hr 2 3 (pos (pnode 32 2 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 32 3 0) t ht (by decide))
  omega

theorem cyclic33 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 33) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 33 0 1) t ht (by decide))
  have h1 := hr 1 3 (pos (pnode 33 1 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 33 3 0) t ht (by decide))
  omega

theorem cyclic34 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 34) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 34 0 1) t ht (by decide))
  have h1 := hr 1 2 (pos (pnode 34 1 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 34 2 0) t ht (by decide))
  omega

theorem cyclic35 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 35) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 35 0 1) t ht (by decide))
  have h1 := hr 1 2 (pos (pnode 35 1 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 35 2 0) t ht (by decide))
  omega

theorem cyclic36 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 36) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 36 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 36 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 36 1 0) t ht (by decide))
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
  have h0 := hr 0 3 (pos (pnode 39 0 3) t ht (by decide))
  have h1 := hr 3 2 (pos (pnode 39 3 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 39 2 0) t ht (by decide))
  omega

theorem cyclic40 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 40) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 40 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 40 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 40 1 0) t ht (by decide))
  omega

theorem cyclic41 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 41) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 41 0 1) t ht (by decide))
  have h1 := hr 1 2 (pos (pnode 41 1 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 41 2 0) t ht (by decide))
  omega

theorem cyclic42 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 42) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 42 0 1) t ht (by decide))
  have h1 := hr 1 2 (pos (pnode 42 1 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 42 2 0) t ht (by decide))
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
  have h1 := hr 2 3 (pos (pnode 46 2 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 46 3 0) t ht (by decide))
  omega

theorem cyclic47 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 47) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 47 0 3) t ht (by decide))
  have h1 := hr 3 2 (pos (pnode 47 3 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 47 2 0) t ht (by decide))
  omega

theorem cyclic48 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 48) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 48 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (pnode 48 3 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 48 1 0) t ht (by decide))
  omega

theorem cyclic49 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 49) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 49 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (pnode 49 3 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 49 1 0) t ht (by decide))
  omega

theorem cyclic50 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 50) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 50 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 50 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 50 1 0) t ht (by decide))
  omega

theorem cyclic51 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 51) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 51 0 1) t ht (by decide))
  have h1 := hr 1 3 (pos (pnode 51 1 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 51 3 0) t ht (by decide))
  omega

theorem cyclic52 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 52) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 52 0 1) t ht (by decide))
  have h1 := hr 1 2 (pos (pnode 52 1 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 52 2 0) t ht (by decide))
  omega

theorem cyclic53 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 53) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 53 0 1) t ht (by decide))
  have h1 := hr 1 2 (pos (pnode 53 1 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 53 2 0) t ht (by decide))
  omega

theorem cyclic54 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 54) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 54 0 1) t ht (by decide))
  have h1 := hr 1 2 (pos (pnode 54 1 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 54 2 0) t ht (by decide))
  omega

theorem cyclic55 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 55) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 55 0 1) t ht (by decide))
  have h1 := hr 1 3 (pos (pnode 55 1 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 55 3 0) t ht (by decide))
  omega

theorem cyclic56 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 56) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 56 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 56 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 56 1 0) t ht (by decide))
  omega

theorem cyclic57 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 57) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 57 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 57 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 57 1 0) t ht (by decide))
  omega

theorem cyclic58 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 58) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 58 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 58 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 58 1 0) t ht (by decide))
  omega

theorem cyclic59 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 59) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 59 0 3) t ht (by decide))
  have h1 := hr 3 2 (pos (pnode 59 3 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 59 2 0) t ht (by decide))
  omega

theorem cyclic60 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 60) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 60 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (pnode 60 3 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 60 1 0) t ht (by decide))
  omega

theorem cyclic61 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 61) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 61 0 3) t ht (by decide))
  have h1 := hr 3 2 (pos (pnode 61 3 2) t ht (by decide))
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
  have h0 := hr 0 1 (pos (pnode 63 0 1) t ht (by decide))
  have h1 := hr 1 2 (pos (pnode 63 1 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 63 2 0) t ht (by decide))
  omega

theorem cyclic64 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 64) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 64 0 1) t ht (by decide))
  have h1 := hr 1 3 (pos (pnode 64 1 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 64 3 0) t ht (by decide))
  omega

theorem cyclic65 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 65) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 65 0 1) t ht (by decide))
  have h1 := hr 1 2 (pos (pnode 65 1 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 65 2 0) t ht (by decide))
  omega

theorem cyclic66 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 66) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 66 0 3) t ht (by decide))
  have h1 := hr 3 2 (pos (pnode 66 3 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 66 2 0) t ht (by decide))
  omega

theorem cyclic67 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 67) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 67 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 67 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 67 1 0) t ht (by decide))
  omega

theorem cyclic68 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 68) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 68 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 68 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 68 1 0) t ht (by decide))
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
  have h0 := hr 0 2 (pos (pnode 71 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 71 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 71 1 0) t ht (by decide))
  omega

theorem cyclic72 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 72) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 72 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (pnode 72 3 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 72 1 0) t ht (by decide))
  omega

theorem cyclic73 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 73) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 73 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 73 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 73 1 0) t ht (by decide))
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
  have h1 := hr 2 1 (pos (pnode 75 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 75 1 0) t ht (by decide))
  omega

theorem cyclic76 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 76) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 76 0 2) t ht (by decide))
  have h1 := hr 2 3 (pos (pnode 76 2 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 76 3 0) t ht (by decide))
  omega

theorem cyclic77 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 77) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 77 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 77 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 77 1 0) t ht (by decide))
  omega

theorem cyclic78 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 78) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 78 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (pnode 78 3 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 78 1 0) t ht (by decide))
  omega

theorem cyclic79 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 79) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 79 0 1) t ht (by decide))
  have h1 := hr 1 2 (pos (pnode 79 1 2) t ht (by decide))
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
  have h0 := hr 0 1 (pos (pnode 81 0 1) t ht (by decide))
  have h1 := hr 1 3 (pos (pnode 81 1 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 81 3 0) t ht (by decide))
  omega

theorem cyclic82 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 82) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 82 0 1) t ht (by decide))
  have h1 := hr 1 2 (pos (pnode 82 1 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 82 2 0) t ht (by decide))
  omega

theorem cyclic83 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 83) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 83 0 1) t ht (by decide))
  have h1 := hr 1 2 (pos (pnode 83 1 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 83 2 0) t ht (by decide))
  omega

theorem cyclic84 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 84) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 84 0 1) t ht (by decide))
  have h1 := hr 1 3 (pos (pnode 84 1 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 84 3 0) t ht (by decide))
  omega

theorem cyclic85 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 85) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 85 0 1) t ht (by decide))
  have h1 := hr 1 2 (pos (pnode 85 1 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 85 2 0) t ht (by decide))
  omega

theorem cyclic86 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 86) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 86 0 1) t ht (by decide))
  have h1 := hr 1 2 (pos (pnode 86 1 2) t ht (by decide))
  have h2 := hr 2 0 (pos (pnode 86 2 0) t ht (by decide))
  omega

theorem cyclic87 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 87) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 87 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (pnode 87 3 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 87 1 0) t ht (by decide))
  omega

theorem cyclic88 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 88) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 88 0 2) t ht (by decide))
  have h1 := hr 2 3 (pos (pnode 88 2 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 88 3 0) t ht (by decide))
  omega

theorem cyclic89 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 89) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 89 0 1) t ht (by decide))
  have h1 := hr 1 3 (pos (pnode 89 1 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 89 3 0) t ht (by decide))
  omega

theorem cyclic90 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 90) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (pnode 90 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (pnode 90 3 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 90 1 0) t ht (by decide))
  omega

theorem cyclic91 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 91) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 91 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 91 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 91 1 0) t ht (by decide))
  omega

theorem cyclic92 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 92) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (pnode 92 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (pnode 92 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (pnode 92 1 0) t ht (by decide))
  omega

theorem cyclic93 (t : Int) (ht : 0≤t) : ¬ Acyclic (node t 93) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (pos (pnode 93 0 1) t ht (by decide))
  have h1 := hr 1 3 (pos (pnode 93 1 3) t ht (by decide))
  have h2 := hr 3 0 (pos (pnode 93 3 0) t ht (by decide))
  omega

theorem edge0_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 0) 0) := by
  have he := mutation_equal (pnode 0) (prelabel (pnode 1) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 0) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 1) perm0.symm

theorem edge0_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 0) 1) := by
  have he := mutation_equal (pnode 0) (prelabel (pnode 2) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 0) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 2) perm0.symm

theorem edge0_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 0) 2) := by
  have he := mutation_equal (pnode 0) (prelabel (pnode 3) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 0) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 3) perm0.symm

theorem edge0_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 0) 3) := by
  have he := mutation_equal (pnode 0) (prelabel (pnode 4) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 0) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 4) perm0.symm

theorem edge1_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 1) 0) := by
  have he := mutation_equal (pnode 1) (prelabel (pnode 0) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 1) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 0) perm0.symm

theorem edge1_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 1) 1) := by
  have he := mutation_equal (pnode 1) (prelabel (pnode 5) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 1) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 5) perm0.symm

theorem edge1_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 1) 2) := by
  have he := mutation_equal (pnode 1) (prelabel (pnode 6) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 1) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 6) perm0.symm

theorem edge1_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 1) 3) := by
  have he := mutation_equal (pnode 1) (prelabel (pnode 7) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 1) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 7) perm0.symm

theorem edge2_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 2) 0) := by
  have he := mutation_equal (pnode 2) (prelabel (pnode 8) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 2) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 8) perm0.symm

theorem edge2_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 2) 1) := by
  have he := mutation_equal (pnode 2) (prelabel (pnode 0) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 2) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 0) perm0.symm

theorem edge2_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 2) 2) := by
  have he := mutation_equal (pnode 2) (prelabel (pnode 9) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 2) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 9) perm0.symm

theorem edge2_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 2) 3) := by
  have he := mutation_equal (pnode 2) (prelabel (pnode 10) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 2) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 10) perm0.symm

theorem edge3_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 3) 0) := by
  have he := mutation_equal (pnode 3) (preverse (prelabel (fork [2,1] [9,7,1] [2] [13,22,9,1] [5,2] [4,1]) perm3.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (node_safe t 3)
  rw [show mutate (node t 3) 0=(reverse (relabel (matrix (fork [2,1] [9,7,1] [2] [13,22,9,1] [5,2] [4,1]) t) perm3.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [2,1] [9,7,1] [2] [13,22,9,1] [5,2] [4,1] t ht (by decide)) perm3.symm)

theorem edge3_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 3) 1) := by
  have he := mutation_equal (pnode 3) (prelabel (pnode 11) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 3) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 11) perm0.symm

theorem edge3_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 3) 2) := by
  have he := mutation_equal (pnode 3) (prelabel (pnode 0) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 3) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 0) perm0.symm

theorem edge3_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 3) 3) := by
  have he := mutation_equal (pnode 3) (prelabel (fork [5,1] [9,7,1] [4,1] [43,43,12,1] [19,9,1] [2]) perm22.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 3 (node_safe t 3)
  rw [show mutate (node t 3) 3=(relabel (matrix (fork [5,1] [9,7,1] [4,1] [43,43,12,1] [19,9,1] [2]) t) perm22.symm) from he]
  exact IsFork.relabelled (fork_sound [5,1] [9,7,1] [4,1] [43,43,12,1] [19,9,1] [2] t ht (by decide)) perm22.symm

theorem edge4_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 4) 0) := by
  have he := mutation_equal (pnode 4) (prelabel (pnode 12) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 4) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 12) perm0.symm

theorem edge4_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 4) 1) := by
  have he := mutation_equal (pnode 4) (prelabel (pnode 13) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 4) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 13) perm0.symm

theorem edge4_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 4) 2) := by
  have he := mutation_equal (pnode 4) (preverse (prelabel (fork [5,1] [4,1] [3] [19,9,1] [14,3] [2]) perm17.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 2 (node_safe t 4)
  rw [show mutate (node t 4) 2=(reverse (relabel (matrix (fork [5,1] [4,1] [3] [19,9,1] [14,3] [2]) t) perm17.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [5,1] [4,1] [3] [19,9,1] [14,3] [2] t ht (by decide)) perm17.symm)

theorem edge4_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 4) 3) := by
  have he := mutation_equal (pnode 4) (prelabel (pnode 0) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 4) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 0) perm0.symm

theorem edge5_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 5) 0) := by
  have he := mutation_equal (pnode 5) (preverse (prelabel (root [2] [5,2] [7] [2,1] [5] []) perm0.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 5) 0
  rw [show mutate (node t 5) 0=(reverse (relabel (matrix (root [2] [5,2] [7] [2,1] [5] []) t) perm0.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [2] [5,2] [7] [2,1] [5] [] t ht (by decide)) perm0.symm)

theorem edge5_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 5) 1) := by
  have he := mutation_equal (pnode 5) (prelabel (pnode 1) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 5) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 1) perm0.symm

theorem edge5_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 5) 2) := by
  have he := mutation_equal (pnode 5) (prelabel (pnode 14) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 5) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 14) perm0.symm

theorem edge5_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 5) 3) := by
  have he := mutation_equal (pnode 5) (prelabel (pnode 15) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 5) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 15) perm0.symm

theorem edge6_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 6) 0) := by
  have he := mutation_equal (pnode 6) (prelabel (pnode 16) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 6) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 16) perm0.symm

theorem edge6_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 6) 1) := by
  have he := mutation_equal (pnode 6) (prelabel (pnode 17) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 6) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 17) perm0.symm

theorem edge6_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 6) 2) := by
  have he := mutation_equal (pnode 6) (prelabel (pnode 1) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 6) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 1) perm0.symm

theorem edge6_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 6) 3) := by
  have he := mutation_equal (pnode 6) (prelabel (pnode 18) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 6) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 18) perm0.symm

theorem edge7_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 7) 0) := by
  have he := mutation_equal (pnode 7) (prelabel (pnode 12) perm21.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 7) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 12) perm21.symm

theorem edge7_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 7) 1) := by
  have he := mutation_equal (pnode 7) (prelabel (pnode 19) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 7) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 19) perm0.symm

theorem edge7_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 7) 2) := by
  have he := mutation_equal (pnode 7) (prelabel (root [3] [7,3] [21] [2,1] [8] [1]) perm16.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 7) 2
  rw [show mutate (node t 7) 2=(relabel (matrix (root [3] [7,3] [21] [2,1] [8] [1]) t) perm16.symm) from he]
  exact IsRoot.relabelled (root_sound [3] [7,3] [21] [2,1] [8] [1] t ht (by decide)) perm16.symm

theorem edge7_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 7) 3) := by
  have he := mutation_equal (pnode 7) (prelabel (pnode 1) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 7) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 1) perm0.symm

theorem edge8_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 8) 0) := by
  have he := mutation_equal (pnode 8) (prelabel (pnode 2) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 8) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 2) perm0.symm

theorem edge8_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 8) 1) := by
  have he := mutation_equal (pnode 8) (prelabel (pnode 20) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 8) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 20) perm0.symm

theorem edge8_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 8) 2) := by
  have he := mutation_equal (pnode 8) (prelabel (pnode 21) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 8) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 21) perm0.symm

theorem edge8_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 8) 3) := by
  have he := mutation_equal (pnode 8) (prelabel (pnode 22) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 8) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 22) perm0.symm

theorem edge9_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 9) 0) := by
  have he := mutation_equal (pnode 9) (prelabel (root [4,1] [7,6,1] [56,46,12,1] [2,1] [15,8,1] [1]) perm2.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 9) 0
  rw [show mutate (node t 9) 0=(relabel (matrix (root [4,1] [7,6,1] [56,46,12,1] [2,1] [15,8,1] [1]) t) perm2.symm) from he]
  exact IsRoot.relabelled (root_sound [4,1] [7,6,1] [56,46,12,1] [2,1] [15,8,1] [1] t ht (by decide)) perm2.symm

theorem edge9_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 9) 1) := by
  have he := mutation_equal (pnode 9) (prelabel (pnode 11) perm2.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 9) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 11) perm2.symm

theorem edge9_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 9) 2) := by
  have he := mutation_equal (pnode 9) (prelabel (pnode 2) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 9) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 2) perm0.symm

theorem edge9_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 9) 3) := by
  have he := mutation_equal (pnode 9) (prelabel (pnode 23) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 9) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 23) perm0.symm

theorem edge10_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 10) 0) := by
  have he := mutation_equal (pnode 10) (prelabel (pnode 17) perm23.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 10) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 17) perm23.symm

theorem edge10_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 10) 1) := by
  have he := mutation_equal (pnode 10) (prelabel (pnode 13) perm5.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 10) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 13) perm5.symm

theorem edge10_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 10) 2) := by
  have he := mutation_equal (pnode 10) (prelabel (pnode 18) perm23.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 10) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 18) perm23.symm

theorem edge10_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 10) 3) := by
  have he := mutation_equal (pnode 10) (prelabel (pnode 2) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 10) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 2) perm0.symm

theorem edge11_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 11) 0) := by
  have he := mutation_equal (pnode 11) (preverse (prelabel (root [17,9,1] [33,35,11,1] [30,17,2] [2,1] [2] [1]) perm5.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 11) 0
  rw [show mutate (node t 11) 0=(reverse (relabel (matrix (root [17,9,1] [33,35,11,1] [30,17,2] [2,1] [2] [1]) t) perm5.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [17,9,1] [33,35,11,1] [30,17,2] [2,1] [2] [1] t ht (by decide)) perm5.symm)

theorem edge11_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 11) 1) := by
  have he := mutation_equal (pnode 11) (prelabel (pnode 3) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 11) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 3) perm0.symm

theorem edge11_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 11) 2) := by
  have he := mutation_equal (pnode 11) (prelabel (pnode 9) perm2.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 11) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 9) perm2.symm

theorem edge11_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 11) 3) := by
  have he := mutation_equal (pnode 11) (prelabel (pnode 24) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 11) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 24) perm0.symm

theorem edge12_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 12) 0) := by
  have he := mutation_equal (pnode 12) (prelabel (pnode 4) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 12) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 4) perm0.symm

theorem edge12_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 12) 1) := by
  have he := mutation_equal (pnode 12) (prelabel (pnode 25) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 12) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 25) perm0.symm

theorem edge12_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 12) 2) := by
  have he := mutation_equal (pnode 12) (preverse (prelabel (root [10,1] [28,3] [19,12,1] [3] [2,1] [1]) perm14.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 12) 2
  rw [show mutate (node t 12) 2=(reverse (relabel (matrix (root [10,1] [28,3] [19,12,1] [3] [2,1] [1]) t) perm14.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [10,1] [28,3] [19,12,1] [3] [2,1] [1] t ht (by decide)) perm14.symm)

theorem edge12_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 12) 3) := by
  have he := mutation_equal (pnode 12) (prelabel (pnode 7) perm21.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 12) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 7) perm21.symm

theorem edge13_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 13) 0) := by
  have he := mutation_equal (pnode 13) (prelabel (fork [3] [2] [3] [5] [8] [4,1]) perm4.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (node_safe t 13)
  rw [show mutate (node t 13) 0=(relabel (matrix (fork [3] [2] [3] [5] [8] [4,1]) t) perm4.symm) from he]
  exact IsFork.relabelled (fork_sound [3] [2] [3] [5] [8] [4,1] t ht (by decide)) perm4.symm

theorem edge13_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 13) 1) := by
  have he := mutation_equal (pnode 13) (prelabel (pnode 4) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 13) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 4) perm0.symm

theorem edge13_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 13) 2) := by
  have he := mutation_equal (pnode 13) (prelabel (pnode 26) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 13) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 26) perm0.symm

theorem edge13_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 13) 3) := by
  have he := mutation_equal (pnode 13) (prelabel (pnode 10) perm5.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 13) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 10) perm5.symm

theorem edge14_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 14) 0) := by
  have he := mutation_equal (pnode 14) (prelabel (root [5] [7] [10,5] [2] [2,1] [1]) perm4.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 14) 0
  rw [show mutate (node t 14) 0=(relabel (matrix (root [5] [7] [10,5] [2] [2,1] [1]) t) perm4.symm) from he]
  exact IsRoot.relabelled (root_sound [5] [7] [10,5] [2] [2,1] [1] t ht (by decide)) perm4.symm

theorem edge14_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 14) 1) := by
  have he := mutation_equal (pnode 14) (prelabel (pnode 17) perm2.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 14) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 17) perm2.symm

theorem edge14_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 14) 2) := by
  have he := mutation_equal (pnode 14) (prelabel (pnode 5) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 14) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 5) perm0.symm

theorem edge14_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 14) 3) := by
  have he := mutation_equal (pnode 14) (prelabel (pnode 27) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 14) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 27) perm0.symm

theorem edge15_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 15) 0) := by
  have he := mutation_equal (pnode 15) (preverse (prelabel (root [5] [62] [10,5] [13] [2,1] [1]) perm4.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 15) 0
  rw [show mutate (node t 15) 0=(reverse (relabel (matrix (root [5] [62] [10,5] [13] [2,1] [1]) t) perm4.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [5] [62] [10,5] [13] [2,1] [1] t ht (by decide)) perm4.symm)

theorem edge15_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 15) 1) := by
  have he := mutation_equal (pnode 15) (prelabel (pnode 28) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 15) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 28) perm0.symm

theorem edge15_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 15) 2) := by
  have he := mutation_equal (pnode 15) (prelabel (pnode 27) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 15) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 27) perm0.symm

theorem edge15_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 15) 3) := by
  have he := mutation_equal (pnode 15) (prelabel (pnode 5) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 15) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 5) perm0.symm

theorem edge16_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 16) 0) := by
  have he := mutation_equal (pnode 16) (prelabel (pnode 6) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 16) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 6) perm0.symm

theorem edge16_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 16) 1) := by
  have he := mutation_equal (pnode 16) (preverse (prelabel (fork [4,1] [7,6,1] [4,1] [26,30,10,1] [15,8,1] [3]) perm6.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (node_safe t 16)
  rw [show mutate (node t 16) 1=(reverse (relabel (matrix (fork [4,1] [7,6,1] [4,1] [26,30,10,1] [15,8,1] [3]) t) perm6.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [4,1] [7,6,1] [4,1] [26,30,10,1] [15,8,1] [3] t ht (by decide)) perm6.symm)

theorem edge16_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 16) 2) := by
  have he := mutation_equal (pnode 16) (prelabel (fork [2,1] [7,6,1] [3] [10,18,8,1] [7,3] [4,1]) perm12.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 2 (node_safe t 16)
  rw [show mutate (node t 16) 2=(relabel (matrix (fork [2,1] [7,6,1] [3] [10,18,8,1] [7,3] [4,1]) t) perm12.symm) from he]
  exact IsFork.relabelled (fork_sound [2,1] [7,6,1] [3] [10,18,8,1] [7,3] [4,1] t ht (by decide)) perm12.symm

theorem edge16_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 16) 3) := by
  have he := mutation_equal (pnode 16) (prelabel (pnode 29) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 16) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 29) perm0.symm

theorem edge17_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 17) 0) := by
  have he := mutation_equal (pnode 17) (prelabel (pnode 22) perm2.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 17) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 22) perm2.symm

theorem edge17_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 17) 1) := by
  have he := mutation_equal (pnode 17) (prelabel (pnode 6) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 17) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 6) perm0.symm

theorem edge17_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 17) 2) := by
  have he := mutation_equal (pnode 17) (prelabel (pnode 14) perm2.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 17) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 14) perm2.symm

theorem edge17_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 17) 3) := by
  have he := mutation_equal (pnode 17) (prelabel (pnode 10) perm23.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 17) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 10) perm23.symm

theorem edge18_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 18) 0) := by
  have he := mutation_equal (pnode 18) (prelabel (pnode 30) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 18) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 30) perm0.symm

theorem edge18_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 18) 1) := by
  have he := mutation_equal (pnode 18) (prelabel (pnode 10) perm23.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 18) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 10) perm23.symm

theorem edge18_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 18) 2) := by
  have he := mutation_equal (pnode 18) (prelabel (pnode 31) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 18) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 31) perm0.symm

theorem edge18_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 18) 3) := by
  have he := mutation_equal (pnode 18) (prelabel (pnode 6) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 18) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 6) perm0.symm

theorem edge19_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 19) 0) := by
  have he := mutation_equal (pnode 19) (prelabel (pnode 32) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 19) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 32) perm0.symm

theorem edge19_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 19) 1) := by
  have he := mutation_equal (pnode 19) (prelabel (pnode 7) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 19) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 7) perm0.symm

theorem edge19_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 19) 2) := by
  have he := mutation_equal (pnode 19) (preverse (prelabel (fork [8] [21] [2,1] [165] [17,8] [2]) perm15.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 2 (node_safe t 19)
  rw [show mutate (node t 19) 2=(reverse (relabel (matrix (fork [8] [21] [2,1] [165] [17,8] [2]) t) perm15.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [8] [21] [2,1] [165] [17,8] [2] t ht (by decide)) perm15.symm)

theorem edge19_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 19) 3) := by
  have he := mutation_equal (pnode 19) (prelabel (fork [3] [21] [2] [55] [5] [2,1]) perm21.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 3 (node_safe t 19)
  rw [show mutate (node t 19) 3=(relabel (matrix (fork [3] [21] [2] [55] [5] [2,1]) t) perm21.symm) from he]
  exact IsFork.relabelled (fork_sound [3] [21] [2] [55] [5] [2,1] t ht (by decide)) perm21.symm

theorem edge20_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 20) 0) := by
  have he := mutation_equal (pnode 20) (prelabel (root [2] [13,4] [5] [10,3] [3] []) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 20) 0
  rw [show mutate (node t 20) 0=(relabel (matrix (root [2] [13,4] [5] [10,3] [3] []) t) perm0.symm) from he]
  exact IsRoot.relabelled (root_sound [2] [13,4] [5] [10,3] [3] [] t ht (by decide)) perm0.symm

theorem edge20_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 20) 1) := by
  have he := mutation_equal (pnode 20) (prelabel (pnode 8) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 20) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 8) perm0.symm

theorem edge20_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 20) 2) := by
  have he := mutation_equal (pnode 20) (prelabel (zero param8_0 param8_1 param8_2 param8_3 0) perm22.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 20) t) 2)
  rw [he]
  exact Safe.framed (region8_safe t ht 0) perm22.symm

theorem edge20_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 20) 3) := by
  have he := mutation_equal (pnode 20) (prelabel (pnode 33) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 20) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 33) perm0.symm

theorem edge21_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 21) 0) := by
  have he := mutation_equal (pnode 21) (prelabel (pnode 34) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 21) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 34) perm0.symm

theorem edge21_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 21) 1) := by
  have he := mutation_equal (pnode 21) (prelabel (pnode 35) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 21) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 35) perm0.symm

theorem edge21_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 21) 2) := by
  have he := mutation_equal (pnode 21) (prelabel (pnode 8) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 21) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 8) perm0.symm

theorem edge21_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 21) 3) := by
  have he := mutation_equal (pnode 21) (prelabel (pnode 36) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 21) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 36) perm0.symm

theorem edge22_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 22) 0) := by
  have he := mutation_equal (pnode 22) (prelabel (pnode 17) perm2.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 22) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 17) perm2.symm

theorem edge22_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 22) 1) := by
  have he := mutation_equal (pnode 22) (prelabel (pnode 37) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 22) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 37) perm0.symm

theorem edge22_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 22) 2) := by
  have he := mutation_equal (pnode 22) (prelabel (pnode 36) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 22) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 36) perm0.symm

theorem edge22_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 22) 3) := by
  have he := mutation_equal (pnode 22) (prelabel (pnode 8) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 22) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 8) perm0.symm

theorem edge23_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 23) 0) := by
  have he := mutation_equal (pnode 23) (preverse (prelabel (fork [15,8,1] [56,46,12,1] [2,1] [836,1137,604,157,20,1] [31,31,10,1] [5,1]) perm5.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (node_safe t 23)
  rw [show mutate (node t 23) 0=(reverse (relabel (matrix (fork [15,8,1] [56,46,12,1] [2,1] [836,1137,604,157,20,1] [31,31,10,1] [5,1]) t) perm5.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [15,8,1] [56,46,12,1] [2,1] [836,1137,604,157,20,1] [31,31,10,1] [5,1] t ht (by decide)) perm5.symm)

theorem edge23_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 23) 1) := by
  have he := mutation_equal (pnode 23) (prelabel (pnode 38) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 23) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 38) perm0.symm

theorem edge23_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 23) 2) := by
  have he := mutation_equal (pnode 23) (prelabel (fork [4,1] [56,46,12,1] [5,1] [209,232,93,16,1] [19,9,1] [2,1]) perm16.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 2 (node_safe t 23)
  rw [show mutate (node t 23) 2=(relabel (matrix (fork [4,1] [56,46,12,1] [5,1] [209,232,93,16,1] [19,9,1] [2,1]) t) perm16.symm) from he]
  exact IsFork.relabelled (fork_sound [4,1] [56,46,12,1] [5,1] [209,232,93,16,1] [19,9,1] [2,1] t ht (by decide)) perm16.symm

theorem edge23_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 23) 3) := by
  have he := mutation_equal (pnode 23) (prelabel (pnode 9) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 23) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 9) perm0.symm

theorem edge24_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 24) 0) := by
  have he := mutation_equal (pnode 24) (prelabel (root [17,9,1] [1118,1494,764,187,22,1] [254,271,104,17,1] [66,53,13,1] [15,8,1] [1]) perm4.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 24) 0
  rw [show mutate (node t 24) 0=(relabel (matrix (root [17,9,1] [1118,1494,764,187,22,1] [254,271,104,17,1] [66,53,13,1] [15,8,1] [1]) t) perm4.symm) from he]
  exact IsRoot.relabelled (root_sound [17,9,1] [1118,1494,764,187,22,1] [254,271,104,17,1] [66,53,13,1] [15,8,1] [1] t ht (by decide)) perm4.symm

theorem edge24_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 24) 1) := by
  have he := mutation_equal (pnode 24) (preverse (prelabel (generic param0_0 param0_1 param0_2 param0_3 1) perm9.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 24) t) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (region0_safe t ht 1) perm9.symm)

theorem edge24_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 24) 2) := by
  have he := mutation_equal (pnode 24) (prelabel (pnode 38) perm4.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 24) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 38) perm4.symm

theorem edge24_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 24) 3) := by
  have he := mutation_equal (pnode 24) (prelabel (pnode 11) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 24) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 11) perm0.symm

theorem edge25_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 25) 0) := by
  have he := mutation_equal (pnode 25) (prelabel (pnode 40) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 25) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 40) perm0.symm

theorem edge25_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 25) 1) := by
  have he := mutation_equal (pnode 25) (prelabel (pnode 12) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 25) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 12) perm0.symm

theorem edge25_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 25) 2) := by
  have he := mutation_equal (pnode 25) (prelabel (root [10,1] [79,8] [168,37,2] [8] [17,2] [1]) perm15.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 25) 2
  rw [show mutate (node t 25) 2=(relabel (matrix (root [10,1] [79,8] [168,37,2] [8] [17,2] [1]) t) perm15.symm) from he]
  exact IsRoot.relabelled (root_sound [10,1] [79,8] [168,37,2] [8] [17,2] [1] t ht (by decide)) perm15.symm

theorem edge25_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 25) 3) := by
  have he := mutation_equal (pnode 25) (prelabel (pnode 32) perm11.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 25) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 32) perm11.symm

theorem edge26_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 26) 0) := by
  have he := mutation_equal (pnode 26) (prelabel (pnode 41) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 26) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 41) perm0.symm

theorem edge26_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 26) 1) := by
  have he := mutation_equal (pnode 26) (prelabel (pnode 42) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 26) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 42) perm0.symm

theorem edge26_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 26) 2) := by
  have he := mutation_equal (pnode 26) (prelabel (pnode 13) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 26) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 13) perm0.symm

theorem edge26_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 26) 3) := by
  have he := mutation_equal (pnode 26) (prelabel (pnode 31) perm11.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 26) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 31) perm11.symm

theorem edge27_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 27) 0) := by
  have he := mutation_equal (pnode 27) (prelabel (root [13] [27,13] [62] [2,1] [5] []) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 27) 0
  rw [show mutate (node t 27) 0=(relabel (matrix (root [13] [27,13] [62] [2,1] [5] []) t) perm0.symm) from he]
  exact IsRoot.relabelled (root_sound [13] [27,13] [62] [2,1] [5] [] t ht (by decide)) perm0.symm

theorem edge27_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 27) 1) := by
  have he := mutation_equal (pnode 27) (prelabel (pnode 43) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 27) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 43) perm0.symm

theorem edge27_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 27) 2) := by
  have he := mutation_equal (pnode 27) (prelabel (pnode 15) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 27) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 15) perm0.symm

theorem edge27_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 27) 3) := by
  have he := mutation_equal (pnode 27) (prelabel (pnode 14) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 27) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 14) perm0.symm

theorem edge28_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 28) 0) := by
  have he := mutation_equal (pnode 28) (preverse (prelabel (root [13] [194,13] [439] [15,1] [34] []) perm0.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 28) 0
  rw [show mutate (node t 28) 0=(reverse (relabel (matrix (root [13] [194,13] [439] [15,1] [34] []) t) perm0.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [13] [194,13] [439] [15,1] [34] [] t ht (by decide)) perm0.symm)

theorem edge28_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 28) 1) := by
  have he := mutation_equal (pnode 28) (prelabel (pnode 15) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 28) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 15) perm0.symm

theorem edge28_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 28) 2) := by
  have he := mutation_equal (pnode 28) (prelabel (pnode 44) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 28) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 44) perm0.symm

theorem edge28_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 28) 3) := by
  have he := mutation_equal (pnode 28) (preverse (prelabel (zero param9_0 param9_1 param9_2 param9_3 0) perm16.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 28) t) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (region9_safe t ht 0) perm16.symm)

theorem edge29_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 29) 0) := by
  have he := mutation_equal (pnode 29) (prelabel (pnode 30) perm21.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 29) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 30) perm21.symm

theorem edge29_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 29) 1) := by
  have he := mutation_equal (pnode 29) (preverse (prelabel (zero param10_0 param10_1 param10_2 param10_3 1) perm0.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 29) t) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (region10_safe t ht 1) perm0.symm)

theorem edge29_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 29) 2) := by
  have he := mutation_equal (pnode 29) (prelabel (root [19,9,1] [38,37,11,1] [53,26,3] [2,1] [3] [1]) perm14.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 29) 2
  rw [show mutate (node t 29) 2=(relabel (matrix (root [19,9,1] [38,37,11,1] [53,26,3] [2,1] [3] [1]) t) perm14.symm) from he]
  exact IsRoot.relabelled (root_sound [19,9,1] [38,37,11,1] [53,26,3] [2,1] [3] [1] t ht (by decide)) perm14.symm

theorem edge29_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 29) 3) := by
  have he := mutation_equal (pnode 29) (prelabel (pnode 16) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 29) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 16) perm0.symm

theorem edge30_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 30) 0) := by
  have he := mutation_equal (pnode 30) (prelabel (pnode 18) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 30) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 18) perm0.symm

theorem edge30_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 30) 1) := by
  have he := mutation_equal (pnode 30) (preverse (prelabel (zero param10_0 param10_1 param10_2 param10_3 0) perm21.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 30) t) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (region10_safe t ht 0) perm21.symm)

theorem edge30_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 30) 2) := by
  have he := mutation_equal (pnode 30) (preverse (prelabel (root [5,1] [91,63,14,1] [9,7,1] [19,9,1] [2,1] []) perm12.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 30) 2
  rw [show mutate (node t 30) 2=(reverse (relabel (matrix (root [5,1] [91,63,14,1] [9,7,1] [19,9,1] [2,1] []) t) perm12.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [5,1] [91,63,14,1] [9,7,1] [19,9,1] [2,1] [] t ht (by decide)) perm12.symm)

theorem edge30_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 30) 3) := by
  have he := mutation_equal (pnode 30) (prelabel (pnode 29) perm21.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 30) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 29) perm21.symm

theorem edge31_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 31) 0) := by
  have he := mutation_equal (pnode 31) (prelabel (pnode 45) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 31) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 45) perm0.symm

theorem edge31_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 31) 1) := by
  have he := mutation_equal (pnode 31) (prelabel (pnode 26) perm19.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 31) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 26) perm19.symm

theorem edge31_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 31) 2) := by
  have he := mutation_equal (pnode 31) (prelabel (pnode 18) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 31) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 18) perm0.symm

theorem edge31_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 31) 3) := by
  have he := mutation_equal (pnode 31) (prelabel (pnode 46) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 31) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 46) perm0.symm

theorem edge32_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 32) 0) := by
  have he := mutation_equal (pnode 32) (prelabel (pnode 19) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 32) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 19) perm0.symm

theorem edge32_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 32) 1) := by
  have he := mutation_equal (pnode 32) (prelabel (pnode 25) perm19.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 32) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 25) perm19.symm

theorem edge32_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 32) 2) := by
  have he := mutation_equal (pnode 32) (preverse (prelabel (root [25,2] [199,16] [48,29,2] [8] [2,1] [1]) perm17.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 32) 2
  rw [show mutate (node t 32) 2=(reverse (relabel (matrix (root [25,2] [199,16] [48,29,2] [8] [2,1] [1]) t) perm17.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [25,2] [199,16] [48,29,2] [8] [2,1] [1] t ht (by decide)) perm17.symm)

theorem edge32_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 32) 3) := by
  have he := mutation_equal (pnode 32) (prelabel (pnode 47) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 32) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 47) perm0.symm

theorem edge33_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 33) 0) := by
  have he := mutation_equal (pnode 33) (prelabel (pnode 48) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 33) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 48) perm0.symm

theorem edge33_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 33) 1) := by
  have he := mutation_equal (pnode 33) (prelabel (pnode 37) perm5.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 33) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 37) perm5.symm

theorem edge33_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 33) 2) := by
  have he := mutation_equal (pnode 33) (prelabel (zero param8_0 param8_1 param8_2 param8_3 1) perm22.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 33) t) 2)
  rw [he]
  exact Safe.framed (region8_safe t ht 1) perm22.symm

theorem edge33_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 33) 3) := by
  have he := mutation_equal (pnode 33) (prelabel (pnode 20) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 33) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 20) perm0.symm

theorem edge34_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 34) 0) := by
  have he := mutation_equal (pnode 34) (prelabel (pnode 21) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 34) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 21) perm0.symm

theorem edge34_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 34) 1) := by
  have he := mutation_equal (pnode 34) (prelabel (root [26,15,2] [2518,3638,2052,565,76,4] [701,795,331,60,4] [97,84,23,2] [27,15,2] []) perm6.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 34) 1
  rw [show mutate (node t 34) 1=(relabel (matrix (root [26,15,2] [2518,3638,2052,565,76,4] [701,795,331,60,4] [97,84,23,2] [27,15,2] []) t) perm6.symm) from he]
  exact IsRoot.relabelled (root_sound [26,15,2] [2518,3638,2052,565,76,4] [701,795,331,60,4] [97,84,23,2] [27,15,2] [] t ht (by decide)) perm6.symm

theorem edge34_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 34) 2) := by
  have he := mutation_equal (pnode 34) (prelabel (zero param11_0 param11_1 param11_2 param11_3 0) perm23.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 34) t) 2)
  rw [he]
  exact Safe.framed (region11_safe t ht 0) perm23.symm

theorem edge34_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 34) 3) := by
  have he := mutation_equal (pnode 34) (prelabel (pnode 49) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 34) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 49) perm0.symm

theorem edge35_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 35) 0) := by
  have he := mutation_equal (pnode 35) (prelabel (pnode 50) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 35) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 50) perm0.symm

theorem edge35_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 35) 1) := by
  have he := mutation_equal (pnode 35) (prelabel (pnode 21) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 35) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 21) perm0.symm

theorem edge35_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 35) 2) := by
  have he := mutation_equal (pnode 35) (prelabel (root [7,2] [1220,1433,618,116,8] [48,28,4] [178,156,44,4] [7,2] [1]) perm14.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 35) 2
  rw [show mutate (node t 35) 2=(relabel (matrix (root [7,2] [1220,1433,618,116,8] [48,28,4] [178,156,44,4] [7,2] [1]) t) perm14.symm) from he]
  exact IsRoot.relabelled (root_sound [7,2] [1220,1433,618,116,8] [48,28,4] [178,156,44,4] [7,2] [1] t ht (by decide)) perm14.symm

theorem edge35_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 35) 3) := by
  have he := mutation_equal (pnode 35) (prelabel (pnode 51) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 35) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 51) perm0.symm

theorem edge36_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 36) 0) := by
  have he := mutation_equal (pnode 36) (prelabel (pnode 52) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 36) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 52) perm0.symm

theorem edge36_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 36) 1) := by
  have he := mutation_equal (pnode 36) (prelabel (pnode 53) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 36) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 53) perm0.symm

theorem edge36_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 36) 2) := by
  have he := mutation_equal (pnode 36) (prelabel (pnode 22) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 36) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 22) perm0.symm

theorem edge36_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 36) 3) := by
  have he := mutation_equal (pnode 36) (prelabel (pnode 21) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 36) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 21) perm0.symm

theorem edge37_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 37) 0) := by
  have he := mutation_equal (pnode 37) (prelabel (pnode 54) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 37) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 54) perm0.symm

theorem edge37_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 37) 1) := by
  have he := mutation_equal (pnode 37) (prelabel (pnode 22) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 37) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 22) perm0.symm

theorem edge37_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 37) 2) := by
  have he := mutation_equal (pnode 37) (preverse (prelabel (root [7,2] [68,41,6] [48,28,4] [10,3] [7,2] [1]) perm14.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 37) 2
  rw [show mutate (node t 37) 2=(reverse (relabel (matrix (root [7,2] [68,41,6] [48,28,4] [10,3] [7,2] [1]) t) perm14.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [7,2] [68,41,6] [48,28,4] [10,3] [7,2] [1] t ht (by decide)) perm14.symm)

theorem edge37_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 37) 3) := by
  have he := mutation_equal (pnode 37) (prelabel (pnode 33) perm5.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 37) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 33) perm5.symm

theorem edge38_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 38) 0) := by
  have he := mutation_equal (pnode 38) (preverse (prelabel (root [66,53,13,1] [991,1323,685,172,21,1] [127,171,79,15,1] [15,8,1] [2,1] [1]) perm3.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 38) 0
  rw [show mutate (node t 38) 0=(reverse (relabel (matrix (root [66,53,13,1] [991,1323,685,172,21,1] [127,171,79,15,1] [15,8,1] [2,1] [1]) t) perm3.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [66,53,13,1] [991,1323,685,172,21,1] [127,171,79,15,1] [15,8,1] [2,1] [1] t ht (by decide)) perm3.symm)

theorem edge38_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 38) 1) := by
  have he := mutation_equal (pnode 38) (prelabel (pnode 23) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 38) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 23) perm0.symm

theorem edge38_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 38) 2) := by
  have he := mutation_equal (pnode 38) (prelabel (pnode 39) perm5.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 38) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 39) perm5.symm

theorem edge38_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 38) 3) := by
  have he := mutation_equal (pnode 38) (prelabel (pnode 24) perm3.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 38) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 24) perm3.symm

theorem edge39_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 39) 0) := by
  have he := mutation_equal (pnode 39) (preverse (prelabel (root [328,330,118,18,1] [4924,7575,4738,1544,277,26,1] [21643,39163,29542,12060,2884,405,31,1] [15,8,1] [66,53,13,1] [1]) perm4.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 39) 0
  rw [show mutate (node t 39) 0=(reverse (relabel (matrix (root [328,330,118,18,1] [4924,7575,4738,1544,277,26,1] [21643,39163,29542,12060,2884,405,31,1] [15,8,1] [66,53,13,1] [1]) t) perm4.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [328,330,118,18,1] [4924,7575,4738,1544,277,26,1] [21643,39163,29542,12060,2884,405,31,1] [15,8,1] [66,53,13,1] [1] t ht (by decide)) perm4.symm)

theorem edge39_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 39) 1) := by
  have he := mutation_equal (pnode 39) (preverse (prelabel (generic param0_0 param0_1 param0_2 param0_3 2) perm9.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 39) t) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (region0_safe t ht 2) perm9.symm)

theorem edge39_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 39) 2) := by
  have he := mutation_equal (pnode 39) (prelabel (pnode 38) perm5.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 39) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 38) perm5.symm

theorem edge39_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 39) 3) := by
  have he := mutation_equal (pnode 39) (prelabel (fork [5,1] [4,1] [328,330,118,18,1] [19,9,1] [1574,1925,907,207,23,1] [15,8,1]) perm23.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 3 (node_safe t 39)
  rw [show mutate (node t 39) 3=(relabel (matrix (fork [5,1] [4,1] [328,330,118,18,1] [19,9,1] [1574,1925,907,207,23,1] [15,8,1]) t) perm23.symm) from he]
  exact IsFork.relabelled (fork_sound [5,1] [4,1] [328,330,118,18,1] [19,9,1] [1574,1925,907,207,23,1] [15,8,1] t ht (by decide)) perm23.symm

theorem edge40_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 40) 0) := by
  have he := mutation_equal (pnode 40) (prelabel (pnode 25) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 40) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 25) perm0.symm

theorem edge40_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 40) 1) := by
  have he := mutation_equal (pnode 40) (prelabel (fork [2] [24,3] [3] [31,4] [5] [8]) perm6.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (node_safe t 40)
  rw [show mutate (node t 40) 1=(relabel (matrix (fork [2] [24,3] [3] [31,4] [5] [8]) t) perm6.symm) from he]
  exact IsFork.relabelled (fork_sound [2] [24,3] [3] [31,4] [5] [8] t ht (by decide)) perm6.symm

theorem edge40_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 40) 2) := by
  have he := mutation_equal (pnode 40) (preverse (prelabel (fork [17,2] [24,3] [8] [406,99,6] [137,16] [3]) perm12.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 2 (node_safe t 40)
  rw [show mutate (node t 40) 2=(reverse (relabel (matrix (fork [17,2] [24,3] [8] [406,99,6] [137,16] [3]) t) perm12.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [17,2] [24,3] [8] [406,99,6] [137,16] [3] t ht (by decide)) perm12.symm)

theorem edge40_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 40) 3) := by
  have he := mutation_equal (pnode 40) (prelabel (pnode 55) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 40) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 55) perm0.symm

theorem edge41_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 41) 0) := by
  have he := mutation_equal (pnode 41) (prelabel (pnode 26) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 41) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 26) perm0.symm

theorem edge41_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 41) 1) := by
  have he := mutation_equal (pnode 41) (prelabel (pnode 56) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 41) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 56) perm0.symm

theorem edge41_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 41) 2) := by
  have he := mutation_equal (pnode 41) (prelabel (pnode 57) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 41) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 57) perm0.symm

theorem edge41_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 41) 3) := by
  have he := mutation_equal (pnode 41) (prelabel (pnode 46) perm11.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 41) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 46) perm11.symm

theorem edge42_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 42) 0) := by
  have he := mutation_equal (pnode 42) (preverse (prelabel (root [14,3] [195,84,9] [738,522,120,9] [14,3] [53,26,3] [1]) perm1.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 42) 0
  rw [show mutate (node t 42) 0=(reverse (relabel (matrix (root [14,3] [195,84,9] [738,522,120,9] [14,3] [53,26,3] [1]) t) perm1.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [14,3] [195,84,9] [738,522,120,9] [14,3] [53,26,3] [1] t ht (by decide)) perm1.symm)

theorem edge42_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 42) 1) := by
  have he := mutation_equal (pnode 42) (prelabel (pnode 26) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 42) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 26) perm0.symm

theorem edge42_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 42) 2) := by
  have he := mutation_equal (pnode 42) (prelabel (pnode 58) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 42) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 58) perm0.symm

theorem edge42_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 42) 3) := by
  have he := mutation_equal (pnode 42) (prelabel (pnode 59) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 42) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 59) perm0.symm

theorem edge43_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 43) 0) := by
  have he := mutation_equal (pnode 43) (prelabel (root [34] [71,34] [439] [2,1] [13] [1]) perm5.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 43) 0
  rw [show mutate (node t 43) 0=(relabel (matrix (root [34] [71,34] [439] [2,1] [13] [1]) t) perm5.symm) from he]
  exact IsRoot.relabelled (root_sound [34] [71,34] [439] [2,1] [13] [1] t ht (by decide)) perm5.symm

theorem edge43_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 43) 1) := by
  have he := mutation_equal (pnode 43) (prelabel (pnode 27) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 43) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 27) perm0.symm

theorem edge43_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 43) 2) := by
  have he := mutation_equal (pnode 43) (prelabel (pnode 44) perm2.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 43) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 44) perm2.symm

theorem edge43_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 43) 3) := by
  have he := mutation_equal (pnode 43) (preverse (prelabel (fork [3] [3] [34] [8] [89] [2,1]) perm21.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 3 (node_safe t 43)
  rw [show mutate (node t 43) 3=(reverse (relabel (matrix (fork [3] [3] [34] [8] [89] [2,1]) t) perm21.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [3] [3] [34] [8] [89] [2,1] t ht (by decide)) perm21.symm)

theorem edge44_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 44) 0) := by
  have he := mutation_equal (pnode 44) (prelabel (fork [15,1] [2,1] [34] [29,17,1] [510,34] [3]) perm2.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (node_safe t 44)
  rw [show mutate (node t 44) 0=(relabel (matrix (fork [15,1] [2,1] [34] [29,17,1] [510,34] [3]) t) perm2.symm) from he]
  exact IsFork.relabelled (fork_sound [15,1] [2,1] [34] [29,17,1] [510,34] [3] t ht (by decide)) perm2.symm

theorem edge44_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 44) 1) := by
  have he := mutation_equal (pnode 44) (prelabel (pnode 43) perm2.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 44) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 43) perm2.symm

theorem edge44_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 44) 2) := by
  have he := mutation_equal (pnode 44) (prelabel (pnode 28) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 44) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 28) perm0.symm

theorem edge44_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 44) 3) := by
  have he := mutation_equal (pnode 44) (preverse (prelabel (zero param9_0 param9_1 param9_2 param9_3 1) perm16.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 44) t) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (region9_safe t ht 1) perm16.symm)

theorem edge45_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 45) 0) := by
  have he := mutation_equal (pnode 45) (prelabel (pnode 31) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 45) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 31) perm0.symm

theorem edge45_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 45) 1) := by
  have he := mutation_equal (pnode 45) (prelabel (pnode 59) perm21.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 45) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 59) perm21.symm

theorem edge45_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 45) 2) := by
  have he := mutation_equal (pnode 45) (prelabel (root [5,1] [19,9,1] [321,209,44,3] [4,1] [67,29,3] []) perm12.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 45) 2
  rw [show mutate (node t 45) 2=(relabel (matrix (root [5,1] [19,9,1] [321,209,44,3] [4,1] [67,29,3] []) t) perm12.symm) from he]
  exact IsRoot.relabelled (root_sound [5,1] [19,9,1] [321,209,44,3] [4,1] [67,29,3] [] t ht (by decide)) perm12.symm

theorem edge45_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 45) 3) := by
  have he := mutation_equal (pnode 45) (prelabel (zero param12_0 param12_1 param12_2 param12_3 0) perm11.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 45) t) 3)
  rw [he]
  exact Safe.framed (region12_safe t ht 0) perm11.symm

theorem edge46_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 46) 0) := by
  have he := mutation_equal (pnode 46) (prelabel (pnode 60) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 46) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 60) perm0.symm

theorem edge46_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 46) 1) := by
  have he := mutation_equal (pnode 46) (prelabel (pnode 41) perm19.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 46) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 41) perm19.symm

theorem edge46_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 46) 2) := by
  have he := mutation_equal (pnode 46) (prelabel (pnode 61) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 46) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 61) perm0.symm

theorem edge46_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 46) 3) := by
  have he := mutation_equal (pnode 46) (prelabel (pnode 31) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 46) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 31) perm0.symm

theorem edge47_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 47) 0) := by
  have he := mutation_equal (pnode 47) (preverse (prelabel (generic param1_0 param1_1 param1_2 param1_3 1) perm1.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 47) t) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (region1_safe t ht 1) perm1.symm)

theorem edge47_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 47) 1) := by
  have he := mutation_equal (pnode 47) (prelabel (pnode 55) perm6.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 47) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 55) perm6.symm

theorem edge47_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 47) 2) := by
  have he := mutation_equal (pnode 47) (prelabel (root [25,2] [1198,171,6] [424,84,4] [48,3] [17,2] [1]) perm16.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 47) 2
  rw [show mutate (node t 47) 2=(relabel (matrix (root [25,2] [1198,171,6] [424,84,4] [48,3] [17,2] [1]) t) perm16.symm) from he]
  exact IsRoot.relabelled (root_sound [25,2] [1198,171,6] [424,84,4] [48,3] [17,2] [1] t ht (by decide)) perm16.symm

theorem edge47_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 47) 3) := by
  have he := mutation_equal (pnode 47) (prelabel (pnode 32) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 47) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 32) perm0.symm

theorem edge48_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 48) 0) := by
  have he := mutation_equal (pnode 48) (prelabel (pnode 33) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 48) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 33) perm0.symm

theorem edge48_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 48) 1) := by
  have he := mutation_equal (pnode 48) (prelabel (pnode 63) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 48) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 63) perm0.symm

theorem edge48_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 48) 2) := by
  have he := mutation_equal (pnode 48) (prelabel (root [30,9] [212,123,18] [297,180,27] [7,2] [10,3] [1]) perm17.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 48) 2
  rw [show mutate (node t 48) 2=(relabel (matrix (root [30,9] [212,123,18] [297,180,27] [7,2] [10,3] [1]) t) perm17.symm) from he]
  exact IsRoot.relabelled (root_sound [30,9] [212,123,18] [297,180,27] [7,2] [10,3] [1] t ht (by decide)) perm17.symm

theorem edge48_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 48) 3) := by
  have he := mutation_equal (pnode 48) (preverse (prelabel (fork [3] [2] [30,9] [5] [80,24] [7,2]) perm18.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 3 (node_safe t 48)
  rw [show mutate (node t 48) 3=(reverse (relabel (matrix (fork [3] [2] [30,9] [5] [80,24] [7,2]) t) perm18.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [3] [2] [30,9] [5] [80,24] [7,2] t ht (by decide)) perm18.symm)

theorem edge49_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 49) 0) := by
  have he := mutation_equal (pnode 49) (prelabel (pnode 52) perm21.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 49) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 52) perm21.symm

theorem edge49_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 49) 1) := by
  have he := mutation_equal (pnode 49) (prelabel (pnode 64) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 49) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 64) perm0.symm

theorem edge49_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 49) 2) := by
  have he := mutation_equal (pnode 49) (prelabel (zero param11_0 param11_1 param11_2 param11_3 1) perm23.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 49) t) 2)
  rw [he]
  exact Safe.framed (region11_safe t ht 1) perm23.symm

theorem edge49_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 49) 3) := by
  have he := mutation_equal (pnode 49) (prelabel (pnode 34) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 49) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 34) perm0.symm

theorem edge50_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 50) 0) := by
  have he := mutation_equal (pnode 50) (prelabel (pnode 35) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 50) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 35) perm0.symm

theorem edge50_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 50) 1) := by
  have he := mutation_equal (pnode 50) (prelabel (pnode 65) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 50) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 65) perm0.symm

theorem edge50_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 50) 2) := by
  have he := mutation_equal (pnode 50) (prelabel (root [178,156,44,4] [32929,56984,40620,15268,3192,352,16] [822512,1917733,1935786,1104908,390056,87216,12064,944,32] [185,158,44,4] [4621,6724,3840,1076,148,8] [1]) perm13.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 50) 2
  rw [show mutate (node t 50) 2=(relabel (matrix (root [178,156,44,4] [32929,56984,40620,15268,3192,352,16] [822512,1917733,1935786,1104908,390056,87216,12064,944,32] [185,158,44,4] [4621,6724,3840,1076,148,8] [1]) t) perm13.symm) from he]
  exact IsRoot.relabelled (root_sound [178,156,44,4] [32929,56984,40620,15268,3192,352,16] [822512,1917733,1935786,1104908,390056,87216,12064,944,32] [185,158,44,4] [4621,6724,3840,1076,148,8] [1] t ht (by decide)) perm13.symm

theorem edge50_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 50) 3) := by
  have he := mutation_equal (pnode 50) (prelabel (pnode 66) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 50) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 66) perm0.symm

theorem edge51_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 51) 0) := by
  have he := mutation_equal (pnode 51) (prelabel (pnode 67) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 51) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 67) perm0.symm

theorem edge51_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 51) 1) := by
  have he := mutation_equal (pnode 51) (prelabel (pnode 53) perm5.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 51) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 53) perm5.symm

theorem edge51_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 51) 2) := by
  have he := mutation_equal (pnode 51) (preverse (prelabel (zero param13_0 param13_1 param13_2 param13_3 1) perm8.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 51) t) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (region13_safe t ht 1) perm8.symm)

theorem edge51_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 51) 3) := by
  have he := mutation_equal (pnode 51) (prelabel (pnode 35) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 51) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 35) perm0.symm

theorem edge52_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 52) 0) := by
  have he := mutation_equal (pnode 52) (prelabel (pnode 36) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 52) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 36) perm0.symm

theorem edge52_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 52) 1) := by
  have he := mutation_equal (pnode 52) (prelabel (pnode 68) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 52) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 68) perm0.symm

theorem edge52_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 52) 2) := by
  have he := mutation_equal (pnode 52) (preverse (prelabel (root [4,1] [362,418,174,31,2] [15,8,1] [97,84,23,2] [4,1] [1]) perm12.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 52) 2
  rw [show mutate (node t 52) 2=(reverse (relabel (matrix (root [4,1] [362,418,174,31,2] [15,8,1] [97,84,23,2] [4,1] [1]) t) perm12.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [4,1] [362,418,174,31,2] [15,8,1] [97,84,23,2] [4,1] [1] t ht (by decide)) perm12.symm)

theorem edge52_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 52) 3) := by
  have he := mutation_equal (pnode 52) (prelabel (pnode 49) perm21.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 52) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 49) perm21.symm

theorem edge53_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 53) 0) := by
  have he := mutation_equal (pnode 53) (preverse (prelabel (root [26,15,2] [4621,6724,3840,1076,148,8] [701,795,331,60,4] [178,156,44,4] [27,15,2] []) perm0.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 53) 0
  rw [show mutate (node t 53) 0=(reverse (relabel (matrix (root [26,15,2] [4621,6724,3840,1076,148,8] [701,795,331,60,4] [178,156,44,4] [27,15,2] []) t) perm0.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [26,15,2] [4621,6724,3840,1076,148,8] [701,795,331,60,4] [178,156,44,4] [27,15,2] [] t ht (by decide)) perm0.symm)

theorem edge53_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 53) 1) := by
  have he := mutation_equal (pnode 53) (prelabel (pnode 36) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 53) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 36) perm0.symm

theorem edge53_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 53) 2) := by
  have he := mutation_equal (pnode 53) (preverse (prelabel (zero param13_0 param13_1 param13_2 param13_3 0) perm22.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 53) t) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (region13_safe t ht 0) perm22.symm)

theorem edge53_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 53) 3) := by
  have he := mutation_equal (pnode 53) (prelabel (pnode 51) perm5.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 53) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 51) perm5.symm

theorem edge54_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 54) 0) := by
  have he := mutation_equal (pnode 54) (prelabel (pnode 37) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 54) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 37) perm0.symm

theorem edge54_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 54) 1) := by
  have he := mutation_equal (pnode 54) (prelabel (pnode 69) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 54) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 69) perm0.symm

theorem edge54_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 54) 2) := by
  have he := mutation_equal (pnode 54) (preverse (prelabel (root [10,3] [169,101,15] [128,79,12] [17,5] [13,4] [1]) perm13.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 54) 2
  rw [show mutate (node t 54) 2=(reverse (relabel (matrix (root [10,3] [169,101,15] [128,79,12] [17,5] [13,4] [1]) t) perm13.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [10,3] [169,101,15] [128,79,12] [17,5] [13,4] [1] t ht (by decide)) perm13.symm)

theorem edge54_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 54) 3) := by
  have he := mutation_equal (pnode 54) (prelabel (pnode 63) perm19.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 54) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 63) perm19.symm

theorem edge55_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 55) 0) := by
  have he := mutation_equal (pnode 55) (prelabel (pnode 47) perm6.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 55) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 47) perm6.symm

theorem edge55_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 55) 1) := by
  have he := mutation_equal (pnode 55) (prelabel (pnode 62) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 55) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 62) perm0.symm

theorem edge55_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 55) 2) := by
  have he := mutation_equal (pnode 55) (preverse (prelabel (root [48,3] [817,147,6] [381,24] [17,2] [8] [1]) perm14.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 55) 2
  rw [show mutate (node t 55) 2=(reverse (relabel (matrix (root [48,3] [817,147,6] [381,24] [17,2] [8] [1]) t) perm14.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [48,3] [817,147,6] [381,24] [17,2] [8] [1] t ht (by decide)) perm14.symm)

theorem edge55_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 55) 3) := by
  have he := mutation_equal (pnode 55) (prelabel (pnode 40) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 55) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 40) perm0.symm

theorem edge56_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 56) 0) := by
  have he := mutation_equal (pnode 56) (preverse (prelabel (zero param14_0 param14_1 param14_2 param14_3 0) perm19.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 56) t) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (region14_safe t ht 0) perm19.symm)

theorem edge56_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 56) 1) := by
  have he := mutation_equal (pnode 56) (prelabel (pnode 41) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 56) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 41) perm0.symm

theorem edge56_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 56) 2) := by
  have he := mutation_equal (pnode 56) (preverse (prelabel (root [38,8] [20088,12817,2720,192] [1405,600,64] [529,226,24] [37,8] []) perm14.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 56) 2
  rw [show mutate (node t 56) 2=(reverse (relabel (matrix (root [38,8] [20088,12817,2720,192] [1405,600,64] [529,226,24] [37,8] []) t) perm14.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [38,8] [20088,12817,2720,192] [1405,600,64] [529,226,24] [37,8] [] t ht (by decide)) perm14.symm)

theorem edge56_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 56) 3) := by
  have he := mutation_equal (pnode 56) (prelabel (pnode 70) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 56) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 70) perm0.symm

theorem edge57_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 57) 0) := by
  have he := mutation_equal (pnode 57) (prelabel (zero param15_0 param15_1 param15_2 param15_3 0) perm18.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 57) t) 0)
  rw [he]
  exact Safe.framed (region15_safe t ht 0) perm18.symm

theorem edge57_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 57) 1) := by
  have he := mutation_equal (pnode 57) (prelabel (root [38,8] [3797,1598,168] [1405,600,64] [100,21] [37,8] []) perm8.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 57) 1
  rw [show mutate (node t 57) 1=(relabel (matrix (root [38,8] [3797,1598,168] [1405,600,64] [100,21] [37,8] []) t) perm8.symm) from he]
  exact IsRoot.relabelled (root_sound [38,8] [3797,1598,168] [1405,600,64] [100,21] [37,8] [] t ht (by decide)) perm8.symm

theorem edge57_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 57) 2) := by
  have he := mutation_equal (pnode 57) (prelabel (pnode 41) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 57) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 41) perm0.symm

theorem edge57_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 57) 3) := by
  have he := mutation_equal (pnode 57) (prelabel (pnode 71) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 57) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 71) perm0.symm

theorem edge58_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 58) 0) := by
  have he := mutation_equal (pnode 58) (prelabel (fork [53,26,3] [198,154,38,3] [14,3] [10490,13309,6612,1609,192,9] [743,523,120,9] [5,1]) perm2.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (node_safe t 58)
  rw [show mutate (node t 58) 0=(relabel (matrix (fork [53,26,3] [198,154,38,3] [14,3] [10490,13309,6612,1609,192,9] [743,523,120,9] [5,1]) t) perm2.symm) from he]
  exact IsFork.relabelled (fork_sound [53,26,3] [198,154,38,3] [14,3] [10490,13309,6612,1609,192,9] [743,523,120,9] [5,1] t ht (by decide)) perm2.symm

theorem edge58_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 58) 1) := by
  have he := mutation_equal (pnode 58) (preverse (prelabel (fork [4,1] [198,154,38,3] [5,1] [739,788,303,50,3] [19,9,1] [14,3]) perm8.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (node_safe t 58)
  rw [show mutate (node t 58) 1=(reverse (relabel (matrix (fork [4,1] [198,154,38,3] [5,1] [739,788,303,50,3] [19,9,1] [14,3]) t) perm8.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [4,1] [198,154,38,3] [5,1] [739,788,303,50,3] [19,9,1] [14,3] t ht (by decide)) perm8.symm)

theorem edge58_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 58) 2) := by
  have he := mutation_equal (pnode 58) (prelabel (pnode 42) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 58) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 42) perm0.symm

theorem edge58_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 58) 3) := by
  have he := mutation_equal (pnode 58) (prelabel (pnode 72) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 58) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 72) perm0.symm

theorem edge59_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 59) 0) := by
  have he := mutation_equal (pnode 59) (prelabel (zero param12_0 param12_1 param12_2 param12_3 1) perm6.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 59) t) 0)
  rw [he]
  exact Safe.framed (region12_safe t ht 1) perm6.symm

theorem edge59_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 59) 1) := by
  have he := mutation_equal (pnode 59) (prelabel (pnode 45) perm21.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 59) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 45) perm21.symm

theorem edge59_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 59) 2) := by
  have he := mutation_equal (pnode 59) (prelabel (pnode 73) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 59) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 73) perm0.symm

theorem edge59_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 59) 3) := by
  have he := mutation_equal (pnode 59) (prelabel (pnode 42) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 59) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 42) perm0.symm

theorem edge60_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 60) 0) := by
  have he := mutation_equal (pnode 60) (prelabel (pnode 46) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 60) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 46) perm0.symm

theorem edge60_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 60) 1) := by
  have he := mutation_equal (pnode 60) (prelabel (pnode 70) perm21.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 60) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 70) perm21.symm

theorem edge60_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 60) 2) := by
  have he := mutation_equal (pnode 60) (prelabel (pnode 74) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 60) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 74) perm0.symm

theorem edge60_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 60) 3) := by
  have he := mutation_equal (pnode 60) (prelabel (root [14,3] [195,84,9] [7173,4659,1005,72] [14,3] [515,223,24] [1]) perm18.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 60) 3
  rw [show mutate (node t 60) 3=(relabel (matrix (root [14,3] [195,84,9] [7173,4659,1005,72] [14,3] [515,223,24] [1]) t) perm18.symm) from he]
  exact IsRoot.relabelled (root_sound [14,3] [195,84,9] [7173,4659,1005,72] [14,3] [515,223,24] [1] t ht (by decide)) perm18.symm

theorem edge61_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 61) 0) := by
  have he := mutation_equal (pnode 61) (prelabel (pnode 75) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 61) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 75) perm0.symm

theorem edge61_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 61) 1) := by
  have he := mutation_equal (pnode 61) (prelabel (pnode 71) perm18.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 61) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 71) perm18.symm

theorem edge61_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 61) 2) := by
  have he := mutation_equal (pnode 61) (prelabel (pnode 46) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 61) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 46) perm0.symm

theorem edge61_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 61) 3) := by
  have he := mutation_equal (pnode 61) (preverse (prelabel (root [3] [8] [254,55] [3] [97,21] [1]) perm23.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 61) 3
  rw [show mutate (node t 61) 3=(reverse (relabel (matrix (root [3] [8] [254,55] [3] [97,21] [1]) t) perm23.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [3] [8] [254,55] [3] [97,21] [1] t ht (by decide)) perm23.symm)

theorem edge62_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 62) 0) := by
  have he := mutation_equal (pnode 62) (preverse (prelabel (generic param1_0 param1_1 param1_2 param1_3 2) perm1.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 62) t) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (region1_safe t ht 2) perm1.symm)

theorem edge62_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 62) 1) := by
  have he := mutation_equal (pnode 62) (prelabel (pnode 55) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 62) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 55) perm0.symm

theorem edge62_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 62) 2) := by
  have he := mutation_equal (pnode 62) (preverse (prelabel (root [136,9] [2314,425,18] [6525,840,27] [17,2] [48,3] [1]) perm16.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 62) 2
  rw [show mutate (node t 62) 2=(reverse (relabel (matrix (root [136,9] [2314,425,18] [6525,840,27] [17,2] [48,3] [1]) t) perm16.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [136,9] [2314,425,18] [6525,840,27] [17,2] [48,3] [1] t ht (by decide)) perm16.symm)

theorem edge62_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 62) 3) := by
  have he := mutation_equal (pnode 62) (prelabel (fork [3] [2] [136,9] [5] [360,24] [17,2]) perm20.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 3 (node_safe t 62)
  rw [show mutate (node t 62) 3=(relabel (matrix (fork [3] [2] [136,9] [5] [360,24] [17,2]) t) perm20.symm) from he]
  exact IsFork.relabelled (fork_sound [3] [2] [136,9] [5] [360,24] [17,2] t ht (by decide)) perm20.symm

theorem edge63_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 63) 0) := by
  have he := mutation_equal (pnode 63) (prelabel (pnode 54) perm11.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 63) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 54) perm11.symm

theorem edge63_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 63) 1) := by
  have he := mutation_equal (pnode 63) (prelabel (pnode 48) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 63) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 48) perm0.symm

theorem edge63_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 63) 2) := by
  have he := mutation_equal (pnode 63) (prelabel (fork [17,5] [7,2] [30,9] [118,69,10] [509,303,45] [2]) perm12.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 2 (node_safe t 63)
  rw [show mutate (node t 63) 2=(relabel (matrix (fork [17,5] [7,2] [30,9] [118,69,10] [509,303,45] [2]) t) perm12.symm) from he]
  exact IsFork.relabelled (fork_sound [17,5] [7,2] [30,9] [118,69,10] [509,303,45] [2] t ht (by decide)) perm12.symm

theorem edge63_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 63) 3) := by
  have he := mutation_equal (pnode 63) (prelabel (pnode 76) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 63) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 76) perm0.symm

theorem edge64_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 64) 0) := by
  have he := mutation_equal (pnode 64) (prelabel (pnode 77) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 64) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 77) perm0.symm

theorem edge64_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 64) 1) := by
  have he := mutation_equal (pnode 64) (prelabel (pnode 49) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 64) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 49) perm0.symm

theorem edge64_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 64) 2) := by
  have he := mutation_equal (pnode 64) (prelabel (root [2619,3723,2075,567,76,4] [10502,17526,12025,4343,871,92,4] [254016,581112,574242,320166,110171,23963,3218,244,8] [4,1] [97,84,23,2] [1]) perm16.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 64) 2
  rw [show mutate (node t 64) 2=(relabel (matrix (root [2619,3723,2075,567,76,4] [10502,17526,12025,4343,871,92,4] [254016,581112,574242,320166,110171,23963,3218,244,8] [4,1] [97,84,23,2] [1]) t) perm16.symm) from he]
  exact IsRoot.relabelled (root_sound [2619,3723,2075,567,76,4] [10502,17526,12025,4343,871,92,4] [254016,581112,574242,320166,110171,23963,3218,244,8] [4,1] [97,84,23,2] [1] t ht (by decide)) perm16.symm

theorem edge64_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 64) 3) := by
  have he := mutation_equal (pnode 64) (preverse (prelabel (fork [27,15,2] [26,15,2] [2619,3723,2075,567,76,4] [701,795,331,60,4] [70616,139722,117085,53878,14707,2382,212,8] [4,1]) perm20.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 3 (node_safe t 64)
  rw [show mutate (node t 64) 3=(reverse (relabel (matrix (fork [27,15,2] [26,15,2] [2619,3723,2075,567,76,4] [701,795,331,60,4] [70616,139722,117085,53878,14707,2382,212,8] [4,1]) t) perm20.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [27,15,2] [26,15,2] [2619,3723,2075,567,76,4] [701,795,331,60,4] [70616,139722,117085,53878,14707,2382,212,8] [4,1] t ht (by decide)) perm20.symm)

theorem edge65_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 65) 0) := by
  have he := mutation_equal (pnode 65) (prelabel (fork [26,15,2] [119968,243983,209898,99020,27668,4580,416,16] [27,15,2] [3114547,8136354,9353189,6209880,2624316,732132,134852,15816,1072,32] [701,795,331,60,4] [185,158,44,4]) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (node_safe t 65)
  rw [show mutate (node t 65) 0=(relabel (matrix (fork [26,15,2] [119968,243983,209898,99020,27668,4580,416,16] [27,15,2] [3114547,8136354,9353189,6209880,2624316,732132,134852,15816,1072,32] [701,795,331,60,4] [185,158,44,4]) t) perm0.symm) from he]
  exact IsFork.relabelled (fork_sound [26,15,2] [119968,243983,209898,99020,27668,4580,416,16] [27,15,2] [3114547,8136354,9353189,6209880,2624316,732132,134852,15816,1072,32] [701,795,331,60,4] [185,158,44,4] t ht (by decide)) perm0.symm

theorem edge65_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 65) 1) := by
  have he := mutation_equal (pnode 65) (prelabel (pnode 50) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 65) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 50) perm0.symm

theorem edge65_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 65) 2) := by
  have he := mutation_equal (pnode 65) (preverse (prelabel (fork [4621,6724,3840,1076,148,8] [119968,243983,209898,99020,27668,4580,416,16] [185,158,44,4] [554372102,1934110260,3071157468,2934905860,1879953600,850360088,278525664,66563232,11520128,1408240,115424,5696,128] [854886,1974058,1976116,1120120,393244,87568,12080,944,32] [27,15,2]) perm14.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 2 (node_safe t 65)
  rw [show mutate (node t 65) 2=(reverse (relabel (matrix (fork [4621,6724,3840,1076,148,8] [119968,243983,209898,99020,27668,4580,416,16] [185,158,44,4] [554372102,1934110260,3071157468,2934905860,1879953600,850360088,278525664,66563232,11520128,1408240,115424,5696,128] [854886,1974058,1976116,1120120,393244,87568,12080,944,32] [27,15,2]) t) perm14.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [4621,6724,3840,1076,148,8] [119968,243983,209898,99020,27668,4580,416,16] [185,158,44,4] [554372102,1934110260,3071157468,2934905860,1879953600,850360088,278525664,66563232,11520128,1408240,115424,5696,128] [854886,1974058,1976116,1120120,393244,87568,12080,944,32] [27,15,2] t ht (by decide)) perm14.symm)

theorem edge65_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 65) 3) := by
  have he := mutation_equal (pnode 65) (prelabel (pnode 78) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 65) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 78) perm0.symm

theorem edge66_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 66) 0) := by
  have he := mutation_equal (pnode 66) (prelabel (pnode 67) perm21.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 66) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 67) perm21.symm

theorem edge66_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 66) 1) := by
  have he := mutation_equal (pnode 66) (prelabel (pnode 79) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 66) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 79) perm0.symm

theorem edge66_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 66) 2) := by
  have he := mutation_equal (pnode 66) (preverse (prelabel (fork [185,158,44,4] [7,2] [4806,6882,3884,1080,148,8] [1294,1476,624,116,8] [889109,2032518,2017360,1135504,396444,87920,12096,944,32] [26,15,2]) perm16.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 2 (node_safe t 66)
  rw [show mutate (node t 66) 2=(reverse (relabel (matrix (fork [185,158,44,4] [7,2] [4806,6882,3884,1080,148,8] [1294,1476,624,116,8] [889109,2032518,2017360,1135504,396444,87920,12096,944,32] [26,15,2]) t) perm16.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [185,158,44,4] [7,2] [4806,6882,3884,1080,148,8] [1294,1476,624,116,8] [889109,2032518,2017360,1135504,396444,87920,12096,944,32] [26,15,2] t ht (by decide)) perm16.symm)

theorem edge66_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 66) 3) := by
  have he := mutation_equal (pnode 66) (prelabel (pnode 50) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 66) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 50) perm0.symm

theorem edge67_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 67) 0) := by
  have he := mutation_equal (pnode 67) (prelabel (pnode 51) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 67) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 51) perm0.symm

theorem edge67_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 67) 1) := by
  have he := mutation_equal (pnode 67) (prelabel (fork [27,15,2] [26,15,2] [4806,6882,3884,1080,148,8] [701,795,331,60,4] [129584,257748,217666,101180,27964,4596,416,16] [7,2]) perm7.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (node_safe t 67)
  rw [show mutate (node t 67) 1=(relabel (matrix (fork [27,15,2] [26,15,2] [4806,6882,3884,1080,148,8] [701,795,331,60,4] [129584,257748,217666,101180,27964,4596,416,16] [7,2]) t) perm7.symm) from he]
  exact IsFork.relabelled (fork_sound [27,15,2] [26,15,2] [4806,6882,3884,1080,148,8] [701,795,331,60,4] [129584,257748,217666,101180,27964,4596,416,16] [7,2] t ht (by decide)) perm7.symm

theorem edge67_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 67) 2) := by
  have he := mutation_equal (pnode 67) (preverse (prelabel (root [4806,6882,3884,1080,148,8] [33668,57801,40954,15328,3196,352,16] [855441,1974717,1976406,1120176,393248,87568,12080,944,32] [7,2] [178,156,44,4] [1]) perm15.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 67) 2
  rw [show mutate (node t 67) 2=(reverse (relabel (matrix (root [4806,6882,3884,1080,148,8] [33668,57801,40954,15328,3196,352,16] [855441,1974717,1976406,1120176,393248,87568,12080,944,32] [7,2] [178,156,44,4] [1]) t) perm15.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [4806,6882,3884,1080,148,8] [33668,57801,40954,15328,3196,352,16] [855441,1974717,1976406,1120176,393248,87568,12080,944,32] [7,2] [178,156,44,4] [1] t ht (by decide)) perm15.symm)

theorem edge67_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 67) 3) := by
  have he := mutation_equal (pnode 67) (prelabel (pnode 66) perm21.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 67) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 66) perm21.symm

theorem edge68_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 68) 0) := by
  have he := mutation_equal (pnode 68) (prelabel (pnode 80) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 68) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 80) perm0.symm

theorem edge68_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 68) 1) := by
  have he := mutation_equal (pnode 68) (prelabel (pnode 52) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 68) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 52) perm0.symm

theorem edge68_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 68) 2) := by
  have he := mutation_equal (pnode 68) (preverse (prelabel (root [97,84,23,2] [9796,16729,11694,4283,867,92,4] [244220,564383,562548,315883,109304,23871,3214,244,8] [101,85,23,2] [2518,3638,2052,565,76,4] [1]) perm15.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 68) 2
  rw [show mutate (node t 68) 2=(reverse (relabel (matrix (root [97,84,23,2] [9796,16729,11694,4283,867,92,4] [244220,564383,562548,315883,109304,23871,3214,244,8] [101,85,23,2] [2518,3638,2052,565,76,4] [1]) t) perm15.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [97,84,23,2] [9796,16729,11694,4283,867,92,4] [244220,564383,562548,315883,109304,23871,3214,244,8] [101,85,23,2] [2518,3638,2052,565,76,4] [1] t ht (by decide)) perm15.symm)

theorem edge68_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 68) 3) := by
  have he := mutation_equal (pnode 68) (prelabel (pnode 77) perm11.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 68) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 77) perm11.symm

theorem edge69_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 69) 0) := by
  have he := mutation_equal (pnode 69) (preverse (prelabel (fork [2] [16,5] [3] [19,6] [5] [17,5]) perm0.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (node_safe t 69)
  rw [show mutate (node t 69) 0=(reverse (relabel (matrix (fork [2] [16,5] [3] [19,6] [5] [17,5]) t) perm0.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [2] [16,5] [3] [19,6] [5] [17,5] t ht (by decide)) perm0.symm)

theorem edge69_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 69) 1) := by
  have he := mutation_equal (pnode 69) (prelabel (pnode 54) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 69) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 54) perm0.symm

theorem edge69_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 69) 2) := by
  have he := mutation_equal (pnode 69) (prelabel (fork [13,4] [16,5] [17,5] [206,129,20] [222,133,20] [3]) perm14.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 2 (node_safe t 69)
  rw [show mutate (node t 69) 2=(relabel (matrix (fork [13,4] [16,5] [17,5] [206,129,20] [222,133,20] [3]) t) perm14.symm) from he]
  exact IsFork.relabelled (fork_sound [13,4] [16,5] [17,5] [206,129,20] [222,133,20] [3] t ht (by decide)) perm14.symm

theorem edge69_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 69) 3) := by
  have he := mutation_equal (pnode 69) (prelabel (pnode 81) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 69) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 81) perm0.symm

theorem edge70_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 70) 0) := by
  have he := mutation_equal (pnode 70) (preverse (prelabel (zero param14_0 param14_1 param14_2 param14_3 1) perm19.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 70) t) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (region14_safe t ht 1) perm19.symm)

theorem edge70_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 70) 1) := by
  have he := mutation_equal (pnode 70) (prelabel (pnode 60) perm21.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 70) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 60) perm21.symm

theorem edge70_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 70) 2) := by
  have he := mutation_equal (pnode 70) (prelabel (pnode 82) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 70) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 82) perm0.symm

theorem edge70_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 70) 3) := by
  have he := mutation_equal (pnode 70) (prelabel (pnode 56) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 70) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 56) perm0.symm

theorem edge71_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 71) 0) := by
  have he := mutation_equal (pnode 71) (prelabel (zero param15_0 param15_1 param15_2 param15_3 1) perm18.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 71) t) 0)
  rw [he]
  exact Safe.framed (region15_safe t ht 1) perm18.symm

theorem edge71_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 71) 1) := by
  have he := mutation_equal (pnode 71) (prelabel (pnode 83) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 71) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 83) perm0.symm

theorem edge71_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 71) 2) := by
  have he := mutation_equal (pnode 71) (prelabel (pnode 61) perm9.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 71) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 61) perm9.symm

theorem edge71_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 71) 3) := by
  have he := mutation_equal (pnode 71) (prelabel (pnode 57) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 71) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 57) perm0.symm

theorem edge72_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 72) 0) := by
  have he := mutation_equal (pnode 72) (prelabel (root [268,183,41,3] [14205,16667,7735,1774,201,9] [3747,3365,1123,165,9] [53,26,3] [14,3] [1]) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 72) 0
  rw [show mutate (node t 72) 0=(relabel (matrix (root [268,183,41,3] [14205,16667,7735,1774,201,9] [3747,3365,1123,165,9] [53,26,3] [14,3] [1]) t) perm0.symm) from he]
  exact IsRoot.relabelled (root_sound [268,183,41,3] [14205,16667,7735,1774,201,9] [3747,3365,1123,165,9] [53,26,3] [14,3] [1] t ht (by decide)) perm0.symm

theorem edge72_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 72) 1) := by
  have he := mutation_equal (pnode 72) (prelabel (pnode 84) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 72) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 84) perm0.symm

theorem edge72_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 72) 2) := by
  have he := mutation_equal (pnode 72) (prelabel (pnode 73) perm1.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 72) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 73) perm1.symm

theorem edge72_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 72) 3) := by
  have he := mutation_equal (pnode 72) (prelabel (pnode 58) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 72) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 58) perm0.symm

theorem edge73_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 73) 0) := by
  have he := mutation_equal (pnode 73) (preverse (prelabel (root [67,29,3] [17952,20032,8858,1939,210,9] [3550,3279,1114,165,9] [268,183,41,3] [53,26,3] [1]) perm2.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 73) 0
  rw [show mutate (node t 73) 0=(reverse (relabel (matrix (root [67,29,3] [17952,20032,8858,1939,210,9] [3550,3279,1114,165,9] [268,183,41,3] [53,26,3] [1]) t) perm2.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [67,29,3] [17952,20032,8858,1939,210,9] [3550,3279,1114,165,9] [268,183,41,3] [53,26,3] [1] t ht (by decide)) perm2.symm)

theorem edge73_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 73) 1) := by
  have he := mutation_equal (pnode 73) (prelabel (generic param2_0 param2_1 param2_2 param2_3 1) perm11.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 73) t) 1)
  rw [he]
  exact Safe.framed (region2_safe t ht 1) perm11.symm

theorem edge73_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 73) 2) := by
  have he := mutation_equal (pnode 73) (prelabel (pnode 59) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 73) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 59) perm0.symm

theorem edge73_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 73) 3) := by
  have he := mutation_equal (pnode 73) (prelabel (pnode 72) perm1.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 73) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 72) perm1.symm

theorem edge74_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 74) 0) := by
  have he := mutation_equal (pnode 74) (prelabel (fork [37,8] [19041,12368,2672,192] [38,8] [704002,609721,197784,28480,1536] [1405,600,64] [14,3]) perm3.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (node_safe t 74)
  rw [show mutate (node t 74) 0=(relabel (matrix (fork [37,8] [19041,12368,2672,192] [38,8] [704002,609721,197784,28480,1536] [1405,600,64] [14,3]) t) perm3.symm) from he]
  exact IsFork.relabelled (fork_sound [37,8] [19041,12368,2672,192] [38,8] [704002,609721,197784,28480,1536] [1405,600,64] [14,3] t ht (by decide)) perm3.symm

theorem edge74_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 74) 1) := by
  have he := mutation_equal (pnode 74) (prelabel (pnode 85) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 74) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 85) perm0.symm

theorem edge74_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 74) 2) := by
  have he := mutation_equal (pnode 74) (prelabel (pnode 60) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 74) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 60) perm0.symm

theorem edge74_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 74) 3) := by
  have he := mutation_equal (pnode 74) (preverse (prelabel (fork [515,223,24] [19041,12368,2672,192] [14,3] [9806078,10615655,4591128,991568,106944,4608] [7211,4667,1005,72] [38,8]) perm22.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 3 (node_safe t 74)
  rw [show mutate (node t 74) 3=(reverse (relabel (matrix (fork [515,223,24] [19041,12368,2672,192] [14,3] [9806078,10615655,4591128,991568,106944,4608] [7211,4667,1005,72] [38,8]) t) perm22.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [515,223,24] [19041,12368,2672,192] [14,3] [9806078,10615655,4591128,991568,106944,4608] [7211,4667,1005,72] [38,8] t ht (by decide)) perm22.symm)

theorem edge75_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 75) 0) := by
  have he := mutation_equal (pnode 75) (prelabel (pnode 61) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 75) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 61) perm0.symm

theorem edge75_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 75) 1) := by
  have he := mutation_equal (pnode 75) (prelabel (pnode 86) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 75) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 86) perm0.symm

theorem edge75_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 75) 2) := by
  have he := mutation_equal (pnode 75) (preverse (prelabel (fork [37,8] [3586,1553,168] [38,8] [132585,86128,18640,1344] [1405,600,64] [3]) perm13.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 2 (node_safe t 75)
  rw [show mutate (node t 75) 2=(reverse (relabel (matrix (fork [37,8] [3586,1553,168] [38,8] [132585,86128,18640,1344] [1405,600,64] [3]) t) perm13.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [37,8] [3586,1553,168] [38,8] [132585,86128,18640,1344] [1405,600,64] [3] t ht (by decide)) perm13.symm)

theorem edge75_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 75) 3) := by
  have he := mutation_equal (pnode 75) (prelabel (fork [97,21] [3586,1553,168] [3] [347805,225939,48909,3528] [292,63] [38,8]) perm19.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 3 (node_safe t 75)
  rw [show mutate (node t 75) 3=(relabel (matrix (fork [97,21] [3586,1553,168] [3] [347805,225939,48909,3528] [292,63] [38,8]) t) perm19.symm) from he]
  exact IsFork.relabelled (fork_sound [97,21] [3586,1553,168] [3] [347805,225939,48909,3528] [292,63] [38,8] t ht (by decide)) perm19.symm

theorem edge76_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 76) 0) := by
  have he := mutation_equal (pnode 76) (prelabel (pnode 81) perm6.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 76) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 81) perm6.symm

theorem edge76_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 76) 1) := by
  have he := mutation_equal (pnode 76) (prelabel (generic param3_0 param3_1 param3_2 param3_3 1) perm7.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 76) t) 1)
  rw [he]
  exact Safe.framed (region3_safe t ht 1) perm7.symm

theorem edge76_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 76) 2) := by
  have he := mutation_equal (pnode 76) (preverse (prelabel (root [30,9] [2008,1203,180] [389,237,36] [67,20] [13,4] [1]) perm17.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 76) 2
  rw [show mutate (node t 76) 2=(reverse (relabel (matrix (root [30,9] [2008,1203,180] [389,237,36] [67,20] [13,4] [1]) t) perm17.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [30,9] [2008,1203,180] [389,237,36] [67,20] [13,4] [1] t ht (by decide)) perm17.symm)

theorem edge76_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 76) 3) := by
  have he := mutation_equal (pnode 76) (prelabel (pnode 63) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 76) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 63) perm0.symm

theorem edge77_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 77) 0) := by
  have he := mutation_equal (pnode 77) (prelabel (pnode 64) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 77) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 64) perm0.symm

theorem edge77_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 77) 1) := by
  have he := mutation_equal (pnode 77) (prelabel (pnode 68) perm19.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 77) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 68) perm19.symm

theorem edge77_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 77) 2) := by
  have he := mutation_equal (pnode 77) (prelabel (fork [101,85,23,2] [4,1] [2619,3723,2075,567,76,4] [403,441,177,31,2] [264518,598638,586267,324509,111042,24055,3222,244,8] [26,15,2]) perm14.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 2 (node_safe t 77)
  rw [show mutate (node t 77) 2=(relabel (matrix (fork [101,85,23,2] [4,1] [2619,3723,2075,567,76,4] [403,441,177,31,2] [264518,598638,586267,324509,111042,24055,3222,244,8] [26,15,2]) t) perm14.symm) from he]
  exact IsFork.relabelled (fork_sound [101,85,23,2] [4,1] [2619,3723,2075,567,76,4] [403,441,177,31,2] [264518,598638,586267,324509,111042,24055,3222,244,8] [26,15,2] t ht (by decide)) perm14.symm

theorem edge77_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 77) 3) := by
  have he := mutation_equal (pnode 77) (prelabel (pnode 88) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 77) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 88) perm0.symm

theorem edge78_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 78) 0) := by
  have he := mutation_equal (pnode 78) (prelabel (pnode 89) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 78) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 89) perm0.symm

theorem edge78_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 78) 1) := by
  have he := mutation_equal (pnode 78) (prelabel (pnode 79) perm5.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 78) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 79) perm5.symm

theorem edge78_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 78) 2) := by
  have he := mutation_equal (pnode 78) (preverse (prelabel (root [124963,251024,213826,100104,27816,4588,416,16] [577454024,2000233116,3155833242,2998738956,1911325220,860863324,280951832,66945056,11559312,1410608,115488,5696,128] [23118128,66183579,84717972,63848656,31374832,10503588,2426184,381824,39184,2368,64] [4621,6724,3840,1076,148,8] [185,158,44,4] [1]) perm12.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 78) 2
  rw [show mutate (node t 78) 2=(reverse (relabel (matrix (root [124963,251024,213826,100104,27816,4588,416,16] [577454024,2000233116,3155833242,2998738956,1911325220,860863324,280951832,66945056,11559312,1410608,115488,5696,128] [23118128,66183579,84717972,63848656,31374832,10503588,2426184,381824,39184,2368,64] [4621,6724,3840,1076,148,8] [185,158,44,4] [1]) t) perm12.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [124963,251024,213826,100104,27816,4588,416,16] [577454024,2000233116,3155833242,2998738956,1911325220,860863324,280951832,66945056,11559312,1410608,115488,5696,128] [23118128,66183579,84717972,63848656,31374832,10503588,2426184,381824,39184,2368,64] [4621,6724,3840,1076,148,8] [185,158,44,4] [1] t ht (by decide)) perm12.symm)

theorem edge78_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 78) 3) := by
  have he := mutation_equal (pnode 78) (prelabel (pnode 65) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 78) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 65) perm0.symm

theorem edge79_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 79) 0) := by
  have he := mutation_equal (pnode 79) (preverse (prelabel (generic param4_0 param4_1 param4_2 param4_3 1) perm4.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 79) t) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (region4_safe t ht 1) perm4.symm)

theorem edge79_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 79) 1) := by
  have he := mutation_equal (pnode 79) (prelabel (pnode 66) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 79) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 66) perm0.symm

theorem edge79_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 79) 2) := by
  have he := mutation_equal (pnode 79) (prelabel (root [4806,6882,3884,1080,148,8] [600572152,2066416695,3240551214,3062587612,1942700052,871366912,283378016,67326880,11598496,1412976,115552,5696,128] [22208525,64117266,82677572,62704832,30976708,10415488,2414080,380880,39152,2368,64] [124963,251024,213826,100104,27816,4588,416,16] [4621,6724,3840,1076,148,8] [1]) perm14.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 79) 2
  rw [show mutate (node t 79) 2=(relabel (matrix (root [4806,6882,3884,1080,148,8] [600572152,2066416695,3240551214,3062587612,1942700052,871366912,283378016,67326880,11598496,1412976,115552,5696,128] [22208525,64117266,82677572,62704832,30976708,10415488,2414080,380880,39152,2368,64] [124963,251024,213826,100104,27816,4588,416,16] [4621,6724,3840,1076,148,8] [1]) t) perm14.symm) from he]
  exact IsRoot.relabelled (root_sound [4806,6882,3884,1080,148,8] [600572152,2066416695,3240551214,3062587612,1942700052,871366912,283378016,67326880,11598496,1412976,115552,5696,128] [22208525,64117266,82677572,62704832,30976708,10415488,2414080,380880,39152,2368,64] [124963,251024,213826,100104,27816,4588,416,16] [4621,6724,3840,1076,148,8] [1] t ht (by decide)) perm14.symm

theorem edge79_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 79) 3) := by
  have he := mutation_equal (pnode 79) (prelabel (pnode 78) perm5.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 79) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 78) perm5.symm

theorem edge80_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 80) 0) := by
  have he := mutation_equal (pnode 80) (prelabel (pnode 68) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 80) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 68) perm0.symm

theorem edge80_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 80) 1) := by
  have he := mutation_equal (pnode 80) (preverse (prelabel (fork [26,15,2] [65371,132274,112935,52744,14555,2374,212,8] [27,15,2] [1697128,4416051,5049110,3329352,1395384,385533,70232,8136,544,16] [701,795,331,60,4] [101,85,23,2]) perm6.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (node_safe t 80)
  rw [show mutate (node t 80) 1=(reverse (relabel (matrix (fork [26,15,2] [65371,132274,112935,52744,14555,2374,212,8] [27,15,2] [1697128,4416051,5049110,3329352,1395384,385533,70232,8136,544,16] [701,795,331,60,4] [101,85,23,2]) t) perm6.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [26,15,2] [65371,132274,112935,52744,14555,2374,212,8] [27,15,2] [1697128,4416051,5049110,3329352,1395384,385533,70232,8136,544,16] [701,795,331,60,4] [101,85,23,2] t ht (by decide)) perm6.symm)

theorem edge80_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 80) 2) := by
  have he := mutation_equal (pnode 80) (prelabel (fork [2518,3638,2052,565,76,4] [65371,132274,112935,52744,14555,2374,212,8] [101,85,23,2] [164604152,570885615,899724432,852027785,539977788,241282093,77949804,18346707,3122594,374840,30128,1456,32] [254319,581468,574396,320195,110173,23963,3218,244,8] [27,15,2]) perm12.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 2 (node_safe t 80)
  rw [show mutate (node t 80) 2=(relabel (matrix (fork [2518,3638,2052,565,76,4] [65371,132274,112935,52744,14555,2374,212,8] [101,85,23,2] [164604152,570885615,899724432,852027785,539977788,241282093,77949804,18346707,3122594,374840,30128,1456,32] [254319,581468,574396,320195,110173,23963,3218,244,8] [27,15,2]) t) perm12.symm) from he]
  exact IsFork.relabelled (fork_sound [2518,3638,2052,565,76,4] [65371,132274,112935,52744,14555,2374,212,8] [101,85,23,2] [164604152,570885615,899724432,852027785,539977788,241282093,77949804,18346707,3122594,374840,30128,1456,32] [254319,581468,574396,320195,110173,23963,3218,244,8] [27,15,2] t ht (by decide)) perm12.symm

theorem edge80_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 80) 3) := by
  have he := mutation_equal (pnode 80) (prelabel (pnode 90) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 80) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 90) perm0.symm

theorem edge81_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 81) 0) := by
  have he := mutation_equal (pnode 81) (prelabel (pnode 87) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 81) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 87) perm0.symm

theorem edge81_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 81) 1) := by
  have he := mutation_equal (pnode 81) (prelabel (pnode 76) perm6.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 81) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 76) perm6.symm

theorem edge81_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 81) 2) := by
  have he := mutation_equal (pnode 81) (prelabel (root [67,20] [872,528,80] [1136,675,100] [13,4] [17,5] [1]) perm12.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 81) 2
  rw [show mutate (node t 81) 2=(relabel (matrix (root [67,20] [872,528,80] [1136,675,100] [13,4] [17,5] [1]) t) perm12.symm) from he]
  exact IsRoot.relabelled (root_sound [67,20] [872,528,80] [1136,675,100] [13,4] [17,5] [1] t ht (by decide)) perm12.symm

theorem edge81_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 81) 3) := by
  have he := mutation_equal (pnode 81) (prelabel (pnode 69) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 81) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 69) perm0.symm

theorem edge82_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 82) 0) := by
  have he := mutation_equal (pnode 82) (prelabel (root [529,226,24] [10354080,11085716,4742180,1013120,108096,4608] [272434,234357,75454,10776,576] [19573,12594,2696,192] [515,223,24] [1]) perm3.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 82) 0
  rw [show mutate (node t 82) 0=(relabel (matrix (root [529,226,24] [10354080,11085716,4742180,1013120,108096,4608] [272434,234357,75454,10776,576] [19573,12594,2696,192] [515,223,24] [1]) t) perm3.symm) from he]
  exact IsRoot.relabelled (root_sound [529,226,24] [10354080,11085716,4742180,1013120,108096,4608] [272434,234357,75454,10776,576] [19573,12594,2696,192] [515,223,24] [1] t ht (by decide)) perm3.symm

theorem edge82_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 82) 1) := by
  have he := mutation_equal (pnode 82) (prelabel (pnode 85) perm23.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 82) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 85) perm23.symm

theorem edge82_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 82) 2) := by
  have he := mutation_equal (pnode 82) (prelabel (pnode 70) perm0.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 82) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 70) perm0.symm

theorem edge82_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 82) 3) := by
  have he := mutation_equal (pnode 82) (preverse (prelabel (generic param5_0 param5_1 param5_2 param5_3 1) perm21.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 82) t) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (region5_safe t ht 1) perm21.symm)

theorem edge83_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 83) 0) := by
  have he := mutation_equal (pnode 83) (preverse (prelabel (root [100,21] [369963,235392,49917,3528] [9699,4137,441] [3700,1577,168] [97,21] [1]) perm1.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 83) 0
  rw [show mutate (node t 83) 0=(reverse (relabel (matrix (root [100,21] [369963,235392,49917,3528] [9699,4137,441] [3700,1577,168] [97,21] [1]) t) perm1.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [100,21] [369963,235392,49917,3528] [9699,4137,441] [3700,1577,168] [97,21] [1] t ht (by decide)) perm1.symm)

theorem edge83_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 83) 1) := by
  have he := mutation_equal (pnode 83) (prelabel (pnode 71) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 83) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 71) perm0.symm

theorem edge83_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 83) 2) := by
  have he := mutation_equal (pnode 83) (prelabel (pnode 86) perm15.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 83) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 86) perm15.symm

theorem edge83_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 83) 3) := by
  have he := mutation_equal (pnode 83) (prelabel (generic param6_0 param6_1 param6_2 param6_3 1) perm23.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 83) t) 3)
  rw [he]
  exact Safe.framed (region6_safe t ht 1) perm23.symm

theorem edge84_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 84) 0) := by
  have he := mutation_equal (pnode 84) (prelabel (root [1326,1180,388,56,3] [70282,97017,55222,16596,2779,246,9] [355363,558897,374290,138370,30500,4009,291,9] [53,26,3] [268,183,41,3] [1]) perm5.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 84) 0
  rw [show mutate (node t 84) 0=(relabel (matrix (root [1326,1180,388,56,3] [70282,97017,55222,16596,2779,246,9] [355363,558897,374290,138370,30500,4009,291,9] [53,26,3] [268,183,41,3] [1]) t) perm5.symm) from he]
  exact IsRoot.relabelled (root_sound [1326,1180,388,56,3] [70282,97017,55222,16596,2779,246,9] [355363,558897,374290,138370,30500,4009,291,9] [53,26,3] [268,183,41,3] [1] t ht (by decide)) perm5.symm

theorem edge84_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 84) 1) := by
  have he := mutation_equal (pnode 84) (prelabel (pnode 72) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 84) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 72) perm0.symm

theorem edge84_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 84) 2) := by
  have he := mutation_equal (pnode 84) (prelabel (generic param2_0 param2_1 param2_2 param2_3 2) perm15.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 84) t) 2)
  rw [he]
  exact Safe.framed (region2_safe t ht 2) perm15.symm

theorem edge84_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 84) 3) := by
  have he := mutation_equal (pnode 84) (preverse (prelabel (fork [5,1] [4,1] [1326,1180,388,56,3] [19,9,1] [6362,7043,3079,665,71,3] [53,26,3]) perm21.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 3 (node_safe t 84)
  rw [show mutate (node t 84) 3=(reverse (relabel (matrix (fork [5,1] [4,1] [1326,1180,388,56,3] [19,9,1] [6362,7043,3079,665,71,3] [53,26,3]) t) perm21.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [5,1] [4,1] [1326,1180,388,56,3] [19,9,1] [6362,7043,3079,665,71,3] [53,26,3] t ht (by decide)) perm21.symm)

theorem edge85_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 85) 0) := by
  have he := mutation_equal (pnode 85) (prelabel (pnode 91) perm18.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 85) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 91) perm18.symm

theorem edge85_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 85) 1) := by
  have he := mutation_equal (pnode 85) (prelabel (pnode 74) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 85) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 74) perm0.symm

theorem edge85_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 85) 2) := by
  have he := mutation_equal (pnode 85) (prelabel (pnode 82) perm23.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 85) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 82) perm23.symm

theorem edge85_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 85) 3) := by
  have he := mutation_equal (pnode 85) (preverse (prelabel (root [19573,12594,2696,192] [10080096,10850689,4666654,1002344,107520,4608] [273984,235027,75526,10776,576] [515,223,24] [14,3] [1]) perm19.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 85) 3
  rw [show mutate (node t 85) 3=(reverse (relabel (matrix (root [19573,12594,2696,192] [10080096,10850689,4666654,1002344,107520,4608] [273984,235027,75526,10776,576] [515,223,24] [14,3] [1]) t) perm19.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [19573,12594,2696,192] [10080096,10850689,4666654,1002344,107520,4608] [273984,235027,75526,10776,576] [515,223,24] [14,3] [1] t ht (by decide)) perm19.symm)

theorem edge86_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 86) 0) := by
  have he := mutation_equal (pnode 86) (prelabel (pnode 83) perm20.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 86) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 83) perm20.symm

theorem edge86_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 86) 1) := by
  have he := mutation_equal (pnode 86) (prelabel (pnode 75) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 86) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 75) perm0.symm

theorem edge86_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 86) 2) := by
  have he := mutation_equal (pnode 86) (prelabel (pnode 92) perm21.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 86) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 92) perm21.symm

theorem edge86_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 86) 3) := by
  have he := mutation_equal (pnode 86) (prelabel (root [3700,1577,168] [358901,230669,49413,3528] [11062,4723,504] [97,21] [3] [1]) perm22.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 86) 3
  rw [show mutate (node t 86) 3=(relabel (matrix (root [3700,1577,168] [358901,230669,49413,3528] [11062,4723,504] [97,21] [3] [1]) t) perm22.symm) from he]
  exact IsRoot.relabelled (root_sound [3700,1577,168] [358901,230669,49413,3528] [11062,4723,504] [97,21] [3] [1] t ht (by decide)) perm22.symm

theorem edge87_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 87) 0) := by
  have he := mutation_equal (pnode 87) (prelabel (pnode 81) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 87) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 81) perm0.symm

theorem edge87_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 87) 1) := by
  have he := mutation_equal (pnode 87) (prelabel (generic param3_0 param3_1 param3_2 param3_3 2) perm7.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 87) t) 1)
  rw [he]
  exact Safe.framed (region3_safe t ht 2) perm7.symm

theorem edge87_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 87) 2) := by
  have he := mutation_equal (pnode 87) (prelabel (root [184,55] [2394,1451,220] [12325,7365,1100] [13,4] [67,20] [1]) perm17.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 87) 2
  rw [show mutate (node t 87) 2=(relabel (matrix (root [184,55] [2394,1451,220] [12325,7365,1100] [13,4] [67,20] [1]) t) perm17.symm) from he]
  exact IsRoot.relabelled (root_sound [184,55] [2394,1451,220] [12325,7365,1100] [13,4] [67,20] [1] t ht (by decide)) perm17.symm

theorem edge87_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 87) 3) := by
  have he := mutation_equal (pnode 87) (preverse (prelabel (fork [3] [2] [184,55] [5] [485,145] [13,4]) perm18.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 3 (node_safe t 87)
  rw [show mutate (node t 87) 3=(reverse (relabel (matrix (fork [3] [2] [184,55] [5] [485,145] [13,4]) t) perm18.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [3] [2] [184,55] [5] [485,145] [13,4] t ht (by decide)) perm18.symm)

theorem edge88_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 88) 0) := by
  have he := mutation_equal (pnode 88) (prelabel (generic param7_0 param7_1 param7_2 param7_3 1) perm1.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 88) t) 0)
  rw [he]
  exact Safe.framed (region7_safe t ht 1) perm1.symm

theorem edge88_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 88) 1) := by
  have he := mutation_equal (pnode 88) (prelabel (pnode 90) perm6.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 88) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 90) perm6.symm

theorem edge88_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 88) 2) := by
  have he := mutation_equal (pnode 88) (preverse (prelabel (root [2619,3723,2075,567,76,4] [178348636,609932835,949215507,888880472,557831439,247162157,79283162,18552275,3143218,376056,30160,1456,32] [6594641,18902436,24143312,18095887,8814553,2915843,663451,102540,10304,608,16] [68098,136084,115033,53313,14631,2378,212,8] [2518,3638,2052,565,76,4] [1]) perm16.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 88) 2
  rw [show mutate (node t 88) 2=(reverse (relabel (matrix (root [2619,3723,2075,567,76,4] [178348636,609932835,949215507,888880472,557831439,247162157,79283162,18552275,3143218,376056,30160,1456,32] [6594641,18902436,24143312,18095887,8814553,2915843,663451,102540,10304,608,16] [68098,136084,115033,53313,14631,2378,212,8] [2518,3638,2052,565,76,4] [1]) t) perm16.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [2619,3723,2075,567,76,4] [178348636,609932835,949215507,888880472,557831439,247162157,79283162,18552275,3143218,376056,30160,1456,32] [6594641,18902436,24143312,18095887,8814553,2915843,663451,102540,10304,608,16] [68098,136084,115033,53313,14631,2378,212,8] [2518,3638,2052,565,76,4] [1] t ht (by decide)) perm16.symm)

theorem edge88_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 88) 3) := by
  have he := mutation_equal (pnode 88) (prelabel (pnode 77) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 88) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 77) perm0.symm

theorem edge89_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 89) 0) := by
  have he := mutation_equal (pnode 89) (prelabel (pnode 78) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 89) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 78) perm0.symm

theorem edge89_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 89) 1) := by
  have he := mutation_equal (pnode 89) (preverse (prelabel (generic param4_0 param4_1 param4_2 param4_3 2) perm7.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 89) t) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (region4_safe t ht 2) perm7.symm)

theorem edge89_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 89) 2) := by
  have he := mutation_equal (pnode 89) (preverse (prelabel (root [3373816,8651935,9788544,6412242,2680244,741324,135684,15848,1072,32] [15590403762,62666130434,116363926206,132302796554,102898138520,57910578392,24321287684,7743519696,1878180896,345366208,47395920,4707328,319872,13312,256] [421602168781,1928080540974,4116458735326,5446193596276,4997542543220,3372561399104,1731419247320,689783794400,215517952032,52986059360,10216660464,1528774768,174038432,14572160,846336,30464,512] [4621,6724,3840,1076,148,8] [124963,251024,213826,100104,27816,4588,416,16] [1]) perm17.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 89) 2
  rw [show mutate (node t 89) 2=(reverse (relabel (matrix (root [3373816,8651935,9788544,6412242,2680244,741324,135684,15848,1072,32] [15590403762,62666130434,116363926206,132302796554,102898138520,57910578392,24321287684,7743519696,1878180896,345366208,47395920,4707328,319872,13312,256] [421602168781,1928080540974,4116458735326,5446193596276,4997542543220,3372561399104,1731419247320,689783794400,215517952032,52986059360,10216660464,1528774768,174038432,14572160,846336,30464,512] [4621,6724,3840,1076,148,8] [124963,251024,213826,100104,27816,4588,416,16] [1]) t) perm17.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [3373816,8651935,9788544,6412242,2680244,741324,135684,15848,1072,32] [15590403762,62666130434,116363926206,132302796554,102898138520,57910578392,24321287684,7743519696,1878180896,345366208,47395920,4707328,319872,13312,256] [421602168781,1928080540974,4116458735326,5446193596276,4997542543220,3372561399104,1731419247320,689783794400,215517952032,52986059360,10216660464,1528774768,174038432,14572160,846336,30464,512] [4621,6724,3840,1076,148,8] [124963,251024,213826,100104,27816,4588,416,16] [1] t ht (by decide)) perm17.symm)

theorem edge89_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 89) 3) := by
  have he := mutation_equal (pnode 89) (prelabel (fork [27,15,2] [26,15,2] [3373816,8651935,9788544,6412242,2680244,741324,135684,15848,1072,32] [701,795,331,60,4] [90968069,283958461,400603519,337162460,188099490,73039304,20143400,3945788,538032,48640,2624,64] [4621,6724,3840,1076,148,8]) perm18.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 3 (node_safe t 89)
  rw [show mutate (node t 89) 3=(relabel (matrix (fork [27,15,2] [26,15,2] [3373816,8651935,9788544,6412242,2680244,741324,135684,15848,1072,32] [701,795,331,60,4] [90968069,283958461,400603519,337162460,188099490,73039304,20143400,3945788,538032,48640,2624,64] [4621,6724,3840,1076,148,8]) t) perm18.symm) from he]
  exact IsFork.relabelled (fork_sound [27,15,2] [26,15,2] [3373816,8651935,9788544,6412242,2680244,741324,135684,15848,1072,32] [701,795,331,60,4] [90968069,283958461,400603519,337162460,188099490,73039304,20143400,3945788,538032,48640,2624,64] [4621,6724,3840,1076,148,8] t ht (by decide)) perm18.symm

theorem edge90_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 90) 0) := by
  have he := mutation_equal (pnode 90) (prelabel (pnode 88) perm6.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 90) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 88) perm6.symm

theorem edge90_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 90) 1) := by
  have he := mutation_equal (pnode 90) (prelabel (pnode 93) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 90) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 93) perm0.symm

theorem edge90_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 90) 2) := by
  have he := mutation_equal (pnode 90) (prelabel (root [68098,136084,115033,53313,14631,2378,212,8] [171470765,590400036,924463782,870451926,548904176,244222079,78616481,18449491,3132906,375448,30144,1456,32] [6877871,19532799,24751725,18428546,8927263,2940078,666681,102784,10312,608,16] [2518,3638,2052,565,76,4] [101,85,23,2] [1]) perm14.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 90) 2
  rw [show mutate (node t 90) 2=(relabel (matrix (root [68098,136084,115033,53313,14631,2378,212,8] [171470765,590400036,924463782,870451926,548904176,244222079,78616481,18449491,3132906,375448,30144,1456,32] [6877871,19532799,24751725,18428546,8927263,2940078,666681,102784,10312,608,16] [2518,3638,2052,565,76,4] [101,85,23,2] [1]) t) perm14.symm) from he]
  exact IsRoot.relabelled (root_sound [68098,136084,115033,53313,14631,2378,212,8] [171470765,590400036,924463782,870451926,548904176,244222079,78616481,18449491,3132906,375448,30144,1456,32] [6877871,19532799,24751725,18428546,8927263,2940078,666681,102784,10312,608,16] [2518,3638,2052,565,76,4] [101,85,23,2] [1] t ht (by decide)) perm14.symm

theorem edge90_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 90) 3) := by
  have he := mutation_equal (pnode 90) (prelabel (pnode 80) perm0.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 90) t) 3)
  rw [he]
  exact Safe.framed (node_safe t 80) perm0.symm

theorem edge91_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 91) 0) := by
  have he := mutation_equal (pnode 91) (preverse (prelabel (root [743760,635153,203200,28864,1536] [383036437,492962283,264137359,75422232,12104512,1035264,36864] [14557614442,21798763101,13981527442,4979230280,1063353920,136176128,9682944,294912] [515,223,24] [19573,12594,2696,192] [1]) perm3.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 91) 0
  rw [show mutate (node t 91) 0=(reverse (relabel (matrix (root [743760,635153,203200,28864,1536] [383036437,492962283,264137359,75422232,12104512,1035264,36864] [14557614442,21798763101,13981527442,4979230280,1063353920,136176128,9682944,294912] [515,223,24] [19573,12594,2696,192] [1]) t) perm3.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [743760,635153,203200,28864,1536] [383036437,492962283,264137359,75422232,12104512,1035264,36864] [14557614442,21798763101,13981527442,4979230280,1063353920,136176128,9682944,294912] [515,223,24] [19573,12594,2696,192] [1] t ht (by decide)) perm3.symm)

theorem edge91_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 91) 1) := by
  have he := mutation_equal (pnode 91) (prelabel (pnode 85) perm9.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 91) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 85) perm9.symm

theorem edge91_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 91) 2) := by
  have he := mutation_equal (pnode 91) (prelabel (fork [38,8] [37,8] [743760,635153,203200,28864,1536] [1405,600,64] [28243307,30073300,12800128,2722240,289280,12288] [515,223,24]) perm15.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 2 (node_safe t 91)
  rw [show mutate (node t 91) 2=(relabel (matrix (fork [38,8] [37,8] [743760,635153,203200,28864,1536] [1405,600,64] [28243307,30073300,12800128,2722240,289280,12288] [515,223,24]) t) perm15.symm) from he]
  exact IsFork.relabelled (fork_sound [38,8] [37,8] [743760,635153,203200,28864,1536] [1405,600,64] [28243307,30073300,12800128,2722240,289280,12288] [515,223,24] t ht (by decide)) perm15.symm

theorem edge91_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 91) 3) := by
  have he := mutation_equal (pnode 91) (preverse (prelabel (generic param5_0 param5_1 param5_2 param5_3 2) perm21.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 91) t) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (region5_safe t ht 2) perm21.symm)

theorem edge92_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 92) 0) := by
  have he := mutation_equal (pnode 92) (prelabel (root [140597,89526,19000,1344] [13637946,11636567,3723046,529368,28224] [520208862,552967661,235102798,49976168,5311488,225792] [97,21] [3700,1577,168] [1]) perm1.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 92) 0
  rw [show mutate (node t 92) 0=(relabel (matrix (root [140597,89526,19000,1344] [13637946,11636567,3723046,529368,28224] [520208862,552967661,235102798,49976168,5311488,225792] [97,21] [3700,1577,168] [1]) t) perm1.symm) from he]
  exact IsRoot.relabelled (root_sound [140597,89526,19000,1344] [13637946,11636567,3723046,529368,28224] [520208862,552967661,235102798,49976168,5311488,225792] [97,21] [3700,1577,168] [1] t ht (by decide)) perm1.symm

theorem edge92_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 92) 1) := by
  have he := mutation_equal (pnode 92) (preverse (prelabel (fork [38,8] [37,8] [140597,89526,19000,1344] [1405,600,64] [5338986,4525187,1438040,203072,10752] [97,21]) perm9.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (node_safe t 92)
  rw [show mutate (node t 92) 1=(reverse (relabel (matrix (fork [38,8] [37,8] [140597,89526,19000,1344] [1405,600,64] [5338986,4525187,1438040,203072,10752] [97,21]) t) perm9.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [38,8] [37,8] [140597,89526,19000,1344] [1405,600,64] [5338986,4525187,1438040,203072,10752] [97,21] t ht (by decide)) perm9.symm)

theorem edge92_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 92) 2) := by
  have he := mutation_equal (pnode 92) (prelabel (pnode 86) perm21.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 92) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 86) perm21.symm

theorem edge92_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 92) 3) := by
  have he := mutation_equal (pnode 92) (prelabel (generic param6_0 param6_1 param6_2 param6_3 2) perm23.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 92) t) 3)
  rw [he]
  exact Safe.framed (region6_safe t ht 2) perm23.symm

theorem edge93_0 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 93) 0) := by
  have he := mutation_equal (pnode 93) (prelabel (generic param7_0 param7_1 param7_2 param7_3 2) perm1.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 93) t) 0)
  rw [he]
  exact Safe.framed (region7_safe t ht 2) perm1.symm

theorem edge93_1 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 93) 1) := by
  have he := mutation_equal (pnode 93) (prelabel (pnode 90) perm0.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 93) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 90) perm0.symm

theorem edge93_2 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 93) 2) := by
  have he := mutation_equal (pnode 93) (prelabel (root [1838545,4695653,5283324,3437112,1424798,390297,70656,8152,544,16] [4629456336,18512280979,34158889788,38549638609,29726009033,16568438662,6883781306,2165827386,518563781,94029668,12711420,1242368,82992,3392,64] [125201237383,569961135759,1210280387587,1591209717326,1449757553588,970595972299,493922597444,194889893515,60259379475,14649290995,2790811146,412276028,46299176,3821200,218592,7744,128] [2518,3638,2052,565,76,4] [68098,136084,115033,53313,14631,2378,212,8] [1]) perm16.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 93) 2
  rw [show mutate (node t 93) 2=(relabel (matrix (root [1838545,4695653,5283324,3437112,1424798,390297,70656,8152,544,16] [4629456336,18512280979,34158889788,38549638609,29726009033,16568438662,6883781306,2165827386,518563781,94029668,12711420,1242368,82992,3392,64] [125201237383,569961135759,1210280387587,1591209717326,1449757553588,970595972299,493922597444,194889893515,60259379475,14649290995,2790811146,412276028,46299176,3821200,218592,7744,128] [2518,3638,2052,565,76,4] [68098,136084,115033,53313,14631,2378,212,8] [1]) t) perm16.symm) from he]
  exact IsRoot.relabelled (root_sound [1838545,4695653,5283324,3437112,1424798,390297,70656,8152,544,16] [4629456336,18512280979,34158889788,38549638609,29726009033,16568438662,6883781306,2165827386,518563781,94029668,12711420,1242368,82992,3392,64] [125201237383,569961135759,1210280387587,1591209717326,1449757553588,970595972299,493922597444,194889893515,60259379475,14649290995,2790811146,412276028,46299176,3821200,218592,7744,128] [2518,3638,2052,565,76,4] [68098,136084,115033,53313,14631,2378,212,8] [1] t ht (by decide)) perm16.symm

theorem edge93_3 (t : Int) (ht : 0≤t) : SafeCore t (mutate (node t 93) 3) := by
  have he := mutation_equal (pnode 93) (preverse (prelabel (fork [27,15,2] [26,15,2] [1838545,4695653,5283324,3437112,1424798,390297,70656,8152,544,16] [701,795,331,60,4] [49572617,154224722,216646600,181389877,100578243,38781835,10611551,2060530,278280,24896,1328,32] [2518,3638,2052,565,76,4]) perm20.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 3 (node_safe t 93)
  rw [show mutate (node t 93) 3=(reverse (relabel (matrix (fork [27,15,2] [26,15,2] [1838545,4695653,5283324,3437112,1424798,390297,70656,8152,544,16] [701,795,331,60,4] [49572617,154224722,216646600,181389877,100578243,38781835,10611551,2060530,278280,24896,1328,32] [2518,3638,2052,565,76,4]) t) perm20.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [27,15,2] [26,15,2] [1838545,4695653,5283324,3437112,1424798,390297,70656,8152,544,16] [701,795,331,60,4] [49572617,154224722,216646600,181389877,100578243,38781835,10611551,2060530,278280,24896,1328,32] [2518,3638,2052,565,76,4] t ht (by decide)) perm20.symm)

theorem all_cyclic (t : Int) (ht : 0≤t) (i : Fin 94) : ¬ Acyclic (node t i) := by
  rcases finCore i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
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
  · exact cyclic83 t ht
  · exact cyclic84 t ht
  · exact cyclic85 t ht
  · exact cyclic86 t ht
  · exact cyclic87 t ht
  · exact cyclic88 t ht
  · exact cyclic89 t ht
  · exact cyclic90 t ht
  · exact cyclic91 t ht
  · exact cyclic92 t ht
  · exact cyclic93 t ht

theorem all_edges (t : Int) (ht : 0≤t) (i : Fin 94) (k : Fin 4) : SafeCore t (mutate (node t i) k) := by
  have hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
  rcases finCore i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rcases hk with rfl|rfl|rfl|rfl
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
  · exact edge83_0 t ht
  · exact edge83_1 t ht
  · exact edge83_2 t ht
  · exact edge83_3 t ht
  · exact edge84_0 t ht
  · exact edge84_1 t ht
  · exact edge84_2 t ht
  · exact edge84_3 t ht
  · exact edge85_0 t ht
  · exact edge85_1 t ht
  · exact edge85_2 t ht
  · exact edge85_3 t ht
  · exact edge86_0 t ht
  · exact edge86_1 t ht
  · exact edge86_2 t ht
  · exact edge86_3 t ht
  · exact edge87_0 t ht
  · exact edge87_1 t ht
  · exact edge87_2 t ht
  · exact edge87_3 t ht
  · exact edge88_0 t ht
  · exact edge88_1 t ht
  · exact edge88_2 t ht
  · exact edge88_3 t ht
  · exact edge89_0 t ht
  · exact edge89_1 t ht
  · exact edge89_2 t ht
  · exact edge89_3 t ht
  · exact edge90_0 t ht
  · exact edge90_1 t ht
  · exact edge90_2 t ht
  · exact edge90_3 t ht
  · exact edge91_0 t ht
  · exact edge91_1 t ht
  · exact edge91_2 t ht
  · exact edge91_3 t ht
  · exact edge92_0 t ht
  · exact edge92_1 t ht
  · exact edge92_2 t ht
  · exact edge92_3 t ht
  · exact edge93_0 t ht
  · exact edge93_1 t ht
  · exact edge93_2 t ht
  · exact edge93_3 t ht

theorem NMA (t : Int) (ht : 0≤t) : ¬ MutationAcyclic (node t 0) := by
  apply safe_NMA data rules (Core t)
  · rintro B ⟨i,rfl⟩; exact node_skew t i
  · rintro B ⟨i,rfl⟩; exact all_cyclic t ht i
  · rintro B ⟨i,rfl⟩ k; exact all_edges t ht i k
  · exact node_safe t 0
end HalfLine

end QuiverProofs.Rank4StructureRound2.PFamily
