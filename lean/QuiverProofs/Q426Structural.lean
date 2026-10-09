import QuiverProofs.QFamilyPolynomialInterfaces
namespace QuiverProofs.Q426Structural
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

private theorem finiteFin (i : Fin 60) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 ∨ i=15 ∨ i=16 ∨ i=17 ∨ i=18 ∨ i=19 ∨ i=20 ∨ i=21 ∨ i=22 ∨ i=23 ∨ i=24 ∨ i=25 ∨ i=26 ∨ i=27 ∨ i=28 ∨ i=29 ∨ i=30 ∨ i=31 ∨ i=32 ∨ i=33 ∨ i=34 ∨ i=35 ∨ i=36 ∨ i=37 ∨ i=38 ∨ i=39 ∨ i=40 ∨ i=41 ∨ i=42 ∨ i=43 ∨ i=44 ∨ i=45 ∨ i=46 ∨ i=47 ∨ i=48 ∨ i=49 ∨ i=50 ∨ i=51 ∨ i=52 ∨ i=53 ∨ i=54 ∨ i=55 ∨ i=56 ∨ i=57 ∨ i=58 ∨ i=59 := by omega
def finiteP (i : Fin 60) : PMatrix := match i.val with
  | 0 => six [-2] [-1] [1] [-2] [1] [-2]
  | 1 => six [-5] [-1] [2] [-2] [-4] [-1]
  | 2 => six [-5] [-1] [2] [1] [-4] [-1]
  | 3 => six [-5] [1] [1] [-4] [-2] [-1]
  | 4 => six [-5] [1] [1] [-3] [-1] [-1]
  | 5 => six [-3] [1] [1] [-2] [-2] [-1]
  | 6 => six [] [-5] [2] [1] [-1] [-2]
  | 7 => six [-3] [-1] [2] [-2] [-2] [-1]
  | 8 => six [] [-2] [1] [1] [-2] [-1]
  | 9 => six [-4] [-1] [2] [-2] [-3] [-1]
  | 10 => six [-18] [-5] [4] [1] [-5] [-1]
  | 11 => six [-4] [-1] [2] [1] [-3] [-1]
  | 12 => six [-14] [-1] [4] [-4] [-1] [-1]
  | 13 => six [-55] [-3] [4] [-4] [-14] [-1]
  | 14 => six [-4] [1] [1] [-3] [-2] [-1]
  | 15 => six [-3] [1] [1] [-1] [-1] [-1]
  | 16 => six [-4] [1] [1] [-2] [-1] [-1]
  | 17 => six [] [-5] [2] [-1] [1] [-8]
  | 18 => six [] [-5] [2] [-1] [1] [-3]
  | 19 => six [-8] [-5] [5] [1] [-2] [-1]
  | 20 => six [] [-2] [1] [-1] [2] [-1]
  | 21 => six [] [-2] [1] [-1] [2] [-3]
  | 22 => six [-2] [-1] [1] [1] [-2] [1]
  | 23 => six [-86] [-6] [5] [5] [-18] [-1]
  | 24 => six [-23] [-1] [5] [-5] [-1] [-1]
  | 25 => six [-10] [-4] [3] [1] [-4] [-1]
  | 26 => six [-3] [-1] [2] [1] [-2] [-1]
  | 27 => six [-57] [-1] [5] [-10] [-4] [-1]
  | 28 => six [-281] [-4] [5] [-10] [-57] [-1]
  | 29 => six [-7] [-1] [3] [-3] [-1] [-1]
  | 30 => six [-20] [-2] [3] [-3] [-7] [-1]
  | 31 => six [] [-5] [2] [1] [-1] [-7]
  | 32 => six [] [-38] [5] [-7] [1] [-8]
  | 33 => six [] [-11] [2] [-7] [1] [-8]
  | 34 => six [] [-13] [5] [-2] [1] [-3]
  | 35 => six [-11] [-5] [8] [3] [-2] [1]
  | 36 => six [] [-13] [5] [2] [-1] [-1]
  | 37 => six [] [-2] [1] [-1] [-1] [-1]
  | 38 => six [] [-2] [1] [1] [1] [-1]
  | 39 => six [-116] [-1] [6] [-18] [-5] [-1]
  | 40 => six [-114] [-4] [5] [-5] [-23] [-1]
  | 41 => six [-691] [-5] [6] [-18] [-116] [-1]
  | 42 => six [-37] [-5] [4] [4] [-10] [-1]
  | 43 => six [-4] [-3] [2] [1] [-3] [-1]
  | 44 => six [-22] [-1] [4] [-4] [-3] [-1]
  | 45 => six [-85] [-3] [4] [-4] [-22] [-1]
  | 46 => six [-33] [-5] [5] [1] [-7] [-1]
  | 47 => six [-9] [-2] [2] [1] [-7] [-1]
  | 48 => six [] [-38] [5] [7] [-1] [-1]
  | 49 => six [] [-11] [2] [7] [-1] [-1]
  | 50 => six [-26] [-1] [3] [-8] [-5] [-1]
  | 51 => six [-73] [-2] [3] [-8] [-26] [-1]
  | 52 => six [-1] [-1] [-1] [-1] [1] [-1]
  | 53 => six [-10] [-4] [3] [3] [-4] [-1]
  | 54 => six [-226] [-8] [7] [5] [-33] [-1]
  | 55 => six [-61] [-8] [7] [2] [-9] [-1]
  | 56 => six [-266] [-1] [8] [-33] [-5] [-1]
  | 57 => six [-2123] [-7] [8] [-33] [-266] [-1]
  | 58 => six [-77] [-1] [8] [-9] [-2] [-1]
  | _ => six [-614] [-7] [8] [-9] [-77] [-1]
def finiteNode (i : Fin 60) : Matrix 4 := matrix (finiteP i) 0

private theorem polyFin (i : Fin 16) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 ∨ i=15 := by omega
def polyP (i : Fin 16) : PMatrix := match i.val with
  | 0 => six [-6,-1] [-1] [2] [-2] [-5,-1] [-1]
  | 1 => six [-6,-1] [-1] [2] [1] [-5,-1] [-1]
  | 2 => six [-6,-1] [1] [1] [-5,-1] [-2] [-1]
  | 3 => six [-6,-1] [1] [1] [-4,-1] [-1] [-1]
  | 4 => six [-28,-11,-1] [-6,-1] [5,1] [1] [-6,-1] [-1]
  | 5 => six [-23,-10,-1] [-1] [5,1] [-5,-1] [-1] [-1]
  | 6 => six [-114,-73,-15,-1] [-4,-1] [5,1] [-5,-1] [-23,-10,-1] [-1]
  | 7 => six [-163,-93,-17,-1] [-7,-1] [6,1] [6,1] [-28,-11,-1] [-1]
  | 8 => six [-34,-12,-1] [-1] [6,1] [-6,-1] [-1] [-1]
  | 9 => six [-116,-73,-15,-1] [-1] [6,1] [-18,-9,-1] [-5,-1] [-1]
  | 10 => six [-691,-553,-163,-21,-1] [-5,-1] [6,1] [-18,-9,-1] [-116,-73,-15,-1] [-1]
  | 11 => six [-18,-9,-1] [-5,-1] [4,1] [1] [-5,-1] [-1]
  | 12 => six [-205,-106,-18,-1] [-1] [7,1] [-28,-11,-1] [-6,-1] [-1]
  | 13 => six [-203,-106,-18,-1] [-5,-1] [6,1] [-6,-1] [-34,-12,-1] [-1]
  | 14 => six [-1429,-946,-232,-25,-1] [-6,-1] [7,1] [-28,-11,-1] [-205,-106,-18,-1] [-1]
  | _ => six [-86,-62,-14,-1] [-6,-1] [5,1] [5,1] [-18,-9,-1] [-1]
def polyNode (t : Int) (i : Fin 16) : Matrix 4 := matrix (polyP i) t

def Core (B : Matrix 4) : Prop :=
  (∃ i, B=finiteNode i) ∨ ∃ t : Int, 0≤t ∧ ∃ i, B=polyNode t i
abbrev SafeCore := Safe data Core

theorem finite_safe (i : Fin 60) : SafeCore (finiteNode i) := Safe.central (Or.inl ⟨i,rfl⟩)
theorem poly_safe (t : Int) (ht : 0≤t) (i : Fin 16) : SafeCore (polyNode t i) :=
  Safe.central (Or.inr ⟨t,ht,i,rfl⟩)

def tail (k : Int) (i : Fin 4) : Matrix 4 := match i.val with
  | 0 => ofSix (-k) (-1) 2 (-2) (-k+1) (-1)
  | 1 => ofSix (-k) (-1) 2 1 (-k+1) (-1)
  | 2 => ofSix (-k) 1 1 (-k+1) (-2) (-1)
  | _ => ofSix (-k) 1 1 (-k+2) (-1) (-1)

def tailP (k : P) (i : Fin 4) : PMatrix := match i.val with
  | 0 => six (neg k) [-1] [2] [-2] (add (neg k) [1]) [-1]
  | 1 => six (neg k) [-1] [2] [1] (add (neg k) [1]) [-1]
  | 2 => six (neg k) [1] [1] (add (neg k) [1]) [-2] [-1]
  | _ => six (neg k) [1] [1] (add (neg k) [2]) [-1] [-1]

theorem tailP_eval (k : P) (i : Fin 4) (t : Int) : matrix (tailP k i) t=tail (eval k t) i := by
  have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  rcases hi with rfl|rfl|rfl|rfl <;> simp [tailP,tail,matrix_six,eval_neg,eval_add,eval]

theorem tail_safe (k : Int) (hk : 5≤k) (i : Fin 4) : SafeCore (tail k i) := by
  have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  by_cases he : k=5
  · subst k
    rcases hi with rfl|rfl|rfl|rfl
    · simpa [finiteNode,finiteP,matrix_six,eval,tail] using finite_safe 1
    · simpa [finiteNode,finiteP,matrix_six,eval,tail] using finite_safe 2
    · simpa [finiteNode,finiteP,matrix_six,eval,tail] using finite_safe 3
    · simpa [finiteNode,finiteP,matrix_six,eval,tail] using finite_safe 4
  · have ht : 0≤k-6 := by omega
    rcases hi with rfl|rfl|rfl|rfl
    all_goals
      have h0 : polyNode (k-6) 0=tail k 0 := by
        simp only [polyNode,polyP,matrix_six,eval,tail]; congr 1 <;> omega
      have h1 : polyNode (k-6) 1=tail k 1 := by
        simp only [polyNode,polyP,matrix_six,eval,tail]; congr 1 <;> omega
      have h2 : polyNode (k-6) 2=tail k 2 := by
        simp only [polyNode,polyP,matrix_six,eval,tail]; congr 1 <;> omega
      have h3 : polyNode (k-6) 3=tail k 3 := by
        simp only [polyNode,polyP,matrix_six,eval,tail]; congr 1 <;> omega
    · rw [←h0]; exact poly_safe (k-6) ht 0
    · rw [←h1]; exact poly_safe (k-6) ht 1
    · rw [←h2]; exact poly_safe (k-6) ht 2
    · rw [←h3]; exact poly_safe (k-6) ht 3

theorem tailP_safe (k : P) (i : Fin 4) (t : Int) (ht : 0≤t) (hk : leb [5] k=true) :
    SafeCore (matrix (tailP k i) t) := by
  rw [tailP_eval]
  exact tail_safe (eval k t) (by simpa [eval] using le [5] k t ht hk) i

def finiteParam0_0 : P := [3]
def finiteParam0_1 : P := [14]
def finiteParam0_2 : P := [4]
def finiteParam0_3 : P := [5]
theorem finiteDomain0 : GenericStrip.Domain (eval finiteParam0_0 0) (eval finiteParam0_1 0) (eval finiteParam0_2 0) (eval finiteParam0_3 0) :=
  generic_domain finiteParam0_0 finiteParam0_1 finiteParam0_2 finiteParam0_3 0 (by decide) (by decide)
def finiteRegion0 : Region := .inl (.inl ⟨eval finiteParam0_0 0,⟨eval finiteParam0_1 0,eval finiteParam0_2 0,eval finiteParam0_3 0⟩,finiteDomain0⟩)
theorem finiteParent0_0 : data.parent (finiteRegion0) (0 : Fin 3)=(reverse (relabel (matrix (finiteP 12) 0) perm4.symm)) := by
  have he := mutation_equal (generic finiteParam0_0 finiteParam0_1 finiteParam0_2 finiteParam0_3 0) (preverse (prelabel (finiteP 12) perm4.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParent0_1 : data.parent (finiteRegion0) (1 : Fin 3)=(relabel (matrix (tailP [5] 3) 0) perm22.symm) := by
  have he := mutation_equal (generic finiteParam0_0 finiteParam0_1 finiteParam0_2 finiteParam0_3 0) (prelabel (tailP [5] 3) perm22.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParent0_2 : data.parent (finiteRegion0) (2 : Fin 3)=(reverse (relabel (matrix (finiteP 13) 0) perm16.symm)) := by
  have he := mutation_equal (generic finiteParam0_0 finiteParam0_1 finiteParam0_2 finiteParam0_3 2) (preverse (prelabel (finiteP 13) perm16.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParents0_safe (p : Fin 3) : SafeCore (data.parent (finiteRegion0) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hp with rfl|rfl|rfl
  · rw [finiteParent0_0]
    exact Safe.reversed (Safe.framed (finite_safe 12) perm4.symm)
  · rw [finiteParent0_1]
    exact Safe.framed (tailP_safe [5] 3 0 (by decide) (by decide)) perm22.symm
  · rw [finiteParent0_2]
    exact Safe.reversed (Safe.framed (finite_safe 13) perm16.symm)
theorem finiteRegion0_safe (i : Fin 3) : SafeCore (matrix (generic finiteParam0_0 finiteParam0_1 finiteParam0_2 finiteParam0_3 i) 0) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core) (finiteRegion0) (finiteParents0_safe) (0,Fin.castLE (by decide) i)

def finiteParam1_0 : P := [4]
def finiteParam1_1 : P := [57]
def finiteParam1_2 : P := [10]
def finiteParam1_3 : P := [14]
theorem finiteDomain1 : GenericStrip.Domain (eval finiteParam1_0 0) (eval finiteParam1_1 0) (eval finiteParam1_2 0) (eval finiteParam1_3 0) :=
  generic_domain finiteParam1_0 finiteParam1_1 finiteParam1_2 finiteParam1_3 0 (by decide) (by decide)
def finiteRegion1 : Region := .inl (.inl ⟨eval finiteParam1_0 0,⟨eval finiteParam1_1 0,eval finiteParam1_2 0,eval finiteParam1_3 0⟩,finiteDomain1⟩)
theorem finiteParent1_0 : data.parent (finiteRegion1) (0 : Fin 3)=(reverse (relabel (matrix (finiteP 27) 0) perm4.symm)) := by
  have he := mutation_equal (generic finiteParam1_0 finiteParam1_1 finiteParam1_2 finiteParam1_3 0) (preverse (prelabel (finiteP 27) perm4.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParent1_1 : data.parent (finiteRegion1) (1 : Fin 3)=(relabel (matrix (finiteP 12) 0) perm22.symm) := by
  have he := mutation_equal (generic finiteParam1_0 finiteParam1_1 finiteParam1_2 finiteParam1_3 0) (prelabel (finiteP 12) perm22.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParent1_2 : data.parent (finiteRegion1) (2 : Fin 3)=(reverse (relabel (matrix (finiteP 28) 0) perm16.symm)) := by
  have he := mutation_equal (generic finiteParam1_0 finiteParam1_1 finiteParam1_2 finiteParam1_3 2) (preverse (prelabel (finiteP 28) perm16.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParents1_safe (p : Fin 3) : SafeCore (data.parent (finiteRegion1) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hp with rfl|rfl|rfl
  · rw [finiteParent1_0]
    exact Safe.reversed (Safe.framed (finite_safe 27) perm4.symm)
  · rw [finiteParent1_1]
    exact Safe.framed (finite_safe 12) perm22.symm
  · rw [finiteParent1_2]
    exact Safe.reversed (Safe.framed (finite_safe 28) perm16.symm)
theorem finiteRegion1_safe (i : Fin 3) : SafeCore (matrix (generic finiteParam1_0 finiteParam1_1 finiteParam1_2 finiteParam1_3 i) 0) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core) (finiteRegion1) (finiteParents1_safe) (0,Fin.castLE (by decide) i)

def finiteParam2_0 : P := [2]
def finiteParam2_1 : P := [7]
def finiteParam2_2 : P := [3]
def finiteParam2_3 : P := [4]
theorem finiteDomain2 : GenericStrip.Domain (eval finiteParam2_0 0) (eval finiteParam2_1 0) (eval finiteParam2_2 0) (eval finiteParam2_3 0) :=
  generic_domain finiteParam2_0 finiteParam2_1 finiteParam2_2 finiteParam2_3 0 (by decide) (by decide)
def finiteRegion2 : Region := .inl (.inl ⟨eval finiteParam2_0 0,⟨eval finiteParam2_1 0,eval finiteParam2_2 0,eval finiteParam2_3 0⟩,finiteDomain2⟩)
theorem finiteParent2_0 : data.parent (finiteRegion2) (0 : Fin 3)=(reverse (relabel (matrix (finiteP 29) 0) perm4.symm)) := by
  have he := mutation_equal (generic finiteParam2_0 finiteParam2_1 finiteParam2_2 finiteParam2_3 0) (preverse (prelabel (finiteP 29) perm4.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParent2_1 : data.parent (finiteRegion2) (1 : Fin 3)=(relabel (matrix (finiteP 16) 0) perm22.symm) := by
  have he := mutation_equal (generic finiteParam2_0 finiteParam2_1 finiteParam2_2 finiteParam2_3 0) (prelabel (finiteP 16) perm22.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParent2_2 : data.parent (finiteRegion2) (2 : Fin 3)=(reverse (relabel (matrix (finiteP 30) 0) perm16.symm)) := by
  have he := mutation_equal (generic finiteParam2_0 finiteParam2_1 finiteParam2_2 finiteParam2_3 2) (preverse (prelabel (finiteP 30) perm16.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParents2_safe (p : Fin 3) : SafeCore (data.parent (finiteRegion2) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hp with rfl|rfl|rfl
  · rw [finiteParent2_0]
    exact Safe.reversed (Safe.framed (finite_safe 29) perm4.symm)
  · rw [finiteParent2_1]
    exact Safe.framed (finite_safe 16) perm22.symm
  · rw [finiteParent2_2]
    exact Safe.reversed (Safe.framed (finite_safe 30) perm16.symm)
theorem finiteRegion2_safe (i : Fin 3) : SafeCore (matrix (generic finiteParam2_0 finiteParam2_1 finiteParam2_2 finiteParam2_3 i) 0) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core) (finiteRegion2) (finiteParents2_safe) (0,Fin.castLE (by decide) i)

def finiteParam3_0 : P := [5]
def finiteParam3_1 : P := [116]
def finiteParam3_2 : P := [18]
def finiteParam3_3 : P := [23]
theorem finiteDomain3 : GenericStrip.Domain (eval finiteParam3_0 0) (eval finiteParam3_1 0) (eval finiteParam3_2 0) (eval finiteParam3_3 0) :=
  generic_domain finiteParam3_0 finiteParam3_1 finiteParam3_2 finiteParam3_3 0 (by decide) (by decide)
def finiteRegion3 : Region := .inl (.inl ⟨eval finiteParam3_0 0,⟨eval finiteParam3_1 0,eval finiteParam3_2 0,eval finiteParam3_3 0⟩,finiteDomain3⟩)
theorem finiteParent3_0 : data.parent (finiteRegion3) (0 : Fin 3)=(reverse (relabel (matrix (finiteP 39) 0) perm4.symm)) := by
  have he := mutation_equal (generic finiteParam3_0 finiteParam3_1 finiteParam3_2 finiteParam3_3 0) (preverse (prelabel (finiteP 39) perm4.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParent3_1 : data.parent (finiteRegion3) (1 : Fin 3)=(relabel (matrix (finiteP 24) 0) perm22.symm) := by
  have he := mutation_equal (generic finiteParam3_0 finiteParam3_1 finiteParam3_2 finiteParam3_3 0) (prelabel (finiteP 24) perm22.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParent3_2 : data.parent (finiteRegion3) (2 : Fin 3)=(reverse (relabel (matrix (finiteP 41) 0) perm16.symm)) := by
  have he := mutation_equal (generic finiteParam3_0 finiteParam3_1 finiteParam3_2 finiteParam3_3 2) (preverse (prelabel (finiteP 41) perm16.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParents3_safe (p : Fin 3) : SafeCore (data.parent (finiteRegion3) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hp with rfl|rfl|rfl
  · rw [finiteParent3_0]
    exact Safe.reversed (Safe.framed (finite_safe 39) perm4.symm)
  · rw [finiteParent3_1]
    exact Safe.framed (finite_safe 24) perm22.symm
  · rw [finiteParent3_2]
    exact Safe.reversed (Safe.framed (finite_safe 41) perm16.symm)
theorem finiteRegion3_safe (i : Fin 3) : SafeCore (matrix (generic finiteParam3_0 finiteParam3_1 finiteParam3_2 finiteParam3_3 i) 0) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core) (finiteRegion3) (finiteParents3_safe) (0,Fin.castLE (by decide) i)

def finiteParam4_0 : P := [4]
def finiteParam4_1 : P := [23]
def finiteParam4_2 : P := [5]
def finiteParam4_3 : P := [6]
theorem finiteDomain4 : GenericStrip.Domain (eval finiteParam4_0 0) (eval finiteParam4_1 0) (eval finiteParam4_2 0) (eval finiteParam4_3 0) :=
  generic_domain finiteParam4_0 finiteParam4_1 finiteParam4_2 finiteParam4_3 0 (by decide) (by decide)
def finiteRegion4 : Region := .inl (.inl ⟨eval finiteParam4_0 0,⟨eval finiteParam4_1 0,eval finiteParam4_2 0,eval finiteParam4_3 0⟩,finiteDomain4⟩)
theorem finiteParent4_0 : data.parent (finiteRegion4) (0 : Fin 3)=(reverse (relabel (matrix (finiteP 24) 0) perm4.symm)) := by
  have he := mutation_equal (generic finiteParam4_0 finiteParam4_1 finiteParam4_2 finiteParam4_3 0) (preverse (prelabel (finiteP 24) perm4.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParent4_1 : data.parent (finiteRegion4) (1 : Fin 3)=(relabel (matrix (tailP [6] 3) 0) perm22.symm) := by
  have he := mutation_equal (generic finiteParam4_0 finiteParam4_1 finiteParam4_2 finiteParam4_3 0) (prelabel (tailP [6] 3) perm22.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParent4_2 : data.parent (finiteRegion4) (2 : Fin 3)=(reverse (relabel (matrix (finiteP 40) 0) perm16.symm)) := by
  have he := mutation_equal (generic finiteParam4_0 finiteParam4_1 finiteParam4_2 finiteParam4_3 2) (preverse (prelabel (finiteP 40) perm16.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParents4_safe (p : Fin 3) : SafeCore (data.parent (finiteRegion4) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hp with rfl|rfl|rfl
  · rw [finiteParent4_0]
    exact Safe.reversed (Safe.framed (finite_safe 24) perm4.symm)
  · rw [finiteParent4_1]
    exact Safe.framed (tailP_safe [6] 3 0 (by decide) (by decide)) perm22.symm
  · rw [finiteParent4_2]
    exact Safe.reversed (Safe.framed (finite_safe 40) perm16.symm)
theorem finiteRegion4_safe (i : Fin 3) : SafeCore (matrix (generic finiteParam4_0 finiteParam4_1 finiteParam4_2 finiteParam4_3 i) 0) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core) (finiteRegion4) (finiteParents4_safe) (0,Fin.castLE (by decide) i)

def finiteParam5_0 : P := [3]
def finiteParam5_1 : P := [22]
def finiteParam5_2 : P := [4]
def finiteParam5_3 : P := [7]
theorem finiteDomain5 : GenericStrip.Domain (eval finiteParam5_0 0) (eval finiteParam5_1 0) (eval finiteParam5_2 0) (eval finiteParam5_3 0) :=
  generic_domain finiteParam5_0 finiteParam5_1 finiteParam5_2 finiteParam5_3 0 (by decide) (by decide)
def finiteRegion5 : Region := .inl (.inl ⟨eval finiteParam5_0 0,⟨eval finiteParam5_1 0,eval finiteParam5_2 0,eval finiteParam5_3 0⟩,finiteDomain5⟩)
theorem finiteParent5_0 : data.parent (finiteRegion5) (0 : Fin 3)=(reverse (relabel (matrix (finiteP 44) 0) perm4.symm)) := by
  have he := mutation_equal (generic finiteParam5_0 finiteParam5_1 finiteParam5_2 finiteParam5_3 0) (preverse (prelabel (finiteP 44) perm4.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParent5_1 : data.parent (finiteRegion5) (1 : Fin 3)=(relabel (matrix (finiteP 29) 0) perm22.symm) := by
  have he := mutation_equal (generic finiteParam5_0 finiteParam5_1 finiteParam5_2 finiteParam5_3 0) (prelabel (finiteP 29) perm22.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParent5_2 : data.parent (finiteRegion5) (2 : Fin 3)=(reverse (relabel (matrix (finiteP 45) 0) perm16.symm)) := by
  have he := mutation_equal (generic finiteParam5_0 finiteParam5_1 finiteParam5_2 finiteParam5_3 2) (preverse (prelabel (finiteP 45) perm16.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParents5_safe (p : Fin 3) : SafeCore (data.parent (finiteRegion5) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hp with rfl|rfl|rfl
  · rw [finiteParent5_0]
    exact Safe.reversed (Safe.framed (finite_safe 44) perm4.symm)
  · rw [finiteParent5_1]
    exact Safe.framed (finite_safe 29) perm22.symm
  · rw [finiteParent5_2]
    exact Safe.reversed (Safe.framed (finite_safe 45) perm16.symm)
theorem finiteRegion5_safe (i : Fin 3) : SafeCore (matrix (generic finiteParam5_0 finiteParam5_1 finiteParam5_2 finiteParam5_3 i) 0) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core) (finiteRegion5) (finiteParents5_safe) (0,Fin.castLE (by decide) i)

def finiteParam6_0 : P := [5]
def finiteParam6_1 : P := [7]
def finiteParam6_2 : P := [38]
def finiteParam6_3 : P := [182]
theorem finiteDomain6 : UnitZeroStrip.Domain (eval finiteParam6_0 0) (eval finiteParam6_1 0) (eval finiteParam6_2 0) (eval finiteParam6_3 0) :=
  zero_domain finiteParam6_0 finiteParam6_1 finiteParam6_2 finiteParam6_3 0 (by decide) (by decide)
def finiteRegion6 : Region := .inl (.inr (.n (eval finiteParam6_0 0) ⟨eval finiteParam6_1 0,eval finiteParam6_2 0,eval finiteParam6_3 0⟩ (finiteDomain6)))
theorem finiteParent6_0 : data.parent (finiteRegion6) (0 : Fin 2)=(relabel (matrix (finiteP 32) 0) perm6.symm) := by
  have he := mutation_equal (zero finiteParam6_0 finiteParam6_1 finiteParam6_2 finiteParam6_3 0) (prelabel (finiteP 32) perm6.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,zero_eval] at he
  exact he

theorem finiteParent6_1 : data.parent (finiteRegion6) (1 : Fin 2)=(relabel (matrix (finiteP 48) 0) perm6.symm) := by
  have he := mutation_equal (zero finiteParam6_0 finiteParam6_1 finiteParam6_2 finiteParam6_3 1) (prelabel (finiteP 48) perm6.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,zero_eval] at he
  exact he

theorem finiteParents6_safe (p : Fin 2) : SafeCore (data.parent (finiteRegion6) p) := by
  have hp : p=0 ∨ p=1 := by change p=(0 : Fin 2) ∨ p=(1 : Fin 2); omega
  rcases hp with rfl|rfl
  · rw [finiteParent6_0]
    exact Safe.framed (finite_safe 32) perm6.symm
  · rw [finiteParent6_1]
    exact Safe.framed (finite_safe 48) perm6.symm
theorem finiteRegion6_safe (i : Fin 2) : SafeCore (matrix (zero finiteParam6_0 finiteParam6_1 finiteParam6_2 finiteParam6_3 i) 0) := by
  rw [zero_eval]
  exact Safe.region (D:=data) (core:=Core) (finiteRegion6) (finiteParents6_safe) (0,Fin.castLE (by decide) i)

def finiteParam7_0 : P := [2]
def finiteParam7_1 : P := [7]
def finiteParam7_2 : P := [11]
def finiteParam7_3 : P := [14]
theorem finiteDomain7 : UnitZeroStrip.Domain (eval finiteParam7_0 0) (eval finiteParam7_1 0) (eval finiteParam7_2 0) (eval finiteParam7_3 0) :=
  zero_domain finiteParam7_0 finiteParam7_1 finiteParam7_2 finiteParam7_3 0 (by decide) (by decide)
def finiteRegion7 : Region := .inl (.inr (.n (eval finiteParam7_0 0) ⟨eval finiteParam7_1 0,eval finiteParam7_2 0,eval finiteParam7_3 0⟩ (finiteDomain7)))
theorem finiteParent7_0 : data.parent (finiteRegion7) (0 : Fin 2)=(relabel (matrix (finiteP 33) 0) perm6.symm) := by
  have he := mutation_equal (zero finiteParam7_0 finiteParam7_1 finiteParam7_2 finiteParam7_3 0) (prelabel (finiteP 33) perm6.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,zero_eval] at he
  exact he

theorem finiteParent7_1 : data.parent (finiteRegion7) (1 : Fin 2)=(relabel (matrix (finiteP 49) 0) perm6.symm) := by
  have he := mutation_equal (zero finiteParam7_0 finiteParam7_1 finiteParam7_2 finiteParam7_3 1) (prelabel (finiteP 49) perm6.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,zero_eval] at he
  exact he

theorem finiteParents7_safe (p : Fin 2) : SafeCore (data.parent (finiteRegion7) p) := by
  have hp : p=0 ∨ p=1 := by change p=(0 : Fin 2) ∨ p=(1 : Fin 2); omega
  rcases hp with rfl|rfl
  · rw [finiteParent7_0]
    exact Safe.framed (finite_safe 33) perm6.symm
  · rw [finiteParent7_1]
    exact Safe.framed (finite_safe 49) perm6.symm
theorem finiteRegion7_safe (i : Fin 2) : SafeCore (matrix (zero finiteParam7_0 finiteParam7_1 finiteParam7_2 finiteParam7_3 i) 0) := by
  rw [zero_eval]
  exact Safe.region (D:=data) (core:=Core) (finiteRegion7) (finiteParents7_safe) (0,Fin.castLE (by decide) i)

def finiteParam8_0 : P := [5]
def finiteParam8_1 : P := [2]
def finiteParam8_2 : P := [13]
def finiteParam8_3 : P := [62]
theorem finiteDomain8 : UnitZeroStrip.Domain (eval finiteParam8_0 0) (eval finiteParam8_1 0) (eval finiteParam8_2 0) (eval finiteParam8_3 0) :=
  zero_domain finiteParam8_0 finiteParam8_1 finiteParam8_2 finiteParam8_3 0 (by decide) (by decide)
def finiteRegion8 : Region := .inl (.inr (.n (eval finiteParam8_0 0) ⟨eval finiteParam8_1 0,eval finiteParam8_2 0,eval finiteParam8_3 0⟩ (finiteDomain8)))
theorem finiteParent8_0 : data.parent (finiteRegion8) (0 : Fin 2)=(relabel (matrix (finiteP 34) 0) perm6.symm) := by
  have he := mutation_equal (zero finiteParam8_0 finiteParam8_1 finiteParam8_2 finiteParam8_3 0) (prelabel (finiteP 34) perm6.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,zero_eval] at he
  exact he

theorem finiteParent8_1 : data.parent (finiteRegion8) (1 : Fin 2)=(relabel (matrix (finiteP 36) 0) perm6.symm) := by
  have he := mutation_equal (zero finiteParam8_0 finiteParam8_1 finiteParam8_2 finiteParam8_3 1) (prelabel (finiteP 36) perm6.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,zero_eval] at he
  exact he

theorem finiteParents8_safe (p : Fin 2) : SafeCore (data.parent (finiteRegion8) p) := by
  have hp : p=0 ∨ p=1 := by change p=(0 : Fin 2) ∨ p=(1 : Fin 2); omega
  rcases hp with rfl|rfl
  · rw [finiteParent8_0]
    exact Safe.framed (finite_safe 34) perm6.symm
  · rw [finiteParent8_1]
    exact Safe.framed (finite_safe 36) perm6.symm
theorem finiteRegion8_safe (i : Fin 2) : SafeCore (matrix (zero finiteParam8_0 finiteParam8_1 finiteParam8_2 finiteParam8_3 i) 0) := by
  rw [zero_eval]
  exact Safe.region (D:=data) (core:=Core) (finiteRegion8) (finiteParents8_safe) (0,Fin.castLE (by decide) i)

def finiteParam9_0 : P := [2]
def finiteParam9_1 : P := [26]
def finiteParam9_2 : P := [8]
def finiteParam9_3 : P := [13]
theorem finiteDomain9 : GenericStrip.Domain (eval finiteParam9_0 0) (eval finiteParam9_1 0) (eval finiteParam9_2 0) (eval finiteParam9_3 0) :=
  generic_domain finiteParam9_0 finiteParam9_1 finiteParam9_2 finiteParam9_3 0 (by decide) (by decide)
def finiteRegion9 : Region := .inl (.inl ⟨eval finiteParam9_0 0,⟨eval finiteParam9_1 0,eval finiteParam9_2 0,eval finiteParam9_3 0⟩,finiteDomain9⟩)
theorem finiteParent9_0 : data.parent (finiteRegion9) (0 : Fin 3)=(reverse (relabel (matrix (finiteP 50) 0) perm4.symm)) := by
  have he := mutation_equal (generic finiteParam9_0 finiteParam9_1 finiteParam9_2 finiteParam9_3 0) (preverse (prelabel (finiteP 50) perm4.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParent9_1 : data.parent (finiteRegion9) (1 : Fin 3)=(relabel (matrix (finiteP 36) 0) perm19.symm) := by
  have he := mutation_equal (generic finiteParam9_0 finiteParam9_1 finiteParam9_2 finiteParam9_3 0) (prelabel (finiteP 36) perm19.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParent9_2 : data.parent (finiteRegion9) (2 : Fin 3)=(reverse (relabel (matrix (finiteP 51) 0) perm16.symm)) := by
  have he := mutation_equal (generic finiteParam9_0 finiteParam9_1 finiteParam9_2 finiteParam9_3 2) (preverse (prelabel (finiteP 51) perm16.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParents9_safe (p : Fin 3) : SafeCore (data.parent (finiteRegion9) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hp with rfl|rfl|rfl
  · rw [finiteParent9_0]
    exact Safe.reversed (Safe.framed (finite_safe 50) perm4.symm)
  · rw [finiteParent9_1]
    exact Safe.framed (finite_safe 36) perm19.symm
  · rw [finiteParent9_2]
    exact Safe.reversed (Safe.framed (finite_safe 51) perm16.symm)
theorem finiteRegion9_safe (i : Fin 3) : SafeCore (matrix (generic finiteParam9_0 finiteParam9_1 finiteParam9_2 finiteParam9_3 i) 0) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core) (finiteRegion9) (finiteParents9_safe) (0,Fin.castLE (by decide) i)

def finiteParam10_0 : P := [7]
def finiteParam10_1 : P := [266]
def finiteParam10_2 : P := [33]
def finiteParam10_3 : P := [38]
theorem finiteDomain10 : GenericStrip.Domain (eval finiteParam10_0 0) (eval finiteParam10_1 0) (eval finiteParam10_2 0) (eval finiteParam10_3 0) :=
  generic_domain finiteParam10_0 finiteParam10_1 finiteParam10_2 finiteParam10_3 0 (by decide) (by decide)
def finiteRegion10 : Region := .inl (.inl ⟨eval finiteParam10_0 0,⟨eval finiteParam10_1 0,eval finiteParam10_2 0,eval finiteParam10_3 0⟩,finiteDomain10⟩)
theorem finiteParent10_0 : data.parent (finiteRegion10) (0 : Fin 3)=(reverse (relabel (matrix (finiteP 56) 0) perm4.symm)) := by
  have he := mutation_equal (generic finiteParam10_0 finiteParam10_1 finiteParam10_2 finiteParam10_3 0) (preverse (prelabel (finiteP 56) perm4.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParent10_1 : data.parent (finiteRegion10) (1 : Fin 3)=(relabel (matrix (finiteP 48) 0) perm19.symm) := by
  have he := mutation_equal (generic finiteParam10_0 finiteParam10_1 finiteParam10_2 finiteParam10_3 0) (prelabel (finiteP 48) perm19.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParent10_2 : data.parent (finiteRegion10) (2 : Fin 3)=(reverse (relabel (matrix (finiteP 57) 0) perm16.symm)) := by
  have he := mutation_equal (generic finiteParam10_0 finiteParam10_1 finiteParam10_2 finiteParam10_3 2) (preverse (prelabel (finiteP 57) perm16.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParents10_safe (p : Fin 3) : SafeCore (data.parent (finiteRegion10) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hp with rfl|rfl|rfl
  · rw [finiteParent10_0]
    exact Safe.reversed (Safe.framed (finite_safe 56) perm4.symm)
  · rw [finiteParent10_1]
    exact Safe.framed (finite_safe 48) perm19.symm
  · rw [finiteParent10_2]
    exact Safe.reversed (Safe.framed (finite_safe 57) perm16.symm)
theorem finiteRegion10_safe (i : Fin 3) : SafeCore (matrix (generic finiteParam10_0 finiteParam10_1 finiteParam10_2 finiteParam10_3 i) 0) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core) (finiteRegion10) (finiteParents10_safe) (0,Fin.castLE (by decide) i)

def finiteParam11_0 : P := [7]
def finiteParam11_1 : P := [77]
def finiteParam11_2 : P := [9]
def finiteParam11_3 : P := [11]
theorem finiteDomain11 : GenericStrip.Domain (eval finiteParam11_0 0) (eval finiteParam11_1 0) (eval finiteParam11_2 0) (eval finiteParam11_3 0) :=
  generic_domain finiteParam11_0 finiteParam11_1 finiteParam11_2 finiteParam11_3 0 (by decide) (by decide)
def finiteRegion11 : Region := .inl (.inl ⟨eval finiteParam11_0 0,⟨eval finiteParam11_1 0,eval finiteParam11_2 0,eval finiteParam11_3 0⟩,finiteDomain11⟩)
theorem finiteParent11_0 : data.parent (finiteRegion11) (0 : Fin 3)=(reverse (relabel (matrix (finiteP 58) 0) perm4.symm)) := by
  have he := mutation_equal (generic finiteParam11_0 finiteParam11_1 finiteParam11_2 finiteParam11_3 0) (preverse (prelabel (finiteP 58) perm4.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParent11_1 : data.parent (finiteRegion11) (1 : Fin 3)=(relabel (matrix (finiteP 49) 0) perm19.symm) := by
  have he := mutation_equal (generic finiteParam11_0 finiteParam11_1 finiteParam11_2 finiteParam11_3 0) (prelabel (finiteP 49) perm19.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParent11_2 : data.parent (finiteRegion11) (2 : Fin 3)=(reverse (relabel (matrix (finiteP 59) 0) perm16.symm)) := by
  have he := mutation_equal (generic finiteParam11_0 finiteParam11_1 finiteParam11_2 finiteParam11_3 2) (preverse (prelabel (finiteP 59) perm16.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParents11_safe (p : Fin 3) : SafeCore (data.parent (finiteRegion11) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hp with rfl|rfl|rfl
  · rw [finiteParent11_0]
    exact Safe.reversed (Safe.framed (finite_safe 58) perm4.symm)
  · rw [finiteParent11_1]
    exact Safe.framed (finite_safe 49) perm19.symm
  · rw [finiteParent11_2]
    exact Safe.reversed (Safe.framed (finite_safe 59) perm16.symm)
theorem finiteRegion11_safe (i : Fin 3) : SafeCore (matrix (generic finiteParam11_0 finiteParam11_1 finiteParam11_2 finiteParam11_3 i) 0) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core) (finiteRegion11) (finiteParents11_safe) (0,Fin.castLE (by decide) i)

theorem finite_skew (i : Fin 60) : SkewSymmetric (finiteNode i) := by
  rcases finiteFin i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp only [finiteNode,finiteP,matrix_six] <;> exact ofSix_skew _ _ _ _ _ _

theorem finiteCyclic0 : ¬ Acyclic (finiteNode 0) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 0 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 2 (pos (finiteP 0 3 2) 0 (by decide) (by decide))
  have h2 := hr 2 0 (pos (finiteP 0 2 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic1 : ¬ Acyclic (finiteNode 1) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 1 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 1 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 1 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic2 : ¬ Acyclic (finiteNode 2) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 2 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 2 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 2 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic3 : ¬ Acyclic (finiteNode 3) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (finiteP 3 0 2) 0 (by decide) (by decide))
  have h1 := hr 2 1 (pos (finiteP 3 2 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 3 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic4 : ¬ Acyclic (finiteNode 4) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (finiteP 4 0 2) 0 (by decide) (by decide))
  have h1 := hr 2 1 (pos (finiteP 4 2 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 4 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic5 : ¬ Acyclic (finiteNode 5) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (finiteP 5 0 2) 0 (by decide) (by decide))
  have h1 := hr 2 1 (pos (finiteP 5 2 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 5 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic6 : ¬ Acyclic (finiteNode 6) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 6 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 2 (pos (finiteP 6 3 2) 0 (by decide) (by decide))
  have h2 := hr 2 0 (pos (finiteP 6 2 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic7 : ¬ Acyclic (finiteNode 7) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 7 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 7 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 7 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic8 : ¬ Acyclic (finiteNode 8) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 8 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 2 (pos (finiteP 8 3 2) 0 (by decide) (by decide))
  have h2 := hr 2 0 (pos (finiteP 8 2 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic9 : ¬ Acyclic (finiteNode 9) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 9 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 9 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 9 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic10 : ¬ Acyclic (finiteNode 10) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 10 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 10 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 10 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic11 : ¬ Acyclic (finiteNode 11) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 11 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 11 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 11 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic12 : ¬ Acyclic (finiteNode 12) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 12 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 12 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 12 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic13 : ¬ Acyclic (finiteNode 13) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 13 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 13 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 13 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic14 : ¬ Acyclic (finiteNode 14) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (finiteP 14 0 2) 0 (by decide) (by decide))
  have h1 := hr 2 1 (pos (finiteP 14 2 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 14 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic15 : ¬ Acyclic (finiteNode 15) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (finiteP 15 0 2) 0 (by decide) (by decide))
  have h1 := hr 2 1 (pos (finiteP 15 2 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 15 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic16 : ¬ Acyclic (finiteNode 16) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (finiteP 16 0 2) 0 (by decide) (by decide))
  have h1 := hr 2 1 (pos (finiteP 16 2 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 16 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic17 : ¬ Acyclic (finiteNode 17) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 17 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 2 (pos (finiteP 17 3 2) 0 (by decide) (by decide))
  have h2 := hr 2 0 (pos (finiteP 17 2 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic18 : ¬ Acyclic (finiteNode 18) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 18 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 2 (pos (finiteP 18 3 2) 0 (by decide) (by decide))
  have h2 := hr 2 0 (pos (finiteP 18 2 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic19 : ¬ Acyclic (finiteNode 19) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 19 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 19 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 19 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic20 : ¬ Acyclic (finiteNode 20) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 20 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 2 (pos (finiteP 20 3 2) 0 (by decide) (by decide))
  have h2 := hr 2 0 (pos (finiteP 20 2 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic21 : ¬ Acyclic (finiteNode 21) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 21 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 2 (pos (finiteP 21 3 2) 0 (by decide) (by decide))
  have h2 := hr 2 0 (pos (finiteP 21 2 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic22 : ¬ Acyclic (finiteNode 22) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 22 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 22 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 22 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic23 : ¬ Acyclic (finiteNode 23) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 23 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 23 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 23 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic24 : ¬ Acyclic (finiteNode 24) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 24 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 24 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 24 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic25 : ¬ Acyclic (finiteNode 25) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 25 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 25 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 25 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic26 : ¬ Acyclic (finiteNode 26) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 26 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 26 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 26 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic27 : ¬ Acyclic (finiteNode 27) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 27 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 27 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 27 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic28 : ¬ Acyclic (finiteNode 28) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 28 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 28 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 28 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic29 : ¬ Acyclic (finiteNode 29) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 29 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 29 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 29 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic30 : ¬ Acyclic (finiteNode 30) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 30 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 30 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 30 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic31 : ¬ Acyclic (finiteNode 31) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 31 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 2 (pos (finiteP 31 3 2) 0 (by decide) (by decide))
  have h2 := hr 2 0 (pos (finiteP 31 2 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic32 : ¬ Acyclic (finiteNode 32) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 32 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 2 (pos (finiteP 32 3 2) 0 (by decide) (by decide))
  have h2 := hr 2 0 (pos (finiteP 32 2 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic33 : ¬ Acyclic (finiteNode 33) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 33 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 2 (pos (finiteP 33 3 2) 0 (by decide) (by decide))
  have h2 := hr 2 0 (pos (finiteP 33 2 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic34 : ¬ Acyclic (finiteNode 34) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 34 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 2 (pos (finiteP 34 3 2) 0 (by decide) (by decide))
  have h2 := hr 2 0 (pos (finiteP 34 2 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic35 : ¬ Acyclic (finiteNode 35) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 35 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 35 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 35 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic36 : ¬ Acyclic (finiteNode 36) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 36 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 2 (pos (finiteP 36 3 2) 0 (by decide) (by decide))
  have h2 := hr 2 0 (pos (finiteP 36 2 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic37 : ¬ Acyclic (finiteNode 37) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 37 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 2 (pos (finiteP 37 3 2) 0 (by decide) (by decide))
  have h2 := hr 2 0 (pos (finiteP 37 2 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic38 : ¬ Acyclic (finiteNode 38) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 38 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 2 (pos (finiteP 38 3 2) 0 (by decide) (by decide))
  have h2 := hr 2 0 (pos (finiteP 38 2 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic39 : ¬ Acyclic (finiteNode 39) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 39 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 39 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 39 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic40 : ¬ Acyclic (finiteNode 40) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 40 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 40 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 40 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic41 : ¬ Acyclic (finiteNode 41) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 41 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 41 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 41 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic42 : ¬ Acyclic (finiteNode 42) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 42 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 42 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 42 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic43 : ¬ Acyclic (finiteNode 43) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 43 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 43 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 43 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic44 : ¬ Acyclic (finiteNode 44) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 44 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 44 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 44 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic45 : ¬ Acyclic (finiteNode 45) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 45 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 45 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 45 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic46 : ¬ Acyclic (finiteNode 46) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 46 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 46 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 46 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic47 : ¬ Acyclic (finiteNode 47) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 47 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 47 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 47 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic48 : ¬ Acyclic (finiteNode 48) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 48 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 2 (pos (finiteP 48 3 2) 0 (by decide) (by decide))
  have h2 := hr 2 0 (pos (finiteP 48 2 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic49 : ¬ Acyclic (finiteNode 49) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 49 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 2 (pos (finiteP 49 3 2) 0 (by decide) (by decide))
  have h2 := hr 2 0 (pos (finiteP 49 2 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic50 : ¬ Acyclic (finiteNode 50) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 50 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 50 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 50 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic51 : ¬ Acyclic (finiteNode 51) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 51 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 51 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 51 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic52 : ¬ Acyclic (finiteNode 52) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 1 3 (pos (finiteP 52 1 3) 0 (by decide) (by decide))
  have h1 := hr 3 2 (pos (finiteP 52 3 2) 0 (by decide) (by decide))
  have h2 := hr 2 1 (pos (finiteP 52 2 1) 0 (by decide) (by decide))
  omega

theorem finiteCyclic53 : ¬ Acyclic (finiteNode 53) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 53 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 53 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 53 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic54 : ¬ Acyclic (finiteNode 54) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 54 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 54 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 54 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic55 : ¬ Acyclic (finiteNode 55) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 55 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 55 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 55 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic56 : ¬ Acyclic (finiteNode 56) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 56 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 56 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 56 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic57 : ¬ Acyclic (finiteNode 57) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 57 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 57 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 57 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic58 : ¬ Acyclic (finiteNode 58) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 58 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 58 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 58 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic59 : ¬ Acyclic (finiteNode 59) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 59 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 59 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 59 1 0) 0 (by decide) (by decide))
  omega

theorem finiteEdge0_0 : SafeCore (mutate (finiteNode 0) 0) := by
  have he := mutation_equal (finiteP 0) (prelabel (finiteP 5) perm21.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 0) 0) 0)
  rw [he]
  exact Safe.framed (finite_safe 5) perm21.symm

theorem finiteEdge0_1 : SafeCore (mutate (finiteNode 0) 1) := by
  have he := mutation_equal (finiteP 0) (preverse (prelabel (finiteP 6) perm16.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 0) 0) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 6) perm16.symm)

theorem finiteEdge0_2 : SafeCore (mutate (finiteNode 0) 2) := by
  have he := mutation_equal (finiteP 0) (preverse (prelabel (finiteP 7) perm20.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 0) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 7) perm20.symm)

theorem finiteEdge0_3 : SafeCore (mutate (finiteNode 0) 3) := by
  have he := mutation_equal (finiteP 0) (preverse (prelabel (finiteP 8) perm15.symm)) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 0) 0) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 8) perm15.symm)

theorem finiteEdge1_0 : SafeCore (mutate (finiteNode 1) 0) := by
  have he := mutation_equal (finiteP 1) (prelabel (tailP [6] 0) perm21.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 1) 0) 0)
  rw [he]
  exact Safe.framed (tailP_safe [6] 0 0 (by decide) (by decide)) perm21.symm

theorem finiteEdge1_1 : SafeCore (mutate (finiteNode 1) 1) := by
  have he := mutation_equal (finiteP 1) (preverse (prelabel (root [5] [11] [18] [2] [4] [1]) perm6.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 1) 1
  rw [show mutate (finiteNode 1) 1=(reverse (relabel (matrix (root [5] [11] [18] [2] [4] [1]) 0) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [5] [11] [18] [2] [4] [1] 0 (by decide) (by decide)) perm6.symm)

theorem finiteEdge1_2 : SafeCore (mutate (finiteNode 1) 2) := by
  have he := mutation_equal (finiteP 1) (preverse (prelabel (tailP [6] 2) perm20.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 1) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (tailP_safe [6] 2 0 (by decide) (by decide)) perm20.symm)

theorem finiteEdge1_3 : SafeCore (mutate (finiteNode 1) 3) := by
  have he := mutation_equal (finiteP 1) (prelabel (finiteP 9) perm21.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 1) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 9) perm21.symm

theorem finiteEdge2_0 : SafeCore (mutate (finiteNode 2) 0) := by
  have he := mutation_equal (finiteP 2) (prelabel (tailP [6] 1) perm21.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 2) 0) 0)
  rw [he]
  exact Safe.framed (tailP_safe [6] 1 0 (by decide) (by decide)) perm21.symm

theorem finiteEdge2_1 : SafeCore (mutate (finiteNode 2) 1) := by
  have he := mutation_equal (finiteP 2) (preverse (prelabel (finiteP 10) perm19.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 2) 0) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 10) perm19.symm)

theorem finiteEdge2_2 : SafeCore (mutate (finiteNode 2) 2) := by
  have he := mutation_equal (finiteP 2) (prelabel (tailP [6] 3) perm1.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 2) 0) 2)
  rw [he]
  exact Safe.framed (tailP_safe [6] 3 0 (by decide) (by decide)) perm1.symm

theorem finiteEdge2_3 : SafeCore (mutate (finiteNode 2) 3) := by
  have he := mutation_equal (finiteP 2) (prelabel (finiteP 11) perm21.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 2) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 11) perm21.symm

theorem finiteEdge3_0 : SafeCore (mutate (finiteNode 3) 0) := by
  have he := mutation_equal (finiteP 3) (preverse (prelabel (tailP [5] 3) perm1.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 3) 0) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (tailP_safe [5] 3 0 (by decide) (by decide)) perm1.symm)

theorem finiteEdge3_1 : SafeCore (mutate (finiteNode 3) 1) := by
  have he := mutation_equal (finiteP 3) (preverse (prelabel (root [5] [19] [9] [4] [2] [1]) perm6.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 3) 1
  rw [show mutate (finiteNode 3) 1=(reverse (relabel (matrix (root [5] [19] [9] [4] [2] [1]) 0) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [5] [19] [9] [4] [2] [1] 0 (by decide) (by decide)) perm6.symm)

theorem finiteEdge3_2 : SafeCore (mutate (finiteNode 3) 2) := by
  have he := mutation_equal (finiteP 3) (preverse (prelabel (tailP [6] 3) perm21.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 3) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (tailP_safe [6] 3 0 (by decide) (by decide)) perm21.symm)

theorem finiteEdge3_3 : SafeCore (mutate (finiteNode 3) 3) := by
  have he := mutation_equal (finiteP 3) (preverse (prelabel (finiteP 9) perm15.symm)) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 3) 0) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 9) perm15.symm)

theorem finiteEdge4_0 : SafeCore (mutate (finiteNode 4) 0) := by
  have he := mutation_equal (finiteP 4) (preverse (prelabel (tailP [5] 2) perm1.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 4) 0) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (tailP_safe [5] 2 0 (by decide) (by decide)) perm1.symm)

theorem finiteEdge4_1 : SafeCore (mutate (finiteNode 4) 1) := by
  have he := mutation_equal (finiteP 4) (prelabel (generic finiteParam0_0 finiteParam0_1 finiteParam0_2 finiteParam0_3 0) perm17.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 4) 0) 1)
  rw [he]
  exact Safe.framed (finiteRegion0_safe 0) perm17.symm

theorem finiteEdge4_2 : SafeCore (mutate (finiteNode 4) 2) := by
  have he := mutation_equal (finiteP 4) (preverse (prelabel (finiteP 14) perm21.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 4) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 14) perm21.symm)

theorem finiteEdge4_3 : SafeCore (mutate (finiteNode 4) 3) := by
  have he := mutation_equal (finiteP 4) (prelabel (finiteP 11) perm1.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 4) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 11) perm1.symm

theorem finiteEdge5_0 : SafeCore (mutate (finiteNode 5) 0) := by
  have he := mutation_equal (finiteP 5) (prelabel (finiteP 15) perm6.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 5) 0) 0)
  rw [he]
  exact Safe.framed (finite_safe 15) perm6.symm

theorem finiteEdge5_1 : SafeCore (mutate (finiteNode 5) 1) := by
  have he := mutation_equal (finiteP 5) (preverse (prelabel (root [3] [5] [5] [2] [2] [1]) perm6.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 5) 1
  rw [show mutate (finiteNode 5) 1=(reverse (relabel (matrix (root [3] [5] [5] [2] [2] [1]) 0) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [3] [5] [5] [2] [2] [1] 0 (by decide) (by decide)) perm6.symm)

theorem finiteEdge5_2 : SafeCore (mutate (finiteNode 5) 2) := by
  have he := mutation_equal (finiteP 5) (preverse (prelabel (finiteP 16) perm21.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 5) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 16) perm21.symm)

theorem finiteEdge5_3 : SafeCore (mutate (finiteNode 5) 3) := by
  have he := mutation_equal (finiteP 5) (prelabel (finiteP 0) perm21.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 5) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 0) perm21.symm

theorem finiteEdge6_0 : SafeCore (mutate (finiteNode 6) 0) := by
  have he := mutation_equal (finiteP 6) (preverse (prelabel (finiteP 17) perm0.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 6) 0) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 17) perm0.symm)

theorem finiteEdge6_1 : SafeCore (mutate (finiteNode 6) 1) := by
  have he := mutation_equal (finiteP 6) (prelabel (finiteP 18) perm0.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 6) 0) 1)
  rw [he]
  exact Safe.framed (finite_safe 18) perm0.symm

theorem finiteEdge6_2 : SafeCore (mutate (finiteNode 6) 2) := by
  have he := mutation_equal (finiteP 6) (prelabel (finiteP 19) perm4.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 6) 0) 2)
  rw [he]
  exact Safe.framed (finite_safe 19) perm4.symm

theorem finiteEdge6_3 : SafeCore (mutate (finiteNode 6) 3) := by
  have he := mutation_equal (finiteP 6) (preverse (prelabel (finiteP 0) perm16.symm)) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 6) 0) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 0) perm16.symm)

theorem finiteEdge7_0 : SafeCore (mutate (finiteNode 7) 0) := by
  have he := mutation_equal (finiteP 7) (prelabel (finiteP 9) perm21.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 7) 0) 0)
  rw [he]
  exact Safe.framed (finite_safe 9) perm21.symm

theorem finiteEdge7_1 : SafeCore (mutate (finiteNode 7) 1) := by
  have he := mutation_equal (finiteP 7) (preverse (prelabel (root [3] [7] [4] [2] [2] [1]) perm6.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 7) 1
  rw [show mutate (finiteNode 7) 1=(reverse (relabel (matrix (root [3] [7] [4] [2] [2] [1]) 0) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [3] [7] [4] [2] [2] [1] 0 (by decide) (by decide)) perm6.symm)

theorem finiteEdge7_2 : SafeCore (mutate (finiteNode 7) 2) := by
  have he := mutation_equal (finiteP 7) (preverse (prelabel (finiteP 14) perm20.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 7) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 14) perm20.symm)

theorem finiteEdge7_3 : SafeCore (mutate (finiteNode 7) 3) := by
  have he := mutation_equal (finiteP 7) (preverse (prelabel (finiteP 0) perm15.symm)) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 7) 0) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 0) perm15.symm)

theorem finiteEdge8_0 : SafeCore (mutate (finiteNode 8) 0) := by
  have he := mutation_equal (finiteP 8) (prelabel (finiteP 20) perm7.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 8) 0) 0)
  rw [he]
  exact Safe.framed (finite_safe 20) perm7.symm

theorem finiteEdge8_1 : SafeCore (mutate (finiteNode 8) 1) := by
  have he := mutation_equal (finiteP 8) (prelabel (finiteP 21) perm0.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 8) 0) 1)
  rw [he]
  exact Safe.framed (finite_safe 21) perm0.symm

theorem finiteEdge8_2 : SafeCore (mutate (finiteNode 8) 2) := by
  have he := mutation_equal (finiteP 8) (preverse (prelabel (finiteP 0) perm20.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 8) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 0) perm20.symm)

theorem finiteEdge8_3 : SafeCore (mutate (finiteNode 8) 3) := by
  have he := mutation_equal (finiteP 8) (prelabel (finiteP 22) perm21.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 8) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 22) perm21.symm

theorem finiteEdge9_0 : SafeCore (mutate (finiteNode 9) 0) := by
  have he := mutation_equal (finiteP 9) (prelabel (tailP [5] 0) perm21.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 9) 0) 0)
  rw [he]
  exact Safe.framed (tailP_safe [5] 0 0 (by decide) (by decide)) perm21.symm

theorem finiteEdge9_1 : SafeCore (mutate (finiteNode 9) 1) := by
  have he := mutation_equal (finiteP 9) (preverse (prelabel (root [4] [9] [10] [2] [3] [1]) perm6.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 9) 1
  rw [show mutate (finiteNode 9) 1=(reverse (relabel (matrix (root [4] [9] [10] [2] [3] [1]) 0) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [4] [9] [10] [2] [3] [1] 0 (by decide) (by decide)) perm6.symm)

theorem finiteEdge9_2 : SafeCore (mutate (finiteNode 9) 2) := by
  have he := mutation_equal (finiteP 9) (preverse (prelabel (tailP [5] 2) perm20.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 9) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (tailP_safe [5] 2 0 (by decide) (by decide)) perm20.symm)

theorem finiteEdge9_3 : SafeCore (mutate (finiteNode 9) 3) := by
  have he := mutation_equal (finiteP 9) (prelabel (finiteP 7) perm21.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 9) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 7) perm21.symm

theorem finiteEdge10_0 : SafeCore (mutate (finiteNode 10) 0) := by
  have he := mutation_equal (finiteP 10) (preverse (prelabel (root [4] [19] [67] [5] [18] [1]) perm5.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 10) 0
  rw [show mutate (finiteNode 10) 0=(reverse (relabel (matrix (root [4] [19] [67] [5] [18] [1]) 0) perm5.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [4] [19] [67] [5] [18] [1] 0 (by decide) (by decide)) perm5.symm)

theorem finiteEdge10_1 : SafeCore (mutate (finiteNode 10) 1) := by
  have he := mutation_equal (finiteP 10) (preverse (prelabel (finiteP 23) perm19.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 10) 0) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 23) perm19.symm)

theorem finiteEdge10_2 : SafeCore (mutate (finiteNode 10) 2) := by
  have he := mutation_equal (finiteP 10) (prelabel (finiteP 24) perm1.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 10) 0) 2)
  rw [he]
  exact Safe.framed (finite_safe 24) perm1.symm

theorem finiteEdge10_3 : SafeCore (mutate (finiteNode 10) 3) := by
  have he := mutation_equal (finiteP 10) (preverse (prelabel (tailP [5] 1) perm11.symm)) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 10) 0) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (tailP_safe [5] 1 0 (by decide) (by decide)) perm11.symm)

theorem finiteEdge11_0 : SafeCore (mutate (finiteNode 11) 0) := by
  have he := mutation_equal (finiteP 11) (prelabel (tailP [5] 1) perm21.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 11) 0) 0)
  rw [he]
  exact Safe.framed (tailP_safe [5] 1 0 (by decide) (by decide)) perm21.symm

theorem finiteEdge11_1 : SafeCore (mutate (finiteNode 11) 1) := by
  have he := mutation_equal (finiteP 11) (preverse (prelabel (finiteP 25) perm19.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 11) 0) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 25) perm19.symm)

theorem finiteEdge11_2 : SafeCore (mutate (finiteNode 11) 2) := by
  have he := mutation_equal (finiteP 11) (prelabel (tailP [5] 3) perm1.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 11) 0) 2)
  rw [he]
  exact Safe.framed (tailP_safe [5] 3 0 (by decide) (by decide)) perm1.symm

theorem finiteEdge11_3 : SafeCore (mutate (finiteNode 11) 3) := by
  have he := mutation_equal (finiteP 11) (prelabel (finiteP 26) perm21.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 11) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 26) perm21.symm

theorem finiteEdge12_0 : SafeCore (mutate (finiteNode 12) 0) := by
  have he := mutation_equal (finiteP 12) (prelabel (finiteP 13) perm21.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 12) 0) 0)
  rw [he]
  exact Safe.framed (finite_safe 13) perm21.symm

theorem finiteEdge12_1 : SafeCore (mutate (finiteNode 12) 1) := by
  have he := mutation_equal (finiteP 12) (prelabel (generic finiteParam1_0 finiteParam1_1 finiteParam1_2 finiteParam1_3 0) perm17.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 12) 0) 1)
  rw [he]
  exact Safe.framed (finiteRegion1_safe 0) perm17.symm

theorem finiteEdge12_2 : SafeCore (mutate (finiteNode 12) 2) := by
  have he := mutation_equal (finiteP 12) (preverse (prelabel (generic finiteParam0_0 finiteParam0_1 finiteParam0_2 finiteParam0_3 0) perm3.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 12) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finiteRegion0_safe 0) perm3.symm)

theorem finiteEdge12_3 : SafeCore (mutate (finiteNode 12) 3) := by
  have he := mutation_equal (finiteP 12) (prelabel (finiteP 25) perm1.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 12) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 25) perm1.symm

theorem finiteEdge13_0 : SafeCore (mutate (finiteNode 13) 0) := by
  have he := mutation_equal (finiteP 13) (prelabel (fork [4] [3] [55] [11] [206] [4]) perm5.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (finite_safe 13)
  rw [show mutate (finiteNode 13) 0=(relabel (matrix (fork [4] [3] [55] [11] [206] [4]) 0) perm5.symm) from he]
  exact IsFork.relabelled (fork_sound [4] [3] [55] [11] [206] [4] 0 (by decide) (by decide)) perm5.symm

theorem finiteEdge13_1 : SafeCore (mutate (finiteNode 13) 1) := by
  have he := mutation_equal (finiteP 13) (preverse (prelabel (root [55] [223] [766] [4] [14] [1]) perm6.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 13) 1
  rw [show mutate (finiteNode 13) 1=(reverse (relabel (matrix (root [55] [223] [766] [4] [14] [1]) 0) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [55] [223] [766] [4] [14] [1] 0 (by decide) (by decide)) perm6.symm)

theorem finiteEdge13_2 : SafeCore (mutate (finiteNode 13) 2) := by
  have he := mutation_equal (finiteP 13) (preverse (prelabel (generic finiteParam0_0 finiteParam0_1 finiteParam0_2 finiteParam0_3 2) perm16.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 13) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finiteRegion0_safe 2) perm16.symm)

theorem finiteEdge13_3 : SafeCore (mutate (finiteNode 13) 3) := by
  have he := mutation_equal (finiteP 13) (prelabel (finiteP 12) perm21.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 13) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 12) perm21.symm

theorem finiteEdge14_0 : SafeCore (mutate (finiteNode 14) 0) := by
  have he := mutation_equal (finiteP 14) (preverse (prelabel (finiteP 16) perm1.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 14) 0) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 16) perm1.symm)

theorem finiteEdge14_1 : SafeCore (mutate (finiteNode 14) 1) := by
  have he := mutation_equal (finiteP 14) (preverse (prelabel (root [4] [11] [7] [3] [2] [1]) perm6.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 14) 1
  rw [show mutate (finiteNode 14) 1=(reverse (relabel (matrix (root [4] [11] [7] [3] [2] [1]) 0) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [4] [11] [7] [3] [2] [1] 0 (by decide) (by decide)) perm6.symm)

theorem finiteEdge14_2 : SafeCore (mutate (finiteNode 14) 2) := by
  have he := mutation_equal (finiteP 14) (preverse (prelabel (tailP [5] 3) perm21.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 14) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (tailP_safe [5] 3 0 (by decide) (by decide)) perm21.symm)

theorem finiteEdge14_3 : SafeCore (mutate (finiteNode 14) 3) := by
  have he := mutation_equal (finiteP 14) (preverse (prelabel (finiteP 7) perm15.symm)) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 14) 0) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 7) perm15.symm)

theorem finiteEdge15_0 : SafeCore (mutate (finiteNode 15) 0) := by
  have he := mutation_equal (finiteP 15) (preverse (prelabel (finiteP 5) perm1.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 15) 0) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 5) perm1.symm)

theorem finiteEdge15_1 : SafeCore (mutate (finiteNode 15) 1) := by
  have he := mutation_equal (finiteP 15) (prelabel (finiteP 5) perm6.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 15) 0) 1)
  rw [he]
  exact Safe.framed (finite_safe 5) perm6.symm

theorem finiteEdge15_2 : SafeCore (mutate (finiteNode 15) 2) := by
  have he := mutation_equal (finiteP 15) (prelabel (finiteP 22) perm0.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 15) 0) 2)
  rw [he]
  exact Safe.framed (finite_safe 22) perm0.symm

theorem finiteEdge15_3 : SafeCore (mutate (finiteNode 15) 3) := by
  have he := mutation_equal (finiteP 15) (preverse (prelabel (finiteP 22) perm7.symm)) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 15) 0) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 22) perm7.symm)

theorem finiteEdge16_0 : SafeCore (mutate (finiteNode 16) 0) := by
  have he := mutation_equal (finiteP 16) (preverse (prelabel (finiteP 14) perm1.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 16) 0) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 14) perm1.symm)

theorem finiteEdge16_1 : SafeCore (mutate (finiteNode 16) 1) := by
  have he := mutation_equal (finiteP 16) (prelabel (generic finiteParam2_0 finiteParam2_1 finiteParam2_2 finiteParam2_3 0) perm17.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 16) 0) 1)
  rw [he]
  exact Safe.framed (finiteRegion2_safe 0) perm17.symm

theorem finiteEdge16_2 : SafeCore (mutate (finiteNode 16) 2) := by
  have he := mutation_equal (finiteP 16) (preverse (prelabel (finiteP 5) perm21.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 16) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 5) perm21.symm)

theorem finiteEdge16_3 : SafeCore (mutate (finiteNode 16) 3) := by
  have he := mutation_equal (finiteP 16) (prelabel (finiteP 26) perm1.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 16) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 26) perm1.symm

theorem finiteEdge17_0 : SafeCore (mutate (finiteNode 17) 0) := by
  have he := mutation_equal (finiteP 17) (preverse (prelabel (finiteP 6) perm0.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 17) 0) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 6) perm0.symm)

theorem finiteEdge17_1 : SafeCore (mutate (finiteNode 17) 1) := by
  have he := mutation_equal (finiteP 17) (prelabel (finiteP 31) perm0.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 17) 0) 1)
  rw [he]
  exact Safe.framed (finite_safe 31) perm0.symm

theorem finiteEdge17_2 : SafeCore (mutate (finiteNode 17) 2) := by
  have he := mutation_equal (finiteP 17) (prelabel (finiteP 32) perm1.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 17) 0) 2)
  rw [he]
  exact Safe.framed (finite_safe 32) perm1.symm

theorem finiteEdge17_3 : SafeCore (mutate (finiteNode 17) 3) := by
  have he := mutation_equal (finiteP 17) (preverse (prelabel (finiteP 33) perm0.symm)) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 17) 0) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 33) perm0.symm)

theorem finiteEdge18_0 : SafeCore (mutate (finiteNode 18) 0) := by
  have he := mutation_equal (finiteP 18) (preverse (prelabel (finiteP 31) perm0.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 18) 0) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 31) perm0.symm)

theorem finiteEdge18_1 : SafeCore (mutate (finiteNode 18) 1) := by
  have he := mutation_equal (finiteP 18) (prelabel (finiteP 6) perm0.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 18) 0) 1)
  rw [he]
  exact Safe.framed (finite_safe 6) perm0.symm

theorem finiteEdge18_2 : SafeCore (mutate (finiteNode 18) 2) := by
  have he := mutation_equal (finiteP 18) (prelabel (finiteP 34) perm1.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 18) 0) 2)
  rw [he]
  exact Safe.framed (finite_safe 34) perm1.symm

theorem finiteEdge18_3 : SafeCore (mutate (finiteNode 18) 3) := by
  have he := mutation_equal (finiteP 18) (prelabel (finiteP 21) perm1.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 18) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 21) perm1.symm

theorem finiteEdge19_0 : SafeCore (mutate (finiteNode 19) 0) := by
  have he := mutation_equal (finiteP 19) (preverse (prelabel (root [5] [24] [38] [5] [8] [1]) perm5.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 19) 0
  rw [show mutate (finiteNode 19) 0=(reverse (relabel (matrix (root [5] [24] [38] [5] [8] [1]) 0) perm5.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [5] [24] [38] [5] [8] [1] 0 (by decide) (by decide)) perm5.symm)

theorem finiteEdge19_1 : SafeCore (mutate (finiteNode 19) 1) := by
  have he := mutation_equal (finiteP 19) (prelabel (finiteP 35) perm5.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 19) 0) 1)
  rw [he]
  exact Safe.framed (finite_safe 35) perm5.symm

theorem finiteEdge19_2 : SafeCore (mutate (finiteNode 19) 2) := by
  have he := mutation_equal (finiteP 19) (prelabel (finiteP 36) perm4.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 19) 0) 2)
  rw [he]
  exact Safe.framed (finite_safe 36) perm4.symm

theorem finiteEdge19_3 : SafeCore (mutate (finiteNode 19) 3) := by
  have he := mutation_equal (finiteP 19) (prelabel (finiteP 6) perm3.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 19) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 6) perm3.symm

theorem finiteEdge20_0 : SafeCore (mutate (finiteNode 20) 0) := by
  have he := mutation_equal (finiteP 20) (preverse (prelabel (finiteP 8) perm0.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 20) 0) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 8) perm0.symm)

theorem finiteEdge20_1 : SafeCore (mutate (finiteNode 20) 1) := by
  have he := mutation_equal (finiteP 20) (prelabel (finiteP 8) perm7.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 20) 0) 1)
  rw [he]
  exact Safe.framed (finite_safe 8) perm7.symm

theorem finiteEdge20_2 : SafeCore (mutate (finiteNode 20) 2) := by
  have he := mutation_equal (finiteP 20) (preverse (prelabel (finiteP 37) perm0.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 20) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 37) perm0.symm)

theorem finiteEdge20_3 : SafeCore (mutate (finiteNode 20) 3) := by
  have he := mutation_equal (finiteP 20) (prelabel (finiteP 37) perm7.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 20) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 37) perm7.symm

theorem finiteEdge21_0 : SafeCore (mutate (finiteNode 21) 0) := by
  have he := mutation_equal (finiteP 21) (preverse (prelabel (finiteP 8) perm7.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 21) 0) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 8) perm7.symm)

theorem finiteEdge21_1 : SafeCore (mutate (finiteNode 21) 1) := by
  have he := mutation_equal (finiteP 21) (prelabel (finiteP 8) perm0.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 21) 0) 1)
  rw [he]
  exact Safe.framed (finite_safe 8) perm0.symm

theorem finiteEdge21_2 : SafeCore (mutate (finiteNode 21) 2) := by
  have he := mutation_equal (finiteP 21) (prelabel (finiteP 18) perm1.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 21) 0) 2)
  rw [he]
  exact Safe.framed (finite_safe 18) perm1.symm

theorem finiteEdge21_3 : SafeCore (mutate (finiteNode 21) 3) := by
  have he := mutation_equal (finiteP 21) (preverse (prelabel (finiteP 18) perm6.symm)) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 21) 0) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 18) perm6.symm)

theorem finiteEdge22_0 : SafeCore (mutate (finiteNode 22) 0) := by
  have he := mutation_equal (finiteP 22) (prelabel (finiteP 8) perm21.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 22) 0) 0)
  rw [he]
  exact Safe.framed (finite_safe 8) perm21.symm

theorem finiteEdge22_1 : SafeCore (mutate (finiteNode 22) 1) := by
  have he := mutation_equal (finiteP 22) (preverse (prelabel (finiteP 26) perm19.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 22) 0) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 26) perm19.symm)

theorem finiteEdge22_2 : SafeCore (mutate (finiteNode 22) 2) := by
  have he := mutation_equal (finiteP 22) (prelabel (finiteP 15) perm0.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 22) 0) 2)
  rw [he]
  exact Safe.framed (finite_safe 15) perm0.symm

theorem finiteEdge22_3 : SafeCore (mutate (finiteNode 22) 3) := by
  have he := mutation_equal (finiteP 22) (preverse (prelabel (finiteP 38) perm7.symm)) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 22) 0) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 38) perm7.symm)

theorem finiteEdge23_0 : SafeCore (mutate (finiteNode 23) 0) := by
  have he := mutation_equal (finiteP 23) (prelabel (fork [5] [86] [6] [412] [29] [5]) perm4.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (finite_safe 23)
  rw [show mutate (finiteNode 23) 0=(relabel (matrix (fork [5] [86] [6] [412] [29] [5]) 0) perm4.symm) from he]
  exact IsFork.relabelled (fork_sound [5] [86] [6] [412] [29] [5] 0 (by decide) (by decide)) perm4.symm

theorem finiteEdge23_1 : SafeCore (mutate (finiteNode 23) 1) := by
  have he := mutation_equal (finiteP 23) (preverse (prelabel (fork [18] [86] [5] [1543] [91] [6]) perm10.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (finite_safe 23)
  rw [show mutate (finiteNode 23) 1=(reverse (relabel (matrix (fork [18] [86] [5] [1543] [91] [6]) 0) perm10.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [18] [86] [5] [1543] [91] [6] 0 (by decide) (by decide)) perm10.symm)

theorem finiteEdge23_2 : SafeCore (mutate (finiteNode 23) 2) := by
  have he := mutation_equal (finiteP 23) (prelabel (finiteP 39) perm1.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 23) 0) 2)
  rw [he]
  exact Safe.framed (finite_safe 39) perm1.symm

theorem finiteEdge23_3 : SafeCore (mutate (finiteNode 23) 3) := by
  have he := mutation_equal (finiteP 23) (preverse (prelabel (finiteP 10) perm11.symm)) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 23) 0) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 10) perm11.symm)

theorem finiteEdge24_0 : SafeCore (mutate (finiteNode 24) 0) := by
  have he := mutation_equal (finiteP 24) (prelabel (finiteP 40) perm21.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 24) 0) 0)
  rw [he]
  exact Safe.framed (finite_safe 40) perm21.symm

theorem finiteEdge24_1 : SafeCore (mutate (finiteNode 24) 1) := by
  have he := mutation_equal (finiteP 24) (prelabel (generic finiteParam3_0 finiteParam3_1 finiteParam3_2 finiteParam3_3 0) perm17.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 24) 0) 1)
  rw [he]
  exact Safe.framed (finiteRegion3_safe 0) perm17.symm

theorem finiteEdge24_2 : SafeCore (mutate (finiteNode 24) 2) := by
  have he := mutation_equal (finiteP 24) (preverse (prelabel (generic finiteParam4_0 finiteParam4_1 finiteParam4_2 finiteParam4_3 0) perm3.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 24) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finiteRegion4_safe 0) perm3.symm)

theorem finiteEdge24_3 : SafeCore (mutate (finiteNode 24) 3) := by
  have he := mutation_equal (finiteP 24) (prelabel (finiteP 10) perm1.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 24) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 10) perm1.symm

theorem finiteEdge25_0 : SafeCore (mutate (finiteNode 25) 0) := by
  have he := mutation_equal (finiteP 25) (preverse (prelabel (root [3] [11] [26] [4] [10] [1]) perm5.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 25) 0
  rw [show mutate (finiteNode 25) 0=(reverse (relabel (matrix (root [3] [11] [26] [4] [10] [1]) 0) perm5.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [3] [11] [26] [4] [10] [1] 0 (by decide) (by decide)) perm5.symm)

theorem finiteEdge25_1 : SafeCore (mutate (finiteNode 25) 1) := by
  have he := mutation_equal (finiteP 25) (preverse (prelabel (finiteP 42) perm19.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 25) 0) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 42) perm19.symm)

theorem finiteEdge25_2 : SafeCore (mutate (finiteNode 25) 2) := by
  have he := mutation_equal (finiteP 25) (prelabel (finiteP 12) perm1.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 25) 0) 2)
  rw [he]
  exact Safe.framed (finite_safe 12) perm1.symm

theorem finiteEdge25_3 : SafeCore (mutate (finiteNode 25) 3) := by
  have he := mutation_equal (finiteP 25) (preverse (prelabel (finiteP 11) perm11.symm)) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 25) 0) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 11) perm11.symm)

theorem finiteEdge26_0 : SafeCore (mutate (finiteNode 26) 0) := by
  have he := mutation_equal (finiteP 26) (prelabel (finiteP 11) perm21.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 26) 0) 0)
  rw [he]
  exact Safe.framed (finite_safe 11) perm21.symm

theorem finiteEdge26_1 : SafeCore (mutate (finiteNode 26) 1) := by
  have he := mutation_equal (finiteP 26) (preverse (prelabel (finiteP 43) perm19.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 26) 0) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 43) perm19.symm)

theorem finiteEdge26_2 : SafeCore (mutate (finiteNode 26) 2) := by
  have he := mutation_equal (finiteP 26) (prelabel (finiteP 16) perm1.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 26) 0) 2)
  rw [he]
  exact Safe.framed (finite_safe 16) perm1.symm

theorem finiteEdge26_3 : SafeCore (mutate (finiteNode 26) 3) := by
  have he := mutation_equal (finiteP 26) (preverse (prelabel (finiteP 22) perm11.symm)) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 26) 0) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 22) perm11.symm)

theorem finiteEdge27_0 : SafeCore (mutate (finiteNode 27) 0) := by
  have he := mutation_equal (finiteP 27) (prelabel (finiteP 28) perm21.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 27) 0) 0)
  rw [he]
  exact Safe.framed (finite_safe 28) perm21.symm

theorem finiteEdge27_1 : SafeCore (mutate (finiteNode 27) 1) := by
  have he := mutation_equal (finiteP 27) (preverse (prelabel (root [57] [571] [223] [10] [4] [1]) perm6.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 27) 1
  rw [show mutate (finiteNode 27) 1=(reverse (relabel (matrix (root [57] [571] [223] [10] [4] [1]) 0) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [57] [571] [223] [10] [4] [1] 0 (by decide) (by decide)) perm6.symm)

theorem finiteEdge27_2 : SafeCore (mutate (finiteNode 27) 2) := by
  have he := mutation_equal (finiteP 27) (preverse (prelabel (generic finiteParam1_0 finiteParam1_1 finiteParam1_2 finiteParam1_3 0) perm3.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 27) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finiteRegion1_safe 0) perm3.symm)

theorem finiteEdge27_3 : SafeCore (mutate (finiteNode 27) 3) := by
  have he := mutation_equal (finiteP 27) (prelabel (finiteP 42) perm1.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 27) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 42) perm1.symm

theorem finiteEdge28_0 : SafeCore (mutate (finiteNode 28) 0) := by
  have he := mutation_equal (finiteP 28) (prelabel (fork [5] [4] [281] [19] [1348] [10]) perm5.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (finite_safe 28)
  rw [show mutate (finiteNode 28) 0=(relabel (matrix (fork [5] [4] [281] [19] [1348] [10]) 0) perm5.symm) from he]
  exact IsFork.relabelled (fork_sound [5] [4] [281] [19] [1348] [10] 0 (by decide) (by decide)) perm5.symm

theorem finiteEdge28_1 : SafeCore (mutate (finiteNode 28) 1) := by
  have he := mutation_equal (finiteP 28) (preverse (prelabel (root [281] [2814] [16012] [10] [57] [1]) perm6.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 28) 1
  rw [show mutate (finiteNode 28) 1=(reverse (relabel (matrix (root [281] [2814] [16012] [10] [57] [1]) 0) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [281] [2814] [16012] [10] [57] [1] 0 (by decide) (by decide)) perm6.symm)

theorem finiteEdge28_2 : SafeCore (mutate (finiteNode 28) 2) := by
  have he := mutation_equal (finiteP 28) (preverse (prelabel (generic finiteParam1_0 finiteParam1_1 finiteParam1_2 finiteParam1_3 2) perm16.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 28) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finiteRegion1_safe 2) perm16.symm)

theorem finiteEdge28_3 : SafeCore (mutate (finiteNode 28) 3) := by
  have he := mutation_equal (finiteP 28) (prelabel (finiteP 27) perm21.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 28) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 27) perm21.symm

theorem finiteEdge29_0 : SafeCore (mutate (finiteNode 29) 0) := by
  have he := mutation_equal (finiteP 29) (prelabel (finiteP 30) perm21.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 29) 0) 0)
  rw [he]
  exact Safe.framed (finite_safe 30) perm21.symm

theorem finiteEdge29_1 : SafeCore (mutate (finiteNode 29) 1) := by
  have he := mutation_equal (finiteP 29) (prelabel (generic finiteParam5_0 finiteParam5_1 finiteParam5_2 finiteParam5_3 0) perm17.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 29) 0) 1)
  rw [he]
  exact Safe.framed (finiteRegion5_safe 0) perm17.symm

theorem finiteEdge29_2 : SafeCore (mutate (finiteNode 29) 2) := by
  have he := mutation_equal (finiteP 29) (preverse (prelabel (generic finiteParam2_0 finiteParam2_1 finiteParam2_2 finiteParam2_3 0) perm3.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 29) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finiteRegion2_safe 0) perm3.symm)

theorem finiteEdge29_3 : SafeCore (mutate (finiteNode 29) 3) := by
  have he := mutation_equal (finiteP 29) (prelabel (finiteP 43) perm1.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 29) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 43) perm1.symm

theorem finiteEdge30_0 : SafeCore (mutate (finiteNode 30) 0) := by
  have he := mutation_equal (finiteP 30) (prelabel (fork [3] [2] [20] [5] [53] [3]) perm5.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (finite_safe 30)
  rw [show mutate (finiteNode 30) 0=(relabel (matrix (fork [3] [2] [20] [5] [53] [3]) 0) perm5.symm) from he]
  exact IsFork.relabelled (fork_sound [3] [2] [20] [5] [53] [3] 0 (by decide) (by decide)) perm5.symm

theorem finiteEdge30_1 : SafeCore (mutate (finiteNode 30) 1) := by
  have he := mutation_equal (finiteP 30) (preverse (prelabel (root [20] [62] [137] [3] [7] [1]) perm6.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 30) 1
  rw [show mutate (finiteNode 30) 1=(reverse (relabel (matrix (root [20] [62] [137] [3] [7] [1]) 0) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [20] [62] [137] [3] [7] [1] 0 (by decide) (by decide)) perm6.symm)

theorem finiteEdge30_2 : SafeCore (mutate (finiteNode 30) 2) := by
  have he := mutation_equal (finiteP 30) (preverse (prelabel (generic finiteParam2_0 finiteParam2_1 finiteParam2_2 finiteParam2_3 2) perm16.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 30) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finiteRegion2_safe 2) perm16.symm)

theorem finiteEdge30_3 : SafeCore (mutate (finiteNode 30) 3) := by
  have he := mutation_equal (finiteP 30) (prelabel (finiteP 29) perm21.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 30) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 29) perm21.symm

theorem finiteEdge31_0 : SafeCore (mutate (finiteNode 31) 0) := by
  have he := mutation_equal (finiteP 31) (preverse (prelabel (finiteP 18) perm0.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 31) 0) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 18) perm0.symm)

theorem finiteEdge31_1 : SafeCore (mutate (finiteNode 31) 1) := by
  have he := mutation_equal (finiteP 31) (prelabel (finiteP 17) perm0.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 31) 0) 1)
  rw [he]
  exact Safe.framed (finite_safe 17) perm0.symm

theorem finiteEdge31_2 : SafeCore (mutate (finiteNode 31) 2) := by
  have he := mutation_equal (finiteP 31) (prelabel (finiteP 46) perm4.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 31) 0) 2)
  rw [he]
  exact Safe.framed (finite_safe 46) perm4.symm

theorem finiteEdge31_3 : SafeCore (mutate (finiteNode 31) 3) := by
  have he := mutation_equal (finiteP 31) (preverse (prelabel (finiteP 47) perm2.symm)) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 31) 0) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 47) perm2.symm)

theorem finiteEdge32_0 : SafeCore (mutate (finiteNode 32) 0) := by
  have he := mutation_equal (finiteP 32) (prelabel (zero finiteParam6_0 finiteParam6_1 finiteParam6_2 finiteParam6_3 0) perm6.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 32) 0) 0)
  rw [he]
  exact Safe.framed (finiteRegion6_safe 0) perm6.symm

theorem finiteEdge32_1 : SafeCore (mutate (finiteNode 32) 1) := by
  have he := mutation_equal (finiteP 32) (prelabel (finiteP 48) perm0.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 32) 0) 1)
  rw [he]
  exact Safe.framed (finite_safe 48) perm0.symm

theorem finiteEdge32_2 : SafeCore (mutate (finiteNode 32) 2) := by
  have he := mutation_equal (finiteP 32) (prelabel (root [8] [299] [55] [38] [7] []) perm16.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 32) 2
  rw [show mutate (finiteNode 32) 2=(relabel (matrix (root [8] [299] [55] [38] [7] []) 0) perm16.symm) from he]
  exact IsRoot.relabelled (root_sound [8] [299] [55] [38] [7] [] 0 (by decide) (by decide)) perm16.symm

theorem finiteEdge32_3 : SafeCore (mutate (finiteNode 32) 3) := by
  have he := mutation_equal (finiteP 32) (prelabel (finiteP 17) perm1.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 32) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 17) perm1.symm

theorem finiteEdge33_0 : SafeCore (mutate (finiteNode 33) 0) := by
  have he := mutation_equal (finiteP 33) (prelabel (zero finiteParam7_0 finiteParam7_1 finiteParam7_2 finiteParam7_3 0) perm6.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 33) 0) 0)
  rw [he]
  exact Safe.framed (finiteRegion7_safe 0) perm6.symm

theorem finiteEdge33_1 : SafeCore (mutate (finiteNode 33) 1) := by
  have he := mutation_equal (finiteP 33) (prelabel (finiteP 49) perm0.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 33) 0) 1)
  rw [he]
  exact Safe.framed (finite_safe 49) perm0.symm

theorem finiteEdge33_2 : SafeCore (mutate (finiteNode 33) 2) := by
  have he := mutation_equal (finiteP 33) (prelabel (root [8] [86] [55] [11] [7] []) perm16.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 33) 2
  rw [show mutate (finiteNode 33) 2=(relabel (matrix (root [8] [86] [55] [11] [7] []) 0) perm16.symm) from he]
  exact IsRoot.relabelled (root_sound [8] [86] [55] [11] [7] [] 0 (by decide) (by decide)) perm16.symm

theorem finiteEdge33_3 : SafeCore (mutate (finiteNode 33) 3) := by
  have he := mutation_equal (finiteP 33) (preverse (prelabel (finiteP 17) perm0.symm)) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 33) 0) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 17) perm0.symm)

theorem finiteEdge34_0 : SafeCore (mutate (finiteNode 34) 0) := by
  have he := mutation_equal (finiteP 34) (prelabel (zero finiteParam8_0 finiteParam8_1 finiteParam8_2 finiteParam8_3 0) perm6.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 34) 0) 0)
  rw [he]
  exact Safe.framed (finiteRegion8_safe 0) perm6.symm

theorem finiteEdge34_1 : SafeCore (mutate (finiteNode 34) 1) := by
  have he := mutation_equal (finiteP 34) (prelabel (finiteP 36) perm0.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 34) 0) 1)
  rw [he]
  exact Safe.framed (finite_safe 36) perm0.symm

theorem finiteEdge34_2 : SafeCore (mutate (finiteNode 34) 2) := by
  have he := mutation_equal (finiteP 34) (prelabel (root [3] [34] [5] [13] [2] []) perm16.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 34) 2
  rw [show mutate (finiteNode 34) 2=(relabel (matrix (root [3] [34] [5] [13] [2] []) 0) perm16.symm) from he]
  exact IsRoot.relabelled (root_sound [3] [34] [5] [13] [2] [] 0 (by decide) (by decide)) perm16.symm

theorem finiteEdge34_3 : SafeCore (mutate (finiteNode 34) 3) := by
  have he := mutation_equal (finiteP 34) (prelabel (finiteP 18) perm1.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 34) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 18) perm1.symm

theorem finiteEdge35_0 : SafeCore (mutate (finiteNode 35) 0) := by
  have he := mutation_equal (finiteP 35) (prelabel (fork [8] [11] [5] [86] [41] [3]) perm4.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (finite_safe 35)
  rw [show mutate (finiteNode 35) 0=(relabel (matrix (fork [8] [11] [5] [86] [41] [3]) 0) perm4.symm) from he]
  exact IsFork.relabelled (fork_sound [8] [11] [5] [86] [41] [3] 0 (by decide) (by decide)) perm4.symm

theorem finiteEdge35_1 : SafeCore (mutate (finiteNode 35) 1) := by
  have he := mutation_equal (finiteP 35) (preverse (prelabel (fork [2] [11] [3] [14] [5] [5]) perm10.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (finite_safe 35)
  rw [show mutate (finiteNode 35) 1=(reverse (relabel (matrix (fork [2] [11] [3] [14] [5] [5]) 0) perm10.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [2] [11] [3] [14] [5] [5] 0 (by decide) (by decide)) perm10.symm)

theorem finiteEdge35_2 : SafeCore (mutate (finiteNode 35) 2) := by
  have he := mutation_equal (finiteP 35) (preverse (prelabel (finiteP 50) perm7.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 35) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 50) perm7.symm)

theorem finiteEdge35_3 : SafeCore (mutate (finiteNode 35) 3) := by
  have he := mutation_equal (finiteP 35) (prelabel (finiteP 19) perm5.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 35) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 19) perm5.symm

theorem finiteEdge36_0 : SafeCore (mutate (finiteNode 36) 0) := by
  have he := mutation_equal (finiteP 36) (prelabel (zero finiteParam8_0 finiteParam8_1 finiteParam8_2 finiteParam8_3 1) perm6.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 36) 0) 0)
  rw [he]
  exact Safe.framed (finiteRegion8_safe 1) perm6.symm

theorem finiteEdge36_1 : SafeCore (mutate (finiteNode 36) 1) := by
  have he := mutation_equal (finiteP 36) (prelabel (finiteP 34) perm0.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 36) 0) 1)
  rw [he]
  exact Safe.framed (finite_safe 34) perm0.symm

theorem finiteEdge36_2 : SafeCore (mutate (finiteNode 36) 2) := by
  have he := mutation_equal (finiteP 36) (prelabel (generic finiteParam9_0 finiteParam9_1 finiteParam9_2 finiteParam9_3 0) perm11.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 36) 0) 2)
  rw [he]
  exact Safe.framed (finiteRegion9_safe 0) perm11.symm

theorem finiteEdge36_3 : SafeCore (mutate (finiteNode 36) 3) := by
  have he := mutation_equal (finiteP 36) (prelabel (finiteP 19) perm3.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 36) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 19) perm3.symm

theorem finiteEdge37_0 : SafeCore (mutate (finiteNode 37) 0) := by
  have he := mutation_equal (finiteP 37) (preverse (prelabel (finiteP 38) perm0.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 37) 0) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 38) perm0.symm)

theorem finiteEdge37_1 : SafeCore (mutate (finiteNode 37) 1) := by
  have he := mutation_equal (finiteP 37) (prelabel (finiteP 38) perm0.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 37) 0) 1)
  rw [he]
  exact Safe.framed (finite_safe 38) perm0.symm

theorem finiteEdge37_2 : SafeCore (mutate (finiteNode 37) 2) := by
  have he := mutation_equal (finiteP 37) (prelabel (finiteP 20) perm7.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 37) 0) 2)
  rw [he]
  exact Safe.framed (finite_safe 20) perm7.symm

theorem finiteEdge37_3 : SafeCore (mutate (finiteNode 37) 3) := by
  have he := mutation_equal (finiteP 37) (preverse (prelabel (finiteP 52) perm12.symm)) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 37) 0) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 52) perm12.symm)

theorem finiteEdge38_0 : SafeCore (mutate (finiteNode 38) 0) := by
  have he := mutation_equal (finiteP 38) (preverse (prelabel (finiteP 37) perm0.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 38) 0) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 37) perm0.symm)

theorem finiteEdge38_1 : SafeCore (mutate (finiteNode 38) 1) := by
  have he := mutation_equal (finiteP 38) (prelabel (finiteP 37) perm0.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 38) 0) 1)
  rw [he]
  exact Safe.framed (finite_safe 37) perm0.symm

theorem finiteEdge38_2 : SafeCore (mutate (finiteNode 38) 2) := by
  have he := mutation_equal (finiteP 38) (preverse (prelabel (finiteP 22) perm7.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 38) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 22) perm7.symm)

theorem finiteEdge38_3 : SafeCore (mutate (finiteNode 38) 3) := by
  have he := mutation_equal (finiteP 38) (preverse (prelabel (finiteP 38) perm6.symm)) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 38) 0) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 38) perm6.symm)

theorem finiteEdge39_0 : SafeCore (mutate (finiteNode 39) 0) := by
  have he := mutation_equal (finiteP 39) (prelabel (finiteP 41) perm21.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 39) 0) 0)
  rw [he]
  exact Safe.framed (finite_safe 41) perm21.symm

theorem finiteEdge39_1 : SafeCore (mutate (finiteNode 39) 1) := by
  have he := mutation_equal (finiteP 39) (preverse (prelabel (root [116] [2089] [574] [18] [5] [1]) perm6.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 39) 1
  rw [show mutate (finiteNode 39) 1=(reverse (relabel (matrix (root [116] [2089] [574] [18] [5] [1]) 0) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [116] [2089] [574] [18] [5] [1] 0 (by decide) (by decide)) perm6.symm)

theorem finiteEdge39_2 : SafeCore (mutate (finiteNode 39) 2) := by
  have he := mutation_equal (finiteP 39) (preverse (prelabel (generic finiteParam3_0 finiteParam3_1 finiteParam3_2 finiteParam3_3 0) perm3.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 39) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finiteRegion3_safe 0) perm3.symm)

theorem finiteEdge39_3 : SafeCore (mutate (finiteNode 39) 3) := by
  have he := mutation_equal (finiteP 39) (prelabel (finiteP 23) perm1.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 39) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 23) perm1.symm

theorem finiteEdge40_0 : SafeCore (mutate (finiteNode 40) 0) := by
  have he := mutation_equal (finiteP 40) (prelabel (fork [5] [4] [114] [19] [547] [5]) perm5.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (finite_safe 40)
  rw [show mutate (finiteNode 40) 0=(relabel (matrix (fork [5] [4] [114] [19] [547] [5]) 0) perm5.symm) from he]
  exact IsFork.relabelled (fork_sound [5] [4] [114] [19] [547] [5] 0 (by decide) (by decide)) perm5.symm

theorem finiteEdge40_1 : SafeCore (mutate (finiteNode 40) 1) := by
  have he := mutation_equal (finiteP 40) (preverse (prelabel (root [114] [574] [2617] [5] [23] [1]) perm6.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 40) 1
  rw [show mutate (finiteNode 40) 1=(reverse (relabel (matrix (root [114] [574] [2617] [5] [23] [1]) 0) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [114] [574] [2617] [5] [23] [1] 0 (by decide) (by decide)) perm6.symm)

theorem finiteEdge40_2 : SafeCore (mutate (finiteNode 40) 2) := by
  have he := mutation_equal (finiteP 40) (preverse (prelabel (generic finiteParam4_0 finiteParam4_1 finiteParam4_2 finiteParam4_3 2) perm16.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 40) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finiteRegion4_safe 2) perm16.symm)

theorem finiteEdge40_3 : SafeCore (mutate (finiteNode 40) 3) := by
  have he := mutation_equal (finiteP 40) (prelabel (finiteP 24) perm21.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 40) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 24) perm21.symm

theorem finiteEdge41_0 : SafeCore (mutate (finiteNode 41) 0) := by
  have he := mutation_equal (finiteP 41) (prelabel (fork [6] [5] [691] [29] [4030] [18]) perm5.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (finite_safe 41)
  rw [show mutate (finiteNode 41) 0=(relabel (matrix (fork [6] [5] [691] [29] [4030] [18]) 0) perm5.symm) from he]
  exact IsFork.relabelled (fork_sound [6] [5] [691] [29] [4030] [18] 0 (by decide) (by decide)) perm5.symm

theorem finiteEdge41_1 : SafeCore (mutate (finiteNode 41) 1) := by
  have he := mutation_equal (finiteP 41) (preverse (prelabel (root [691] [12443] [80150] [18] [116] [1]) perm6.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 41) 1
  rw [show mutate (finiteNode 41) 1=(reverse (relabel (matrix (root [691] [12443] [80150] [18] [116] [1]) 0) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [691] [12443] [80150] [18] [116] [1] 0 (by decide) (by decide)) perm6.symm)

theorem finiteEdge41_2 : SafeCore (mutate (finiteNode 41) 2) := by
  have he := mutation_equal (finiteP 41) (preverse (prelabel (generic finiteParam3_0 finiteParam3_1 finiteParam3_2 finiteParam3_3 2) perm16.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 41) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finiteRegion3_safe 2) perm16.symm)

theorem finiteEdge41_3 : SafeCore (mutate (finiteNode 41) 3) := by
  have he := mutation_equal (finiteP 41) (prelabel (finiteP 39) perm21.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 41) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 39) perm21.symm

theorem finiteEdge42_0 : SafeCore (mutate (finiteNode 42) 0) := by
  have he := mutation_equal (finiteP 42) (prelabel (fork [4] [37] [5] [138] [19] [4]) perm4.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (finite_safe 42)
  rw [show mutate (finiteNode 42) 0=(relabel (matrix (fork [4] [37] [5] [138] [19] [4]) 0) perm4.symm) from he]
  exact IsFork.relabelled (fork_sound [4] [37] [5] [138] [19] [4] 0 (by decide) (by decide)) perm4.symm

theorem finiteEdge42_1 : SafeCore (mutate (finiteNode 42) 1) := by
  have he := mutation_equal (finiteP 42) (preverse (prelabel (fork [10] [37] [4] [366] [41] [5]) perm10.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (finite_safe 42)
  rw [show mutate (finiteNode 42) 1=(reverse (relabel (matrix (fork [10] [37] [4] [366] [41] [5]) 0) perm10.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [10] [37] [4] [366] [41] [5] 0 (by decide) (by decide)) perm10.symm)

theorem finiteEdge42_2 : SafeCore (mutate (finiteNode 42) 2) := by
  have he := mutation_equal (finiteP 42) (prelabel (finiteP 27) perm1.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 42) 0) 2)
  rw [he]
  exact Safe.framed (finite_safe 27) perm1.symm

theorem finiteEdge42_3 : SafeCore (mutate (finiteNode 42) 3) := by
  have he := mutation_equal (finiteP 42) (preverse (prelabel (finiteP 25) perm11.symm)) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 42) 0) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 25) perm11.symm)

theorem finiteEdge43_0 : SafeCore (mutate (finiteNode 43) 0) := by
  have he := mutation_equal (finiteP 43) (preverse (prelabel (root [2] [5] [5] [3] [4] [1]) perm5.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 43) 0
  rw [show mutate (finiteNode 43) 0=(reverse (relabel (matrix (root [2] [5] [5] [3] [4] [1]) 0) perm5.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [2] [5] [5] [3] [4] [1] 0 (by decide) (by decide)) perm5.symm)

theorem finiteEdge43_1 : SafeCore (mutate (finiteNode 43) 1) := by
  have he := mutation_equal (finiteP 43) (preverse (prelabel (finiteP 53) perm19.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 43) 0) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 53) perm19.symm)

theorem finiteEdge43_2 : SafeCore (mutate (finiteNode 43) 2) := by
  have he := mutation_equal (finiteP 43) (prelabel (finiteP 29) perm1.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 43) 0) 2)
  rw [he]
  exact Safe.framed (finite_safe 29) perm1.symm

theorem finiteEdge43_3 : SafeCore (mutate (finiteNode 43) 3) := by
  have he := mutation_equal (finiteP 43) (preverse (prelabel (finiteP 26) perm11.symm)) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 43) 0) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 26) perm11.symm)

theorem finiteEdge44_0 : SafeCore (mutate (finiteNode 44) 0) := by
  have he := mutation_equal (finiteP 44) (prelabel (finiteP 45) perm21.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 44) 0) 0)
  rw [he]
  exact Safe.framed (finite_safe 45) perm21.symm

theorem finiteEdge44_1 : SafeCore (mutate (finiteNode 44) 1) := by
  have he := mutation_equal (finiteP 44) (preverse (prelabel (root [22] [89] [62] [4] [3] [1]) perm6.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 44) 1
  rw [show mutate (finiteNode 44) 1=(reverse (relabel (matrix (root [22] [89] [62] [4] [3] [1]) 0) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [22] [89] [62] [4] [3] [1] 0 (by decide) (by decide)) perm6.symm)

theorem finiteEdge44_2 : SafeCore (mutate (finiteNode 44) 2) := by
  have he := mutation_equal (finiteP 44) (preverse (prelabel (generic finiteParam5_0 finiteParam5_1 finiteParam5_2 finiteParam5_3 0) perm3.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 44) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finiteRegion5_safe 0) perm3.symm)

theorem finiteEdge44_3 : SafeCore (mutate (finiteNode 44) 3) := by
  have he := mutation_equal (finiteP 44) (prelabel (finiteP 53) perm1.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 44) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 53) perm1.symm

theorem finiteEdge45_0 : SafeCore (mutate (finiteNode 45) 0) := by
  have he := mutation_equal (finiteP 45) (prelabel (fork [4] [3] [85] [11] [318] [4]) perm5.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (finite_safe 45)
  rw [show mutate (finiteNode 45) 0=(relabel (matrix (fork [4] [3] [85] [11] [318] [4]) 0) perm5.symm) from he]
  exact IsFork.relabelled (fork_sound [4] [3] [85] [11] [318] [4] 0 (by decide) (by decide)) perm5.symm

theorem finiteEdge45_1 : SafeCore (mutate (finiteNode 45) 1) := by
  have he := mutation_equal (finiteP 45) (preverse (prelabel (root [85] [343] [1866] [4] [22] [1]) perm6.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 45) 1
  rw [show mutate (finiteNode 45) 1=(reverse (relabel (matrix (root [85] [343] [1866] [4] [22] [1]) 0) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [85] [343] [1866] [4] [22] [1] 0 (by decide) (by decide)) perm6.symm)

theorem finiteEdge45_2 : SafeCore (mutate (finiteNode 45) 2) := by
  have he := mutation_equal (finiteP 45) (preverse (prelabel (generic finiteParam5_0 finiteParam5_1 finiteParam5_2 finiteParam5_3 2) perm16.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 45) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finiteRegion5_safe 2) perm16.symm)

theorem finiteEdge45_3 : SafeCore (mutate (finiteNode 45) 3) := by
  have he := mutation_equal (finiteP 45) (prelabel (finiteP 44) perm21.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 45) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 44) perm21.symm

theorem finiteEdge46_0 : SafeCore (mutate (finiteNode 46) 0) := by
  have he := mutation_equal (finiteP 46) (preverse (prelabel (root [5] [24] [158] [5] [33] [1]) perm5.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 46) 0
  rw [show mutate (finiteNode 46) 0=(reverse (relabel (matrix (root [5] [24] [158] [5] [33] [1]) 0) perm5.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [5] [24] [158] [5] [33] [1] 0 (by decide) (by decide)) perm5.symm)

theorem finiteEdge46_1 : SafeCore (mutate (finiteNode 46) 1) := by
  have he := mutation_equal (finiteP 46) (preverse (prelabel (finiteP 54) perm19.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 46) 0) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 54) perm19.symm)

theorem finiteEdge46_2 : SafeCore (mutate (finiteNode 46) 2) := by
  have he := mutation_equal (finiteP 46) (prelabel (finiteP 48) perm4.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 46) 0) 2)
  rw [he]
  exact Safe.framed (finite_safe 48) perm4.symm

theorem finiteEdge46_3 : SafeCore (mutate (finiteNode 46) 3) := by
  have he := mutation_equal (finiteP 46) (prelabel (finiteP 31) perm3.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 46) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 31) perm3.symm

theorem finiteEdge47_0 : SafeCore (mutate (finiteNode 47) 0) := by
  have he := mutation_equal (finiteP 47) (preverse (prelabel (root [2] [3] [11] [2] [9] [1]) perm5.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 47) 0
  rw [show mutate (finiteNode 47) 0=(reverse (relabel (matrix (root [2] [3] [11] [2] [9] [1]) 0) perm5.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [2] [3] [11] [2] [9] [1] 0 (by decide) (by decide)) perm5.symm)

theorem finiteEdge47_1 : SafeCore (mutate (finiteNode 47) 1) := by
  have he := mutation_equal (finiteP 47) (preverse (prelabel (finiteP 55) perm19.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 47) 0) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 55) perm19.symm)

theorem finiteEdge47_2 : SafeCore (mutate (finiteNode 47) 2) := by
  have he := mutation_equal (finiteP 47) (prelabel (finiteP 49) perm4.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 47) 0) 2)
  rw [he]
  exact Safe.framed (finite_safe 49) perm4.symm

theorem finiteEdge47_3 : SafeCore (mutate (finiteNode 47) 3) := by
  have he := mutation_equal (finiteP 47) (preverse (prelabel (finiteP 31) perm2.symm)) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 47) 0) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 31) perm2.symm)

theorem finiteEdge48_0 : SafeCore (mutate (finiteNode 48) 0) := by
  have he := mutation_equal (finiteP 48) (prelabel (zero finiteParam6_0 finiteParam6_1 finiteParam6_2 finiteParam6_3 1) perm6.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 48) 0) 0)
  rw [he]
  exact Safe.framed (finiteRegion6_safe 1) perm6.symm

theorem finiteEdge48_1 : SafeCore (mutate (finiteNode 48) 1) := by
  have he := mutation_equal (finiteP 48) (prelabel (finiteP 32) perm0.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 48) 0) 1)
  rw [he]
  exact Safe.framed (finite_safe 32) perm0.symm

theorem finiteEdge48_2 : SafeCore (mutate (finiteNode 48) 2) := by
  have he := mutation_equal (finiteP 48) (prelabel (generic finiteParam10_0 finiteParam10_1 finiteParam10_2 finiteParam10_3 0) perm11.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 48) 0) 2)
  rw [he]
  exact Safe.framed (finiteRegion10_safe 0) perm11.symm

theorem finiteEdge48_3 : SafeCore (mutate (finiteNode 48) 3) := by
  have he := mutation_equal (finiteP 48) (prelabel (finiteP 46) perm3.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 48) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 46) perm3.symm

theorem finiteEdge49_0 : SafeCore (mutate (finiteNode 49) 0) := by
  have he := mutation_equal (finiteP 49) (prelabel (zero finiteParam7_0 finiteParam7_1 finiteParam7_2 finiteParam7_3 1) perm6.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 49) 0) 0)
  rw [he]
  exact Safe.framed (finiteRegion7_safe 1) perm6.symm

theorem finiteEdge49_1 : SafeCore (mutate (finiteNode 49) 1) := by
  have he := mutation_equal (finiteP 49) (prelabel (finiteP 33) perm0.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 49) 0) 1)
  rw [he]
  exact Safe.framed (finite_safe 33) perm0.symm

theorem finiteEdge49_2 : SafeCore (mutate (finiteNode 49) 2) := by
  have he := mutation_equal (finiteP 49) (prelabel (generic finiteParam11_0 finiteParam11_1 finiteParam11_2 finiteParam11_3 0) perm11.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 49) 0) 2)
  rw [he]
  exact Safe.framed (finiteRegion11_safe 0) perm11.symm

theorem finiteEdge49_3 : SafeCore (mutate (finiteNode 49) 3) := by
  have he := mutation_equal (finiteP 49) (prelabel (finiteP 47) perm3.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 49) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 47) perm3.symm

theorem finiteEdge50_0 : SafeCore (mutate (finiteNode 50) 0) := by
  have he := mutation_equal (finiteP 50) (prelabel (finiteP 51) perm21.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 50) 0) 0)
  rw [he]
  exact Safe.framed (finite_safe 51) perm21.symm

theorem finiteEdge50_1 : SafeCore (mutate (finiteNode 50) 1) := by
  have he := mutation_equal (finiteP 50) (preverse (prelabel (root [26] [209] [127] [8] [5] [1]) perm6.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 50) 1
  rw [show mutate (finiteNode 50) 1=(reverse (relabel (matrix (root [26] [209] [127] [8] [5] [1]) 0) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [26] [209] [127] [8] [5] [1] 0 (by decide) (by decide)) perm6.symm)

theorem finiteEdge50_2 : SafeCore (mutate (finiteNode 50) 2) := by
  have he := mutation_equal (finiteP 50) (preverse (prelabel (generic finiteParam9_0 finiteParam9_1 finiteParam9_2 finiteParam9_3 0) perm3.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 50) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finiteRegion9_safe 0) perm3.symm)

theorem finiteEdge50_3 : SafeCore (mutate (finiteNode 50) 3) := by
  have he := mutation_equal (finiteP 50) (preverse (prelabel (finiteP 35) perm7.symm)) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 50) 0) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 35) perm7.symm)

theorem finiteEdge51_0 : SafeCore (mutate (finiteNode 51) 0) := by
  have he := mutation_equal (finiteP 51) (prelabel (fork [3] [2] [73] [5] [193] [8]) perm5.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (finite_safe 51)
  rw [show mutate (finiteNode 51) 0=(relabel (matrix (fork [3] [2] [73] [5] [193] [8]) 0) perm5.symm) from he]
  exact IsFork.relabelled (fork_sound [3] [2] [73] [5] [193] [8] 0 (by decide) (by decide)) perm5.symm

theorem finiteEdge51_1 : SafeCore (mutate (finiteNode 51) 1) := by
  have he := mutation_equal (finiteP 51) (preverse (prelabel (root [73] [586] [1895] [8] [26] [1]) perm6.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 51) 1
  rw [show mutate (finiteNode 51) 1=(reverse (relabel (matrix (root [73] [586] [1895] [8] [26] [1]) 0) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [73] [586] [1895] [8] [26] [1] 0 (by decide) (by decide)) perm6.symm)

theorem finiteEdge51_2 : SafeCore (mutate (finiteNode 51) 2) := by
  have he := mutation_equal (finiteP 51) (preverse (prelabel (generic finiteParam9_0 finiteParam9_1 finiteParam9_2 finiteParam9_3 2) perm16.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 51) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finiteRegion9_safe 2) perm16.symm)

theorem finiteEdge51_3 : SafeCore (mutate (finiteNode 51) 3) := by
  have he := mutation_equal (finiteP 51) (prelabel (finiteP 50) perm21.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 51) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 50) perm21.symm

theorem finiteEdge52_0 : SafeCore (mutate (finiteNode 52) 0) := by
  have he := mutation_equal (finiteP 52) (preverse (prelabel (finiteP 52) perm1.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 52) 0) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 52) perm1.symm)

theorem finiteEdge52_1 : SafeCore (mutate (finiteNode 52) 1) := by
  have he := mutation_equal (finiteP 52) (preverse (prelabel (finiteP 37) perm16.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 52) 0) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 37) perm16.symm)

theorem finiteEdge52_2 : SafeCore (mutate (finiteNode 52) 2) := by
  have he := mutation_equal (finiteP 52) (preverse (prelabel (finiteP 37) perm20.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 52) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 37) perm20.symm)

theorem finiteEdge52_3 : SafeCore (mutate (finiteNode 52) 3) := by
  have he := mutation_equal (finiteP 52) (preverse (prelabel (finiteP 37) perm8.symm)) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 52) 0) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 37) perm8.symm)

theorem finiteEdge53_0 : SafeCore (mutate (finiteNode 53) 0) := by
  have he := mutation_equal (finiteP 53) (prelabel (fork [3] [10] [4] [26] [11] [3]) perm4.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (finite_safe 53)
  rw [show mutate (finiteNode 53) 0=(relabel (matrix (fork [3] [10] [4] [26] [11] [3]) 0) perm4.symm) from he]
  exact IsFork.relabelled (fork_sound [3] [10] [4] [26] [11] [3] 0 (by decide) (by decide)) perm4.symm

theorem finiteEdge53_1 : SafeCore (mutate (finiteNode 53) 1) := by
  have he := mutation_equal (finiteP 53) (preverse (prelabel (fork [4] [10] [3] [37] [13] [4]) perm10.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (finite_safe 53)
  rw [show mutate (finiteNode 53) 1=(reverse (relabel (matrix (fork [4] [10] [3] [37] [13] [4]) 0) perm10.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [4] [10] [3] [37] [13] [4] 0 (by decide) (by decide)) perm10.symm)

theorem finiteEdge53_2 : SafeCore (mutate (finiteNode 53) 2) := by
  have he := mutation_equal (finiteP 53) (prelabel (finiteP 44) perm1.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 53) 0) 2)
  rw [he]
  exact Safe.framed (finite_safe 44) perm1.symm

theorem finiteEdge53_3 : SafeCore (mutate (finiteNode 53) 3) := by
  have he := mutation_equal (finiteP 53) (preverse (prelabel (finiteP 43) perm11.symm)) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 53) 0) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 43) perm11.symm)

theorem finiteEdge54_0 : SafeCore (mutate (finiteNode 54) 0) := by
  have he := mutation_equal (finiteP 54) (prelabel (fork [7] [226] [8] [1549] [55] [5]) perm4.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (finite_safe 54)
  rw [show mutate (finiteNode 54) 0=(relabel (matrix (fork [7] [226] [8] [1549] [55] [5]) 0) perm4.symm) from he]
  exact IsFork.relabelled (fork_sound [7] [226] [8] [1549] [55] [5] 0 (by decide) (by decide)) perm4.symm

theorem finiteEdge54_1 : SafeCore (mutate (finiteNode 54) 1) := by
  have he := mutation_equal (finiteP 54) (preverse (prelabel (fork [33] [226] [5] [7451] [166] [8]) perm10.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (finite_safe 54)
  rw [show mutate (finiteNode 54) 1=(reverse (relabel (matrix (fork [33] [226] [5] [7451] [166] [8]) 0) perm10.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [33] [226] [5] [7451] [166] [8] 0 (by decide) (by decide)) perm10.symm)

theorem finiteEdge54_2 : SafeCore (mutate (finiteNode 54) 2) := by
  have he := mutation_equal (finiteP 54) (prelabel (finiteP 56) perm1.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 54) 0) 2)
  rw [he]
  exact Safe.framed (finite_safe 56) perm1.symm

theorem finiteEdge54_3 : SafeCore (mutate (finiteNode 54) 3) := by
  have he := mutation_equal (finiteP 54) (preverse (prelabel (finiteP 46) perm11.symm)) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 54) 0) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 46) perm11.symm)

theorem finiteEdge55_0 : SafeCore (mutate (finiteNode 55) 0) := by
  have he := mutation_equal (finiteP 55) (prelabel (fork [7] [61] [8] [418] [55] [2]) perm4.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (finite_safe 55)
  rw [show mutate (finiteNode 55) 0=(relabel (matrix (fork [7] [61] [8] [418] [55] [2]) 0) perm4.symm) from he]
  exact IsFork.relabelled (fork_sound [7] [61] [8] [418] [55] [2] 0 (by decide) (by decide)) perm4.symm

theorem finiteEdge55_1 : SafeCore (mutate (finiteNode 55) 1) := by
  have he := mutation_equal (finiteP 55) (preverse (prelabel (fork [9] [61] [2] [542] [19] [8]) perm10.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (finite_safe 55)
  rw [show mutate (finiteNode 55) 1=(reverse (relabel (matrix (fork [9] [61] [2] [542] [19] [8]) 0) perm10.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [9] [61] [2] [542] [19] [8] 0 (by decide) (by decide)) perm10.symm)

theorem finiteEdge55_2 : SafeCore (mutate (finiteNode 55) 2) := by
  have he := mutation_equal (finiteP 55) (prelabel (finiteP 58) perm1.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 55) 0) 2)
  rw [he]
  exact Safe.framed (finite_safe 58) perm1.symm

theorem finiteEdge55_3 : SafeCore (mutate (finiteNode 55) 3) := by
  have he := mutation_equal (finiteP 55) (preverse (prelabel (finiteP 47) perm11.symm)) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 55) 0) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 47) perm11.symm)

theorem finiteEdge56_0 : SafeCore (mutate (finiteNode 56) 0) := by
  have he := mutation_equal (finiteP 56) (prelabel (finiteP 57) perm21.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 56) 0) 0)
  rw [he]
  exact Safe.framed (finite_safe 57) perm21.symm

theorem finiteEdge56_1 : SafeCore (mutate (finiteNode 56) 1) := by
  have he := mutation_equal (finiteP 56) (preverse (prelabel (root [266] [8779] [1322] [33] [5] [1]) perm6.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 56) 1
  rw [show mutate (finiteNode 56) 1=(reverse (relabel (matrix (root [266] [8779] [1322] [33] [5] [1]) 0) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [266] [8779] [1322] [33] [5] [1] 0 (by decide) (by decide)) perm6.symm)

theorem finiteEdge56_2 : SafeCore (mutate (finiteNode 56) 2) := by
  have he := mutation_equal (finiteP 56) (preverse (prelabel (generic finiteParam10_0 finiteParam10_1 finiteParam10_2 finiteParam10_3 0) perm3.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 56) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finiteRegion10_safe 0) perm3.symm)

theorem finiteEdge56_3 : SafeCore (mutate (finiteNode 56) 3) := by
  have he := mutation_equal (finiteP 56) (prelabel (finiteP 54) perm1.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 56) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 54) perm1.symm

theorem finiteEdge57_0 : SafeCore (mutate (finiteNode 57) 0) := by
  have he := mutation_equal (finiteP 57) (prelabel (fork [8] [7] [2123] [55] [16718] [33]) perm5.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (finite_safe 57)
  rw [show mutate (finiteNode 57) 0=(relabel (matrix (fork [8] [7] [2123] [55] [16718] [33]) 0) perm5.symm) from he]
  exact IsFork.relabelled (fork_sound [8] [7] [2123] [55] [16718] [33] 0 (by decide) (by decide)) perm5.symm

theorem finiteEdge57_1 : SafeCore (mutate (finiteNode 57) 1) := by
  have he := mutation_equal (finiteP 57) (preverse (prelabel (root [2123] [70066] [564710] [33] [266] [1]) perm6.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 57) 1
  rw [show mutate (finiteNode 57) 1=(reverse (relabel (matrix (root [2123] [70066] [564710] [33] [266] [1]) 0) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [2123] [70066] [564710] [33] [266] [1] 0 (by decide) (by decide)) perm6.symm)

theorem finiteEdge57_2 : SafeCore (mutate (finiteNode 57) 2) := by
  have he := mutation_equal (finiteP 57) (preverse (prelabel (generic finiteParam10_0 finiteParam10_1 finiteParam10_2 finiteParam10_3 2) perm16.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 57) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finiteRegion10_safe 2) perm16.symm)

theorem finiteEdge57_3 : SafeCore (mutate (finiteNode 57) 3) := by
  have he := mutation_equal (finiteP 57) (prelabel (finiteP 56) perm21.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 57) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 56) perm21.symm

theorem finiteEdge58_0 : SafeCore (mutate (finiteNode 58) 0) := by
  have he := mutation_equal (finiteP 58) (prelabel (finiteP 59) perm21.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 58) 0) 0)
  rw [he]
  exact Safe.framed (finite_safe 59) perm21.symm

theorem finiteEdge58_1 : SafeCore (mutate (finiteNode 58) 1) := by
  have he := mutation_equal (finiteP 58) (preverse (prelabel (root [77] [694] [146] [9] [2] [1]) perm6.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 58) 1
  rw [show mutate (finiteNode 58) 1=(reverse (relabel (matrix (root [77] [694] [146] [9] [2] [1]) 0) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [77] [694] [146] [9] [2] [1] 0 (by decide) (by decide)) perm6.symm)

theorem finiteEdge58_2 : SafeCore (mutate (finiteNode 58) 2) := by
  have he := mutation_equal (finiteP 58) (preverse (prelabel (generic finiteParam11_0 finiteParam11_1 finiteParam11_2 finiteParam11_3 0) perm3.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 58) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finiteRegion11_safe 0) perm3.symm)

theorem finiteEdge58_3 : SafeCore (mutate (finiteNode 58) 3) := by
  have he := mutation_equal (finiteP 58) (prelabel (finiteP 55) perm1.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 58) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 55) perm1.symm

theorem finiteEdge59_0 : SafeCore (mutate (finiteNode 59) 0) := by
  have he := mutation_equal (finiteP 59) (prelabel (fork [8] [7] [614] [55] [4835] [9]) perm5.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (finite_safe 59)
  rw [show mutate (finiteNode 59) 0=(relabel (matrix (fork [8] [7] [614] [55] [4835] [9]) 0) perm5.symm) from he]
  exact IsFork.relabelled (fork_sound [8] [7] [614] [55] [4835] [9] 0 (by decide) (by decide)) perm5.symm

theorem finiteEdge59_1 : SafeCore (mutate (finiteNode 59) 1) := by
  have he := mutation_equal (finiteP 59) (preverse (prelabel (root [614] [5533] [47270] [9] [77] [1]) perm6.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 59) 1
  rw [show mutate (finiteNode 59) 1=(reverse (relabel (matrix (root [614] [5533] [47270] [9] [77] [1]) 0) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [614] [5533] [47270] [9] [77] [1] 0 (by decide) (by decide)) perm6.symm)

theorem finiteEdge59_2 : SafeCore (mutate (finiteNode 59) 2) := by
  have he := mutation_equal (finiteP 59) (preverse (prelabel (generic finiteParam11_0 finiteParam11_1 finiteParam11_2 finiteParam11_3 2) perm16.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 59) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finiteRegion11_safe 2) perm16.symm)

theorem finiteEdge59_3 : SafeCore (mutate (finiteNode 59) 3) := by
  have he := mutation_equal (finiteP 59) (prelabel (finiteP 58) perm21.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 59) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 58) perm21.symm

theorem finite_cyclic (i : Fin 60) : ¬ Acyclic (finiteNode i) := by
  rcases finiteFin i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact finiteCyclic0
  · exact finiteCyclic1
  · exact finiteCyclic2
  · exact finiteCyclic3
  · exact finiteCyclic4
  · exact finiteCyclic5
  · exact finiteCyclic6
  · exact finiteCyclic7
  · exact finiteCyclic8
  · exact finiteCyclic9
  · exact finiteCyclic10
  · exact finiteCyclic11
  · exact finiteCyclic12
  · exact finiteCyclic13
  · exact finiteCyclic14
  · exact finiteCyclic15
  · exact finiteCyclic16
  · exact finiteCyclic17
  · exact finiteCyclic18
  · exact finiteCyclic19
  · exact finiteCyclic20
  · exact finiteCyclic21
  · exact finiteCyclic22
  · exact finiteCyclic23
  · exact finiteCyclic24
  · exact finiteCyclic25
  · exact finiteCyclic26
  · exact finiteCyclic27
  · exact finiteCyclic28
  · exact finiteCyclic29
  · exact finiteCyclic30
  · exact finiteCyclic31
  · exact finiteCyclic32
  · exact finiteCyclic33
  · exact finiteCyclic34
  · exact finiteCyclic35
  · exact finiteCyclic36
  · exact finiteCyclic37
  · exact finiteCyclic38
  · exact finiteCyclic39
  · exact finiteCyclic40
  · exact finiteCyclic41
  · exact finiteCyclic42
  · exact finiteCyclic43
  · exact finiteCyclic44
  · exact finiteCyclic45
  · exact finiteCyclic46
  · exact finiteCyclic47
  · exact finiteCyclic48
  · exact finiteCyclic49
  · exact finiteCyclic50
  · exact finiteCyclic51
  · exact finiteCyclic52
  · exact finiteCyclic53
  · exact finiteCyclic54
  · exact finiteCyclic55
  · exact finiteCyclic56
  · exact finiteCyclic57
  · exact finiteCyclic58
  · exact finiteCyclic59
theorem finite_edges (i : Fin 60) (k : Fin 4) : SafeCore (mutate (finiteNode i) k) := by
  have hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
  rcases finiteFin i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rcases hk with rfl|rfl|rfl|rfl
  · exact finiteEdge0_0
  · exact finiteEdge0_1
  · exact finiteEdge0_2
  · exact finiteEdge0_3
  · exact finiteEdge1_0
  · exact finiteEdge1_1
  · exact finiteEdge1_2
  · exact finiteEdge1_3
  · exact finiteEdge2_0
  · exact finiteEdge2_1
  · exact finiteEdge2_2
  · exact finiteEdge2_3
  · exact finiteEdge3_0
  · exact finiteEdge3_1
  · exact finiteEdge3_2
  · exact finiteEdge3_3
  · exact finiteEdge4_0
  · exact finiteEdge4_1
  · exact finiteEdge4_2
  · exact finiteEdge4_3
  · exact finiteEdge5_0
  · exact finiteEdge5_1
  · exact finiteEdge5_2
  · exact finiteEdge5_3
  · exact finiteEdge6_0
  · exact finiteEdge6_1
  · exact finiteEdge6_2
  · exact finiteEdge6_3
  · exact finiteEdge7_0
  · exact finiteEdge7_1
  · exact finiteEdge7_2
  · exact finiteEdge7_3
  · exact finiteEdge8_0
  · exact finiteEdge8_1
  · exact finiteEdge8_2
  · exact finiteEdge8_3
  · exact finiteEdge9_0
  · exact finiteEdge9_1
  · exact finiteEdge9_2
  · exact finiteEdge9_3
  · exact finiteEdge10_0
  · exact finiteEdge10_1
  · exact finiteEdge10_2
  · exact finiteEdge10_3
  · exact finiteEdge11_0
  · exact finiteEdge11_1
  · exact finiteEdge11_2
  · exact finiteEdge11_3
  · exact finiteEdge12_0
  · exact finiteEdge12_1
  · exact finiteEdge12_2
  · exact finiteEdge12_3
  · exact finiteEdge13_0
  · exact finiteEdge13_1
  · exact finiteEdge13_2
  · exact finiteEdge13_3
  · exact finiteEdge14_0
  · exact finiteEdge14_1
  · exact finiteEdge14_2
  · exact finiteEdge14_3
  · exact finiteEdge15_0
  · exact finiteEdge15_1
  · exact finiteEdge15_2
  · exact finiteEdge15_3
  · exact finiteEdge16_0
  · exact finiteEdge16_1
  · exact finiteEdge16_2
  · exact finiteEdge16_3
  · exact finiteEdge17_0
  · exact finiteEdge17_1
  · exact finiteEdge17_2
  · exact finiteEdge17_3
  · exact finiteEdge18_0
  · exact finiteEdge18_1
  · exact finiteEdge18_2
  · exact finiteEdge18_3
  · exact finiteEdge19_0
  · exact finiteEdge19_1
  · exact finiteEdge19_2
  · exact finiteEdge19_3
  · exact finiteEdge20_0
  · exact finiteEdge20_1
  · exact finiteEdge20_2
  · exact finiteEdge20_3
  · exact finiteEdge21_0
  · exact finiteEdge21_1
  · exact finiteEdge21_2
  · exact finiteEdge21_3
  · exact finiteEdge22_0
  · exact finiteEdge22_1
  · exact finiteEdge22_2
  · exact finiteEdge22_3
  · exact finiteEdge23_0
  · exact finiteEdge23_1
  · exact finiteEdge23_2
  · exact finiteEdge23_3
  · exact finiteEdge24_0
  · exact finiteEdge24_1
  · exact finiteEdge24_2
  · exact finiteEdge24_3
  · exact finiteEdge25_0
  · exact finiteEdge25_1
  · exact finiteEdge25_2
  · exact finiteEdge25_3
  · exact finiteEdge26_0
  · exact finiteEdge26_1
  · exact finiteEdge26_2
  · exact finiteEdge26_3
  · exact finiteEdge27_0
  · exact finiteEdge27_1
  · exact finiteEdge27_2
  · exact finiteEdge27_3
  · exact finiteEdge28_0
  · exact finiteEdge28_1
  · exact finiteEdge28_2
  · exact finiteEdge28_3
  · exact finiteEdge29_0
  · exact finiteEdge29_1
  · exact finiteEdge29_2
  · exact finiteEdge29_3
  · exact finiteEdge30_0
  · exact finiteEdge30_1
  · exact finiteEdge30_2
  · exact finiteEdge30_3
  · exact finiteEdge31_0
  · exact finiteEdge31_1
  · exact finiteEdge31_2
  · exact finiteEdge31_3
  · exact finiteEdge32_0
  · exact finiteEdge32_1
  · exact finiteEdge32_2
  · exact finiteEdge32_3
  · exact finiteEdge33_0
  · exact finiteEdge33_1
  · exact finiteEdge33_2
  · exact finiteEdge33_3
  · exact finiteEdge34_0
  · exact finiteEdge34_1
  · exact finiteEdge34_2
  · exact finiteEdge34_3
  · exact finiteEdge35_0
  · exact finiteEdge35_1
  · exact finiteEdge35_2
  · exact finiteEdge35_3
  · exact finiteEdge36_0
  · exact finiteEdge36_1
  · exact finiteEdge36_2
  · exact finiteEdge36_3
  · exact finiteEdge37_0
  · exact finiteEdge37_1
  · exact finiteEdge37_2
  · exact finiteEdge37_3
  · exact finiteEdge38_0
  · exact finiteEdge38_1
  · exact finiteEdge38_2
  · exact finiteEdge38_3
  · exact finiteEdge39_0
  · exact finiteEdge39_1
  · exact finiteEdge39_2
  · exact finiteEdge39_3
  · exact finiteEdge40_0
  · exact finiteEdge40_1
  · exact finiteEdge40_2
  · exact finiteEdge40_3
  · exact finiteEdge41_0
  · exact finiteEdge41_1
  · exact finiteEdge41_2
  · exact finiteEdge41_3
  · exact finiteEdge42_0
  · exact finiteEdge42_1
  · exact finiteEdge42_2
  · exact finiteEdge42_3
  · exact finiteEdge43_0
  · exact finiteEdge43_1
  · exact finiteEdge43_2
  · exact finiteEdge43_3
  · exact finiteEdge44_0
  · exact finiteEdge44_1
  · exact finiteEdge44_2
  · exact finiteEdge44_3
  · exact finiteEdge45_0
  · exact finiteEdge45_1
  · exact finiteEdge45_2
  · exact finiteEdge45_3
  · exact finiteEdge46_0
  · exact finiteEdge46_1
  · exact finiteEdge46_2
  · exact finiteEdge46_3
  · exact finiteEdge47_0
  · exact finiteEdge47_1
  · exact finiteEdge47_2
  · exact finiteEdge47_3
  · exact finiteEdge48_0
  · exact finiteEdge48_1
  · exact finiteEdge48_2
  · exact finiteEdge48_3
  · exact finiteEdge49_0
  · exact finiteEdge49_1
  · exact finiteEdge49_2
  · exact finiteEdge49_3
  · exact finiteEdge50_0
  · exact finiteEdge50_1
  · exact finiteEdge50_2
  · exact finiteEdge50_3
  · exact finiteEdge51_0
  · exact finiteEdge51_1
  · exact finiteEdge51_2
  · exact finiteEdge51_3
  · exact finiteEdge52_0
  · exact finiteEdge52_1
  · exact finiteEdge52_2
  · exact finiteEdge52_3
  · exact finiteEdge53_0
  · exact finiteEdge53_1
  · exact finiteEdge53_2
  · exact finiteEdge53_3
  · exact finiteEdge54_0
  · exact finiteEdge54_1
  · exact finiteEdge54_2
  · exact finiteEdge54_3
  · exact finiteEdge55_0
  · exact finiteEdge55_1
  · exact finiteEdge55_2
  · exact finiteEdge55_3
  · exact finiteEdge56_0
  · exact finiteEdge56_1
  · exact finiteEdge56_2
  · exact finiteEdge56_3
  · exact finiteEdge57_0
  · exact finiteEdge57_1
  · exact finiteEdge57_2
  · exact finiteEdge57_3
  · exact finiteEdge58_0
  · exact finiteEdge58_1
  · exact finiteEdge58_2
  · exact finiteEdge58_3
  · exact finiteEdge59_0
  · exact finiteEdge59_1
  · exact finiteEdge59_2
  · exact finiteEdge59_3
def polyParam0_0 : P := [4,1]
def polyParam0_1 : P := [23,10,1]
def polyParam0_2 : P := [5,1]
def polyParam0_3 : P := [6,1]
theorem polyDomain0 (t : Int) (ht : 0≤t) : GenericStrip.Domain (eval polyParam0_0 t) (eval polyParam0_1 t) (eval polyParam0_2 t) (eval polyParam0_3 t) :=
  generic_domain polyParam0_0 polyParam0_1 polyParam0_2 polyParam0_3 t ht (by decide)
def polyRegion0 (t : Int) (ht : 0≤t) : Region := .inl (.inl ⟨eval polyParam0_0 t,⟨eval polyParam0_1 t,eval polyParam0_2 t,eval polyParam0_3 t⟩,polyDomain0 t ht⟩)
theorem polyParent0_0 (t : Int) (ht : 0≤t) : data.parent (polyRegion0 t ht) (0 : Fin 3)=(reverse (relabel (matrix (polyP 5) t) perm4.symm)) := by
  have he := mutation_equal (generic polyParam0_0 polyParam0_1 polyParam0_2 polyParam0_3 0) (preverse (prelabel (polyP 5) perm4.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem polyParent0_1 (t : Int) (ht : 0≤t) : data.parent (polyRegion0 t ht) (1 : Fin 3)=(relabel (matrix (tailP [6,1] 3) t) perm22.symm) := by
  have he := mutation_equal (generic polyParam0_0 polyParam0_1 polyParam0_2 polyParam0_3 0) (prelabel (tailP [6,1] 3) perm22.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem polyParent0_2 (t : Int) (ht : 0≤t) : data.parent (polyRegion0 t ht) (2 : Fin 3)=(reverse (relabel (matrix (polyP 6) t) perm16.symm)) := by
  have he := mutation_equal (generic polyParam0_0 polyParam0_1 polyParam0_2 polyParam0_3 2) (preverse (prelabel (polyP 6) perm16.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem polyParents0_safe (t : Int) (ht : 0≤t) (p : Fin 3) : SafeCore (data.parent (polyRegion0 t ht) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hp with rfl|rfl|rfl
  · rw [polyParent0_0 t ht]
    exact Safe.reversed (Safe.framed (poly_safe t ht 5) perm4.symm)
  · rw [polyParent0_1 t ht]
    exact Safe.framed (tailP_safe [6,1] 3 t ht (by decide)) perm22.symm
  · rw [polyParent0_2 t ht]
    exact Safe.reversed (Safe.framed (poly_safe t ht 6) perm16.symm)
theorem polyRegion0_safe (t : Int) (ht : 0≤t) (i : Fin 3) : SafeCore (matrix (generic polyParam0_0 polyParam0_1 polyParam0_2 polyParam0_3 i) t) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core) (polyRegion0 t ht) (polyParents0_safe t ht) (0,Fin.castLE (by decide) i)

def polyParam1_0 : P := [5,1]
def polyParam1_1 : P := [116,73,15,1]
def polyParam1_2 : P := [18,9,1]
def polyParam1_3 : P := [23,10,1]
theorem polyDomain1 (t : Int) (ht : 0≤t) : GenericStrip.Domain (eval polyParam1_0 t) (eval polyParam1_1 t) (eval polyParam1_2 t) (eval polyParam1_3 t) :=
  generic_domain polyParam1_0 polyParam1_1 polyParam1_2 polyParam1_3 t ht (by decide)
def polyRegion1 (t : Int) (ht : 0≤t) : Region := .inl (.inl ⟨eval polyParam1_0 t,⟨eval polyParam1_1 t,eval polyParam1_2 t,eval polyParam1_3 t⟩,polyDomain1 t ht⟩)
theorem polyParent1_0 (t : Int) (ht : 0≤t) : data.parent (polyRegion1 t ht) (0 : Fin 3)=(reverse (relabel (matrix (polyP 9) t) perm4.symm)) := by
  have he := mutation_equal (generic polyParam1_0 polyParam1_1 polyParam1_2 polyParam1_3 0) (preverse (prelabel (polyP 9) perm4.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem polyParent1_1 (t : Int) (ht : 0≤t) : data.parent (polyRegion1 t ht) (1 : Fin 3)=(relabel (matrix (polyP 5) t) perm22.symm) := by
  have he := mutation_equal (generic polyParam1_0 polyParam1_1 polyParam1_2 polyParam1_3 0) (prelabel (polyP 5) perm22.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem polyParent1_2 (t : Int) (ht : 0≤t) : data.parent (polyRegion1 t ht) (2 : Fin 3)=(reverse (relabel (matrix (polyP 10) t) perm16.symm)) := by
  have he := mutation_equal (generic polyParam1_0 polyParam1_1 polyParam1_2 polyParam1_3 2) (preverse (prelabel (polyP 10) perm16.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem polyParents1_safe (t : Int) (ht : 0≤t) (p : Fin 3) : SafeCore (data.parent (polyRegion1 t ht) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hp with rfl|rfl|rfl
  · rw [polyParent1_0 t ht]
    exact Safe.reversed (Safe.framed (poly_safe t ht 9) perm4.symm)
  · rw [polyParent1_1 t ht]
    exact Safe.framed (poly_safe t ht 5) perm22.symm
  · rw [polyParent1_2 t ht]
    exact Safe.reversed (Safe.framed (poly_safe t ht 10) perm16.symm)
theorem polyRegion1_safe (t : Int) (ht : 0≤t) (i : Fin 3) : SafeCore (matrix (generic polyParam1_0 polyParam1_1 polyParam1_2 polyParam1_3 i) t) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core) (polyRegion1 t ht) (polyParents1_safe t ht) (0,Fin.castLE (by decide) i)

def polyParam2_0 : P := [6,1]
def polyParam2_1 : P := [205,106,18,1]
def polyParam2_2 : P := [28,11,1]
def polyParam2_3 : P := [34,12,1]
theorem polyDomain2 (t : Int) (ht : 0≤t) : GenericStrip.Domain (eval polyParam2_0 t) (eval polyParam2_1 t) (eval polyParam2_2 t) (eval polyParam2_3 t) :=
  generic_domain polyParam2_0 polyParam2_1 polyParam2_2 polyParam2_3 t ht (by decide)
def polyRegion2 (t : Int) (ht : 0≤t) : Region := .inl (.inl ⟨eval polyParam2_0 t,⟨eval polyParam2_1 t,eval polyParam2_2 t,eval polyParam2_3 t⟩,polyDomain2 t ht⟩)
theorem polyParent2_0 (t : Int) (ht : 0≤t) : data.parent (polyRegion2 t ht) (0 : Fin 3)=(reverse (relabel (matrix (polyP 12) t) perm4.symm)) := by
  have he := mutation_equal (generic polyParam2_0 polyParam2_1 polyParam2_2 polyParam2_3 0) (preverse (prelabel (polyP 12) perm4.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem polyParent2_1 (t : Int) (ht : 0≤t) : data.parent (polyRegion2 t ht) (1 : Fin 3)=(relabel (matrix (polyP 8) t) perm22.symm) := by
  have he := mutation_equal (generic polyParam2_0 polyParam2_1 polyParam2_2 polyParam2_3 0) (prelabel (polyP 8) perm22.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem polyParent2_2 (t : Int) (ht : 0≤t) : data.parent (polyRegion2 t ht) (2 : Fin 3)=(reverse (relabel (matrix (polyP 14) t) perm16.symm)) := by
  have he := mutation_equal (generic polyParam2_0 polyParam2_1 polyParam2_2 polyParam2_3 2) (preverse (prelabel (polyP 14) perm16.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem polyParents2_safe (t : Int) (ht : 0≤t) (p : Fin 3) : SafeCore (data.parent (polyRegion2 t ht) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hp with rfl|rfl|rfl
  · rw [polyParent2_0 t ht]
    exact Safe.reversed (Safe.framed (poly_safe t ht 12) perm4.symm)
  · rw [polyParent2_1 t ht]
    exact Safe.framed (poly_safe t ht 8) perm22.symm
  · rw [polyParent2_2 t ht]
    exact Safe.reversed (Safe.framed (poly_safe t ht 14) perm16.symm)
theorem polyRegion2_safe (t : Int) (ht : 0≤t) (i : Fin 3) : SafeCore (matrix (generic polyParam2_0 polyParam2_1 polyParam2_2 polyParam2_3 i) t) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core) (polyRegion2 t ht) (polyParents2_safe t ht) (0,Fin.castLE (by decide) i)

def polyParam3_0 : P := [5,1]
def polyParam3_1 : P := [34,12,1]
def polyParam3_2 : P := [6,1]
def polyParam3_3 : P := [7,1]
theorem polyDomain3 (t : Int) (ht : 0≤t) : GenericStrip.Domain (eval polyParam3_0 t) (eval polyParam3_1 t) (eval polyParam3_2 t) (eval polyParam3_3 t) :=
  generic_domain polyParam3_0 polyParam3_1 polyParam3_2 polyParam3_3 t ht (by decide)
def polyRegion3 (t : Int) (ht : 0≤t) : Region := .inl (.inl ⟨eval polyParam3_0 t,⟨eval polyParam3_1 t,eval polyParam3_2 t,eval polyParam3_3 t⟩,polyDomain3 t ht⟩)
theorem polyParent3_0 (t : Int) (ht : 0≤t) : data.parent (polyRegion3 t ht) (0 : Fin 3)=(reverse (relabel (matrix (polyP 8) t) perm4.symm)) := by
  have he := mutation_equal (generic polyParam3_0 polyParam3_1 polyParam3_2 polyParam3_3 0) (preverse (prelabel (polyP 8) perm4.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem polyParent3_1 (t : Int) (ht : 0≤t) : data.parent (polyRegion3 t ht) (1 : Fin 3)=(relabel (matrix (tailP [7,1] 3) t) perm22.symm) := by
  have he := mutation_equal (generic polyParam3_0 polyParam3_1 polyParam3_2 polyParam3_3 0) (prelabel (tailP [7,1] 3) perm22.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem polyParent3_2 (t : Int) (ht : 0≤t) : data.parent (polyRegion3 t ht) (2 : Fin 3)=(reverse (relabel (matrix (polyP 13) t) perm16.symm)) := by
  have he := mutation_equal (generic polyParam3_0 polyParam3_1 polyParam3_2 polyParam3_3 2) (preverse (prelabel (polyP 13) perm16.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem polyParents3_safe (t : Int) (ht : 0≤t) (p : Fin 3) : SafeCore (data.parent (polyRegion3 t ht) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hp with rfl|rfl|rfl
  · rw [polyParent3_0 t ht]
    exact Safe.reversed (Safe.framed (poly_safe t ht 8) perm4.symm)
  · rw [polyParent3_1 t ht]
    exact Safe.framed (tailP_safe [7,1] 3 t ht (by decide)) perm22.symm
  · rw [polyParent3_2 t ht]
    exact Safe.reversed (Safe.framed (poly_safe t ht 13) perm16.symm)
theorem polyRegion3_safe (t : Int) (ht : 0≤t) (i : Fin 3) : SafeCore (matrix (generic polyParam3_0 polyParam3_1 polyParam3_2 polyParam3_3 i) t) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core) (polyRegion3 t ht) (polyParents3_safe t ht) (0,Fin.castLE (by decide) i)

theorem poly_skew (t : Int) (i : Fin 16) : SkewSymmetric (polyNode t i) := by
  rcases polyFin i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp only [polyNode,polyP,matrix_six] <;> exact ofSix_skew _ _ _ _ _ _

theorem polyCyclic0 (t : Int) (ht : 0≤t) : ¬ Acyclic (polyNode t 0) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (polyP 0 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (polyP 0 3 1) t ht (by decide))
  have h2 := hr 1 0 (pos (polyP 0 1 0) t ht (by decide))
  omega

theorem polyCyclic1 (t : Int) (ht : 0≤t) : ¬ Acyclic (polyNode t 1) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (polyP 1 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (polyP 1 3 1) t ht (by decide))
  have h2 := hr 1 0 (pos (polyP 1 1 0) t ht (by decide))
  omega

theorem polyCyclic2 (t : Int) (ht : 0≤t) : ¬ Acyclic (polyNode t 2) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (polyP 2 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (polyP 2 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (polyP 2 1 0) t ht (by decide))
  omega

theorem polyCyclic3 (t : Int) (ht : 0≤t) : ¬ Acyclic (polyNode t 3) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (polyP 3 0 2) t ht (by decide))
  have h1 := hr 2 1 (pos (polyP 3 2 1) t ht (by decide))
  have h2 := hr 1 0 (pos (polyP 3 1 0) t ht (by decide))
  omega

theorem polyCyclic4 (t : Int) (ht : 0≤t) : ¬ Acyclic (polyNode t 4) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (polyP 4 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (polyP 4 3 1) t ht (by decide))
  have h2 := hr 1 0 (pos (polyP 4 1 0) t ht (by decide))
  omega

theorem polyCyclic5 (t : Int) (ht : 0≤t) : ¬ Acyclic (polyNode t 5) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (polyP 5 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (polyP 5 3 1) t ht (by decide))
  have h2 := hr 1 0 (pos (polyP 5 1 0) t ht (by decide))
  omega

theorem polyCyclic6 (t : Int) (ht : 0≤t) : ¬ Acyclic (polyNode t 6) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (polyP 6 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (polyP 6 3 1) t ht (by decide))
  have h2 := hr 1 0 (pos (polyP 6 1 0) t ht (by decide))
  omega

theorem polyCyclic7 (t : Int) (ht : 0≤t) : ¬ Acyclic (polyNode t 7) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (polyP 7 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (polyP 7 3 1) t ht (by decide))
  have h2 := hr 1 0 (pos (polyP 7 1 0) t ht (by decide))
  omega

theorem polyCyclic8 (t : Int) (ht : 0≤t) : ¬ Acyclic (polyNode t 8) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (polyP 8 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (polyP 8 3 1) t ht (by decide))
  have h2 := hr 1 0 (pos (polyP 8 1 0) t ht (by decide))
  omega

theorem polyCyclic9 (t : Int) (ht : 0≤t) : ¬ Acyclic (polyNode t 9) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (polyP 9 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (polyP 9 3 1) t ht (by decide))
  have h2 := hr 1 0 (pos (polyP 9 1 0) t ht (by decide))
  omega

theorem polyCyclic10 (t : Int) (ht : 0≤t) : ¬ Acyclic (polyNode t 10) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (polyP 10 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (polyP 10 3 1) t ht (by decide))
  have h2 := hr 1 0 (pos (polyP 10 1 0) t ht (by decide))
  omega

theorem polyCyclic11 (t : Int) (ht : 0≤t) : ¬ Acyclic (polyNode t 11) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (polyP 11 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (polyP 11 3 1) t ht (by decide))
  have h2 := hr 1 0 (pos (polyP 11 1 0) t ht (by decide))
  omega

theorem polyCyclic12 (t : Int) (ht : 0≤t) : ¬ Acyclic (polyNode t 12) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (polyP 12 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (polyP 12 3 1) t ht (by decide))
  have h2 := hr 1 0 (pos (polyP 12 1 0) t ht (by decide))
  omega

theorem polyCyclic13 (t : Int) (ht : 0≤t) : ¬ Acyclic (polyNode t 13) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (polyP 13 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (polyP 13 3 1) t ht (by decide))
  have h2 := hr 1 0 (pos (polyP 13 1 0) t ht (by decide))
  omega

theorem polyCyclic14 (t : Int) (ht : 0≤t) : ¬ Acyclic (polyNode t 14) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (polyP 14 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (polyP 14 3 1) t ht (by decide))
  have h2 := hr 1 0 (pos (polyP 14 1 0) t ht (by decide))
  omega

theorem polyCyclic15 (t : Int) (ht : 0≤t) : ¬ Acyclic (polyNode t 15) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (polyP 15 0 3) t ht (by decide))
  have h1 := hr 3 1 (pos (polyP 15 3 1) t ht (by decide))
  have h2 := hr 1 0 (pos (polyP 15 1 0) t ht (by decide))
  omega

theorem polyEdge0_0 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 0) 0) := by
  have he := mutation_equal (polyP 0) (prelabel (tailP [7,1] 0) perm21.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (polyP 0) t) 0)
  rw [he]
  exact Safe.framed (tailP_safe [7,1] 0 t ht (by decide)) perm21.symm

theorem polyEdge0_1 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 0) 1) := by
  have he := mutation_equal (polyP 0) (preverse (prelabel (root [6,1] [13,2] [28,11,1] [2] [5,1] [1]) perm6.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (poly_safe t ht 0) 1
  rw [show mutate (polyNode t 0) 1=(reverse (relabel (matrix (root [6,1] [13,2] [28,11,1] [2] [5,1] [1]) t) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [6,1] [13,2] [28,11,1] [2] [5,1] [1] t ht (by decide)) perm6.symm)

theorem polyEdge0_2 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 0) 2) := by
  have he := mutation_equal (polyP 0) (preverse (prelabel (tailP [7,1] 2) perm20.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (polyP 0) t) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (tailP_safe [7,1] 2 t ht (by decide)) perm20.symm)

theorem polyEdge0_3 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 0) 3) := by
  have he := mutation_equal (polyP 0) (prelabel (tailP [5,1] 0) perm21.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (polyP 0) t) 3)
  rw [he]
  exact Safe.framed (tailP_safe [5,1] 0 t ht (by decide)) perm21.symm

theorem polyEdge1_0 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 1) 0) := by
  have he := mutation_equal (polyP 1) (prelabel (tailP [7,1] 1) perm21.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (polyP 1) t) 0)
  rw [he]
  exact Safe.framed (tailP_safe [7,1] 1 t ht (by decide)) perm21.symm

theorem polyEdge1_1 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 1) 1) := by
  have he := mutation_equal (polyP 1) (preverse (prelabel (polyP 4) perm19.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (polyP 1) t) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (poly_safe t ht 4) perm19.symm)

theorem polyEdge1_2 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 1) 2) := by
  have he := mutation_equal (polyP 1) (prelabel (tailP [7,1] 3) perm1.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (polyP 1) t) 2)
  rw [he]
  exact Safe.framed (tailP_safe [7,1] 3 t ht (by decide)) perm1.symm

theorem polyEdge1_3 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 1) 3) := by
  have he := mutation_equal (polyP 1) (prelabel (tailP [5,1] 1) perm21.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (polyP 1) t) 3)
  rw [he]
  exact Safe.framed (tailP_safe [5,1] 1 t ht (by decide)) perm21.symm

theorem polyEdge2_0 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 2) 0) := by
  have he := mutation_equal (polyP 2) (preverse (prelabel (tailP [6,1] 3) perm1.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (polyP 2) t) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (tailP_safe [6,1] 3 t ht (by decide)) perm1.symm)

theorem polyEdge2_1 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 2) 1) := by
  have he := mutation_equal (polyP 2) (preverse (prelabel (root [6,1] [29,11,1] [11,2] [5,1] [2] [1]) perm6.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (poly_safe t ht 2) 1
  rw [show mutate (polyNode t 2) 1=(reverse (relabel (matrix (root [6,1] [29,11,1] [11,2] [5,1] [2] [1]) t) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [6,1] [29,11,1] [11,2] [5,1] [2] [1] t ht (by decide)) perm6.symm)

theorem polyEdge2_2 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 2) 2) := by
  have he := mutation_equal (polyP 2) (preverse (prelabel (tailP [7,1] 3) perm21.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (polyP 2) t) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (tailP_safe [7,1] 3 t ht (by decide)) perm21.symm)

theorem polyEdge2_3 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 2) 3) := by
  have he := mutation_equal (polyP 2) (preverse (prelabel (tailP [5,1] 0) perm15.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (polyP 2) t) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (tailP_safe [5,1] 0 t ht (by decide)) perm15.symm)

theorem polyEdge3_0 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 3) 0) := by
  have he := mutation_equal (polyP 3) (preverse (prelabel (tailP [6,1] 2) perm1.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (polyP 3) t) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (tailP_safe [6,1] 2 t ht (by decide)) perm1.symm)

theorem polyEdge3_1 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 3) 1) := by
  have he := mutation_equal (polyP 3) (prelabel (generic polyParam0_0 polyParam0_1 polyParam0_2 polyParam0_3 0) perm17.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (polyP 3) t) 1)
  rw [he]
  exact Safe.framed (polyRegion0_safe t ht 0) perm17.symm

theorem polyEdge3_2 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 3) 2) := by
  have he := mutation_equal (polyP 3) (preverse (prelabel (tailP [5,1] 2) perm21.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (polyP 3) t) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (tailP_safe [5,1] 2 t ht (by decide)) perm21.symm)

theorem polyEdge3_3 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 3) 3) := by
  have he := mutation_equal (polyP 3) (prelabel (tailP [5,1] 1) perm1.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (polyP 3) t) 3)
  rw [he]
  exact Safe.framed (tailP_safe [5,1] 1 t ht (by decide)) perm1.symm

theorem polyEdge4_0 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 4) 0) := by
  have he := mutation_equal (polyP 4) (preverse (prelabel (root [5,1] [29,11,1] [134,82,16,1] [6,1] [28,11,1] [1]) perm5.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (poly_safe t ht 4) 0
  rw [show mutate (polyNode t 4) 0=(reverse (relabel (matrix (root [5,1] [29,11,1] [134,82,16,1] [6,1] [28,11,1] [1]) t) perm5.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [5,1] [29,11,1] [134,82,16,1] [6,1] [28,11,1] [1] t ht (by decide)) perm5.symm)

theorem polyEdge4_1 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 4) 1) := by
  have he := mutation_equal (polyP 4) (preverse (prelabel (polyP 7) perm19.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (polyP 4) t) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (poly_safe t ht 7) perm19.symm)

theorem polyEdge4_2 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 4) 2) := by
  have he := mutation_equal (polyP 4) (prelabel (polyP 8) perm1.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (polyP 4) t) 2)
  rw [he]
  exact Safe.framed (poly_safe t ht 8) perm1.symm

theorem polyEdge4_3 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 4) 3) := by
  have he := mutation_equal (polyP 4) (preverse (prelabel (tailP [6,1] 1) perm11.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (polyP 4) t) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (tailP_safe [6,1] 1 t ht (by decide)) perm11.symm)

theorem polyEdge5_0 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 5) 0) := by
  have he := mutation_equal (polyP 5) (prelabel (polyP 6) perm21.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (polyP 5) t) 0)
  rw [he]
  exact Safe.framed (poly_safe t ht 6) perm21.symm

theorem polyEdge5_1 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 5) 1) := by
  have he := mutation_equal (polyP 5) (prelabel (generic polyParam1_0 polyParam1_1 polyParam1_2 polyParam1_3 0) perm17.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (polyP 5) t) 1)
  rw [he]
  exact Safe.framed (polyRegion1_safe t ht 0) perm17.symm

theorem polyEdge5_2 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 5) 2) := by
  have he := mutation_equal (polyP 5) (preverse (prelabel (generic polyParam0_0 polyParam0_1 polyParam0_2 polyParam0_3 0) perm3.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (polyP 5) t) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (polyRegion0_safe t ht 0) perm3.symm)

theorem polyEdge5_3 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 5) 3) := by
  have he := mutation_equal (polyP 5) (prelabel (polyP 11) perm1.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (polyP 5) t) 3)
  rw [he]
  exact Safe.framed (poly_safe t ht 11) perm1.symm

theorem polyEdge6_0 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 6) 0) := by
  have he := mutation_equal (polyP 6) (prelabel (fork [5,1] [4,1] [114,73,15,1] [19,9,1] [547,469,147,20,1] [5,1]) perm5.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (poly_safe t ht 6)
  rw [show mutate (polyNode t 6) 0=(relabel (matrix (fork [5,1] [4,1] [114,73,15,1] [19,9,1] [547,469,147,20,1] [5,1]) t) perm5.symm) from he]
  exact IsFork.relabelled (fork_sound [5,1] [4,1] [114,73,15,1] [19,9,1] [547,469,147,20,1] [5,1] t ht (by decide)) perm5.symm

theorem polyEdge6_1 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 6) 1) := by
  have he := mutation_equal (polyP 6) (preverse (prelabel (root [114,73,15,1] [574,480,148,20,1] [2617,2818,1189,246,25,1] [5,1] [23,10,1] [1]) perm6.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (poly_safe t ht 6) 1
  rw [show mutate (polyNode t 6) 1=(reverse (relabel (matrix (root [114,73,15,1] [574,480,148,20,1] [2617,2818,1189,246,25,1] [5,1] [23,10,1] [1]) t) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [114,73,15,1] [574,480,148,20,1] [2617,2818,1189,246,25,1] [5,1] [23,10,1] [1] t ht (by decide)) perm6.symm)

theorem polyEdge6_2 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 6) 2) := by
  have he := mutation_equal (polyP 6) (preverse (prelabel (generic polyParam0_0 polyParam0_1 polyParam0_2 polyParam0_3 2) perm16.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (polyP 6) t) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (polyRegion0_safe t ht 2) perm16.symm)

theorem polyEdge6_3 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 6) 3) := by
  have he := mutation_equal (polyP 6) (prelabel (polyP 5) perm21.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (polyP 6) t) 3)
  rw [he]
  exact Safe.framed (poly_safe t ht 5) perm21.symm

theorem polyEdge7_0 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 7) 0) := by
  have he := mutation_equal (polyP 7) (prelabel (fork [6,1] [163,93,17,1] [7,1] [950,710,194,23,1] [41,13,1] [6,1]) perm4.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (poly_safe t ht 7)
  rw [show mutate (polyNode t 7) 0=(relabel (matrix (fork [6,1] [163,93,17,1] [7,1] [950,710,194,23,1] [41,13,1] [6,1]) t) perm4.symm) from he]
  exact IsFork.relabelled (fork_sound [6,1] [163,93,17,1] [7,1] [950,710,194,23,1] [41,13,1] [6,1] t ht (by decide)) perm4.symm

theorem polyEdge7_1 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 7) 1) := by
  have he := mutation_equal (polyP 7) (preverse (prelabel (fork [28,11,1] [163,93,17,1] [6,1] [4558,4396,1662,308,28,1] [169,94,17,1] [7,1]) perm10.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (poly_safe t ht 7)
  rw [show mutate (polyNode t 7) 1=(reverse (relabel (matrix (fork [28,11,1] [163,93,17,1] [6,1] [4558,4396,1662,308,28,1] [169,94,17,1] [7,1]) t) perm10.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [28,11,1] [163,93,17,1] [6,1] [4558,4396,1662,308,28,1] [169,94,17,1] [7,1] t ht (by decide)) perm10.symm)

theorem polyEdge7_2 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 7) 2) := by
  have he := mutation_equal (polyP 7) (prelabel (polyP 12) perm1.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (polyP 7) t) 2)
  rw [he]
  exact Safe.framed (poly_safe t ht 12) perm1.symm

theorem polyEdge7_3 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 7) 3) := by
  have he := mutation_equal (polyP 7) (preverse (prelabel (polyP 4) perm11.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (polyP 7) t) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (poly_safe t ht 4) perm11.symm)

theorem polyEdge8_0 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 8) 0) := by
  have he := mutation_equal (polyP 8) (prelabel (polyP 13) perm21.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (polyP 8) t) 0)
  rw [he]
  exact Safe.framed (poly_safe t ht 13) perm21.symm

theorem polyEdge8_1 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 8) 1) := by
  have he := mutation_equal (polyP 8) (prelabel (generic polyParam2_0 polyParam2_1 polyParam2_2 polyParam2_3 0) perm17.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (polyP 8) t) 1)
  rw [he]
  exact Safe.framed (polyRegion2_safe t ht 0) perm17.symm

theorem polyEdge8_2 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 8) 2) := by
  have he := mutation_equal (polyP 8) (preverse (prelabel (generic polyParam3_0 polyParam3_1 polyParam3_2 polyParam3_3 0) perm3.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (polyP 8) t) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (polyRegion3_safe t ht 0) perm3.symm)

theorem polyEdge8_3 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 8) 3) := by
  have he := mutation_equal (polyP 8) (prelabel (polyP 4) perm1.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (polyP 8) t) 3)
  rw [he]
  exact Safe.framed (poly_safe t ht 4) perm1.symm

theorem polyEdge9_0 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 9) 0) := by
  have he := mutation_equal (polyP 9) (prelabel (polyP 10) perm21.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (polyP 9) t) 0)
  rw [he]
  exact Safe.framed (poly_safe t ht 10) perm21.symm

theorem polyEdge9_1 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 9) 1) := by
  have he := mutation_equal (polyP 9) (preverse (prelabel (root [116,73,15,1] [2089,2358,1043,226,24,1] [574,480,148,20,1] [18,9,1] [5,1] [1]) perm6.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (poly_safe t ht 9) 1
  rw [show mutate (polyNode t 9) 1=(reverse (relabel (matrix (root [116,73,15,1] [2089,2358,1043,226,24,1] [574,480,148,20,1] [18,9,1] [5,1] [1]) t) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [116,73,15,1] [2089,2358,1043,226,24,1] [574,480,148,20,1] [18,9,1] [5,1] [1] t ht (by decide)) perm6.symm)

theorem polyEdge9_2 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 9) 2) := by
  have he := mutation_equal (polyP 9) (preverse (prelabel (generic polyParam1_0 polyParam1_1 polyParam1_2 polyParam1_3 0) perm3.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (polyP 9) t) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (polyRegion1_safe t ht 0) perm3.symm)

theorem polyEdge9_3 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 9) 3) := by
  have he := mutation_equal (polyP 9) (prelabel (polyP 15) perm1.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (polyP 9) t) 3)
  rw [he]
  exact Safe.framed (poly_safe t ht 15) perm1.symm

theorem polyEdge10_0 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 10) 0) := by
  have he := mutation_equal (polyP 10) (prelabel (fork [6,1] [5,1] [691,553,163,21,1] [29,11,1] [4030,3936,1516,288,27,1] [18,9,1]) perm5.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (poly_safe t ht 10)
  rw [show mutate (polyNode t 10) 0=(relabel (matrix (fork [6,1] [5,1] [691,553,163,21,1] [29,11,1] [4030,3936,1516,288,27,1] [18,9,1]) t) perm5.symm) from he]
  exact IsFork.relabelled (fork_sound [6,1] [5,1] [691,553,163,21,1] [29,11,1] [4030,3936,1516,288,27,1] [18,9,1] t ht (by decide)) perm5.symm

theorem polyEdge10_1 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 10) 1) := by
  have he := mutation_equal (polyP 10) (preverse (prelabel (root [691,553,163,21,1] [12443,16174,8602,2398,370,30,1] [80150,114590,69642,23321,4647,551,36,1] [18,9,1] [116,73,15,1] [1]) perm6.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (poly_safe t ht 10) 1
  rw [show mutate (polyNode t 10) 1=(reverse (relabel (matrix (root [691,553,163,21,1] [12443,16174,8602,2398,370,30,1] [80150,114590,69642,23321,4647,551,36,1] [18,9,1] [116,73,15,1] [1]) t) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [691,553,163,21,1] [12443,16174,8602,2398,370,30,1] [80150,114590,69642,23321,4647,551,36,1] [18,9,1] [116,73,15,1] [1] t ht (by decide)) perm6.symm)

theorem polyEdge10_2 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 10) 2) := by
  have he := mutation_equal (polyP 10) (preverse (prelabel (generic polyParam1_0 polyParam1_1 polyParam1_2 polyParam1_3 2) perm16.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (polyP 10) t) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (polyRegion1_safe t ht 2) perm16.symm)

theorem polyEdge10_3 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 10) 3) := by
  have he := mutation_equal (polyP 10) (prelabel (polyP 9) perm21.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (polyP 10) t) 3)
  rw [he]
  exact Safe.framed (poly_safe t ht 9) perm21.symm

theorem polyEdge11_0 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 11) 0) := by
  have he := mutation_equal (polyP 11) (preverse (prelabel (root [4,1] [19,9,1] [67,53,13,1] [5,1] [18,9,1] [1]) perm5.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (poly_safe t ht 11) 0
  rw [show mutate (polyNode t 11) 0=(reverse (relabel (matrix (root [4,1] [19,9,1] [67,53,13,1] [5,1] [18,9,1] [1]) t) perm5.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [4,1] [19,9,1] [67,53,13,1] [5,1] [18,9,1] [1] t ht (by decide)) perm5.symm)

theorem polyEdge11_1 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 11) 1) := by
  have he := mutation_equal (polyP 11) (preverse (prelabel (polyP 15) perm19.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (polyP 11) t) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (poly_safe t ht 15) perm19.symm)

theorem polyEdge11_2 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 11) 2) := by
  have he := mutation_equal (polyP 11) (prelabel (polyP 5) perm1.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (polyP 11) t) 2)
  rw [he]
  exact Safe.framed (poly_safe t ht 5) perm1.symm

theorem polyEdge11_3 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 11) 3) := by
  have he := mutation_equal (polyP 11) (preverse (prelabel (tailP [5,1] 1) perm11.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (polyP 11) t) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (tailP_safe [5,1] 1 t ht (by decide)) perm11.symm)

theorem polyEdge12_0 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 12) 0) := by
  have he := mutation_equal (polyP 12) (prelabel (polyP 14) perm21.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (polyP 12) t) 0)
  rw [he]
  exact Safe.framed (poly_safe t ht 14) perm21.symm

theorem polyEdge12_1 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 12) 1) := by
  have he := mutation_equal (polyP 12) (preverse (prelabel (root [205,106,18,1] [5741,5223,1875,332,29,1] [1223,840,214,24,1] [28,11,1] [6,1] [1]) perm6.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (poly_safe t ht 12) 1
  rw [show mutate (polyNode t 12) 1=(reverse (relabel (matrix (root [205,106,18,1] [5741,5223,1875,332,29,1] [1223,840,214,24,1] [28,11,1] [6,1] [1]) t) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [205,106,18,1] [5741,5223,1875,332,29,1] [1223,840,214,24,1] [28,11,1] [6,1] [1] t ht (by decide)) perm6.symm)

theorem polyEdge12_2 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 12) 2) := by
  have he := mutation_equal (polyP 12) (preverse (prelabel (generic polyParam2_0 polyParam2_1 polyParam2_2 polyParam2_3 0) perm3.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (polyP 12) t) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (polyRegion2_safe t ht 0) perm3.symm)

theorem polyEdge12_3 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 12) 3) := by
  have he := mutation_equal (polyP 12) (prelabel (polyP 7) perm1.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (polyP 12) t) 3)
  rw [he]
  exact Safe.framed (poly_safe t ht 7) perm1.symm

theorem polyEdge13_0 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 13) 0) := by
  have he := mutation_equal (polyP 13) (prelabel (fork [6,1] [5,1] [203,106,18,1] [29,11,1] [1184,827,213,24,1] [6,1]) perm5.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (poly_safe t ht 13)
  rw [show mutate (polyNode t 13) 0=(relabel (matrix (fork [6,1] [5,1] [203,106,18,1] [29,11,1] [1184,827,213,24,1] [6,1]) t) perm5.symm) from he]
  exact IsFork.relabelled (fork_sound [6,1] [5,1] [203,106,18,1] [29,11,1] [1184,827,213,24,1] [6,1] t ht (by decide)) perm5.symm

theorem polyEdge13_1 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 13) 1) := by
  have he := mutation_equal (polyP 13) (preverse (prelabel (root [203,106,18,1] [1223,840,214,24,1] [6896,6039,2087,356,30,1] [6,1] [34,12,1] [1]) perm6.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (poly_safe t ht 13) 1
  rw [show mutate (polyNode t 13) 1=(reverse (relabel (matrix (root [203,106,18,1] [1223,840,214,24,1] [6896,6039,2087,356,30,1] [6,1] [34,12,1] [1]) t) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [203,106,18,1] [1223,840,214,24,1] [6896,6039,2087,356,30,1] [6,1] [34,12,1] [1] t ht (by decide)) perm6.symm)

theorem polyEdge13_2 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 13) 2) := by
  have he := mutation_equal (polyP 13) (preverse (prelabel (generic polyParam3_0 polyParam3_1 polyParam3_2 polyParam3_3 2) perm16.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (polyP 13) t) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (polyRegion3_safe t ht 2) perm16.symm)

theorem polyEdge13_3 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 13) 3) := by
  have he := mutation_equal (polyP 13) (prelabel (polyP 8) perm21.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (polyP 13) t) 3)
  rw [he]
  exact Safe.framed (poly_safe t ht 8) perm21.symm

theorem polyEdge14_0 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 14) 0) := by
  have he := mutation_equal (polyP 14) (prelabel (fork [7,1] [6,1] [1429,946,232,25,1] [41,13,1] [9798,7945,2552,406,32,1] [28,11,1]) perm5.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (poly_safe t ht 14)
  rw [show mutate (polyNode t 14) 0=(relabel (matrix (fork [7,1] [6,1] [1429,946,232,25,1] [41,13,1] [9798,7945,2552,406,32,1] [28,11,1]) t) perm5.symm) from he]
  exact IsFork.relabelled (fork_sound [7,1] [6,1] [1429,946,232,25,1] [41,13,1] [9798,7945,2552,406,32,1] [28,11,1] t ht (by decide)) perm5.symm

theorem polyEdge14_1 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 14) 1) := by
  have he := mutation_equal (polyP 14) (preverse (prelabel (root [1429,946,232,25,1] [40018,42208,18331,4198,535,36,1] [292938,345403,173558,48174,7977,788,43,1] [28,11,1] [205,106,18,1] [1]) perm6.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (poly_safe t ht 14) 1
  rw [show mutate (polyNode t 14) 1=(reverse (relabel (matrix (root [1429,946,232,25,1] [40018,42208,18331,4198,535,36,1] [292938,345403,173558,48174,7977,788,43,1] [28,11,1] [205,106,18,1] [1]) t) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [1429,946,232,25,1] [40018,42208,18331,4198,535,36,1] [292938,345403,173558,48174,7977,788,43,1] [28,11,1] [205,106,18,1] [1] t ht (by decide)) perm6.symm)

theorem polyEdge14_2 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 14) 2) := by
  have he := mutation_equal (polyP 14) (preverse (prelabel (generic polyParam2_0 polyParam2_1 polyParam2_2 polyParam2_3 2) perm16.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (polyP 14) t) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (polyRegion2_safe t ht 2) perm16.symm)

theorem polyEdge14_3 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 14) 3) := by
  have he := mutation_equal (polyP 14) (prelabel (polyP 12) perm21.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (polyP 14) t) 3)
  rw [he]
  exact Safe.framed (poly_safe t ht 12) perm21.symm

theorem polyEdge15_0 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 15) 0) := by
  have he := mutation_equal (polyP 15) (prelabel (fork [5,1] [86,62,14,1] [6,1] [412,387,131,19,1] [29,11,1] [5,1]) perm4.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (poly_safe t ht 15)
  rw [show mutate (polyNode t 15) 0=(relabel (matrix (fork [5,1] [86,62,14,1] [6,1] [412,387,131,19,1] [29,11,1] [5,1]) t) perm4.symm) from he]
  exact IsFork.relabelled (fork_sound [5,1] [86,62,14,1] [6,1] [412,387,131,19,1] [29,11,1] [5,1] t ht (by decide)) perm4.symm

theorem polyEdge15_1 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 15) 1) := by
  have he := mutation_equal (polyP 15) (preverse (prelabel (fork [18,9,1] [86,62,14,1] [5,1] [1543,1889,896,206,23,1] [91,63,14,1] [6,1]) perm10.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (poly_safe t ht 15)
  rw [show mutate (polyNode t 15) 1=(reverse (relabel (matrix (fork [18,9,1] [86,62,14,1] [5,1] [1543,1889,896,206,23,1] [91,63,14,1] [6,1]) t) perm10.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [18,9,1] [86,62,14,1] [5,1] [1543,1889,896,206,23,1] [91,63,14,1] [6,1] t ht (by decide)) perm10.symm)

theorem polyEdge15_2 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 15) 2) := by
  have he := mutation_equal (polyP 15) (prelabel (polyP 9) perm1.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (polyP 15) t) 2)
  rw [he]
  exact Safe.framed (poly_safe t ht 9) perm1.symm

theorem polyEdge15_3 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 15) 3) := by
  have he := mutation_equal (polyP 15) (preverse (prelabel (polyP 11) perm11.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (polyP 15) t) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (poly_safe t ht 11) perm11.symm)

theorem poly_cyclic (t : Int) (ht : 0≤t) (i : Fin 16) : ¬ Acyclic (polyNode t i) := by
  rcases polyFin i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact polyCyclic0 t ht
  · exact polyCyclic1 t ht
  · exact polyCyclic2 t ht
  · exact polyCyclic3 t ht
  · exact polyCyclic4 t ht
  · exact polyCyclic5 t ht
  · exact polyCyclic6 t ht
  · exact polyCyclic7 t ht
  · exact polyCyclic8 t ht
  · exact polyCyclic9 t ht
  · exact polyCyclic10 t ht
  · exact polyCyclic11 t ht
  · exact polyCyclic12 t ht
  · exact polyCyclic13 t ht
  · exact polyCyclic14 t ht
  · exact polyCyclic15 t ht
theorem poly_edges (t : Int) (ht : 0≤t) (i : Fin 16) (k : Fin 4) : SafeCore (mutate (polyNode t i) k) := by
  have hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
  rcases polyFin i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rcases hk with rfl|rfl|rfl|rfl
  · exact polyEdge0_0 t ht
  · exact polyEdge0_1 t ht
  · exact polyEdge0_2 t ht
  · exact polyEdge0_3 t ht
  · exact polyEdge1_0 t ht
  · exact polyEdge1_1 t ht
  · exact polyEdge1_2 t ht
  · exact polyEdge1_3 t ht
  · exact polyEdge2_0 t ht
  · exact polyEdge2_1 t ht
  · exact polyEdge2_2 t ht
  · exact polyEdge2_3 t ht
  · exact polyEdge3_0 t ht
  · exact polyEdge3_1 t ht
  · exact polyEdge3_2 t ht
  · exact polyEdge3_3 t ht
  · exact polyEdge4_0 t ht
  · exact polyEdge4_1 t ht
  · exact polyEdge4_2 t ht
  · exact polyEdge4_3 t ht
  · exact polyEdge5_0 t ht
  · exact polyEdge5_1 t ht
  · exact polyEdge5_2 t ht
  · exact polyEdge5_3 t ht
  · exact polyEdge6_0 t ht
  · exact polyEdge6_1 t ht
  · exact polyEdge6_2 t ht
  · exact polyEdge6_3 t ht
  · exact polyEdge7_0 t ht
  · exact polyEdge7_1 t ht
  · exact polyEdge7_2 t ht
  · exact polyEdge7_3 t ht
  · exact polyEdge8_0 t ht
  · exact polyEdge8_1 t ht
  · exact polyEdge8_2 t ht
  · exact polyEdge8_3 t ht
  · exact polyEdge9_0 t ht
  · exact polyEdge9_1 t ht
  · exact polyEdge9_2 t ht
  · exact polyEdge9_3 t ht
  · exact polyEdge10_0 t ht
  · exact polyEdge10_1 t ht
  · exact polyEdge10_2 t ht
  · exact polyEdge10_3 t ht
  · exact polyEdge11_0 t ht
  · exact polyEdge11_1 t ht
  · exact polyEdge11_2 t ht
  · exact polyEdge11_3 t ht
  · exact polyEdge12_0 t ht
  · exact polyEdge12_1 t ht
  · exact polyEdge12_2 t ht
  · exact polyEdge12_3 t ht
  · exact polyEdge13_0 t ht
  · exact polyEdge13_1 t ht
  · exact polyEdge13_2 t ht
  · exact polyEdge13_3 t ht
  · exact polyEdge14_0 t ht
  · exact polyEdge14_1 t ht
  · exact polyEdge14_2 t ht
  · exact polyEdge14_3 t ht
  · exact polyEdge15_0 t ht
  · exact polyEdge15_1 t ht
  · exact polyEdge15_2 t ht
  · exact polyEdge15_3 t ht

theorem core_skew (B : Matrix 4) (h : Core B) : SkewSymmetric B := by
  rcases h with ⟨i,rfl⟩|⟨t,ht,i,rfl⟩
  · exact finite_skew i
  · exact poly_skew t i

theorem core_cyclic (B : Matrix 4) (h : Core B) : ¬ Acyclic B := by
  rcases h with ⟨i,rfl⟩|⟨t,ht,i,rfl⟩
  · exact finite_cyclic i
  · exact poly_cyclic t ht i

theorem core_edges (B : Matrix 4) (h : Core B) (k : Fin 4) : SafeCore (mutate B k) := by
  rcases h with ⟨i,rfl⟩|⟨t,ht,i,rfl⟩
  · exact finite_edges i k
  · exact poly_edges t ht i k

theorem safe_nma (B : Matrix 4) (h : SafeCore B) : ¬ MutationAcyclic B :=
  safe_NMA data rules Core core_skew core_cyclic core_edges h

theorem nma_q426 : ¬ MutationAcyclic (ofSix (-2) (-1) 1 (-2) 1 (-2)) :=
  by simpa [finiteNode,finiteP,matrix_six,eval] using safe_nma _ (finite_safe 0)



theorem frame_q426 : ofSix (-2) (-1) (1) (-2) (1) (-2)=(relabel (finiteNode 0) perm0.symm) := by
  funext i j
  exact (show ∀ a b, (ofSix (-2) (-1) (1) (-2) (1) (-2)) a b=((relabel (finiteNode 0) perm0.symm)) a b from by decide) i j
theorem frame_q442 : ofSix (-2) (-1) (1) (-1) (0) (-2)=(reverse (relabel (finiteNode 8) perm21.symm)) := by
  funext i j
  exact (show ∀ a b, (ofSix (-2) (-1) (1) (-1) (0) (-2)) a b=((reverse (relabel (finiteNode 8) perm21.symm))) a b from by decide) i j
theorem nma_q442 : ¬ MutationAcyclic (ofSix (-2) (-1) (1) (-1) (0) (-2)) := by
  rw [frame_q442]
  exact safe_nma _ (Safe.reversed (Safe.framed (finite_safe 8) perm21.symm))

theorem frame_q457 : ofSix (-2) (-1) (1) (0) (-1) (-2)=(relabel (finiteNode 20) perm15.symm) := by
  funext i j
  exact (show ∀ a b, (ofSix (-2) (-1) (1) (0) (-1) (-2)) a b=((relabel (finiteNode 20) perm15.symm)) a b from by decide) i j
theorem nma_q457 : ¬ MutationAcyclic (ofSix (-2) (-1) (1) (0) (-1) (-2)) := by
  rw [frame_q457]
  exact safe_nma _ (Safe.framed (finite_safe 20) perm15.symm)

theorem frame_q460 : ofSix (-2) (-1) (1) (0) (-1) (1)=(reverse (relabel (finiteNode 37) perm8.symm)) := by
  funext i j
  exact (show ∀ a b, (ofSix (-2) (-1) (1) (0) (-1) (1)) a b=((reverse (relabel (finiteNode 37) perm8.symm))) a b from by decide) i j
theorem nma_q460 : ¬ MutationAcyclic (ofSix (-2) (-1) (1) (0) (-1) (1)) := by
  rw [frame_q460]
  exact safe_nma _ (Safe.reversed (Safe.framed (finite_safe 37) perm8.symm))

theorem frame_q475 : ofSix (-2) (-1) (1) (1) (-2) (1)=(relabel (finiteNode 22) perm0.symm) := by
  funext i j
  exact (show ∀ a b, (ofSix (-2) (-1) (1) (1) (-2) (1)) a b=((relabel (finiteNode 22) perm0.symm)) a b from by decide) i j
theorem nma_q475 : ¬ MutationAcyclic (ofSix (-2) (-1) (1) (1) (-2) (1)) := by
  rw [frame_q475]
  exact safe_nma _ (Safe.framed (finite_safe 22) perm0.symm)

theorem frame_q499 : ofSix (-2) (-1) (2) (-2) (-1) (-1)=(reverse (relabel (finiteNode 0) perm14.symm)) := by
  funext i j
  exact (show ∀ a b, (ofSix (-2) (-1) (2) (-2) (-1) (-1)) a b=((reverse (relabel (finiteNode 0) perm14.symm))) a b from by decide) i j
theorem nma_q499 : ¬ MutationAcyclic (ofSix (-2) (-1) (2) (-2) (-1) (-1)) := by
  rw [frame_q499]
  exact safe_nma _ (Safe.reversed (Safe.framed (finite_safe 0) perm14.symm))

theorem frame_q525 : ofSix (-2) (-1) (2) (1) (-1) (-1)=(reverse (relabel (finiteNode 22) perm6.symm)) := by
  funext i j
  exact (show ∀ a b, (ofSix (-2) (-1) (2) (1) (-1) (-1)) a b=((reverse (relabel (finiteNode 22) perm6.symm))) a b from by decide) i j
theorem nma_q525 : ¬ MutationAcyclic (ofSix (-2) (-1) (2) (1) (-1) (-1)) := by
  rw [frame_q525]
  exact safe_nma _ (Safe.reversed (Safe.framed (finite_safe 22) perm6.symm))

theorem frame_q573 : ofSix (-2) (0) (1) (-1) (-1) (-2)=(relabel (finiteNode 8) perm2.symm) := by
  funext i j
  exact (show ∀ a b, (ofSix (-2) (0) (1) (-1) (-1) (-2)) a b=((relabel (finiteNode 8) perm2.symm)) a b from by decide) i j
theorem nma_q573 : ¬ MutationAcyclic (ofSix (-2) (0) (1) (-1) (-1) (-2)) := by
  rw [frame_q573]
  exact safe_nma _ (Safe.framed (finite_safe 8) perm2.symm)

theorem frame_q576 : ofSix (-2) (0) (1) (-1) (-1) (1)=(relabel (finiteNode 38) perm2.symm) := by
  funext i j
  exact (show ∀ a b, (ofSix (-2) (0) (1) (-1) (-1) (1)) a b=((relabel (finiteNode 38) perm2.symm)) a b from by decide) i j
theorem nma_q576 : ¬ MutationAcyclic (ofSix (-2) (0) (1) (-1) (-1) (1)) := by
  rw [frame_q576]
  exact safe_nma _ (Safe.framed (finite_safe 38) perm2.symm)

theorem frame_q595 : ofSix (-2) (0) (1) (1) (-1) (-1)=(relabel (finiteNode 37) perm2.symm) := by
  funext i j
  exact (show ∀ a b, (ofSix (-2) (0) (1) (1) (-1) (-1)) a b=((relabel (finiteNode 37) perm2.symm)) a b from by decide) i j
theorem nma_q595 : ¬ MutationAcyclic (ofSix (-2) (0) (1) (1) (-1) (-1)) := by
  rw [frame_q595]
  exact safe_nma _ (Safe.framed (finite_safe 37) perm2.symm)

theorem frame_q621 : ofSix (-2) (1) (1) (-1) (0) (1)=(reverse (relabel (finiteNode 38) perm10.symm)) := by
  funext i j
  exact (show ∀ a b, (ofSix (-2) (1) (1) (-1) (0) (1)) a b=((reverse (relabel (finiteNode 38) perm10.symm))) a b from by decide) i j
theorem nma_q621 : ¬ MutationAcyclic (ofSix (-2) (1) (1) (-1) (0) (1)) := by
  rw [frame_q621]
  exact safe_nma _ (Safe.reversed (Safe.framed (finite_safe 38) perm10.symm))

theorem frame_q638 : ofSix (-1) (-1) (-1) (-1) (1) (-1)=(relabel (finiteNode 52) perm0.symm) := by
  funext i j
  exact (show ∀ a b, (ofSix (-1) (-1) (-1) (-1) (1) (-1)) a b=((relabel (finiteNode 52) perm0.symm)) a b from by decide) i j
theorem nma_q638 : ¬ MutationAcyclic (ofSix (-1) (-1) (-1) (-1) (1) (-1)) := by
  rw [frame_q638]
  exact safe_nma _ (Safe.framed (finite_safe 52) perm0.symm)

theorem frame_q655 : ofSix (-1) (-1) (1) (-1) (-1) (1)=(reverse (relabel (finiteNode 52) perm13.symm)) := by
  funext i j
  exact (show ∀ a b, (ofSix (-1) (-1) (1) (-1) (-1) (1)) a b=((reverse (relabel (finiteNode 52) perm13.symm))) a b from by decide) i j
theorem nma_q655 : ¬ MutationAcyclic (ofSix (-1) (-1) (1) (-1) (-1) (1)) := by
  rw [frame_q655]
  exact safe_nma _ (Safe.reversed (Safe.framed (finite_safe 52) perm13.symm))

end QuiverProofs.Q426Structural