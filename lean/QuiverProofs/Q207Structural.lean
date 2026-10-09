import QuiverProofs.QFamilyPolynomialInterfaces
namespace QuiverProofs.Q207Structural
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

private theorem finiteFin (i : Fin 96) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 ∨ i=15 ∨ i=16 ∨ i=17 ∨ i=18 ∨ i=19 ∨ i=20 ∨ i=21 ∨ i=22 ∨ i=23 ∨ i=24 ∨ i=25 ∨ i=26 ∨ i=27 ∨ i=28 ∨ i=29 ∨ i=30 ∨ i=31 ∨ i=32 ∨ i=33 ∨ i=34 ∨ i=35 ∨ i=36 ∨ i=37 ∨ i=38 ∨ i=39 ∨ i=40 ∨ i=41 ∨ i=42 ∨ i=43 ∨ i=44 ∨ i=45 ∨ i=46 ∨ i=47 ∨ i=48 ∨ i=49 ∨ i=50 ∨ i=51 ∨ i=52 ∨ i=53 ∨ i=54 ∨ i=55 ∨ i=56 ∨ i=57 ∨ i=58 ∨ i=59 ∨ i=60 ∨ i=61 ∨ i=62 ∨ i=63 ∨ i=64 ∨ i=65 ∨ i=66 ∨ i=67 ∨ i=68 ∨ i=69 ∨ i=70 ∨ i=71 ∨ i=72 ∨ i=73 ∨ i=74 ∨ i=75 ∨ i=76 ∨ i=77 ∨ i=78 ∨ i=79 ∨ i=80 ∨ i=81 ∨ i=82 ∨ i=83 ∨ i=84 ∨ i=85 ∨ i=86 ∨ i=87 ∨ i=88 ∨ i=89 ∨ i=90 ∨ i=91 ∨ i=92 ∨ i=93 ∨ i=94 ∨ i=95 := by omega
def finiteP (i : Fin 96) : PMatrix := match i.val with
  | 0 => six [] [-2] [-1] [-2] [1] [-1]
  | 1 => six [-2] [-1] [1] [-1] [-1] [1]
  | 2 => six [-6] [-1] [2] [-3] [-4] [-1]
  | 3 => six [-6] [-1] [2] [1] [-4] [-1]
  | 4 => six [-6] [1] [1] [-5] [-3] [-1]
  | 5 => six [-6] [1] [1] [-3] [-1] [-1]
  | 6 => six [-7] [-1] [2] [-3] [-5] [-1]
  | 7 => six [-7] [-1] [2] [1] [-5] [-1]
  | 8 => six [-7] [1] [1] [-6] [-3] [-1]
  | 9 => six [-7] [1] [1] [-4] [-1] [-1]
  | 10 => six [] [-2] [-1] [2] [-1] [1]
  | 11 => six [] [-3] [2] [-1] [2] [-1]
  | 12 => six [-2] [-1] [-1] [-1] [1] [-1]
  | 13 => six [-2] [-1] [1] [1] [-1] [-2]
  | 14 => six [-3] [-1] [1] [1] [-2] [1]
  | 15 => six [-4] [-1] [2] [-3] [-2] [-1]
  | 16 => six [-22] [-5] [4] [1] [-6] [-1]
  | 17 => six [-4] [-1] [2] [1] [-2] [-1]
  | 18 => six [-5] [-1] [2] [-3] [-3] [-1]
  | 19 => six [-17] [-1] [4] [-5] [-1] [-1]
  | 20 => six [-67] [-3] [4] [-5] [-17] [-1]
  | 21 => six [-4] [1] [1] [-3] [-3] [-1]
  | 22 => six [-5] [-1] [2] [1] [-3] [-1]
  | 23 => six [-33] [-6] [5] [1] [-7] [-1]
  | 24 => six [-27] [-1] [5] [-6] [-1] [-1]
  | 25 => six [-134] [-4] [5] [-6] [-27] [-1]
  | 26 => six [-5] [1] [1] [-4] [-3] [-1]
  | 27 => six [] [-3] [1] [1] [1] [-1]
  | 28 => six [] [-3] [2] [1] [-2] [-5]
  | 29 => six [] [-3] [2] [1] [-2] [1]
  | 30 => six [] [-3] [1] [-1] [-1] [-1]
  | 31 => six [] [-3] [1] [-1] [-1] [-2]
  | 32 => six [-3] [-1] [1] [-1] [-1] [-2]
  | 33 => six [-4] [1] [1] [-1] [-1] [-1]
  | 34 => six [-128] [-7] [6] [5] [-22] [-1]
  | 35 => six [-6] [-3] [2] [1] [-4] [-1]
  | 36 => six [-5] [1] [1] [-2] [-1] [-1]
  | 37 => six [-3] [-1] [1] [-3] [1] [-2]
  | 38 => six [-86] [-1] [6] [-13] [-4] [-1]
  | 39 => six [-512] [-5] [6] [-13] [-86] [-1]
  | 40 => six [-13] [-4] [3] [1] [-5] [-1]
  | 41 => six [-226] [-8] [7] [6] [-33] [-1]
  | 42 => six [-39] [-1] [6] [-7] [-1] [-1]
  | 43 => six [-163] [-1] [7] [-22] [-5] [-1]
  | 44 => six [-1136] [-6] [7] [-22] [-163] [-1]
  | 45 => six [-3] [-2] [3] [1] [-1] [-1]
  | 46 => six [] [-3] [2] [-1] [2] [-7]
  | 47 => six [-13] [-3] [3] [2] [-5] [-1]
  | 48 => six [] [-3] [1] [1] [1] [-2]
  | 49 => six [] [-5] [3] [-3] [1] [-2]
  | 50 => six [-4] [-2] [3] [-2] [-1] [-1]
  | 51 => six [-22] [-5] [4] [3] [-6] [-1]
  | 52 => six [-9] [-1] [3] [-4] [-1] [-1]
  | 53 => six [-26] [-2] [3] [-4] [-9] [-1]
  | 54 => six [-10] [-1] [3] [-1] [-3] [-1]
  | 55 => six [-62] [-6] [5] [4] [-13] [-1]
  | 56 => six [-274] [-1] [8] [-33] [-6] [-1]
  | 57 => six [-233] [-5] [6] [-7] [-39] [-1]
  | 58 => six [-2186] [-7] [8] [-33] [-274] [-1]
  | 59 => six [] [-19] [3] [-5] [1] [-7]
  | 60 => six [] [-19] [3] [5] [-1] [-2]
  | 61 => six [-5] [-3] [3] [-1] [-2] [-1]
  | 62 => six [] [-5] [3] [3] [-1] [1]
  | 63 => six [-10] [-1] [4] [-1] [-2] [-1]
  | 64 => six [-37] [-1] [5] [-6] [-3] [-1]
  | 65 => six [-182] [-4] [5] [-6] [-37] [-1]
  | 66 => six [-27] [-2] [3] [-1] [-10] [-1]
  | 67 => six [-27] [-11] [10] [1] [-3] [-1]
  | 68 => six [-8] [-7] [5] [-1] [-1] [-2]
  | 69 => six [-15] [-2] [3] [-3] [-5] [-1]
  | 70 => six [-38] [-3] [4] [-1] [-10] [-1]
  | 71 => six [-16] [-11] [10] [1] [-2] [-1]
  | 72 => six [-267] [-29] [27] [1] [-10] [-1]
  | 73 => six [-27] [-1] [11] [-2] [-1] [-1]
  | 74 => six [-71] [-11] [27] [4] [-3] [1]
  | 75 => six [-38] [-1] [11] [-3] [-1] [-1]
  | 76 => six [-15] [-3] [8] [-2] [-1] [-1]
  | 77 => six [-9] [-8] [7] [3] [-2] [1]
  | 78 => six [-376] [-41] [38] [1] [-10] [-1]
  | 79 => six [-22] [-11] [16] [3] [-2] [1]
  | 80 => six [-2643] [-29] [267] [11] [-10] [1]
  | 81 => six [-296] [-2] [29] [-10] [-1] [-1]
  | 82 => six [-296] [-10] [11] [-2] [-27] [-1]
  | 83 => six [-55] [-1] [3] [-16] [-11] [-1]
  | 84 => six [-154] [-2] [3] [-16] [-55] [-1]
  | 85 => six [-115] [-1] [4] [-27] [-11] [-1]
  | 86 => six [-417] [-10] [11] [-3] [-38] [-1]
  | 87 => six [-449] [-3] [4] [-27] [-115] [-1]
  | 88 => six [-33] [-1] [3] [-7] [-8] [-1]
  | 89 => six [-91] [-2] [3] [-7] [-33] [-1]
  | 90 => six [-3722] [-41] [376] [11] [-10] [1]
  | 91 => six [-417] [-3] [41] [-10] [-1] [-1]
  | 92 => six [-2962] [-1] [11] [-267] [-29] [-1]
  | 93 => six [-32553] [-10] [11] [-267] [-2962] [-1]
  | 94 => six [-4173] [-1] [11] [-376] [-41] [-1]
  | _ => six [-45862] [-10] [11] [-376] [-4173] [-1]
def finiteNode (i : Fin 96) : Matrix 4 := matrix (finiteP i) 0

private theorem polyFin (i : Fin 16) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 ∨ i=15 := by omega
def polyP (i : Fin 16) : PMatrix := match i.val with
  | 0 => six [-8,-1] [-1] [2] [-3] [-6,-1] [-1]
  | 1 => six [-8,-1] [-1] [2] [1] [-6,-1] [-1]
  | 2 => six [-8,-1] [1] [1] [-7,-1] [-3] [-1]
  | 3 => six [-8,-1] [1] [1] [-5,-1] [-1] [-1]
  | 4 => six [-46,-14,-1] [-7,-1] [6,1] [1] [-8,-1] [-1]
  | 5 => six [-39,-13,-1] [-1] [6,1] [-7,-1] [-1] [-1]
  | 6 => six [-233,-117,-19,-1] [-5,-1] [6,1] [-7,-1] [-39,-13,-1] [-1]
  | 7 => six [-362,-157,-22,-1] [-9,-1] [8,1] [7,1] [-46,-14,-1] [-1]
  | 8 => six [-53,-15,-1] [-1] [7,1] [-8,-1] [-1] [-1]
  | 9 => six [-274,-130,-20,-1] [-1] [8,1] [-33,-12,-1] [-6,-1] [-1]
  | 10 => six [-2186,-1313,-290,-28,-1] [-7,-1] [8,1] [-33,-12,-1] [-274,-130,-20,-1] [-1]
  | 11 => six [-33,-12,-1] [-6,-1] [5,1] [1] [-7,-1] [-1]
  | 12 => six [-425,-173,-23,-1] [-1] [9,1] [-46,-14,-1] [-7,-1] [-1]
  | 13 => six [-370,-158,-22,-1] [-6,-1] [7,1] [-8,-1] [-53,-15,-1] [-1]
  | 14 => six [-3818,-1981,-380,-32,-1] [-8,-1] [9,1] [-46,-14,-1] [-425,-173,-23,-1] [-1]
  | _ => six [-226,-116,-19,-1] [-8,-1] [7,1] [6,1] [-33,-12,-1] [-1]
def polyNode (t : Int) (i : Fin 16) : Matrix 4 := matrix (polyP i) t

def Core (B : Matrix 4) : Prop :=
  (∃ i, B=finiteNode i) ∨ ∃ t : Int, 0≤t ∧ ∃ i, B=polyNode t i
abbrev SafeCore := Safe data Core

theorem finite_safe (i : Fin 96) : SafeCore (finiteNode i) := Safe.central (Or.inl ⟨i,rfl⟩)
theorem poly_safe (t : Int) (ht : 0≤t) (i : Fin 16) : SafeCore (polyNode t i) :=
  Safe.central (Or.inr ⟨t,ht,i,rfl⟩)

def tail (k : Int) (i : Fin 4) : Matrix 4 := match i.val with
  | 0 => ofSix (-k) (-1) 2 (-3) (-k+2) (-1)
  | 1 => ofSix (-k) (-1) 2 1 (-k+2) (-1)
  | 2 => ofSix (-k) 1 1 (-k+1) (-3) (-1)
  | _ => ofSix (-k) 1 1 (-k+3) (-1) (-1)

def tailP (k : P) (i : Fin 4) : PMatrix := match i.val with
  | 0 => six (neg k) [-1] [2] [-3] (add (neg k) [2]) [-1]
  | 1 => six (neg k) [-1] [2] [1] (add (neg k) [2]) [-1]
  | 2 => six (neg k) [1] [1] (add (neg k) [1]) [-3] [-1]
  | _ => six (neg k) [1] [1] (add (neg k) [3]) [-1] [-1]

theorem tailP_eval (k : P) (i : Fin 4) (t : Int) : matrix (tailP k i) t=tail (eval k t) i := by
  have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  rcases hi with rfl|rfl|rfl|rfl <;> simp [tailP,tail,matrix_six,eval_neg,eval_add,eval]

theorem tail_safe (k : Int) (hk : 6≤k) (i : Fin 4) : SafeCore (tail k i) := by
  have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  by_cases he : k=6
  · subst k
    rcases hi with rfl|rfl|rfl|rfl
    · simpa [finiteNode,finiteP,matrix_six,eval,tail] using finite_safe 2
    · simpa [finiteNode,finiteP,matrix_six,eval,tail] using finite_safe 3
    · simpa [finiteNode,finiteP,matrix_six,eval,tail] using finite_safe 4
    · simpa [finiteNode,finiteP,matrix_six,eval,tail] using finite_safe 5
  · by_cases he' : k=7
    · subst k
      rcases hi with rfl|rfl|rfl|rfl
      · simpa [finiteNode,finiteP,matrix_six,eval,tail] using finite_safe 6
      · simpa [finiteNode,finiteP,matrix_six,eval,tail] using finite_safe 7
      · simpa [finiteNode,finiteP,matrix_six,eval,tail] using finite_safe 8
      · simpa [finiteNode,finiteP,matrix_six,eval,tail] using finite_safe 9
    · have ht : 0≤k-8 := by omega
      rcases hi with rfl|rfl|rfl|rfl
      all_goals
        have h0 : polyNode (k-8) 0=tail k 0 := by
          simp only [polyNode,polyP,matrix_six,eval,tail]; congr 1 <;> omega
        have h1 : polyNode (k-8) 1=tail k 1 := by
          simp only [polyNode,polyP,matrix_six,eval,tail]; congr 1 <;> omega
        have h2 : polyNode (k-8) 2=tail k 2 := by
          simp only [polyNode,polyP,matrix_six,eval,tail]; congr 1 <;> omega
        have h3 : polyNode (k-8) 3=tail k 3 := by
          simp only [polyNode,polyP,matrix_six,eval,tail]; congr 1 <;> omega
      · rw [←h0]; exact poly_safe (k-8) ht 0
      · rw [←h1]; exact poly_safe (k-8) ht 1
      · rw [←h2]; exact poly_safe (k-8) ht 2
      · rw [←h3]; exact poly_safe (k-8) ht 3

theorem tailP_safe (k : P) (i : Fin 4) (t : Int) (ht : 0≤t) (hk : leb [6] k=true) :
    SafeCore (matrix (tailP k i) t) := by
  rw [tailP_eval]
  exact tail_safe (eval k t) (by simpa [eval] using le [6] k t ht hk) i

def finiteParam0_0 : P := [3]
def finiteParam0_1 : P := [17]
def finiteParam0_2 : P := [5]
def finiteParam0_3 : P := [6]
theorem finiteDomain0 : GenericStrip.Domain (eval finiteParam0_0 0) (eval finiteParam0_1 0) (eval finiteParam0_2 0) (eval finiteParam0_3 0) :=
  generic_domain finiteParam0_0 finiteParam0_1 finiteParam0_2 finiteParam0_3 0 (by decide) (by decide)
def finiteRegion0 : Region := .inl (.inl ⟨eval finiteParam0_0 0,⟨eval finiteParam0_1 0,eval finiteParam0_2 0,eval finiteParam0_3 0⟩,finiteDomain0⟩)
theorem finiteParent0_0 : data.parent (finiteRegion0) (0 : Fin 3)=(reverse (relabel (matrix (finiteP 19) 0) perm4.symm)) := by
  have he := mutation_equal (generic finiteParam0_0 finiteParam0_1 finiteParam0_2 finiteParam0_3 0) (preverse (prelabel (finiteP 19) perm4.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParent0_1 : data.parent (finiteRegion0) (1 : Fin 3)=(relabel (matrix (tailP [6] 3) 0) perm22.symm) := by
  have he := mutation_equal (generic finiteParam0_0 finiteParam0_1 finiteParam0_2 finiteParam0_3 0) (prelabel (tailP [6] 3) perm22.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParent0_2 : data.parent (finiteRegion0) (2 : Fin 3)=(reverse (relabel (matrix (finiteP 20) 0) perm16.symm)) := by
  have he := mutation_equal (generic finiteParam0_0 finiteParam0_1 finiteParam0_2 finiteParam0_3 2) (preverse (prelabel (finiteP 20) perm16.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParents0_safe (p : Fin 3) : SafeCore (data.parent (finiteRegion0) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hp with rfl|rfl|rfl
  · rw [finiteParent0_0]
    exact Safe.reversed (Safe.framed (finite_safe 19) perm4.symm)
  · rw [finiteParent0_1]
    exact Safe.framed (tailP_safe [6] 3 0 (by decide) (by decide)) perm22.symm
  · rw [finiteParent0_2]
    exact Safe.reversed (Safe.framed (finite_safe 20) perm16.symm)
theorem finiteRegion0_safe (i : Fin 3) : SafeCore (matrix (generic finiteParam0_0 finiteParam0_1 finiteParam0_2 finiteParam0_3 i) 0) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core) (finiteRegion0) (finiteParents0_safe) (0,Fin.castLE (by decide) i)

def finiteParam1_0 : P := [4]
def finiteParam1_1 : P := [27]
def finiteParam1_2 : P := [6]
def finiteParam1_3 : P := [7]
theorem finiteDomain1 : GenericStrip.Domain (eval finiteParam1_0 0) (eval finiteParam1_1 0) (eval finiteParam1_2 0) (eval finiteParam1_3 0) :=
  generic_domain finiteParam1_0 finiteParam1_1 finiteParam1_2 finiteParam1_3 0 (by decide) (by decide)
def finiteRegion1 : Region := .inl (.inl ⟨eval finiteParam1_0 0,⟨eval finiteParam1_1 0,eval finiteParam1_2 0,eval finiteParam1_3 0⟩,finiteDomain1⟩)
theorem finiteParent1_0 : data.parent (finiteRegion1) (0 : Fin 3)=(reverse (relabel (matrix (finiteP 24) 0) perm4.symm)) := by
  have he := mutation_equal (generic finiteParam1_0 finiteParam1_1 finiteParam1_2 finiteParam1_3 0) (preverse (prelabel (finiteP 24) perm4.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParent1_1 : data.parent (finiteRegion1) (1 : Fin 3)=(relabel (matrix (tailP [7] 3) 0) perm22.symm) := by
  have he := mutation_equal (generic finiteParam1_0 finiteParam1_1 finiteParam1_2 finiteParam1_3 0) (prelabel (tailP [7] 3) perm22.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParent1_2 : data.parent (finiteRegion1) (2 : Fin 3)=(reverse (relabel (matrix (finiteP 25) 0) perm16.symm)) := by
  have he := mutation_equal (generic finiteParam1_0 finiteParam1_1 finiteParam1_2 finiteParam1_3 2) (preverse (prelabel (finiteP 25) perm16.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParents1_safe (p : Fin 3) : SafeCore (data.parent (finiteRegion1) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hp with rfl|rfl|rfl
  · rw [finiteParent1_0]
    exact Safe.reversed (Safe.framed (finite_safe 24) perm4.symm)
  · rw [finiteParent1_1]
    exact Safe.framed (tailP_safe [7] 3 0 (by decide) (by decide)) perm22.symm
  · rw [finiteParent1_2]
    exact Safe.reversed (Safe.framed (finite_safe 25) perm16.symm)
theorem finiteRegion1_safe (i : Fin 3) : SafeCore (matrix (generic finiteParam1_0 finiteParam1_1 finiteParam1_2 finiteParam1_3 i) 0) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core) (finiteRegion1) (finiteParents1_safe) (0,Fin.castLE (by decide) i)

def finiteParam2_0 : P := [5]
def finiteParam2_1 : P := [86]
def finiteParam2_2 : P := [13]
def finiteParam2_3 : P := [17]
theorem finiteDomain2 : GenericStrip.Domain (eval finiteParam2_0 0) (eval finiteParam2_1 0) (eval finiteParam2_2 0) (eval finiteParam2_3 0) :=
  generic_domain finiteParam2_0 finiteParam2_1 finiteParam2_2 finiteParam2_3 0 (by decide) (by decide)
def finiteRegion2 : Region := .inl (.inl ⟨eval finiteParam2_0 0,⟨eval finiteParam2_1 0,eval finiteParam2_2 0,eval finiteParam2_3 0⟩,finiteDomain2⟩)
theorem finiteParent2_0 : data.parent (finiteRegion2) (0 : Fin 3)=(reverse (relabel (matrix (finiteP 38) 0) perm4.symm)) := by
  have he := mutation_equal (generic finiteParam2_0 finiteParam2_1 finiteParam2_2 finiteParam2_3 0) (preverse (prelabel (finiteP 38) perm4.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParent2_1 : data.parent (finiteRegion2) (1 : Fin 3)=(relabel (matrix (finiteP 19) 0) perm22.symm) := by
  have he := mutation_equal (generic finiteParam2_0 finiteParam2_1 finiteParam2_2 finiteParam2_3 0) (prelabel (finiteP 19) perm22.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParent2_2 : data.parent (finiteRegion2) (2 : Fin 3)=(reverse (relabel (matrix (finiteP 39) 0) perm16.symm)) := by
  have he := mutation_equal (generic finiteParam2_0 finiteParam2_1 finiteParam2_2 finiteParam2_3 2) (preverse (prelabel (finiteP 39) perm16.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParents2_safe (p : Fin 3) : SafeCore (data.parent (finiteRegion2) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hp with rfl|rfl|rfl
  · rw [finiteParent2_0]
    exact Safe.reversed (Safe.framed (finite_safe 38) perm4.symm)
  · rw [finiteParent2_1]
    exact Safe.framed (finite_safe 19) perm22.symm
  · rw [finiteParent2_2]
    exact Safe.reversed (Safe.framed (finite_safe 39) perm16.symm)
theorem finiteRegion2_safe (i : Fin 3) : SafeCore (matrix (generic finiteParam2_0 finiteParam2_1 finiteParam2_2 finiteParam2_3 i) 0) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core) (finiteRegion2) (finiteParents2_safe) (0,Fin.castLE (by decide) i)

def finiteParam3_0 : P := [6]
def finiteParam3_1 : P := [163]
def finiteParam3_2 : P := [22]
def finiteParam3_3 : P := [27]
theorem finiteDomain3 : GenericStrip.Domain (eval finiteParam3_0 0) (eval finiteParam3_1 0) (eval finiteParam3_2 0) (eval finiteParam3_3 0) :=
  generic_domain finiteParam3_0 finiteParam3_1 finiteParam3_2 finiteParam3_3 0 (by decide) (by decide)
def finiteRegion3 : Region := .inl (.inl ⟨eval finiteParam3_0 0,⟨eval finiteParam3_1 0,eval finiteParam3_2 0,eval finiteParam3_3 0⟩,finiteDomain3⟩)
theorem finiteParent3_0 : data.parent (finiteRegion3) (0 : Fin 3)=(reverse (relabel (matrix (finiteP 43) 0) perm4.symm)) := by
  have he := mutation_equal (generic finiteParam3_0 finiteParam3_1 finiteParam3_2 finiteParam3_3 0) (preverse (prelabel (finiteP 43) perm4.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParent3_1 : data.parent (finiteRegion3) (1 : Fin 3)=(relabel (matrix (finiteP 24) 0) perm22.symm) := by
  have he := mutation_equal (generic finiteParam3_0 finiteParam3_1 finiteParam3_2 finiteParam3_3 0) (prelabel (finiteP 24) perm22.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParent3_2 : data.parent (finiteRegion3) (2 : Fin 3)=(reverse (relabel (matrix (finiteP 44) 0) perm16.symm)) := by
  have he := mutation_equal (generic finiteParam3_0 finiteParam3_1 finiteParam3_2 finiteParam3_3 2) (preverse (prelabel (finiteP 44) perm16.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParents3_safe (p : Fin 3) : SafeCore (data.parent (finiteRegion3) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hp with rfl|rfl|rfl
  · rw [finiteParent3_0]
    exact Safe.reversed (Safe.framed (finite_safe 43) perm4.symm)
  · rw [finiteParent3_1]
    exact Safe.framed (finite_safe 24) perm22.symm
  · rw [finiteParent3_2]
    exact Safe.reversed (Safe.framed (finite_safe 44) perm16.symm)
theorem finiteRegion3_safe (i : Fin 3) : SafeCore (matrix (generic finiteParam3_0 finiteParam3_1 finiteParam3_2 finiteParam3_3 i) 0) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core) (finiteRegion3) (finiteParents3_safe) (0,Fin.castLE (by decide) i)

def finiteParam4_0 : P := [2]
def finiteParam4_1 : P := [9]
def finiteParam4_2 : P := [4]
def finiteParam4_3 : P := [5]
theorem finiteDomain4 : GenericStrip.Domain (eval finiteParam4_0 0) (eval finiteParam4_1 0) (eval finiteParam4_2 0) (eval finiteParam4_3 0) :=
  generic_domain finiteParam4_0 finiteParam4_1 finiteParam4_2 finiteParam4_3 0 (by decide) (by decide)
def finiteRegion4 : Region := .inl (.inl ⟨eval finiteParam4_0 0,⟨eval finiteParam4_1 0,eval finiteParam4_2 0,eval finiteParam4_3 0⟩,finiteDomain4⟩)
theorem finiteParent4_0 : data.parent (finiteRegion4) (0 : Fin 3)=(reverse (relabel (matrix (finiteP 52) 0) perm4.symm)) := by
  have he := mutation_equal (generic finiteParam4_0 finiteParam4_1 finiteParam4_2 finiteParam4_3 0) (preverse (prelabel (finiteP 52) perm4.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParent4_1 : data.parent (finiteRegion4) (1 : Fin 3)=(relabel (matrix (finiteP 36) 0) perm22.symm) := by
  have he := mutation_equal (generic finiteParam4_0 finiteParam4_1 finiteParam4_2 finiteParam4_3 0) (prelabel (finiteP 36) perm22.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParent4_2 : data.parent (finiteRegion4) (2 : Fin 3)=(reverse (relabel (matrix (finiteP 53) 0) perm16.symm)) := by
  have he := mutation_equal (generic finiteParam4_0 finiteParam4_1 finiteParam4_2 finiteParam4_3 2) (preverse (prelabel (finiteP 53) perm16.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParents4_safe (p : Fin 3) : SafeCore (data.parent (finiteRegion4) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hp with rfl|rfl|rfl
  · rw [finiteParent4_0]
    exact Safe.reversed (Safe.framed (finite_safe 52) perm4.symm)
  · rw [finiteParent4_1]
    exact Safe.framed (finite_safe 36) perm22.symm
  · rw [finiteParent4_2]
    exact Safe.reversed (Safe.framed (finite_safe 53) perm16.symm)
theorem finiteRegion4_safe (i : Fin 3) : SafeCore (matrix (generic finiteParam4_0 finiteParam4_1 finiteParam4_2 finiteParam4_3 i) 0) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core) (finiteRegion4) (finiteParents4_safe) (0,Fin.castLE (by decide) i)

def finiteParam5_0 : P := [7]
def finiteParam5_1 : P := [274]
def finiteParam5_2 : P := [33]
def finiteParam5_3 : P := [39]
theorem finiteDomain5 : GenericStrip.Domain (eval finiteParam5_0 0) (eval finiteParam5_1 0) (eval finiteParam5_2 0) (eval finiteParam5_3 0) :=
  generic_domain finiteParam5_0 finiteParam5_1 finiteParam5_2 finiteParam5_3 0 (by decide) (by decide)
def finiteRegion5 : Region := .inl (.inl ⟨eval finiteParam5_0 0,⟨eval finiteParam5_1 0,eval finiteParam5_2 0,eval finiteParam5_3 0⟩,finiteDomain5⟩)
theorem finiteParent5_0 : data.parent (finiteRegion5) (0 : Fin 3)=(reverse (relabel (matrix (finiteP 56) 0) perm4.symm)) := by
  have he := mutation_equal (generic finiteParam5_0 finiteParam5_1 finiteParam5_2 finiteParam5_3 0) (preverse (prelabel (finiteP 56) perm4.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParent5_1 : data.parent (finiteRegion5) (1 : Fin 3)=(relabel (matrix (finiteP 42) 0) perm22.symm) := by
  have he := mutation_equal (generic finiteParam5_0 finiteParam5_1 finiteParam5_2 finiteParam5_3 0) (prelabel (finiteP 42) perm22.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParent5_2 : data.parent (finiteRegion5) (2 : Fin 3)=(reverse (relabel (matrix (finiteP 58) 0) perm16.symm)) := by
  have he := mutation_equal (generic finiteParam5_0 finiteParam5_1 finiteParam5_2 finiteParam5_3 2) (preverse (prelabel (finiteP 58) perm16.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParents5_safe (p : Fin 3) : SafeCore (data.parent (finiteRegion5) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hp with rfl|rfl|rfl
  · rw [finiteParent5_0]
    exact Safe.reversed (Safe.framed (finite_safe 56) perm4.symm)
  · rw [finiteParent5_1]
    exact Safe.framed (finite_safe 42) perm22.symm
  · rw [finiteParent5_2]
    exact Safe.reversed (Safe.framed (finite_safe 58) perm16.symm)
theorem finiteRegion5_safe (i : Fin 3) : SafeCore (matrix (generic finiteParam5_0 finiteParam5_1 finiteParam5_2 finiteParam5_3 i) 0) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core) (finiteRegion5) (finiteParents5_safe) (0,Fin.castLE (by decide) i)

def finiteParam6_0 : P := [5]
def finiteParam6_1 : P := [39]
def finiteParam6_2 : P := [7]
def finiteParam6_3 : P := [8]
theorem finiteDomain6 : GenericStrip.Domain (eval finiteParam6_0 0) (eval finiteParam6_1 0) (eval finiteParam6_2 0) (eval finiteParam6_3 0) :=
  generic_domain finiteParam6_0 finiteParam6_1 finiteParam6_2 finiteParam6_3 0 (by decide) (by decide)
def finiteRegion6 : Region := .inl (.inl ⟨eval finiteParam6_0 0,⟨eval finiteParam6_1 0,eval finiteParam6_2 0,eval finiteParam6_3 0⟩,finiteDomain6⟩)
theorem finiteParent6_0 : data.parent (finiteRegion6) (0 : Fin 3)=(reverse (relabel (matrix (finiteP 42) 0) perm4.symm)) := by
  have he := mutation_equal (generic finiteParam6_0 finiteParam6_1 finiteParam6_2 finiteParam6_3 0) (preverse (prelabel (finiteP 42) perm4.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParent6_1 : data.parent (finiteRegion6) (1 : Fin 3)=(relabel (matrix (tailP [8] 3) 0) perm22.symm) := by
  have he := mutation_equal (generic finiteParam6_0 finiteParam6_1 finiteParam6_2 finiteParam6_3 0) (prelabel (tailP [8] 3) perm22.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParent6_2 : data.parent (finiteRegion6) (2 : Fin 3)=(reverse (relabel (matrix (finiteP 57) 0) perm16.symm)) := by
  have he := mutation_equal (generic finiteParam6_0 finiteParam6_1 finiteParam6_2 finiteParam6_3 2) (preverse (prelabel (finiteP 57) perm16.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParents6_safe (p : Fin 3) : SafeCore (data.parent (finiteRegion6) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hp with rfl|rfl|rfl
  · rw [finiteParent6_0]
    exact Safe.reversed (Safe.framed (finite_safe 42) perm4.symm)
  · rw [finiteParent6_1]
    exact Safe.framed (tailP_safe [8] 3 0 (by decide) (by decide)) perm22.symm
  · rw [finiteParent6_2]
    exact Safe.reversed (Safe.framed (finite_safe 57) perm16.symm)
theorem finiteRegion6_safe (i : Fin 3) : SafeCore (matrix (generic finiteParam6_0 finiteParam6_1 finiteParam6_2 finiteParam6_3 i) 0) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core) (finiteRegion6) (finiteParents6_safe) (0,Fin.castLE (by decide) i)

def finiteParam7_0 : P := [3]
def finiteParam7_1 : P := [3]
def finiteParam7_2 : P := [5]
def finiteParam7_3 : P := [13]
theorem finiteDomain7 : UnitZeroStrip.Domain (eval finiteParam7_0 0) (eval finiteParam7_1 0) (eval finiteParam7_2 0) (eval finiteParam7_3 0) :=
  zero_domain finiteParam7_0 finiteParam7_1 finiteParam7_2 finiteParam7_3 0 (by decide) (by decide)
def finiteRegion7 : Region := .inl (.inr (.n (eval finiteParam7_0 0) ⟨eval finiteParam7_1 0,eval finiteParam7_2 0,eval finiteParam7_3 0⟩ (finiteDomain7)))
theorem finiteParent7_0 : data.parent (finiteRegion7) (0 : Fin 2)=(relabel (matrix (finiteP 49) 0) perm6.symm) := by
  have he := mutation_equal (zero finiteParam7_0 finiteParam7_1 finiteParam7_2 finiteParam7_3 0) (prelabel (finiteP 49) perm6.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,zero_eval] at he
  exact he

theorem finiteParent7_1 : data.parent (finiteRegion7) (1 : Fin 2)=(relabel (matrix (finiteP 62) 0) perm6.symm) := by
  have he := mutation_equal (zero finiteParam7_0 finiteParam7_1 finiteParam7_2 finiteParam7_3 1) (prelabel (finiteP 62) perm6.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,zero_eval] at he
  exact he

theorem finiteParents7_safe (p : Fin 2) : SafeCore (data.parent (finiteRegion7) p) := by
  have hp : p=0 ∨ p=1 := by change p=(0 : Fin 2) ∨ p=(1 : Fin 2); omega
  rcases hp with rfl|rfl
  · rw [finiteParent7_0]
    exact Safe.framed (finite_safe 49) perm6.symm
  · rw [finiteParent7_1]
    exact Safe.framed (finite_safe 62) perm6.symm
theorem finiteRegion7_safe (i : Fin 2) : SafeCore (matrix (zero finiteParam7_0 finiteParam7_1 finiteParam7_2 finiteParam7_3 i) 0) := by
  rw [zero_eval]
  exact Safe.region (D:=data) (core:=Core) (finiteRegion7) (finiteParents7_safe) (0,Fin.castLE (by decide) i)

def finiteParam8_0 : P := [4]
def finiteParam8_1 : P := [37]
def finiteParam8_2 : P := [6]
def finiteParam8_3 : P := [9]
theorem finiteDomain8 : GenericStrip.Domain (eval finiteParam8_0 0) (eval finiteParam8_1 0) (eval finiteParam8_2 0) (eval finiteParam8_3 0) :=
  generic_domain finiteParam8_0 finiteParam8_1 finiteParam8_2 finiteParam8_3 0 (by decide) (by decide)
def finiteRegion8 : Region := .inl (.inl ⟨eval finiteParam8_0 0,⟨eval finiteParam8_1 0,eval finiteParam8_2 0,eval finiteParam8_3 0⟩,finiteDomain8⟩)
theorem finiteParent8_0 : data.parent (finiteRegion8) (0 : Fin 3)=(reverse (relabel (matrix (finiteP 64) 0) perm4.symm)) := by
  have he := mutation_equal (generic finiteParam8_0 finiteParam8_1 finiteParam8_2 finiteParam8_3 0) (preverse (prelabel (finiteP 64) perm4.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParent8_1 : data.parent (finiteRegion8) (1 : Fin 3)=(relabel (matrix (finiteP 52) 0) perm22.symm) := by
  have he := mutation_equal (generic finiteParam8_0 finiteParam8_1 finiteParam8_2 finiteParam8_3 0) (prelabel (finiteP 52) perm22.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParent8_2 : data.parent (finiteRegion8) (2 : Fin 3)=(reverse (relabel (matrix (finiteP 65) 0) perm16.symm)) := by
  have he := mutation_equal (generic finiteParam8_0 finiteParam8_1 finiteParam8_2 finiteParam8_3 2) (preverse (prelabel (finiteP 65) perm16.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParents8_safe (p : Fin 3) : SafeCore (data.parent (finiteRegion8) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hp with rfl|rfl|rfl
  · rw [finiteParent8_0]
    exact Safe.reversed (Safe.framed (finite_safe 64) perm4.symm)
  · rw [finiteParent8_1]
    exact Safe.framed (finite_safe 52) perm22.symm
  · rw [finiteParent8_2]
    exact Safe.reversed (Safe.framed (finite_safe 65) perm16.symm)
theorem finiteRegion8_safe (i : Fin 3) : SafeCore (matrix (generic finiteParam8_0 finiteParam8_1 finiteParam8_2 finiteParam8_3 i) 0) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core) (finiteRegion8) (finiteParents8_safe) (0,Fin.castLE (by decide) i)

def finiteParam9_0 : P := [3]
def finiteParam9_1 : P := [5]
def finiteParam9_2 : P := [19]
def finiteParam9_3 : P := [50]
theorem finiteDomain9 : UnitZeroStrip.Domain (eval finiteParam9_0 0) (eval finiteParam9_1 0) (eval finiteParam9_2 0) (eval finiteParam9_3 0) :=
  zero_domain finiteParam9_0 finiteParam9_1 finiteParam9_2 finiteParam9_3 0 (by decide) (by decide)
def finiteRegion9 : Region := .inl (.inr (.n (eval finiteParam9_0 0) ⟨eval finiteParam9_1 0,eval finiteParam9_2 0,eval finiteParam9_3 0⟩ (finiteDomain9)))
theorem finiteParent9_0 : data.parent (finiteRegion9) (0 : Fin 2)=(relabel (matrix (finiteP 59) 0) perm6.symm) := by
  have he := mutation_equal (zero finiteParam9_0 finiteParam9_1 finiteParam9_2 finiteParam9_3 0) (prelabel (finiteP 59) perm6.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,zero_eval] at he
  exact he

theorem finiteParent9_1 : data.parent (finiteRegion9) (1 : Fin 2)=(relabel (matrix (finiteP 60) 0) perm6.symm) := by
  have he := mutation_equal (zero finiteParam9_0 finiteParam9_1 finiteParam9_2 finiteParam9_3 1) (prelabel (finiteP 60) perm6.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,zero_eval] at he
  exact he

theorem finiteParents9_safe (p : Fin 2) : SafeCore (data.parent (finiteRegion9) p) := by
  have hp : p=0 ∨ p=1 := by change p=(0 : Fin 2) ∨ p=(1 : Fin 2); omega
  rcases hp with rfl|rfl
  · rw [finiteParent9_0]
    exact Safe.framed (finite_safe 59) perm6.symm
  · rw [finiteParent9_1]
    exact Safe.framed (finite_safe 60) perm6.symm
theorem finiteRegion9_safe (i : Fin 2) : SafeCore (matrix (zero finiteParam9_0 finiteParam9_1 finiteParam9_2 finiteParam9_3 i) 0) := by
  rw [zero_eval]
  exact Safe.region (D:=data) (core:=Core) (finiteRegion9) (finiteParents9_safe) (0,Fin.castLE (by decide) i)

def finiteParam10_0 : P := [2]
def finiteParam10_1 : P := [55]
def finiteParam10_2 : P := [16]
def finiteParam10_3 : P := [27]
theorem finiteDomain10 : GenericStrip.Domain (eval finiteParam10_0 0) (eval finiteParam10_1 0) (eval finiteParam10_2 0) (eval finiteParam10_3 0) :=
  generic_domain finiteParam10_0 finiteParam10_1 finiteParam10_2 finiteParam10_3 0 (by decide) (by decide)
def finiteRegion10 : Region := .inl (.inl ⟨eval finiteParam10_0 0,⟨eval finiteParam10_1 0,eval finiteParam10_2 0,eval finiteParam10_3 0⟩,finiteDomain10⟩)
theorem finiteParent10_0 : data.parent (finiteRegion10) (0 : Fin 3)=(reverse (relabel (matrix (finiteP 83) 0) perm4.symm)) := by
  have he := mutation_equal (generic finiteParam10_0 finiteParam10_1 finiteParam10_2 finiteParam10_3 0) (preverse (prelabel (finiteP 83) perm4.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParent10_1 : data.parent (finiteRegion10) (1 : Fin 3)=(relabel (matrix (finiteP 73) 0) perm22.symm) := by
  have he := mutation_equal (generic finiteParam10_0 finiteParam10_1 finiteParam10_2 finiteParam10_3 0) (prelabel (finiteP 73) perm22.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParent10_2 : data.parent (finiteRegion10) (2 : Fin 3)=(reverse (relabel (matrix (finiteP 84) 0) perm16.symm)) := by
  have he := mutation_equal (generic finiteParam10_0 finiteParam10_1 finiteParam10_2 finiteParam10_3 2) (preverse (prelabel (finiteP 84) perm16.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParents10_safe (p : Fin 3) : SafeCore (data.parent (finiteRegion10) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hp with rfl|rfl|rfl
  · rw [finiteParent10_0]
    exact Safe.reversed (Safe.framed (finite_safe 83) perm4.symm)
  · rw [finiteParent10_1]
    exact Safe.framed (finite_safe 73) perm22.symm
  · rw [finiteParent10_2]
    exact Safe.reversed (Safe.framed (finite_safe 84) perm16.symm)
theorem finiteRegion10_safe (i : Fin 3) : SafeCore (matrix (generic finiteParam10_0 finiteParam10_1 finiteParam10_2 finiteParam10_3 i) 0) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core) (finiteRegion10) (finiteParents10_safe) (0,Fin.castLE (by decide) i)

def finiteParam11_0 : P := [3]
def finiteParam11_1 : P := [115]
def finiteParam11_2 : P := [27]
def finiteParam11_3 : P := [38]
theorem finiteDomain11 : GenericStrip.Domain (eval finiteParam11_0 0) (eval finiteParam11_1 0) (eval finiteParam11_2 0) (eval finiteParam11_3 0) :=
  generic_domain finiteParam11_0 finiteParam11_1 finiteParam11_2 finiteParam11_3 0 (by decide) (by decide)
def finiteRegion11 : Region := .inl (.inl ⟨eval finiteParam11_0 0,⟨eval finiteParam11_1 0,eval finiteParam11_2 0,eval finiteParam11_3 0⟩,finiteDomain11⟩)
theorem finiteParent11_0 : data.parent (finiteRegion11) (0 : Fin 3)=(reverse (relabel (matrix (finiteP 85) 0) perm4.symm)) := by
  have he := mutation_equal (generic finiteParam11_0 finiteParam11_1 finiteParam11_2 finiteParam11_3 0) (preverse (prelabel (finiteP 85) perm4.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParent11_1 : data.parent (finiteRegion11) (1 : Fin 3)=(relabel (matrix (finiteP 75) 0) perm22.symm) := by
  have he := mutation_equal (generic finiteParam11_0 finiteParam11_1 finiteParam11_2 finiteParam11_3 0) (prelabel (finiteP 75) perm22.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParent11_2 : data.parent (finiteRegion11) (2 : Fin 3)=(reverse (relabel (matrix (finiteP 87) 0) perm16.symm)) := by
  have he := mutation_equal (generic finiteParam11_0 finiteParam11_1 finiteParam11_2 finiteParam11_3 2) (preverse (prelabel (finiteP 87) perm16.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParents11_safe (p : Fin 3) : SafeCore (data.parent (finiteRegion11) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hp with rfl|rfl|rfl
  · rw [finiteParent11_0]
    exact Safe.reversed (Safe.framed (finite_safe 85) perm4.symm)
  · rw [finiteParent11_1]
    exact Safe.framed (finite_safe 75) perm22.symm
  · rw [finiteParent11_2]
    exact Safe.reversed (Safe.framed (finite_safe 87) perm16.symm)
theorem finiteRegion11_safe (i : Fin 3) : SafeCore (matrix (generic finiteParam11_0 finiteParam11_1 finiteParam11_2 finiteParam11_3 i) 0) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core) (finiteRegion11) (finiteParents11_safe) (0,Fin.castLE (by decide) i)

def finiteParam12_0 : P := [2]
def finiteParam12_1 : P := [33]
def finiteParam12_2 : P := [7]
def finiteParam12_3 : P := [15]
theorem finiteDomain12 : GenericStrip.Domain (eval finiteParam12_0 0) (eval finiteParam12_1 0) (eval finiteParam12_2 0) (eval finiteParam12_3 0) :=
  generic_domain finiteParam12_0 finiteParam12_1 finiteParam12_2 finiteParam12_3 0 (by decide) (by decide)
def finiteRegion12 : Region := .inl (.inl ⟨eval finiteParam12_0 0,⟨eval finiteParam12_1 0,eval finiteParam12_2 0,eval finiteParam12_3 0⟩,finiteDomain12⟩)
theorem finiteParent12_0 : data.parent (finiteRegion12) (0 : Fin 3)=(reverse (relabel (matrix (finiteP 88) 0) perm4.symm)) := by
  have he := mutation_equal (generic finiteParam12_0 finiteParam12_1 finiteParam12_2 finiteParam12_3 0) (preverse (prelabel (finiteP 88) perm4.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParent12_1 : data.parent (finiteRegion12) (1 : Fin 3)=(relabel (matrix (finiteP 76) 0) perm22.symm) := by
  have he := mutation_equal (generic finiteParam12_0 finiteParam12_1 finiteParam12_2 finiteParam12_3 0) (prelabel (finiteP 76) perm22.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParent12_2 : data.parent (finiteRegion12) (2 : Fin 3)=(reverse (relabel (matrix (finiteP 89) 0) perm16.symm)) := by
  have he := mutation_equal (generic finiteParam12_0 finiteParam12_1 finiteParam12_2 finiteParam12_3 2) (preverse (prelabel (finiteP 89) perm16.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParents12_safe (p : Fin 3) : SafeCore (data.parent (finiteRegion12) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hp with rfl|rfl|rfl
  · rw [finiteParent12_0]
    exact Safe.reversed (Safe.framed (finite_safe 88) perm4.symm)
  · rw [finiteParent12_1]
    exact Safe.framed (finite_safe 76) perm22.symm
  · rw [finiteParent12_2]
    exact Safe.reversed (Safe.framed (finite_safe 89) perm16.symm)
theorem finiteRegion12_safe (i : Fin 3) : SafeCore (matrix (generic finiteParam12_0 finiteParam12_1 finiteParam12_2 finiteParam12_3 i) 0) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core) (finiteRegion12) (finiteParents12_safe) (0,Fin.castLE (by decide) i)

def finiteParam13_0 : P := [10]
def finiteParam13_1 : P := [2962]
def finiteParam13_2 : P := [267]
def finiteParam13_3 : P := [296]
theorem finiteDomain13 : GenericStrip.Domain (eval finiteParam13_0 0) (eval finiteParam13_1 0) (eval finiteParam13_2 0) (eval finiteParam13_3 0) :=
  generic_domain finiteParam13_0 finiteParam13_1 finiteParam13_2 finiteParam13_3 0 (by decide) (by decide)
def finiteRegion13 : Region := .inl (.inl ⟨eval finiteParam13_0 0,⟨eval finiteParam13_1 0,eval finiteParam13_2 0,eval finiteParam13_3 0⟩,finiteDomain13⟩)
theorem finiteParent13_0 : data.parent (finiteRegion13) (0 : Fin 3)=(reverse (relabel (matrix (finiteP 92) 0) perm4.symm)) := by
  have he := mutation_equal (generic finiteParam13_0 finiteParam13_1 finiteParam13_2 finiteParam13_3 0) (preverse (prelabel (finiteP 92) perm4.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParent13_1 : data.parent (finiteRegion13) (1 : Fin 3)=(relabel (matrix (finiteP 81) 0) perm22.symm) := by
  have he := mutation_equal (generic finiteParam13_0 finiteParam13_1 finiteParam13_2 finiteParam13_3 0) (prelabel (finiteP 81) perm22.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParent13_2 : data.parent (finiteRegion13) (2 : Fin 3)=(reverse (relabel (matrix (finiteP 93) 0) perm16.symm)) := by
  have he := mutation_equal (generic finiteParam13_0 finiteParam13_1 finiteParam13_2 finiteParam13_3 2) (preverse (prelabel (finiteP 93) perm16.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParents13_safe (p : Fin 3) : SafeCore (data.parent (finiteRegion13) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hp with rfl|rfl|rfl
  · rw [finiteParent13_0]
    exact Safe.reversed (Safe.framed (finite_safe 92) perm4.symm)
  · rw [finiteParent13_1]
    exact Safe.framed (finite_safe 81) perm22.symm
  · rw [finiteParent13_2]
    exact Safe.reversed (Safe.framed (finite_safe 93) perm16.symm)
theorem finiteRegion13_safe (i : Fin 3) : SafeCore (matrix (generic finiteParam13_0 finiteParam13_1 finiteParam13_2 finiteParam13_3 i) 0) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core) (finiteRegion13) (finiteParents13_safe) (0,Fin.castLE (by decide) i)

def finiteParam14_0 : P := [10]
def finiteParam14_1 : P := [4173]
def finiteParam14_2 : P := [376]
def finiteParam14_3 : P := [417]
theorem finiteDomain14 : GenericStrip.Domain (eval finiteParam14_0 0) (eval finiteParam14_1 0) (eval finiteParam14_2 0) (eval finiteParam14_3 0) :=
  generic_domain finiteParam14_0 finiteParam14_1 finiteParam14_2 finiteParam14_3 0 (by decide) (by decide)
def finiteRegion14 : Region := .inl (.inl ⟨eval finiteParam14_0 0,⟨eval finiteParam14_1 0,eval finiteParam14_2 0,eval finiteParam14_3 0⟩,finiteDomain14⟩)
theorem finiteParent14_0 : data.parent (finiteRegion14) (0 : Fin 3)=(reverse (relabel (matrix (finiteP 94) 0) perm4.symm)) := by
  have he := mutation_equal (generic finiteParam14_0 finiteParam14_1 finiteParam14_2 finiteParam14_3 0) (preverse (prelabel (finiteP 94) perm4.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParent14_1 : data.parent (finiteRegion14) (1 : Fin 3)=(relabel (matrix (finiteP 91) 0) perm22.symm) := by
  have he := mutation_equal (generic finiteParam14_0 finiteParam14_1 finiteParam14_2 finiteParam14_3 0) (prelabel (finiteP 91) perm22.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParent14_2 : data.parent (finiteRegion14) (2 : Fin 3)=(reverse (relabel (matrix (finiteP 95) 0) perm16.symm)) := by
  have he := mutation_equal (generic finiteParam14_0 finiteParam14_1 finiteParam14_2 finiteParam14_3 2) (preverse (prelabel (finiteP 95) perm16.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem finiteParents14_safe (p : Fin 3) : SafeCore (data.parent (finiteRegion14) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by change p=(0 : Fin 3) ∨ p=(1 : Fin 3) ∨ p=(2 : Fin 3); omega
  rcases hp with rfl|rfl|rfl
  · rw [finiteParent14_0]
    exact Safe.reversed (Safe.framed (finite_safe 94) perm4.symm)
  · rw [finiteParent14_1]
    exact Safe.framed (finite_safe 91) perm22.symm
  · rw [finiteParent14_2]
    exact Safe.reversed (Safe.framed (finite_safe 95) perm16.symm)
theorem finiteRegion14_safe (i : Fin 3) : SafeCore (matrix (generic finiteParam14_0 finiteParam14_1 finiteParam14_2 finiteParam14_3 i) 0) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core) (finiteRegion14) (finiteParents14_safe) (0,Fin.castLE (by decide) i)

theorem finite_skew (i : Fin 96) : SkewSymmetric (finiteNode i) := by
  rcases finiteFin i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp only [finiteNode,finiteP,matrix_six] <;> exact ofSix_skew _ _ _ _ _ _

theorem finiteCyclic0 : ¬ Acyclic (finiteNode 0) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 1 3 (pos (finiteP 0 1 3) 0 (by decide) (by decide))
  have h1 := hr 3 2 (pos (finiteP 0 3 2) 0 (by decide) (by decide))
  have h2 := hr 2 1 (pos (finiteP 0 2 1) 0 (by decide) (by decide))
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
  have h0 := hr 0 3 (pos (finiteP 3 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 3 3 1) 0 (by decide) (by decide))
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
  have h1 := hr 3 1 (pos (finiteP 6 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 6 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic7 : ¬ Acyclic (finiteNode 7) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 7 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 7 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 7 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic8 : ¬ Acyclic (finiteNode 8) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (finiteP 8 0 2) 0 (by decide) (by decide))
  have h1 := hr 2 1 (pos (finiteP 8 2 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 8 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic9 : ¬ Acyclic (finiteNode 9) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (finiteP 9 0 2) 0 (by decide) (by decide))
  have h1 := hr 2 1 (pos (finiteP 9 2 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 9 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic10 : ¬ Acyclic (finiteNode 10) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 1 2 (pos (finiteP 10 1 2) 0 (by decide) (by decide))
  have h1 := hr 2 3 (pos (finiteP 10 2 3) 0 (by decide) (by decide))
  have h2 := hr 3 1 (pos (finiteP 10 3 1) 0 (by decide) (by decide))
  omega

theorem finiteCyclic11 : ¬ Acyclic (finiteNode 11) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 11 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 2 (pos (finiteP 11 3 2) 0 (by decide) (by decide))
  have h2 := hr 2 0 (pos (finiteP 11 2 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic12 : ¬ Acyclic (finiteNode 12) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 1 3 (pos (finiteP 12 1 3) 0 (by decide) (by decide))
  have h1 := hr 3 2 (pos (finiteP 12 3 2) 0 (by decide) (by decide))
  have h2 := hr 2 1 (pos (finiteP 12 2 1) 0 (by decide) (by decide))
  omega

theorem finiteCyclic13 : ¬ Acyclic (finiteNode 13) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 13 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 13 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 13 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic14 : ¬ Acyclic (finiteNode 14) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 14 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 14 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 14 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic15 : ¬ Acyclic (finiteNode 15) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 15 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 15 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 15 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic16 : ¬ Acyclic (finiteNode 16) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 16 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 16 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 16 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic17 : ¬ Acyclic (finiteNode 17) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 17 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 17 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 17 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic18 : ¬ Acyclic (finiteNode 18) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 18 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 18 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 18 1 0) 0 (by decide) (by decide))
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
  have h1 := hr 3 1 (pos (finiteP 20 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 20 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic21 : ¬ Acyclic (finiteNode 21) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (finiteP 21 0 2) 0 (by decide) (by decide))
  have h1 := hr 2 1 (pos (finiteP 21 2 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 21 1 0) 0 (by decide) (by decide))
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
  have h0 := hr 0 2 (pos (finiteP 26 0 2) 0 (by decide) (by decide))
  have h1 := hr 2 1 (pos (finiteP 26 2 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 26 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic27 : ¬ Acyclic (finiteNode 27) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 27 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 2 (pos (finiteP 27 3 2) 0 (by decide) (by decide))
  have h2 := hr 2 0 (pos (finiteP 27 2 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic28 : ¬ Acyclic (finiteNode 28) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 28 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 2 (pos (finiteP 28 3 2) 0 (by decide) (by decide))
  have h2 := hr 2 0 (pos (finiteP 28 2 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic29 : ¬ Acyclic (finiteNode 29) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 1 2 (pos (finiteP 29 1 2) 0 (by decide) (by decide))
  have h1 := hr 2 3 (pos (finiteP 29 2 3) 0 (by decide) (by decide))
  have h2 := hr 3 1 (pos (finiteP 29 3 1) 0 (by decide) (by decide))
  omega

theorem finiteCyclic30 : ¬ Acyclic (finiteNode 30) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 30 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 2 (pos (finiteP 30 3 2) 0 (by decide) (by decide))
  have h2 := hr 2 0 (pos (finiteP 30 2 0) 0 (by decide) (by decide))
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
  have h1 := hr 3 1 (pos (finiteP 32 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 32 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic33 : ¬ Acyclic (finiteNode 33) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (finiteP 33 0 2) 0 (by decide) (by decide))
  have h1 := hr 2 1 (pos (finiteP 33 2 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 33 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic34 : ¬ Acyclic (finiteNode 34) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 34 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 34 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 34 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic35 : ¬ Acyclic (finiteNode 35) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 35 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 35 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 35 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic36 : ¬ Acyclic (finiteNode 36) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (pos (finiteP 36 0 2) 0 (by decide) (by decide))
  have h1 := hr 2 1 (pos (finiteP 36 2 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 36 1 0) 0 (by decide) (by decide))
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
  have h1 := hr 3 1 (pos (finiteP 38 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 38 1 0) 0 (by decide) (by decide))
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
  have h1 := hr 3 2 (pos (finiteP 46 3 2) 0 (by decide) (by decide))
  have h2 := hr 2 0 (pos (finiteP 46 2 0) 0 (by decide) (by decide))
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
  have h0 := hr 0 3 (pos (finiteP 52 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 52 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 52 1 0) 0 (by decide) (by decide))
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
  have h1 := hr 3 2 (pos (finiteP 59 3 2) 0 (by decide) (by decide))
  have h2 := hr 2 0 (pos (finiteP 59 2 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic60 : ¬ Acyclic (finiteNode 60) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 60 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 2 (pos (finiteP 60 3 2) 0 (by decide) (by decide))
  have h2 := hr 2 0 (pos (finiteP 60 2 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic61 : ¬ Acyclic (finiteNode 61) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 61 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 61 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 61 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic62 : ¬ Acyclic (finiteNode 62) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 1 2 (pos (finiteP 62 1 2) 0 (by decide) (by decide))
  have h1 := hr 2 3 (pos (finiteP 62 2 3) 0 (by decide) (by decide))
  have h2 := hr 3 1 (pos (finiteP 62 3 1) 0 (by decide) (by decide))
  omega

theorem finiteCyclic63 : ¬ Acyclic (finiteNode 63) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 63 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 63 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 63 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic64 : ¬ Acyclic (finiteNode 64) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 64 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 64 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 64 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic65 : ¬ Acyclic (finiteNode 65) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 65 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 65 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 65 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic66 : ¬ Acyclic (finiteNode 66) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 66 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 66 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 66 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic67 : ¬ Acyclic (finiteNode 67) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 67 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 67 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 67 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic68 : ¬ Acyclic (finiteNode 68) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 68 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 68 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 68 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic69 : ¬ Acyclic (finiteNode 69) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 69 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 69 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 69 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic70 : ¬ Acyclic (finiteNode 70) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 70 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 70 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 70 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic71 : ¬ Acyclic (finiteNode 71) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 71 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 71 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 71 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic72 : ¬ Acyclic (finiteNode 72) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 72 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 72 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 72 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic73 : ¬ Acyclic (finiteNode 73) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 73 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 73 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 73 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic74 : ¬ Acyclic (finiteNode 74) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 74 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 74 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 74 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic75 : ¬ Acyclic (finiteNode 75) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 75 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 75 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 75 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic76 : ¬ Acyclic (finiteNode 76) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 76 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 76 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 76 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic77 : ¬ Acyclic (finiteNode 77) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 77 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 77 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 77 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic78 : ¬ Acyclic (finiteNode 78) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 78 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 78 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 78 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic79 : ¬ Acyclic (finiteNode 79) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 79 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 79 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 79 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic80 : ¬ Acyclic (finiteNode 80) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 80 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 80 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 80 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic81 : ¬ Acyclic (finiteNode 81) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 81 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 81 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 81 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic82 : ¬ Acyclic (finiteNode 82) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 82 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 82 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 82 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic83 : ¬ Acyclic (finiteNode 83) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 83 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 83 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 83 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic84 : ¬ Acyclic (finiteNode 84) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 84 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 84 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 84 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic85 : ¬ Acyclic (finiteNode 85) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 85 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 85 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 85 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic86 : ¬ Acyclic (finiteNode 86) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 86 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 86 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 86 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic87 : ¬ Acyclic (finiteNode 87) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 87 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 87 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 87 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic88 : ¬ Acyclic (finiteNode 88) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 88 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 88 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 88 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic89 : ¬ Acyclic (finiteNode 89) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 89 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 89 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 89 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic90 : ¬ Acyclic (finiteNode 90) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 90 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 90 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 90 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic91 : ¬ Acyclic (finiteNode 91) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 91 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 91 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 91 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic92 : ¬ Acyclic (finiteNode 92) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 92 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 92 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 92 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic93 : ¬ Acyclic (finiteNode 93) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 93 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 93 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 93 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic94 : ¬ Acyclic (finiteNode 94) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 94 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 94 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 94 1 0) 0 (by decide) (by decide))
  omega

theorem finiteCyclic95 : ¬ Acyclic (finiteNode 95) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (pos (finiteP 95 0 3) 0 (by decide) (by decide))
  have h1 := hr 3 1 (pos (finiteP 95 3 1) 0 (by decide) (by decide))
  have h2 := hr 1 0 (pos (finiteP 95 1 0) 0 (by decide) (by decide))
  omega

theorem finiteEdge0_0 : SafeCore (mutate (finiteNode 0) 0) := by
  have he := mutation_equal (finiteP 0) (preverse (prelabel (finiteP 10) perm0.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 0) 0) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 10) perm0.symm)

theorem finiteEdge0_1 : SafeCore (mutate (finiteNode 0) 1) := by
  have he := mutation_equal (finiteP 0) (prelabel (finiteP 10) perm0.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 0) 0) 1)
  rw [he]
  exact Safe.framed (finite_safe 10) perm0.symm

theorem finiteEdge0_2 : SafeCore (mutate (finiteNode 0) 2) := by
  have he := mutation_equal (finiteP 0) (prelabel (finiteP 11) perm1.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 0) 0) 2)
  rw [he]
  exact Safe.framed (finite_safe 11) perm1.symm

theorem finiteEdge0_3 : SafeCore (mutate (finiteNode 0) 3) := by
  have he := mutation_equal (finiteP 0) (preverse (prelabel (finiteP 12) perm13.symm)) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 0) 0) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 12) perm13.symm)

theorem finiteEdge1_0 : SafeCore (mutate (finiteNode 1) 0) := by
  have he := mutation_equal (finiteP 1) (prelabel (finiteP 13) perm23.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 1) 0) 0)
  rw [he]
  exact Safe.framed (finite_safe 13) perm23.symm

theorem finiteEdge1_1 : SafeCore (mutate (finiteNode 1) 1) := by
  have he := mutation_equal (finiteP 1) (preverse (prelabel (finiteP 14) perm13.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 1) 0) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 14) perm13.symm)

theorem finiteEdge1_2 : SafeCore (mutate (finiteNode 1) 2) := by
  have he := mutation_equal (finiteP 1) (preverse (prelabel (finiteP 1) perm6.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 1) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 1) perm6.symm)

theorem finiteEdge1_3 : SafeCore (mutate (finiteNode 1) 3) := by
  have he := mutation_equal (finiteP 1) (preverse (prelabel (finiteP 1) perm14.symm)) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 1) 0) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 1) perm14.symm)

theorem finiteEdge2_0 : SafeCore (mutate (finiteNode 2) 0) := by
  have he := mutation_equal (finiteP 2) (prelabel (tailP [8] 0) perm21.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 2) 0) 0)
  rw [he]
  exact Safe.framed (tailP_safe [8] 0 0 (by decide) (by decide)) perm21.symm

theorem finiteEdge2_1 : SafeCore (mutate (finiteNode 2) 1) := by
  have he := mutation_equal (finiteP 2) (preverse (prelabel (root [6] [19] [22] [3] [4] [1]) perm6.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 2) 1
  rw [show mutate (finiteNode 2) 1=(reverse (relabel (matrix (root [6] [19] [22] [3] [4] [1]) 0) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [6] [19] [22] [3] [4] [1] 0 (by decide) (by decide)) perm6.symm)

theorem finiteEdge2_2 : SafeCore (mutate (finiteNode 2) 2) := by
  have he := mutation_equal (finiteP 2) (preverse (prelabel (tailP [7] 2) perm20.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 2) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (tailP_safe [7] 2 0 (by decide) (by decide)) perm20.symm)

theorem finiteEdge2_3 : SafeCore (mutate (finiteNode 2) 3) := by
  have he := mutation_equal (finiteP 2) (prelabel (finiteP 15) perm21.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 2) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 15) perm21.symm

theorem finiteEdge3_0 : SafeCore (mutate (finiteNode 3) 0) := by
  have he := mutation_equal (finiteP 3) (prelabel (tailP [8] 1) perm21.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 3) 0) 0)
  rw [he]
  exact Safe.framed (tailP_safe [8] 1 0 (by decide) (by decide)) perm21.symm

theorem finiteEdge3_1 : SafeCore (mutate (finiteNode 3) 1) := by
  have he := mutation_equal (finiteP 3) (preverse (prelabel (finiteP 16) perm19.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 3) 0) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 16) perm19.symm)

theorem finiteEdge3_2 : SafeCore (mutate (finiteNode 3) 2) := by
  have he := mutation_equal (finiteP 3) (prelabel (tailP [7] 3) perm1.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 3) 0) 2)
  rw [he]
  exact Safe.framed (tailP_safe [7] 3 0 (by decide) (by decide)) perm1.symm

theorem finiteEdge3_3 : SafeCore (mutate (finiteNode 3) 3) := by
  have he := mutation_equal (finiteP 3) (prelabel (finiteP 17) perm21.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 3) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 17) perm21.symm

theorem finiteEdge4_0 : SafeCore (mutate (finiteNode 4) 0) := by
  have he := mutation_equal (finiteP 4) (preverse (prelabel (tailP [6] 3) perm1.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 4) 0) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (tailP_safe [6] 3 0 (by decide) (by decide)) perm1.symm)

theorem finiteEdge4_1 : SafeCore (mutate (finiteNode 4) 1) := by
  have he := mutation_equal (finiteP 4) (preverse (prelabel (root [6] [29] [17] [5] [3] [1]) perm6.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 4) 1
  rw [show mutate (finiteNode 4) 1=(reverse (relabel (matrix (root [6] [29] [17] [5] [3] [1]) 0) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [6] [29] [17] [5] [3] [1] 0 (by decide) (by decide)) perm6.symm)

theorem finiteEdge4_2 : SafeCore (mutate (finiteNode 4) 2) := by
  have he := mutation_equal (finiteP 4) (preverse (prelabel (tailP [8] 3) perm21.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 4) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (tailP_safe [8] 3 0 (by decide) (by decide)) perm21.symm)

theorem finiteEdge4_3 : SafeCore (mutate (finiteNode 4) 3) := by
  have he := mutation_equal (finiteP 4) (preverse (prelabel (finiteP 18) perm15.symm)) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 4) 0) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 18) perm15.symm)

theorem finiteEdge5_0 : SafeCore (mutate (finiteNode 5) 0) := by
  have he := mutation_equal (finiteP 5) (preverse (prelabel (tailP [6] 2) perm1.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 5) 0) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (tailP_safe [6] 2 0 (by decide) (by decide)) perm1.symm)

theorem finiteEdge5_1 : SafeCore (mutate (finiteNode 5) 1) := by
  have he := mutation_equal (finiteP 5) (prelabel (generic finiteParam0_0 finiteParam0_1 finiteParam0_2 finiteParam0_3 0) perm17.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 5) 0) 1)
  rw [he]
  exact Safe.framed (finiteRegion0_safe 0) perm17.symm

theorem finiteEdge5_2 : SafeCore (mutate (finiteNode 5) 2) := by
  have he := mutation_equal (finiteP 5) (preverse (prelabel (finiteP 21) perm21.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 5) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 21) perm21.symm)

theorem finiteEdge5_3 : SafeCore (mutate (finiteNode 5) 3) := by
  have he := mutation_equal (finiteP 5) (prelabel (finiteP 22) perm1.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 5) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 22) perm1.symm

theorem finiteEdge6_0 : SafeCore (mutate (finiteNode 6) 0) := by
  have he := mutation_equal (finiteP 6) (prelabel (tailP [9] 0) perm21.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 6) 0) 0)
  rw [he]
  exact Safe.framed (tailP_safe [9] 0 0 (by decide) (by decide)) perm21.symm

theorem finiteEdge6_1 : SafeCore (mutate (finiteNode 6) 1) := by
  have he := mutation_equal (finiteP 6) (preverse (prelabel (root [7] [22] [33] [3] [5] [1]) perm6.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 6) 1
  rw [show mutate (finiteNode 6) 1=(reverse (relabel (matrix (root [7] [22] [33] [3] [5] [1]) 0) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [7] [22] [33] [3] [5] [1] 0 (by decide) (by decide)) perm6.symm)

theorem finiteEdge6_2 : SafeCore (mutate (finiteNode 6) 2) := by
  have he := mutation_equal (finiteP 6) (preverse (prelabel (tailP [8] 2) perm20.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 6) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (tailP_safe [8] 2 0 (by decide) (by decide)) perm20.symm)

theorem finiteEdge6_3 : SafeCore (mutate (finiteNode 6) 3) := by
  have he := mutation_equal (finiteP 6) (prelabel (finiteP 18) perm21.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 6) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 18) perm21.symm

theorem finiteEdge7_0 : SafeCore (mutate (finiteNode 7) 0) := by
  have he := mutation_equal (finiteP 7) (prelabel (tailP [9] 1) perm21.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 7) 0) 0)
  rw [he]
  exact Safe.framed (tailP_safe [9] 1 0 (by decide) (by decide)) perm21.symm

theorem finiteEdge7_1 : SafeCore (mutate (finiteNode 7) 1) := by
  have he := mutation_equal (finiteP 7) (preverse (prelabel (finiteP 23) perm19.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 7) 0) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 23) perm19.symm)

theorem finiteEdge7_2 : SafeCore (mutate (finiteNode 7) 2) := by
  have he := mutation_equal (finiteP 7) (prelabel (tailP [8] 3) perm1.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 7) 0) 2)
  rw [he]
  exact Safe.framed (tailP_safe [8] 3 0 (by decide) (by decide)) perm1.symm

theorem finiteEdge7_3 : SafeCore (mutate (finiteNode 7) 3) := by
  have he := mutation_equal (finiteP 7) (prelabel (finiteP 22) perm21.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 7) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 22) perm21.symm

theorem finiteEdge8_0 : SafeCore (mutate (finiteNode 8) 0) := by
  have he := mutation_equal (finiteP 8) (preverse (prelabel (tailP [7] 3) perm1.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 8) 0) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (tailP_safe [7] 3 0 (by decide) (by decide)) perm1.symm)

theorem finiteEdge8_1 : SafeCore (mutate (finiteNode 8) 1) := by
  have he := mutation_equal (finiteP 8) (preverse (prelabel (root [7] [41] [20] [6] [3] [1]) perm6.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 8) 1
  rw [show mutate (finiteNode 8) 1=(reverse (relabel (matrix (root [7] [41] [20] [6] [3] [1]) 0) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [7] [41] [20] [6] [3] [1] 0 (by decide) (by decide)) perm6.symm)

theorem finiteEdge8_2 : SafeCore (mutate (finiteNode 8) 2) := by
  have he := mutation_equal (finiteP 8) (preverse (prelabel (tailP [9] 3) perm21.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 8) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (tailP_safe [9] 3 0 (by decide) (by decide)) perm21.symm)

theorem finiteEdge8_3 : SafeCore (mutate (finiteNode 8) 3) := by
  have he := mutation_equal (finiteP 8) (preverse (prelabel (tailP [6] 0) perm15.symm)) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 8) 0) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (tailP_safe [6] 0 0 (by decide) (by decide)) perm15.symm)

theorem finiteEdge9_0 : SafeCore (mutate (finiteNode 9) 0) := by
  have he := mutation_equal (finiteP 9) (preverse (prelabel (tailP [7] 2) perm1.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 9) 0) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (tailP_safe [7] 2 0 (by decide) (by decide)) perm1.symm)

theorem finiteEdge9_1 : SafeCore (mutate (finiteNode 9) 1) := by
  have he := mutation_equal (finiteP 9) (prelabel (generic finiteParam1_0 finiteParam1_1 finiteParam1_2 finiteParam1_3 0) perm17.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 9) 0) 1)
  rw [he]
  exact Safe.framed (finiteRegion1_safe 0) perm17.symm

theorem finiteEdge9_2 : SafeCore (mutate (finiteNode 9) 2) := by
  have he := mutation_equal (finiteP 9) (preverse (prelabel (finiteP 26) perm21.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 9) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 26) perm21.symm)

theorem finiteEdge9_3 : SafeCore (mutate (finiteNode 9) 3) := by
  have he := mutation_equal (finiteP 9) (prelabel (tailP [6] 1) perm1.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 9) 0) 3)
  rw [he]
  exact Safe.framed (tailP_safe [6] 1 0 (by decide) (by decide)) perm1.symm

theorem finiteEdge10_0 : SafeCore (mutate (finiteNode 10) 0) := by
  have he := mutation_equal (finiteP 10) (preverse (prelabel (finiteP 0) perm0.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 10) 0) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 0) perm0.symm)

theorem finiteEdge10_1 : SafeCore (mutate (finiteNode 10) 1) := by
  have he := mutation_equal (finiteP 10) (prelabel (finiteP 0) perm0.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 10) 0) 1)
  rw [he]
  exact Safe.framed (finite_safe 0) perm0.symm

theorem finiteEdge10_2 : SafeCore (mutate (finiteNode 10) 2) := by
  have he := mutation_equal (finiteP 10) (preverse (prelabel (finiteP 17) perm7.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 10) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 17) perm7.symm)

theorem finiteEdge10_3 : SafeCore (mutate (finiteNode 10) 3) := by
  have he := mutation_equal (finiteP 10) (prelabel (finiteP 27) perm0.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 10) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 27) perm0.symm

theorem finiteEdge11_0 : SafeCore (mutate (finiteNode 11) 0) := by
  have he := mutation_equal (finiteP 11) (preverse (prelabel (finiteP 28) perm0.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 11) 0) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 28) perm0.symm)

theorem finiteEdge11_1 : SafeCore (mutate (finiteNode 11) 1) := by
  have he := mutation_equal (finiteP 11) (prelabel (finiteP 29) perm0.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 11) 0) 1)
  rw [he]
  exact Safe.framed (finite_safe 29) perm0.symm

theorem finiteEdge11_2 : SafeCore (mutate (finiteNode 11) 2) := by
  have he := mutation_equal (finiteP 11) (preverse (prelabel (finiteP 30) perm0.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 11) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 30) perm0.symm)

theorem finiteEdge11_3 : SafeCore (mutate (finiteNode 11) 3) := by
  have he := mutation_equal (finiteP 11) (prelabel (finiteP 0) perm1.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 11) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 0) perm1.symm

theorem finiteEdge12_0 : SafeCore (mutate (finiteNode 12) 0) := by
  have he := mutation_equal (finiteP 12) (preverse (prelabel (finiteP 12) perm1.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 12) 0) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 12) perm1.symm)

theorem finiteEdge12_1 : SafeCore (mutate (finiteNode 12) 1) := by
  have he := mutation_equal (finiteP 12) (preverse (prelabel (finiteP 31) perm16.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 12) 0) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 31) perm16.symm)

theorem finiteEdge12_2 : SafeCore (mutate (finiteNode 12) 2) := by
  have he := mutation_equal (finiteP 12) (preverse (prelabel (finiteP 0) perm10.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 12) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 0) perm10.symm)

theorem finiteEdge12_3 : SafeCore (mutate (finiteNode 12) 3) := by
  have he := mutation_equal (finiteP 12) (preverse (prelabel (finiteP 30) perm8.symm)) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 12) 0) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 30) perm8.symm)

theorem finiteEdge13_0 : SafeCore (mutate (finiteNode 13) 0) := by
  have he := mutation_equal (finiteP 13) (preverse (prelabel (finiteP 1) perm0.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 13) 0) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 1) perm0.symm)

theorem finiteEdge13_1 : SafeCore (mutate (finiteNode 13) 1) := by
  have he := mutation_equal (finiteP 13) (preverse (prelabel (finiteP 32) perm22.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 13) 0) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 32) perm22.symm)

theorem finiteEdge13_2 : SafeCore (mutate (finiteNode 13) 2) := by
  have he := mutation_equal (finiteP 13) (prelabel (finiteP 32) perm1.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 13) 0) 2)
  rw [he]
  exact Safe.framed (finite_safe 32) perm1.symm

theorem finiteEdge13_3 : SafeCore (mutate (finiteNode 13) 3) := by
  have he := mutation_equal (finiteP 13) (prelabel (finiteP 1) perm23.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 13) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 1) perm23.symm

theorem finiteEdge14_0 : SafeCore (mutate (finiteNode 14) 0) := by
  have he := mutation_equal (finiteP 14) (preverse (prelabel (finiteP 32) perm0.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 14) 0) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 32) perm0.symm)

theorem finiteEdge14_1 : SafeCore (mutate (finiteNode 14) 1) := by
  have he := mutation_equal (finiteP 14) (preverse (prelabel (finiteP 22) perm19.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 14) 0) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 22) perm19.symm)

theorem finiteEdge14_2 : SafeCore (mutate (finiteNode 14) 2) := by
  have he := mutation_equal (finiteP 14) (prelabel (finiteP 33) perm0.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 14) 0) 2)
  rw [he]
  exact Safe.framed (finite_safe 33) perm0.symm

theorem finiteEdge14_3 : SafeCore (mutate (finiteNode 14) 3) := by
  have he := mutation_equal (finiteP 14) (preverse (prelabel (finiteP 1) perm10.symm)) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 14) 0) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 1) perm10.symm)

theorem finiteEdge15_0 : SafeCore (mutate (finiteNode 15) 0) := by
  have he := mutation_equal (finiteP 15) (prelabel (tailP [6] 0) perm21.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 15) 0) 0)
  rw [he]
  exact Safe.framed (tailP_safe [6] 0 0 (by decide) (by decide)) perm21.symm

theorem finiteEdge15_1 : SafeCore (mutate (finiteNode 15) 1) := by
  have he := mutation_equal (finiteP 15) (preverse (prelabel (root [4] [13] [6] [3] [2] [1]) perm6.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 15) 1
  rw [show mutate (finiteNode 15) 1=(reverse (relabel (matrix (root [4] [13] [6] [3] [2] [1]) 0) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [4] [13] [6] [3] [2] [1] 0 (by decide) (by decide)) perm6.symm)

theorem finiteEdge15_2 : SafeCore (mutate (finiteNode 15) 2) := by
  have he := mutation_equal (finiteP 15) (preverse (prelabel (finiteP 26) perm20.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 15) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 26) perm20.symm)

theorem finiteEdge15_3 : SafeCore (mutate (finiteNode 15) 3) := by
  have he := mutation_equal (finiteP 15) (prelabel (finiteP 29) perm6.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 15) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 29) perm6.symm

theorem finiteEdge16_0 : SafeCore (mutate (finiteNode 16) 0) := by
  have he := mutation_equal (finiteP 16) (preverse (prelabel (root [4] [19] [82] [5] [22] [1]) perm5.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 16) 0
  rw [show mutate (finiteNode 16) 0=(reverse (relabel (matrix (root [4] [19] [82] [5] [22] [1]) 0) perm5.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [4] [19] [82] [5] [22] [1] 0 (by decide) (by decide)) perm5.symm)

theorem finiteEdge16_1 : SafeCore (mutate (finiteNode 16) 1) := by
  have he := mutation_equal (finiteP 16) (preverse (prelabel (finiteP 34) perm19.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 16) 0) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 34) perm19.symm)

theorem finiteEdge16_2 : SafeCore (mutate (finiteNode 16) 2) := by
  have he := mutation_equal (finiteP 16) (prelabel (finiteP 24) perm1.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 16) 0) 2)
  rw [he]
  exact Safe.framed (finite_safe 24) perm1.symm

theorem finiteEdge16_3 : SafeCore (mutate (finiteNode 16) 3) := by
  have he := mutation_equal (finiteP 16) (preverse (prelabel (tailP [6] 1) perm11.symm)) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 16) 0) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (tailP_safe [6] 1 0 (by decide) (by decide)) perm11.symm)

theorem finiteEdge17_0 : SafeCore (mutate (finiteNode 17) 0) := by
  have he := mutation_equal (finiteP 17) (prelabel (tailP [6] 1) perm21.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 17) 0) 0)
  rw [he]
  exact Safe.framed (tailP_safe [6] 1 0 (by decide) (by decide)) perm21.symm

theorem finiteEdge17_1 : SafeCore (mutate (finiteNode 17) 1) := by
  have he := mutation_equal (finiteP 17) (preverse (prelabel (finiteP 35) perm19.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 17) 0) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 35) perm19.symm)

theorem finiteEdge17_2 : SafeCore (mutate (finiteNode 17) 2) := by
  have he := mutation_equal (finiteP 17) (prelabel (finiteP 36) perm1.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 17) 0) 2)
  rw [he]
  exact Safe.framed (finite_safe 36) perm1.symm

theorem finiteEdge17_3 : SafeCore (mutate (finiteNode 17) 3) := by
  have he := mutation_equal (finiteP 17) (preverse (prelabel (finiteP 10) perm7.symm)) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 17) 0) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 10) perm7.symm)

theorem finiteEdge18_0 : SafeCore (mutate (finiteNode 18) 0) := by
  have he := mutation_equal (finiteP 18) (prelabel (tailP [7] 0) perm21.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 18) 0) 0)
  rw [he]
  exact Safe.framed (tailP_safe [7] 0 0 (by decide) (by decide)) perm21.symm

theorem finiteEdge18_1 : SafeCore (mutate (finiteNode 18) 1) := by
  have he := mutation_equal (finiteP 18) (preverse (prelabel (root [5] [16] [13] [3] [3] [1]) perm6.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 18) 1
  rw [show mutate (finiteNode 18) 1=(reverse (relabel (matrix (root [5] [16] [13] [3] [3] [1]) 0) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [5] [16] [13] [3] [3] [1] 0 (by decide) (by decide)) perm6.symm)

theorem finiteEdge18_2 : SafeCore (mutate (finiteNode 18) 2) := by
  have he := mutation_equal (finiteP 18) (preverse (prelabel (tailP [6] 2) perm20.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 18) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (tailP_safe [6] 2 0 (by decide) (by decide)) perm20.symm)

theorem finiteEdge18_3 : SafeCore (mutate (finiteNode 18) 3) := by
  have he := mutation_equal (finiteP 18) (preverse (prelabel (finiteP 37) perm15.symm)) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 18) 0) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 37) perm15.symm)

theorem finiteEdge19_0 : SafeCore (mutate (finiteNode 19) 0) := by
  have he := mutation_equal (finiteP 19) (prelabel (finiteP 20) perm21.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 19) 0) 0)
  rw [he]
  exact Safe.framed (finite_safe 20) perm21.symm

theorem finiteEdge19_1 : SafeCore (mutate (finiteNode 19) 1) := by
  have he := mutation_equal (finiteP 19) (prelabel (generic finiteParam2_0 finiteParam2_1 finiteParam2_2 finiteParam2_3 0) perm17.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 19) 0) 1)
  rw [he]
  exact Safe.framed (finiteRegion2_safe 0) perm17.symm

theorem finiteEdge19_2 : SafeCore (mutate (finiteNode 19) 2) := by
  have he := mutation_equal (finiteP 19) (preverse (prelabel (generic finiteParam0_0 finiteParam0_1 finiteParam0_2 finiteParam0_3 0) perm3.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 19) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finiteRegion0_safe 0) perm3.symm)

theorem finiteEdge19_3 : SafeCore (mutate (finiteNode 19) 3) := by
  have he := mutation_equal (finiteP 19) (prelabel (finiteP 40) perm1.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 19) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 40) perm1.symm

theorem finiteEdge20_0 : SafeCore (mutate (finiteNode 20) 0) := by
  have he := mutation_equal (finiteP 20) (prelabel (fork [4] [3] [67] [11] [251] [5]) perm5.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (finite_safe 20)
  rw [show mutate (finiteNode 20) 0=(relabel (matrix (fork [4] [3] [67] [11] [251] [5]) 0) perm5.symm) from he]
  exact IsFork.relabelled (fork_sound [4] [3] [67] [11] [251] [5] 0 (by decide) (by decide)) perm5.symm

theorem finiteEdge20_1 : SafeCore (mutate (finiteNode 20) 1) := by
  have he := mutation_equal (finiteP 20) (preverse (prelabel (root [67] [338] [1135] [5] [17] [1]) perm6.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 20) 1
  rw [show mutate (finiteNode 20) 1=(reverse (relabel (matrix (root [67] [338] [1135] [5] [17] [1]) 0) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [67] [338] [1135] [5] [17] [1] 0 (by decide) (by decide)) perm6.symm)

theorem finiteEdge20_2 : SafeCore (mutate (finiteNode 20) 2) := by
  have he := mutation_equal (finiteP 20) (preverse (prelabel (generic finiteParam0_0 finiteParam0_1 finiteParam0_2 finiteParam0_3 2) perm16.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 20) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finiteRegion0_safe 2) perm16.symm)

theorem finiteEdge20_3 : SafeCore (mutate (finiteNode 20) 3) := by
  have he := mutation_equal (finiteP 20) (prelabel (finiteP 19) perm21.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 20) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 19) perm21.symm

theorem finiteEdge21_0 : SafeCore (mutate (finiteNode 21) 0) := by
  have he := mutation_equal (finiteP 21) (prelabel (finiteP 33) perm6.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 21) 0) 0)
  rw [he]
  exact Safe.framed (finite_safe 33) perm6.symm

theorem finiteEdge21_1 : SafeCore (mutate (finiteNode 21) 1) := by
  have he := mutation_equal (finiteP 21) (preverse (prelabel (root [4] [11] [11] [3] [3] [1]) perm6.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 21) 1
  rw [show mutate (finiteNode 21) 1=(reverse (relabel (matrix (root [4] [11] [11] [3] [3] [1]) 0) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [4] [11] [11] [3] [3] [1] 0 (by decide) (by decide)) perm6.symm)

theorem finiteEdge21_2 : SafeCore (mutate (finiteNode 21) 2) := by
  have he := mutation_equal (finiteP 21) (preverse (prelabel (tailP [6] 3) perm21.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 21) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (tailP_safe [6] 3 0 (by decide) (by decide)) perm21.symm)

theorem finiteEdge21_3 : SafeCore (mutate (finiteNode 21) 3) := by
  have he := mutation_equal (finiteP 21) (prelabel (finiteP 37) perm21.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 21) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 37) perm21.symm

theorem finiteEdge22_0 : SafeCore (mutate (finiteNode 22) 0) := by
  have he := mutation_equal (finiteP 22) (prelabel (tailP [7] 1) perm21.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 22) 0) 0)
  rw [he]
  exact Safe.framed (tailP_safe [7] 1 0 (by decide) (by decide)) perm21.symm

theorem finiteEdge22_1 : SafeCore (mutate (finiteNode 22) 1) := by
  have he := mutation_equal (finiteP 22) (preverse (prelabel (finiteP 40) perm19.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 22) 0) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 40) perm19.symm)

theorem finiteEdge22_2 : SafeCore (mutate (finiteNode 22) 2) := by
  have he := mutation_equal (finiteP 22) (prelabel (tailP [6] 3) perm1.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 22) 0) 2)
  rw [he]
  exact Safe.framed (tailP_safe [6] 3 0 (by decide) (by decide)) perm1.symm

theorem finiteEdge22_3 : SafeCore (mutate (finiteNode 22) 3) := by
  have he := mutation_equal (finiteP 22) (preverse (prelabel (finiteP 14) perm11.symm)) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 22) 0) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 14) perm11.symm)

theorem finiteEdge23_0 : SafeCore (mutate (finiteNode 23) 0) := by
  have he := mutation_equal (finiteP 23) (preverse (prelabel (root [5] [29] [158] [6] [33] [1]) perm5.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 23) 0
  rw [show mutate (finiteNode 23) 0=(reverse (relabel (matrix (root [5] [29] [158] [6] [33] [1]) 0) perm5.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [5] [29] [158] [6] [33] [1] 0 (by decide) (by decide)) perm5.symm)

theorem finiteEdge23_1 : SafeCore (mutate (finiteNode 23) 1) := by
  have he := mutation_equal (finiteP 23) (preverse (prelabel (finiteP 41) perm19.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 23) 0) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 41) perm19.symm)

theorem finiteEdge23_2 : SafeCore (mutate (finiteNode 23) 2) := by
  have he := mutation_equal (finiteP 23) (prelabel (finiteP 42) perm1.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 23) 0) 2)
  rw [he]
  exact Safe.framed (finite_safe 42) perm1.symm

theorem finiteEdge23_3 : SafeCore (mutate (finiteNode 23) 3) := by
  have he := mutation_equal (finiteP 23) (preverse (prelabel (tailP [7] 1) perm11.symm)) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 23) 0) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (tailP_safe [7] 1 0 (by decide) (by decide)) perm11.symm)

theorem finiteEdge24_0 : SafeCore (mutate (finiteNode 24) 0) := by
  have he := mutation_equal (finiteP 24) (prelabel (finiteP 25) perm21.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 24) 0) 0)
  rw [he]
  exact Safe.framed (finite_safe 25) perm21.symm

theorem finiteEdge24_1 : SafeCore (mutate (finiteNode 24) 1) := by
  have he := mutation_equal (finiteP 24) (prelabel (generic finiteParam3_0 finiteParam3_1 finiteParam3_2 finiteParam3_3 0) perm17.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 24) 0) 1)
  rw [he]
  exact Safe.framed (finiteRegion3_safe 0) perm17.symm

theorem finiteEdge24_2 : SafeCore (mutate (finiteNode 24) 2) := by
  have he := mutation_equal (finiteP 24) (preverse (prelabel (generic finiteParam1_0 finiteParam1_1 finiteParam1_2 finiteParam1_3 0) perm3.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 24) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finiteRegion1_safe 0) perm3.symm)

theorem finiteEdge24_3 : SafeCore (mutate (finiteNode 24) 3) := by
  have he := mutation_equal (finiteP 24) (prelabel (finiteP 16) perm1.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 24) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 16) perm1.symm

theorem finiteEdge25_0 : SafeCore (mutate (finiteNode 25) 0) := by
  have he := mutation_equal (finiteP 25) (prelabel (fork [5] [4] [134] [19] [643] [6]) perm5.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (finite_safe 25)
  rw [show mutate (finiteNode 25) 0=(relabel (matrix (fork [5] [4] [134] [19] [643] [6]) 0) perm5.symm) from he]
  exact IsFork.relabelled (fork_sound [5] [4] [134] [19] [643] [6] 0 (by decide) (by decide)) perm5.symm

theorem finiteEdge25_1 : SafeCore (mutate (finiteNode 25) 1) := by
  have he := mutation_equal (finiteP 25) (preverse (prelabel (root [134] [808] [3613] [6] [27] [1]) perm6.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 25) 1
  rw [show mutate (finiteNode 25) 1=(reverse (relabel (matrix (root [134] [808] [3613] [6] [27] [1]) 0) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [134] [808] [3613] [6] [27] [1] 0 (by decide) (by decide)) perm6.symm)

theorem finiteEdge25_2 : SafeCore (mutate (finiteNode 25) 2) := by
  have he := mutation_equal (finiteP 25) (preverse (prelabel (generic finiteParam1_0 finiteParam1_1 finiteParam1_2 finiteParam1_3 2) perm16.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 25) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finiteRegion1_safe 2) perm16.symm)

theorem finiteEdge25_3 : SafeCore (mutate (finiteNode 25) 3) := by
  have he := mutation_equal (finiteP 25) (prelabel (finiteP 24) perm21.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 25) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 24) perm21.symm

theorem finiteEdge26_0 : SafeCore (mutate (finiteNode 26) 0) := by
  have he := mutation_equal (finiteP 26) (preverse (prelabel (finiteP 36) perm1.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 26) 0) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 36) perm1.symm)

theorem finiteEdge26_1 : SafeCore (mutate (finiteNode 26) 1) := by
  have he := mutation_equal (finiteP 26) (preverse (prelabel (root [5] [19] [14] [4] [3] [1]) perm6.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 26) 1
  rw [show mutate (finiteNode 26) 1=(reverse (relabel (matrix (root [5] [19] [14] [4] [3] [1]) 0) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [5] [19] [14] [4] [3] [1] 0 (by decide) (by decide)) perm6.symm)

theorem finiteEdge26_2 : SafeCore (mutate (finiteNode 26) 2) := by
  have he := mutation_equal (finiteP 26) (preverse (prelabel (tailP [7] 3) perm21.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 26) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (tailP_safe [7] 3 0 (by decide) (by decide)) perm21.symm)

theorem finiteEdge26_3 : SafeCore (mutate (finiteNode 26) 3) := by
  have he := mutation_equal (finiteP 26) (preverse (prelabel (finiteP 15) perm15.symm)) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 26) 0) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 15) perm15.symm)

theorem finiteEdge27_0 : SafeCore (mutate (finiteNode 27) 0) := by
  have he := mutation_equal (finiteP 27) (preverse (prelabel (finiteP 31) perm0.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 27) 0) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 31) perm0.symm)

theorem finiteEdge27_1 : SafeCore (mutate (finiteNode 27) 1) := by
  have he := mutation_equal (finiteP 27) (prelabel (finiteP 30) perm0.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 27) 0) 1)
  rw [he]
  exact Safe.framed (finite_safe 30) perm0.symm

theorem finiteEdge27_2 : SafeCore (mutate (finiteNode 27) 2) := by
  have he := mutation_equal (finiteP 27) (prelabel (finiteP 45) perm1.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 27) 0) 2)
  rw [he]
  exact Safe.framed (finite_safe 45) perm1.symm

theorem finiteEdge27_3 : SafeCore (mutate (finiteNode 27) 3) := by
  have he := mutation_equal (finiteP 27) (prelabel (finiteP 10) perm0.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 27) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 10) perm0.symm

theorem finiteEdge28_0 : SafeCore (mutate (finiteNode 28) 0) := by
  have he := mutation_equal (finiteP 28) (preverse (prelabel (finiteP 11) perm0.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 28) 0) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 11) perm0.symm)

theorem finiteEdge28_1 : SafeCore (mutate (finiteNode 28) 1) := by
  have he := mutation_equal (finiteP 28) (prelabel (finiteP 46) perm0.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 28) 0) 1)
  rw [he]
  exact Safe.framed (finite_safe 46) perm0.symm

theorem finiteEdge28_2 : SafeCore (mutate (finiteNode 28) 2) := by
  have he := mutation_equal (finiteP 28) (prelabel (finiteP 47) perm4.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 28) 0) 2)
  rw [he]
  exact Safe.framed (finite_safe 47) perm4.symm

theorem finiteEdge28_3 : SafeCore (mutate (finiteNode 28) 3) := by
  have he := mutation_equal (finiteP 28) (prelabel (root [2] [4] [7] [2] [5] [1]) perm18.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 28) 3
  rw [show mutate (finiteNode 28) 3=(relabel (matrix (root [2] [4] [7] [2] [5] [1]) 0) perm18.symm) from he]
  exact IsRoot.relabelled (root_sound [2] [4] [7] [2] [5] [1] 0 (by decide) (by decide)) perm18.symm

theorem finiteEdge29_0 : SafeCore (mutate (finiteNode 29) 0) := by
  have he := mutation_equal (finiteP 29) (preverse (prelabel (finiteP 46) perm0.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 29) 0) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 46) perm0.symm)

theorem finiteEdge29_1 : SafeCore (mutate (finiteNode 29) 1) := by
  have he := mutation_equal (finiteP 29) (prelabel (finiteP 11) perm0.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 29) 0) 1)
  rw [he]
  exact Safe.framed (finite_safe 11) perm0.symm

theorem finiteEdge29_2 : SafeCore (mutate (finiteNode 29) 2) := by
  have he := mutation_equal (finiteP 29) (preverse (prelabel (finiteP 45) perm3.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 29) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 45) perm3.symm)

theorem finiteEdge29_3 : SafeCore (mutate (finiteNode 29) 3) := by
  have he := mutation_equal (finiteP 29) (prelabel (finiteP 15) perm6.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 29) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 15) perm6.symm

theorem finiteEdge30_0 : SafeCore (mutate (finiteNode 30) 0) := by
  have he := mutation_equal (finiteP 30) (preverse (prelabel (finiteP 48) perm0.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 30) 0) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 48) perm0.symm)

theorem finiteEdge30_1 : SafeCore (mutate (finiteNode 30) 1) := by
  have he := mutation_equal (finiteP 30) (prelabel (finiteP 27) perm0.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 30) 0) 1)
  rw [he]
  exact Safe.framed (finite_safe 27) perm0.symm

theorem finiteEdge30_2 : SafeCore (mutate (finiteNode 30) 2) := by
  have he := mutation_equal (finiteP 30) (preverse (prelabel (finiteP 11) perm0.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 30) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 11) perm0.symm)

theorem finiteEdge30_3 : SafeCore (mutate (finiteNode 30) 3) := by
  have he := mutation_equal (finiteP 30) (preverse (prelabel (finiteP 12) perm12.symm)) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 30) 0) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 12) perm12.symm)

theorem finiteEdge31_0 : SafeCore (mutate (finiteNode 31) 0) := by
  have he := mutation_equal (finiteP 31) (preverse (prelabel (finiteP 27) perm0.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 31) 0) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 27) perm0.symm)

theorem finiteEdge31_1 : SafeCore (mutate (finiteNode 31) 1) := by
  have he := mutation_equal (finiteP 31) (prelabel (finiteP 48) perm0.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 31) 0) 1)
  rw [he]
  exact Safe.framed (finite_safe 48) perm0.symm

theorem finiteEdge31_2 : SafeCore (mutate (finiteNode 31) 2) := by
  have he := mutation_equal (finiteP 31) (prelabel (finiteP 49) perm1.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 31) 0) 2)
  rw [he]
  exact Safe.framed (finite_safe 49) perm1.symm

theorem finiteEdge31_3 : SafeCore (mutate (finiteNode 31) 3) := by
  have he := mutation_equal (finiteP 31) (preverse (prelabel (finiteP 12) perm16.symm)) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 31) 0) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 12) perm16.symm)

theorem finiteEdge32_0 : SafeCore (mutate (finiteNode 32) 0) := by
  have he := mutation_equal (finiteP 32) (preverse (prelabel (finiteP 14) perm0.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 32) 0) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 14) perm0.symm)

theorem finiteEdge32_1 : SafeCore (mutate (finiteNode 32) 1) := by
  have he := mutation_equal (finiteP 32) (prelabel (finiteP 50) perm3.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 32) 0) 1)
  rw [he]
  exact Safe.framed (finite_safe 50) perm3.symm

theorem finiteEdge32_2 : SafeCore (mutate (finiteNode 32) 2) := by
  have he := mutation_equal (finiteP 32) (prelabel (finiteP 37) perm1.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 32) 0) 2)
  rw [he]
  exact Safe.framed (finite_safe 37) perm1.symm

theorem finiteEdge32_3 : SafeCore (mutate (finiteNode 32) 3) := by
  have he := mutation_equal (finiteP 32) (prelabel (finiteP 13) perm1.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 32) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 13) perm1.symm

theorem finiteEdge33_0 : SafeCore (mutate (finiteNode 33) 0) := by
  have he := mutation_equal (finiteP 33) (preverse (prelabel (finiteP 21) perm1.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 33) 0) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 21) perm1.symm)

theorem finiteEdge33_1 : SafeCore (mutate (finiteNode 33) 1) := by
  have he := mutation_equal (finiteP 33) (prelabel (finiteP 21) perm6.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 33) 0) 1)
  rw [he]
  exact Safe.framed (finite_safe 21) perm6.symm

theorem finiteEdge33_2 : SafeCore (mutate (finiteNode 33) 2) := by
  have he := mutation_equal (finiteP 33) (prelabel (finiteP 14) perm0.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 33) 0) 2)
  rw [he]
  exact Safe.framed (finite_safe 14) perm0.symm

theorem finiteEdge33_3 : SafeCore (mutate (finiteNode 33) 3) := by
  have he := mutation_equal (finiteP 33) (preverse (prelabel (finiteP 14) perm7.symm)) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 33) 0) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 14) perm7.symm)

theorem finiteEdge34_0 : SafeCore (mutate (finiteNode 34) 0) := by
  have he := mutation_equal (finiteP 34) (prelabel (fork [6] [128] [7] [746] [41] [5]) perm4.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (finite_safe 34)
  rw [show mutate (finiteNode 34) 0=(relabel (matrix (fork [6] [128] [7] [746] [41] [5]) 0) perm4.symm) from he]
  exact IsFork.relabelled (fork_sound [6] [128] [7] [746] [41] [5] 0 (by decide) (by decide)) perm4.symm

theorem finiteEdge34_1 : SafeCore (mutate (finiteNode 34) 1) := by
  have he := mutation_equal (finiteP 34) (preverse (prelabel (fork [22] [128] [5] [2810] [111] [7]) perm10.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (finite_safe 34)
  rw [show mutate (finiteNode 34) 1=(reverse (relabel (matrix (fork [22] [128] [5] [2810] [111] [7]) 0) perm10.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [22] [128] [5] [2810] [111] [7] 0 (by decide) (by decide)) perm10.symm)

theorem finiteEdge34_2 : SafeCore (mutate (finiteNode 34) 2) := by
  have he := mutation_equal (finiteP 34) (prelabel (finiteP 43) perm1.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 34) 0) 2)
  rw [he]
  exact Safe.framed (finite_safe 43) perm1.symm

theorem finiteEdge34_3 : SafeCore (mutate (finiteNode 34) 3) := by
  have he := mutation_equal (finiteP 34) (preverse (prelabel (finiteP 16) perm11.symm)) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 34) 0) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 16) perm11.symm)

theorem finiteEdge35_0 : SafeCore (mutate (finiteNode 35) 0) := by
  have he := mutation_equal (finiteP 35) (preverse (prelabel (root [2] [5] [8] [3] [6] [1]) perm5.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 35) 0
  rw [show mutate (finiteNode 35) 0=(reverse (relabel (matrix (root [2] [5] [8] [3] [6] [1]) 0) perm5.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [2] [5] [8] [3] [6] [1] 0 (by decide) (by decide)) perm5.symm)

theorem finiteEdge35_1 : SafeCore (mutate (finiteNode 35) 1) := by
  have he := mutation_equal (finiteP 35) (preverse (prelabel (finiteP 51) perm19.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 35) 0) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 51) perm19.symm)

theorem finiteEdge35_2 : SafeCore (mutate (finiteNode 35) 2) := by
  have he := mutation_equal (finiteP 35) (prelabel (finiteP 52) perm1.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 35) 0) 2)
  rw [he]
  exact Safe.framed (finite_safe 52) perm1.symm

theorem finiteEdge35_3 : SafeCore (mutate (finiteNode 35) 3) := by
  have he := mutation_equal (finiteP 35) (preverse (prelabel (finiteP 17) perm11.symm)) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 35) 0) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 17) perm11.symm)

theorem finiteEdge36_0 : SafeCore (mutate (finiteNode 36) 0) := by
  have he := mutation_equal (finiteP 36) (preverse (prelabel (finiteP 26) perm1.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 36) 0) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 26) perm1.symm)

theorem finiteEdge36_1 : SafeCore (mutate (finiteNode 36) 1) := by
  have he := mutation_equal (finiteP 36) (prelabel (generic finiteParam4_0 finiteParam4_1 finiteParam4_2 finiteParam4_3 0) perm17.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 36) 0) 1)
  rw [he]
  exact Safe.framed (finiteRegion4_safe 0) perm17.symm

theorem finiteEdge36_2 : SafeCore (mutate (finiteNode 36) 2) := by
  have he := mutation_equal (finiteP 36) (preverse (prelabel (finiteP 45) perm6.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 36) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 45) perm6.symm)

theorem finiteEdge36_3 : SafeCore (mutate (finiteNode 36) 3) := by
  have he := mutation_equal (finiteP 36) (prelabel (finiteP 17) perm1.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 36) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 17) perm1.symm

theorem finiteEdge37_0 : SafeCore (mutate (finiteNode 37) 0) := by
  have he := mutation_equal (finiteP 37) (prelabel (finiteP 21) perm21.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 37) 0) 0)
  rw [he]
  exact Safe.framed (finite_safe 21) perm21.symm

theorem finiteEdge37_1 : SafeCore (mutate (finiteNode 37) 1) := by
  have he := mutation_equal (finiteP 37) (preverse (prelabel (finiteP 54) perm13.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 37) 0) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 54) perm13.symm)

theorem finiteEdge37_2 : SafeCore (mutate (finiteNode 37) 2) := by
  have he := mutation_equal (finiteP 37) (preverse (prelabel (finiteP 18) perm20.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 37) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 18) perm20.symm)

theorem finiteEdge37_3 : SafeCore (mutate (finiteNode 37) 3) := by
  have he := mutation_equal (finiteP 37) (prelabel (finiteP 32) perm1.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 37) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 32) perm1.symm

theorem finiteEdge38_0 : SafeCore (mutate (finiteNode 38) 0) := by
  have he := mutation_equal (finiteP 38) (prelabel (finiteP 39) perm21.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 38) 0) 0)
  rw [he]
  exact Safe.framed (finite_safe 39) perm21.symm

theorem finiteEdge38_1 : SafeCore (mutate (finiteNode 38) 1) := by
  have he := mutation_equal (finiteP 38) (preverse (prelabel (root [86] [1119] [338] [13] [4] [1]) perm6.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 38) 1
  rw [show mutate (finiteNode 38) 1=(reverse (relabel (matrix (root [86] [1119] [338] [13] [4] [1]) 0) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [86] [1119] [338] [13] [4] [1] 0 (by decide) (by decide)) perm6.symm)

theorem finiteEdge38_2 : SafeCore (mutate (finiteNode 38) 2) := by
  have he := mutation_equal (finiteP 38) (preverse (prelabel (generic finiteParam2_0 finiteParam2_1 finiteParam2_2 finiteParam2_3 0) perm3.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 38) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finiteRegion2_safe 0) perm3.symm)

theorem finiteEdge38_3 : SafeCore (mutate (finiteNode 38) 3) := by
  have he := mutation_equal (finiteP 38) (prelabel (finiteP 55) perm1.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 38) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 55) perm1.symm

theorem finiteEdge39_0 : SafeCore (mutate (finiteNode 39) 0) := by
  have he := mutation_equal (finiteP 39) (prelabel (fork [6] [5] [512] [29] [2986] [13]) perm5.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (finite_safe 39)
  rw [show mutate (finiteNode 39) 0=(relabel (matrix (fork [6] [5] [512] [29] [2986] [13]) 0) perm5.symm) from he]
  exact IsFork.relabelled (fork_sound [6] [5] [512] [29] [2986] [13] 0 (by decide) (by decide)) perm5.symm

theorem finiteEdge39_1 : SafeCore (mutate (finiteNode 39) 1) := by
  have he := mutation_equal (finiteP 39) (preverse (prelabel (root [512] [6661] [44026] [13] [86] [1]) perm6.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 39) 1
  rw [show mutate (finiteNode 39) 1=(reverse (relabel (matrix (root [512] [6661] [44026] [13] [86] [1]) 0) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [512] [6661] [44026] [13] [86] [1] 0 (by decide) (by decide)) perm6.symm)

theorem finiteEdge39_2 : SafeCore (mutate (finiteNode 39) 2) := by
  have he := mutation_equal (finiteP 39) (preverse (prelabel (generic finiteParam2_0 finiteParam2_1 finiteParam2_2 finiteParam2_3 2) perm16.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 39) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finiteRegion2_safe 2) perm16.symm)

theorem finiteEdge39_3 : SafeCore (mutate (finiteNode 39) 3) := by
  have he := mutation_equal (finiteP 39) (prelabel (finiteP 38) perm21.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 39) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 38) perm21.symm

theorem finiteEdge40_0 : SafeCore (mutate (finiteNode 40) 0) := by
  have he := mutation_equal (finiteP 40) (preverse (prelabel (root [3] [11] [34] [4] [13] [1]) perm5.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 40) 0
  rw [show mutate (finiteNode 40) 0=(reverse (relabel (matrix (root [3] [11] [34] [4] [13] [1]) 0) perm5.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [3] [11] [34] [4] [13] [1] 0 (by decide) (by decide)) perm5.symm)

theorem finiteEdge40_1 : SafeCore (mutate (finiteNode 40) 1) := by
  have he := mutation_equal (finiteP 40) (preverse (prelabel (finiteP 55) perm19.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 40) 0) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 55) perm19.symm)

theorem finiteEdge40_2 : SafeCore (mutate (finiteNode 40) 2) := by
  have he := mutation_equal (finiteP 40) (prelabel (finiteP 19) perm1.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 40) 0) 2)
  rw [he]
  exact Safe.framed (finite_safe 19) perm1.symm

theorem finiteEdge40_3 : SafeCore (mutate (finiteNode 40) 3) := by
  have he := mutation_equal (finiteP 40) (preverse (prelabel (finiteP 22) perm11.symm)) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 40) 0) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 22) perm11.symm)

theorem finiteEdge41_0 : SafeCore (mutate (finiteNode 41) 0) := by
  have he := mutation_equal (finiteP 41) (prelabel (fork [7] [226] [8] [1549] [55] [6]) perm4.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (finite_safe 41)
  rw [show mutate (finiteNode 41) 0=(relabel (matrix (fork [7] [226] [8] [1549] [55] [6]) 0) perm4.symm) from he]
  exact IsFork.relabelled (fork_sound [7] [226] [8] [1549] [55] [6] 0 (by decide) (by decide)) perm4.symm

theorem finiteEdge41_1 : SafeCore (mutate (finiteNode 41) 1) := by
  have he := mutation_equal (finiteP 41) (preverse (prelabel (fork [33] [226] [6] [7451] [199] [8]) perm10.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (finite_safe 41)
  rw [show mutate (finiteNode 41) 1=(reverse (relabel (matrix (fork [33] [226] [6] [7451] [199] [8]) 0) perm10.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [33] [226] [6] [7451] [199] [8] 0 (by decide) (by decide)) perm10.symm)

theorem finiteEdge41_2 : SafeCore (mutate (finiteNode 41) 2) := by
  have he := mutation_equal (finiteP 41) (prelabel (finiteP 56) perm1.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 41) 0) 2)
  rw [he]
  exact Safe.framed (finite_safe 56) perm1.symm

theorem finiteEdge41_3 : SafeCore (mutate (finiteNode 41) 3) := by
  have he := mutation_equal (finiteP 41) (preverse (prelabel (finiteP 23) perm11.symm)) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 41) 0) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 23) perm11.symm)

theorem finiteEdge42_0 : SafeCore (mutate (finiteNode 42) 0) := by
  have he := mutation_equal (finiteP 42) (prelabel (finiteP 57) perm21.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 42) 0) 0)
  rw [he]
  exact Safe.framed (finite_safe 57) perm21.symm

theorem finiteEdge42_1 : SafeCore (mutate (finiteNode 42) 1) := by
  have he := mutation_equal (finiteP 42) (prelabel (generic finiteParam5_0 finiteParam5_1 finiteParam5_2 finiteParam5_3 0) perm17.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 42) 0) 1)
  rw [he]
  exact Safe.framed (finiteRegion5_safe 0) perm17.symm

theorem finiteEdge42_2 : SafeCore (mutate (finiteNode 42) 2) := by
  have he := mutation_equal (finiteP 42) (preverse (prelabel (generic finiteParam6_0 finiteParam6_1 finiteParam6_2 finiteParam6_3 0) perm3.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 42) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finiteRegion6_safe 0) perm3.symm)

theorem finiteEdge42_3 : SafeCore (mutate (finiteNode 42) 3) := by
  have he := mutation_equal (finiteP 42) (prelabel (finiteP 23) perm1.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 42) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 23) perm1.symm

theorem finiteEdge43_0 : SafeCore (mutate (finiteNode 43) 0) := by
  have he := mutation_equal (finiteP 43) (prelabel (finiteP 44) perm21.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 43) 0) 0)
  rw [he]
  exact Safe.framed (finite_safe 44) perm21.symm

theorem finiteEdge43_1 : SafeCore (mutate (finiteNode 43) 1) := by
  have he := mutation_equal (finiteP 43) (preverse (prelabel (root [163] [3587] [808] [22] [5] [1]) perm6.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 43) 1
  rw [show mutate (finiteNode 43) 1=(reverse (relabel (matrix (root [163] [3587] [808] [22] [5] [1]) 0) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [163] [3587] [808] [22] [5] [1] 0 (by decide) (by decide)) perm6.symm)

theorem finiteEdge43_2 : SafeCore (mutate (finiteNode 43) 2) := by
  have he := mutation_equal (finiteP 43) (preverse (prelabel (generic finiteParam3_0 finiteParam3_1 finiteParam3_2 finiteParam3_3 0) perm3.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 43) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finiteRegion3_safe 0) perm3.symm)

theorem finiteEdge43_3 : SafeCore (mutate (finiteNode 43) 3) := by
  have he := mutation_equal (finiteP 43) (prelabel (finiteP 34) perm1.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 43) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 34) perm1.symm

theorem finiteEdge44_0 : SafeCore (mutate (finiteNode 44) 0) := by
  have he := mutation_equal (finiteP 44) (prelabel (fork [7] [6] [1136] [41] [7789] [22]) perm5.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (finite_safe 44)
  rw [show mutate (finiteNode 44) 0=(relabel (matrix (fork [7] [6] [1136] [41] [7789] [22]) 0) perm5.symm) from he]
  exact IsFork.relabelled (fork_sound [7] [6] [1136] [41] [7789] [22] 0 (by decide) (by decide)) perm5.symm

theorem finiteEdge44_1 : SafeCore (mutate (finiteNode 44) 1) := by
  have he := mutation_equal (finiteP 44) (preverse (prelabel (root [1136] [24998] [185161] [22] [163] [1]) perm6.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 44) 1
  rw [show mutate (finiteNode 44) 1=(reverse (relabel (matrix (root [1136] [24998] [185161] [22] [163] [1]) 0) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [1136] [24998] [185161] [22] [163] [1] 0 (by decide) (by decide)) perm6.symm)

theorem finiteEdge44_2 : SafeCore (mutate (finiteNode 44) 2) := by
  have he := mutation_equal (finiteP 44) (preverse (prelabel (generic finiteParam3_0 finiteParam3_1 finiteParam3_2 finiteParam3_3 2) perm16.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 44) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finiteRegion3_safe 2) perm16.symm)

theorem finiteEdge44_3 : SafeCore (mutate (finiteNode 44) 3) := by
  have he := mutation_equal (finiteP 44) (prelabel (finiteP 43) perm21.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 44) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 43) perm21.symm

theorem finiteEdge45_0 : SafeCore (mutate (finiteNode 45) 0) := by
  have he := mutation_equal (finiteP 45) (preverse (prelabel (root [3] [5] [8] [2] [3] [1]) perm5.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 45) 0
  rw [show mutate (finiteNode 45) 0=(reverse (relabel (matrix (root [3] [5] [8] [2] [3] [1]) 0) perm5.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [3] [5] [8] [2] [3] [1] 0 (by decide) (by decide)) perm5.symm)

theorem finiteEdge45_1 : SafeCore (mutate (finiteNode 45) 1) := by
  have he := mutation_equal (finiteP 45) (preverse (prelabel (finiteP 29) perm4.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 45) 0) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 29) perm4.symm)

theorem finiteEdge45_2 : SafeCore (mutate (finiteNode 45) 2) := by
  have he := mutation_equal (finiteP 45) (preverse (prelabel (finiteP 36) perm6.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 45) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 36) perm6.symm)

theorem finiteEdge45_3 : SafeCore (mutate (finiteNode 45) 3) := by
  have he := mutation_equal (finiteP 45) (prelabel (finiteP 27) perm1.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 45) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 27) perm1.symm

theorem finiteEdge46_0 : SafeCore (mutate (finiteNode 46) 0) := by
  have he := mutation_equal (finiteP 46) (preverse (prelabel (finiteP 29) perm0.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 46) 0) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 29) perm0.symm)

theorem finiteEdge46_1 : SafeCore (mutate (finiteNode 46) 1) := by
  have he := mutation_equal (finiteP 46) (prelabel (finiteP 28) perm0.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 46) 0) 1)
  rw [he]
  exact Safe.framed (finite_safe 28) perm0.symm

theorem finiteEdge46_2 : SafeCore (mutate (finiteNode 46) 2) := by
  have he := mutation_equal (finiteP 46) (prelabel (finiteP 59) perm1.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 46) 0) 2)
  rw [he]
  exact Safe.framed (finite_safe 59) perm1.symm

theorem finiteEdge46_3 : SafeCore (mutate (finiteNode 46) 3) := by
  have he := mutation_equal (finiteP 46) (preverse (prelabel (root [7] [11] [13] [2] [2] []) perm22.symm)) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 46) 3
  rw [show mutate (finiteNode 46) 3=(reverse (relabel (matrix (root [7] [11] [13] [2] [2] []) 0) perm22.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [7] [11] [13] [2] [2] [] 0 (by decide) (by decide)) perm22.symm)

theorem finiteEdge47_0 : SafeCore (mutate (finiteNode 47) 0) := by
  have he := mutation_equal (finiteP 47) (prelabel (fork [3] [13] [3] [34] [8] [2]) perm4.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (finite_safe 47)
  rw [show mutate (finiteNode 47) 0=(relabel (matrix (fork [3] [13] [3] [34] [8] [2]) 0) perm4.symm) from he]
  exact IsFork.relabelled (fork_sound [3] [13] [3] [34] [8] [2] 0 (by decide) (by decide)) perm4.symm

theorem finiteEdge47_1 : SafeCore (mutate (finiteNode 47) 1) := by
  have he := mutation_equal (finiteP 47) (preverse (prelabel (fork [5] [13] [2] [62] [11] [3]) perm10.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (finite_safe 47)
  rw [show mutate (finiteNode 47) 1=(reverse (relabel (matrix (fork [5] [13] [2] [62] [11] [3]) 0) perm10.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [5] [13] [2] [62] [11] [3] 0 (by decide) (by decide)) perm10.symm)

theorem finiteEdge47_2 : SafeCore (mutate (finiteNode 47) 2) := by
  have he := mutation_equal (finiteP 47) (prelabel (finiteP 60) perm4.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 47) 0) 2)
  rw [he]
  exact Safe.framed (finite_safe 60) perm4.symm

theorem finiteEdge47_3 : SafeCore (mutate (finiteNode 47) 3) := by
  have he := mutation_equal (finiteP 47) (prelabel (finiteP 28) perm3.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 47) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 28) perm3.symm

theorem finiteEdge48_0 : SafeCore (mutate (finiteNode 48) 0) := by
  have he := mutation_equal (finiteP 48) (preverse (prelabel (finiteP 30) perm0.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 48) 0) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 30) perm0.symm)

theorem finiteEdge48_1 : SafeCore (mutate (finiteNode 48) 1) := by
  have he := mutation_equal (finiteP 48) (prelabel (finiteP 31) perm0.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 48) 0) 1)
  rw [he]
  exact Safe.framed (finite_safe 31) perm0.symm

theorem finiteEdge48_2 : SafeCore (mutate (finiteNode 48) 2) := by
  have he := mutation_equal (finiteP 48) (prelabel (finiteP 61) perm4.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 48) 0) 2)
  rw [he]
  exact Safe.framed (finite_safe 61) perm4.symm

theorem finiteEdge48_3 : SafeCore (mutate (finiteNode 48) 3) := by
  have he := mutation_equal (finiteP 48) (preverse (prelabel (finiteP 48) perm6.symm)) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 48) 0) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 48) perm6.symm)

theorem finiteEdge49_0 : SafeCore (mutate (finiteNode 49) 0) := by
  have he := mutation_equal (finiteP 49) (prelabel (zero finiteParam7_0 finiteParam7_1 finiteParam7_2 finiteParam7_3 0) perm6.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 49) 0) 0)
  rw [he]
  exact Safe.framed (finiteRegion7_safe 0) perm6.symm

theorem finiteEdge49_1 : SafeCore (mutate (finiteNode 49) 1) := by
  have he := mutation_equal (finiteP 49) (prelabel (finiteP 62) perm0.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 49) 0) 1)
  rw [he]
  exact Safe.framed (finite_safe 62) perm0.symm

theorem finiteEdge49_2 : SafeCore (mutate (finiteNode 49) 2) := by
  have he := mutation_equal (finiteP 49) (prelabel (root [2] [7] [5] [5] [3] []) perm16.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 49) 2
  rw [show mutate (finiteNode 49) 2=(relabel (matrix (root [2] [7] [5] [5] [3] []) 0) perm16.symm) from he]
  exact IsRoot.relabelled (root_sound [2] [7] [5] [5] [3] [] 0 (by decide) (by decide)) perm16.symm

theorem finiteEdge49_3 : SafeCore (mutate (finiteNode 49) 3) := by
  have he := mutation_equal (finiteP 49) (prelabel (finiteP 31) perm1.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 49) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 31) perm1.symm

theorem finiteEdge50_0 : SafeCore (mutate (finiteNode 50) 0) := by
  have he := mutation_equal (finiteP 50) (prelabel (fork [3] [2] [4] [5] [11] [2]) perm5.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (finite_safe 50)
  rw [show mutate (finiteNode 50) 0=(relabel (matrix (fork [3] [2] [4] [5] [11] [2]) 0) perm5.symm) from he]
  exact IsFork.relabelled (fork_sound [3] [2] [4] [5] [11] [2] 0 (by decide) (by decide)) perm5.symm

theorem finiteEdge50_1 : SafeCore (mutate (finiteNode 50) 1) := by
  have he := mutation_equal (finiteP 50) (prelabel (finiteP 63) perm3.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 50) 0) 1)
  rw [he]
  exact Safe.framed (finite_safe 63) perm3.symm

theorem finiteEdge50_2 : SafeCore (mutate (finiteNode 50) 2) := by
  have he := mutation_equal (finiteP 50) (preverse (prelabel (finiteP 50) perm6.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 50) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 50) perm6.symm)

theorem finiteEdge50_3 : SafeCore (mutate (finiteNode 50) 3) := by
  have he := mutation_equal (finiteP 50) (prelabel (finiteP 32) perm4.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 50) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 32) perm4.symm

theorem finiteEdge51_0 : SafeCore (mutate (finiteNode 51) 0) := by
  have he := mutation_equal (finiteP 51) (prelabel (fork [4] [22] [5] [82] [19] [3]) perm4.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (finite_safe 51)
  rw [show mutate (finiteNode 51) 0=(relabel (matrix (fork [4] [22] [5] [82] [19] [3]) 0) perm4.symm) from he]
  exact IsFork.relabelled (fork_sound [4] [22] [5] [82] [19] [3] 0 (by decide) (by decide)) perm4.symm

theorem finiteEdge51_1 : SafeCore (mutate (finiteNode 51) 1) := by
  have he := mutation_equal (finiteP 51) (preverse (prelabel (fork [6] [22] [3] [128] [19] [5]) perm10.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (finite_safe 51)
  rw [show mutate (finiteNode 51) 1=(reverse (relabel (matrix (fork [6] [22] [3] [128] [19] [5]) 0) perm10.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [6] [22] [3] [128] [19] [5] 0 (by decide) (by decide)) perm10.symm)

theorem finiteEdge51_2 : SafeCore (mutate (finiteNode 51) 2) := by
  have he := mutation_equal (finiteP 51) (prelabel (finiteP 64) perm1.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 51) 0) 2)
  rw [he]
  exact Safe.framed (finite_safe 64) perm1.symm

theorem finiteEdge51_3 : SafeCore (mutate (finiteNode 51) 3) := by
  have he := mutation_equal (finiteP 51) (preverse (prelabel (finiteP 35) perm11.symm)) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 51) 0) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 35) perm11.symm)

theorem finiteEdge52_0 : SafeCore (mutate (finiteNode 52) 0) := by
  have he := mutation_equal (finiteP 52) (prelabel (finiteP 53) perm21.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 52) 0) 0)
  rw [he]
  exact Safe.framed (finite_safe 53) perm21.symm

theorem finiteEdge52_1 : SafeCore (mutate (finiteNode 52) 1) := by
  have he := mutation_equal (finiteP 52) (prelabel (generic finiteParam8_0 finiteParam8_1 finiteParam8_2 finiteParam8_3 0) perm17.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 52) 0) 1)
  rw [he]
  exact Safe.framed (finiteRegion8_safe 0) perm17.symm

theorem finiteEdge52_2 : SafeCore (mutate (finiteNode 52) 2) := by
  have he := mutation_equal (finiteP 52) (preverse (prelabel (generic finiteParam4_0 finiteParam4_1 finiteParam4_2 finiteParam4_3 0) perm3.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 52) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finiteRegion4_safe 0) perm3.symm)

theorem finiteEdge52_3 : SafeCore (mutate (finiteNode 52) 3) := by
  have he := mutation_equal (finiteP 52) (prelabel (finiteP 35) perm1.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 52) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 35) perm1.symm

theorem finiteEdge53_0 : SafeCore (mutate (finiteNode 53) 0) := by
  have he := mutation_equal (finiteP 53) (prelabel (fork [3] [2] [26] [5] [69] [4]) perm5.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (finite_safe 53)
  rw [show mutate (finiteNode 53) 0=(relabel (matrix (fork [3] [2] [26] [5] [69] [4]) 0) perm5.symm) from he]
  exact IsFork.relabelled (fork_sound [3] [2] [26] [5] [69] [4] 0 (by decide) (by decide)) perm5.symm

theorem finiteEdge53_1 : SafeCore (mutate (finiteNode 53) 1) := by
  have he := mutation_equal (finiteP 53) (preverse (prelabel (root [26] [106] [231] [4] [9] [1]) perm6.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 53) 1
  rw [show mutate (finiteNode 53) 1=(reverse (relabel (matrix (root [26] [106] [231] [4] [9] [1]) 0) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [26] [106] [231] [4] [9] [1] 0 (by decide) (by decide)) perm6.symm)

theorem finiteEdge53_2 : SafeCore (mutate (finiteNode 53) 2) := by
  have he := mutation_equal (finiteP 53) (preverse (prelabel (generic finiteParam4_0 finiteParam4_1 finiteParam4_2 finiteParam4_3 2) perm16.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 53) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finiteRegion4_safe 2) perm16.symm)

theorem finiteEdge53_3 : SafeCore (mutate (finiteNode 53) 3) := by
  have he := mutation_equal (finiteP 53) (prelabel (finiteP 52) perm21.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 53) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 52) perm21.symm

theorem finiteEdge54_0 : SafeCore (mutate (finiteNode 54) 0) := by
  have he := mutation_equal (finiteP 54) (prelabel (finiteP 66) perm21.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 54) 0) 0)
  rw [he]
  exact Safe.framed (finite_safe 66) perm21.symm

theorem finiteEdge54_1 : SafeCore (mutate (finiteNode 54) 1) := by
  have he := mutation_equal (finiteP 54) (prelabel (finiteP 67) perm5.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 54) 0) 1)
  rw [he]
  exact Safe.framed (finite_safe 67) perm5.symm

theorem finiteEdge54_2 : SafeCore (mutate (finiteNode 54) 2) := by
  have he := mutation_equal (finiteP 54) (preverse (prelabel (finiteP 63) perm6.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 54) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 63) perm6.symm)

theorem finiteEdge54_3 : SafeCore (mutate (finiteNode 54) 3) := by
  have he := mutation_equal (finiteP 54) (preverse (prelabel (finiteP 37) perm10.symm)) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 54) 0) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 37) perm10.symm)

theorem finiteEdge55_0 : SafeCore (mutate (finiteNode 55) 0) := by
  have he := mutation_equal (finiteP 55) (prelabel (fork [5] [62] [6] [297] [29] [4]) perm4.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (finite_safe 55)
  rw [show mutate (finiteNode 55) 0=(relabel (matrix (fork [5] [62] [6] [297] [29] [4]) 0) perm4.symm) from he]
  exact IsFork.relabelled (fork_sound [5] [62] [6] [297] [29] [4] 0 (by decide) (by decide)) perm4.symm

theorem finiteEdge55_1 : SafeCore (mutate (finiteNode 55) 1) := by
  have he := mutation_equal (finiteP 55) (preverse (prelabel (fork [13] [62] [4] [801] [53] [6]) perm10.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (finite_safe 55)
  rw [show mutate (finiteNode 55) 1=(reverse (relabel (matrix (fork [13] [62] [4] [801] [53] [6]) 0) perm10.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [13] [62] [4] [801] [53] [6] 0 (by decide) (by decide)) perm10.symm)

theorem finiteEdge55_2 : SafeCore (mutate (finiteNode 55) 2) := by
  have he := mutation_equal (finiteP 55) (prelabel (finiteP 38) perm1.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 55) 0) 2)
  rw [he]
  exact Safe.framed (finite_safe 38) perm1.symm

theorem finiteEdge55_3 : SafeCore (mutate (finiteNode 55) 3) := by
  have he := mutation_equal (finiteP 55) (preverse (prelabel (finiteP 40) perm11.symm)) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 55) 0) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 40) perm11.symm)

theorem finiteEdge56_0 : SafeCore (mutate (finiteNode 56) 0) := by
  have he := mutation_equal (finiteP 56) (prelabel (finiteP 58) perm21.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 56) 0) 0)
  rw [he]
  exact Safe.framed (finite_safe 58) perm21.symm

theorem finiteEdge56_1 : SafeCore (mutate (finiteNode 56) 1) := by
  have he := mutation_equal (finiteP 56) (preverse (prelabel (root [274] [9043] [1636] [33] [6] [1]) perm6.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 56) 1
  rw [show mutate (finiteNode 56) 1=(reverse (relabel (matrix (root [274] [9043] [1636] [33] [6] [1]) 0) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [274] [9043] [1636] [33] [6] [1] 0 (by decide) (by decide)) perm6.symm)

theorem finiteEdge56_2 : SafeCore (mutate (finiteNode 56) 2) := by
  have he := mutation_equal (finiteP 56) (preverse (prelabel (generic finiteParam5_0 finiteParam5_1 finiteParam5_2 finiteParam5_3 0) perm3.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 56) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finiteRegion5_safe 0) perm3.symm)

theorem finiteEdge56_3 : SafeCore (mutate (finiteNode 56) 3) := by
  have he := mutation_equal (finiteP 56) (prelabel (finiteP 41) perm1.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 56) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 41) perm1.symm

theorem finiteEdge57_0 : SafeCore (mutate (finiteNode 57) 0) := by
  have he := mutation_equal (finiteP 57) (prelabel (fork [6] [5] [233] [29] [1359] [7]) perm5.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (finite_safe 57)
  rw [show mutate (finiteNode 57) 0=(relabel (matrix (fork [6] [5] [233] [29] [1359] [7]) 0) perm5.symm) from he]
  exact IsFork.relabelled (fork_sound [6] [5] [233] [29] [1359] [7] 0 (by decide) (by decide)) perm5.symm

theorem finiteEdge57_1 : SafeCore (mutate (finiteNode 57) 1) := by
  have he := mutation_equal (finiteP 57) (preverse (prelabel (root [233] [1636] [9081] [7] [39] [1]) perm6.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 57) 1
  rw [show mutate (finiteNode 57) 1=(reverse (relabel (matrix (root [233] [1636] [9081] [7] [39] [1]) 0) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [233] [1636] [9081] [7] [39] [1] 0 (by decide) (by decide)) perm6.symm)

theorem finiteEdge57_2 : SafeCore (mutate (finiteNode 57) 2) := by
  have he := mutation_equal (finiteP 57) (preverse (prelabel (generic finiteParam6_0 finiteParam6_1 finiteParam6_2 finiteParam6_3 2) perm16.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 57) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finiteRegion6_safe 2) perm16.symm)

theorem finiteEdge57_3 : SafeCore (mutate (finiteNode 57) 3) := by
  have he := mutation_equal (finiteP 57) (prelabel (finiteP 42) perm21.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 57) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 42) perm21.symm

theorem finiteEdge58_0 : SafeCore (mutate (finiteNode 58) 0) := by
  have he := mutation_equal (finiteP 58) (prelabel (fork [8] [7] [2186] [55] [17214] [33]) perm5.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (finite_safe 58)
  rw [show mutate (finiteNode 58) 0=(relabel (matrix (fork [8] [7] [2186] [55] [17214] [33]) 0) perm5.symm) from he]
  exact IsFork.relabelled (fork_sound [8] [7] [2186] [55] [17214] [33] 0 (by decide) (by decide)) perm5.symm

theorem finiteEdge58_1 : SafeCore (mutate (finiteNode 58) 1) := by
  have he := mutation_equal (finiteP 58) (preverse (prelabel (root [2186] [72145] [598956] [33] [274] [1]) perm6.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 58) 1
  rw [show mutate (finiteNode 58) 1=(reverse (relabel (matrix (root [2186] [72145] [598956] [33] [274] [1]) 0) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [2186] [72145] [598956] [33] [274] [1] 0 (by decide) (by decide)) perm6.symm)

theorem finiteEdge58_2 : SafeCore (mutate (finiteNode 58) 2) := by
  have he := mutation_equal (finiteP 58) (preverse (prelabel (generic finiteParam5_0 finiteParam5_1 finiteParam5_2 finiteParam5_3 2) perm16.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 58) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finiteRegion5_safe 2) perm16.symm)

theorem finiteEdge58_3 : SafeCore (mutate (finiteNode 58) 3) := by
  have he := mutation_equal (finiteP 58) (prelabel (finiteP 56) perm21.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 58) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 56) perm21.symm

theorem finiteEdge59_0 : SafeCore (mutate (finiteNode 59) 0) := by
  have he := mutation_equal (finiteP 59) (prelabel (zero finiteParam9_0 finiteParam9_1 finiteParam9_2 finiteParam9_3 0) perm6.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 59) 0) 0)
  rw [he]
  exact Safe.framed (finiteRegion9_safe 0) perm6.symm

theorem finiteEdge59_1 : SafeCore (mutate (finiteNode 59) 1) := by
  have he := mutation_equal (finiteP 59) (prelabel (finiteP 60) perm0.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 59) 0) 1)
  rw [he]
  exact Safe.framed (finite_safe 60) perm0.symm

theorem finiteEdge59_2 : SafeCore (mutate (finiteNode 59) 2) := by
  have he := mutation_equal (finiteP 59) (prelabel (root [7] [130] [34] [19] [5] []) perm16.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 59) 2
  rw [show mutate (finiteNode 59) 2=(relabel (matrix (root [7] [130] [34] [19] [5] []) 0) perm16.symm) from he]
  exact IsRoot.relabelled (root_sound [7] [130] [34] [19] [5] [] 0 (by decide) (by decide)) perm16.symm

theorem finiteEdge59_3 : SafeCore (mutate (finiteNode 59) 3) := by
  have he := mutation_equal (finiteP 59) (prelabel (finiteP 46) perm1.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 59) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 46) perm1.symm

theorem finiteEdge60_0 : SafeCore (mutate (finiteNode 60) 0) := by
  have he := mutation_equal (finiteP 60) (prelabel (zero finiteParam9_0 finiteParam9_1 finiteParam9_2 finiteParam9_3 1) perm6.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 60) 0) 0)
  rw [he]
  exact Safe.framed (finiteRegion9_safe 1) perm6.symm

theorem finiteEdge60_1 : SafeCore (mutate (finiteNode 60) 1) := by
  have he := mutation_equal (finiteP 60) (prelabel (finiteP 59) perm0.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 60) 0) 1)
  rw [he]
  exact Safe.framed (finite_safe 59) perm0.symm

theorem finiteEdge60_2 : SafeCore (mutate (finiteNode 60) 2) := by
  have he := mutation_equal (finiteP 60) (preverse (prelabel (root [19] [95] [35] [5] [2] [1]) perm12.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 60) 2
  rw [show mutate (finiteNode 60) 2=(reverse (relabel (matrix (root [19] [95] [35] [5] [2] [1]) 0) perm12.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [19] [95] [35] [5] [2] [1] 0 (by decide) (by decide)) perm12.symm)

theorem finiteEdge60_3 : SafeCore (mutate (finiteNode 60) 3) := by
  have he := mutation_equal (finiteP 60) (prelabel (finiteP 47) perm3.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 60) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 47) perm3.symm

theorem finiteEdge61_0 : SafeCore (mutate (finiteNode 61) 0) := by
  have he := mutation_equal (finiteP 61) (preverse (prelabel (root [3] [13] [8] [5] [3] [1]) perm4.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 61) 0
  rw [show mutate (finiteNode 61) 0=(reverse (relabel (matrix (root [3] [13] [8] [5] [3] [1]) 0) perm4.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [3] [13] [8] [5] [3] [1] 0 (by decide) (by decide)) perm4.symm)

theorem finiteEdge61_1 : SafeCore (mutate (finiteNode 61) 1) := by
  have he := mutation_equal (finiteP 61) (prelabel (finiteP 68) perm3.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 61) 0) 1)
  rw [he]
  exact Safe.framed (finite_safe 68) perm3.symm

theorem finiteEdge61_2 : SafeCore (mutate (finiteNode 61) 2) := by
  have he := mutation_equal (finiteP 61) (prelabel (finiteP 62) perm4.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 61) 0) 2)
  rw [he]
  exact Safe.framed (finite_safe 62) perm4.symm

theorem finiteEdge61_3 : SafeCore (mutate (finiteNode 61) 3) := by
  have he := mutation_equal (finiteP 61) (prelabel (finiteP 48) perm3.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 61) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 48) perm3.symm

theorem finiteEdge62_0 : SafeCore (mutate (finiteNode 62) 0) := by
  have he := mutation_equal (finiteP 62) (prelabel (zero finiteParam7_0 finiteParam7_1 finiteParam7_2 finiteParam7_3 1) perm6.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 62) 0) 0)
  rw [he]
  exact Safe.framed (finiteRegion7_safe 1) perm6.symm

theorem finiteEdge62_1 : SafeCore (mutate (finiteNode 62) 1) := by
  have he := mutation_equal (finiteP 62) (prelabel (finiteP 49) perm0.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 62) 0) 1)
  rw [he]
  exact Safe.framed (finite_safe 49) perm0.symm

theorem finiteEdge62_2 : SafeCore (mutate (finiteNode 62) 2) := by
  have he := mutation_equal (finiteP 62) (preverse (prelabel (finiteP 69) perm7.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 62) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 69) perm7.symm)

theorem finiteEdge62_3 : SafeCore (mutate (finiteNode 62) 3) := by
  have he := mutation_equal (finiteP 62) (prelabel (finiteP 61) perm3.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 62) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 61) perm3.symm

theorem finiteEdge63_0 : SafeCore (mutate (finiteNode 63) 0) := by
  have he := mutation_equal (finiteP 63) (prelabel (finiteP 70) perm21.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 63) 0) 0)
  rw [he]
  exact Safe.framed (finite_safe 70) perm21.symm

theorem finiteEdge63_1 : SafeCore (mutate (finiteNode 63) 1) := by
  have he := mutation_equal (finiteP 63) (prelabel (finiteP 71) perm5.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 63) 0) 1)
  rw [he]
  exact Safe.framed (finite_safe 71) perm5.symm

theorem finiteEdge63_2 : SafeCore (mutate (finiteNode 63) 2) := by
  have he := mutation_equal (finiteP 63) (preverse (prelabel (finiteP 54) perm6.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 63) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 54) perm6.symm)

theorem finiteEdge63_3 : SafeCore (mutate (finiteNode 63) 3) := by
  have he := mutation_equal (finiteP 63) (prelabel (finiteP 50) perm4.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 63) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 50) perm4.symm

theorem finiteEdge64_0 : SafeCore (mutate (finiteNode 64) 0) := by
  have he := mutation_equal (finiteP 64) (prelabel (finiteP 65) perm21.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 64) 0) 0)
  rw [he]
  exact Safe.framed (finite_safe 65) perm21.symm

theorem finiteEdge64_1 : SafeCore (mutate (finiteNode 64) 1) := by
  have he := mutation_equal (finiteP 64) (preverse (prelabel (root [37] [223] [106] [6] [3] [1]) perm6.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 64) 1
  rw [show mutate (finiteNode 64) 1=(reverse (relabel (matrix (root [37] [223] [106] [6] [3] [1]) 0) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [37] [223] [106] [6] [3] [1] 0 (by decide) (by decide)) perm6.symm)

theorem finiteEdge64_2 : SafeCore (mutate (finiteNode 64) 2) := by
  have he := mutation_equal (finiteP 64) (preverse (prelabel (generic finiteParam8_0 finiteParam8_1 finiteParam8_2 finiteParam8_3 0) perm3.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 64) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finiteRegion8_safe 0) perm3.symm)

theorem finiteEdge64_3 : SafeCore (mutate (finiteNode 64) 3) := by
  have he := mutation_equal (finiteP 64) (prelabel (finiteP 51) perm1.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 64) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 51) perm1.symm

theorem finiteEdge65_0 : SafeCore (mutate (finiteNode 65) 0) := by
  have he := mutation_equal (finiteP 65) (prelabel (fork [5] [4] [182] [19] [873] [6]) perm5.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (finite_safe 65)
  rw [show mutate (finiteNode 65) 0=(relabel (matrix (fork [5] [4] [182] [19] [873] [6]) 0) perm5.symm) from he]
  exact IsFork.relabelled (fork_sound [5] [4] [182] [19] [873] [6] 0 (by decide) (by decide)) perm5.symm

theorem finiteEdge65_1 : SafeCore (mutate (finiteNode 65) 1) := by
  have he := mutation_equal (finiteP 65) (preverse (prelabel (root [182] [1096] [6729] [6] [37] [1]) perm6.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 65) 1
  rw [show mutate (finiteNode 65) 1=(reverse (relabel (matrix (root [182] [1096] [6729] [6] [37] [1]) 0) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [182] [1096] [6729] [6] [37] [1] 0 (by decide) (by decide)) perm6.symm)

theorem finiteEdge65_2 : SafeCore (mutate (finiteNode 65) 2) := by
  have he := mutation_equal (finiteP 65) (preverse (prelabel (generic finiteParam8_0 finiteParam8_1 finiteParam8_2 finiteParam8_3 2) perm16.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 65) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finiteRegion8_safe 2) perm16.symm)

theorem finiteEdge65_3 : SafeCore (mutate (finiteNode 65) 3) := by
  have he := mutation_equal (finiteP 65) (prelabel (finiteP 64) perm21.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 65) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 64) perm21.symm

theorem finiteEdge66_0 : SafeCore (mutate (finiteNode 66) 0) := by
  have he := mutation_equal (finiteP 66) (preverse (prelabel (root [3] [71] [5] [27] [2] [1]) perm4.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 66) 0
  rw [show mutate (finiteNode 66) 0=(reverse (relabel (matrix (root [3] [71] [5] [27] [2] [1]) 0) perm4.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [3] [71] [5] [27] [2] [1] 0 (by decide) (by decide)) perm4.symm)

theorem finiteEdge66_1 : SafeCore (mutate (finiteNode 66) 1) := by
  have he := mutation_equal (finiteP 66) (prelabel (finiteP 72) perm5.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 66) 0) 1)
  rw [he]
  exact Safe.framed (finite_safe 72) perm5.symm

theorem finiteEdge66_2 : SafeCore (mutate (finiteNode 66) 2) := by
  have he := mutation_equal (finiteP 66) (preverse (prelabel (finiteP 73) perm6.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 66) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 73) perm6.symm)

theorem finiteEdge66_3 : SafeCore (mutate (finiteNode 66) 3) := by
  have he := mutation_equal (finiteP 66) (prelabel (finiteP 54) perm21.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 66) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 54) perm21.symm

theorem finiteEdge67_0 : SafeCore (mutate (finiteNode 67) 0) := by
  have he := mutation_equal (finiteP 67) (preverse (prelabel (root [10] [109] [267] [11] [27] [1]) perm5.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 67) 0
  rw [show mutate (finiteNode 67) 0=(reverse (relabel (matrix (root [10] [109] [267] [11] [27] [1]) 0) perm5.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [10] [109] [267] [11] [27] [1] 0 (by decide) (by decide)) perm5.symm)

theorem finiteEdge67_1 : SafeCore (mutate (finiteNode 67) 1) := by
  have he := mutation_equal (finiteP 67) (prelabel (finiteP 74) perm5.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 67) 0) 1)
  rw [he]
  exact Safe.framed (finite_safe 74) perm5.symm

theorem finiteEdge67_2 : SafeCore (mutate (finiteNode 67) 2) := by
  have he := mutation_equal (finiteP 67) (prelabel (finiteP 75) perm1.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 67) 0) 2)
  rw [he]
  exact Safe.framed (finite_safe 75) perm1.symm

theorem finiteEdge67_3 : SafeCore (mutate (finiteNode 67) 3) := by
  have he := mutation_equal (finiteP 67) (prelabel (finiteP 54) perm5.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 67) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 54) perm5.symm

theorem finiteEdge68_0 : SafeCore (mutate (finiteNode 68) 0) := by
  have he := mutation_equal (finiteP 68) (preverse (prelabel (root [5] [39] [33] [8] [7] [1]) perm4.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 68) 0
  rw [show mutate (finiteNode 68) 0=(reverse (relabel (matrix (root [5] [39] [33] [8] [7] [1]) 0) perm4.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [5] [39] [33] [8] [7] [1] 0 (by decide) (by decide)) perm4.symm)

theorem finiteEdge68_1 : SafeCore (mutate (finiteNode 68) 1) := by
  have he := mutation_equal (finiteP 68) (prelabel (finiteP 76) perm3.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 68) 0) 1)
  rw [he]
  exact Safe.framed (finite_safe 76) perm3.symm

theorem finiteEdge68_2 : SafeCore (mutate (finiteNode 68) 2) := by
  have he := mutation_equal (finiteP 68) (prelabel (finiteP 77) perm4.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 68) 0) 2)
  rw [he]
  exact Safe.framed (finite_safe 77) perm4.symm

theorem finiteEdge68_3 : SafeCore (mutate (finiteNode 68) 3) := by
  have he := mutation_equal (finiteP 68) (prelabel (finiteP 61) perm4.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 68) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 61) perm4.symm

theorem finiteEdge69_0 : SafeCore (mutate (finiteNode 69) 0) := by
  have he := mutation_equal (finiteP 69) (prelabel (fork [3] [2] [15] [5] [40] [3]) perm5.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (finite_safe 69)
  rw [show mutate (finiteNode 69) 0=(relabel (matrix (fork [3] [2] [15] [5] [40] [3]) 0) perm5.symm) from he]
  exact IsFork.relabelled (fork_sound [3] [2] [15] [5] [40] [3] 0 (by decide) (by decide)) perm5.symm

theorem finiteEdge69_1 : SafeCore (mutate (finiteNode 69) 1) := by
  have he := mutation_equal (finiteP 69) (preverse (prelabel (root [15] [47] [72] [3] [5] [1]) perm6.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 69) 1
  rw [show mutate (finiteNode 69) 1=(reverse (relabel (matrix (root [15] [47] [72] [3] [5] [1]) 0) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [15] [47] [72] [3] [5] [1] 0 (by decide) (by decide)) perm6.symm)

theorem finiteEdge69_2 : SafeCore (mutate (finiteNode 69) 2) := by
  have he := mutation_equal (finiteP 69) (preverse (prelabel (finiteP 76) perm6.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 69) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 76) perm6.symm)

theorem finiteEdge69_3 : SafeCore (mutate (finiteNode 69) 3) := by
  have he := mutation_equal (finiteP 69) (preverse (prelabel (finiteP 62) perm7.symm)) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 69) 0) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 62) perm7.symm)

theorem finiteEdge70_0 : SafeCore (mutate (finiteNode 70) 0) := by
  have he := mutation_equal (finiteP 70) (preverse (prelabel (root [4] [142] [11] [38] [3] [1]) perm4.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 70) 0
  rw [show mutate (finiteNode 70) 0=(reverse (relabel (matrix (root [4] [142] [11] [38] [3] [1]) 0) perm4.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [4] [142] [11] [38] [3] [1] 0 (by decide) (by decide)) perm4.symm)

theorem finiteEdge70_1 : SafeCore (mutate (finiteNode 70) 1) := by
  have he := mutation_equal (finiteP 70) (prelabel (finiteP 78) perm5.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 70) 0) 1)
  rw [he]
  exact Safe.framed (finite_safe 78) perm5.symm

theorem finiteEdge70_2 : SafeCore (mutate (finiteNode 70) 2) := by
  have he := mutation_equal (finiteP 70) (preverse (prelabel (finiteP 75) perm6.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 70) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 75) perm6.symm)

theorem finiteEdge70_3 : SafeCore (mutate (finiteNode 70) 3) := by
  have he := mutation_equal (finiteP 70) (prelabel (finiteP 63) perm21.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 70) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 63) perm21.symm

theorem finiteEdge71_0 : SafeCore (mutate (finiteNode 71) 0) := by
  have he := mutation_equal (finiteP 71) (preverse (prelabel (root [10] [109] [158] [11] [16] [1]) perm5.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 71) 0
  rw [show mutate (finiteNode 71) 0=(reverse (relabel (matrix (root [10] [109] [158] [11] [16] [1]) 0) perm5.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [10] [109] [158] [11] [16] [1] 0 (by decide) (by decide)) perm5.symm)

theorem finiteEdge71_1 : SafeCore (mutate (finiteNode 71) 1) := by
  have he := mutation_equal (finiteP 71) (prelabel (finiteP 79) perm5.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 71) 0) 1)
  rw [he]
  exact Safe.framed (finite_safe 79) perm5.symm

theorem finiteEdge71_2 : SafeCore (mutate (finiteNode 71) 2) := by
  have he := mutation_equal (finiteP 71) (prelabel (finiteP 73) perm1.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 71) 0) 2)
  rw [he]
  exact Safe.framed (finite_safe 73) perm1.symm

theorem finiteEdge71_3 : SafeCore (mutate (finiteNode 71) 3) := by
  have he := mutation_equal (finiteP 71) (prelabel (finiteP 63) perm5.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 71) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 63) perm5.symm

theorem finiteEdge72_0 : SafeCore (mutate (finiteNode 72) 0) := by
  have he := mutation_equal (finiteP 72) (preverse (prelabel (root [27] [782] [7199] [29] [267] [1]) perm5.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 72) 0
  rw [show mutate (finiteNode 72) 0=(reverse (relabel (matrix (root [27] [782] [7199] [29] [267] [1]) 0) perm5.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [27] [782] [7199] [29] [267] [1] 0 (by decide) (by decide)) perm5.symm)

theorem finiteEdge72_1 : SafeCore (mutate (finiteNode 72) 1) := by
  have he := mutation_equal (finiteP 72) (prelabel (finiteP 80) perm5.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 72) 0) 1)
  rw [he]
  exact Safe.framed (finite_safe 80) perm5.symm

theorem finiteEdge72_2 : SafeCore (mutate (finiteNode 72) 2) := by
  have he := mutation_equal (finiteP 72) (prelabel (finiteP 81) perm1.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 72) 0) 2)
  rw [he]
  exact Safe.framed (finite_safe 81) perm1.symm

theorem finiteEdge72_3 : SafeCore (mutate (finiteNode 72) 3) := by
  have he := mutation_equal (finiteP 72) (prelabel (finiteP 66) perm5.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 72) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 66) perm5.symm

theorem finiteEdge73_0 : SafeCore (mutate (finiteNode 73) 0) := by
  have he := mutation_equal (finiteP 73) (prelabel (finiteP 82) perm21.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 73) 0) 0)
  rw [he]
  exact Safe.framed (finite_safe 82) perm21.symm

theorem finiteEdge73_1 : SafeCore (mutate (finiteNode 73) 1) := by
  have he := mutation_equal (finiteP 73) (prelabel (generic finiteParam10_0 finiteParam10_1 finiteParam10_2 finiteParam10_3 0) perm17.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 73) 0) 1)
  rw [he]
  exact Safe.framed (finiteRegion10_safe 0) perm17.symm

theorem finiteEdge73_2 : SafeCore (mutate (finiteNode 73) 2) := by
  have he := mutation_equal (finiteP 73) (preverse (prelabel (finiteP 66) perm6.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 73) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 66) perm6.symm)

theorem finiteEdge73_3 : SafeCore (mutate (finiteNode 73) 3) := by
  have he := mutation_equal (finiteP 73) (prelabel (finiteP 71) perm1.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 73) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 71) perm1.symm

theorem finiteEdge74_0 : SafeCore (mutate (finiteNode 74) 0) := by
  have he := mutation_equal (finiteP 74) (prelabel (fork [27] [71] [11] [1914] [298] [4]) perm4.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (finite_safe 74)
  rw [show mutate (finiteNode 74) 0=(relabel (matrix (fork [27] [71] [11] [1914] [298] [4]) 0) perm4.symm) from he]
  exact IsFork.relabelled (fork_sound [27] [71] [11] [1914] [298] [4] 0 (by decide) (by decide)) perm4.symm

theorem finiteEdge74_1 : SafeCore (mutate (finiteNode 74) 1) := by
  have he := mutation_equal (finiteP 74) (preverse (prelabel (fork [3] [71] [4] [186] [11] [11]) perm10.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (finite_safe 74)
  rw [show mutate (finiteNode 74) 1=(reverse (relabel (matrix (fork [3] [71] [4] [186] [11] [11]) 0) perm10.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [3] [71] [4] [186] [11] [11] 0 (by decide) (by decide)) perm10.symm)

theorem finiteEdge74_2 : SafeCore (mutate (finiteNode 74) 2) := by
  have he := mutation_equal (finiteP 74) (preverse (prelabel (finiteP 85) perm7.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 74) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 85) perm7.symm)

theorem finiteEdge74_3 : SafeCore (mutate (finiteNode 74) 3) := by
  have he := mutation_equal (finiteP 74) (prelabel (finiteP 67) perm5.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 74) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 67) perm5.symm

theorem finiteEdge75_0 : SafeCore (mutate (finiteNode 75) 0) := by
  have he := mutation_equal (finiteP 75) (prelabel (finiteP 86) perm21.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 75) 0) 0)
  rw [he]
  exact Safe.framed (finite_safe 86) perm21.symm

theorem finiteEdge75_1 : SafeCore (mutate (finiteNode 75) 1) := by
  have he := mutation_equal (finiteP 75) (prelabel (generic finiteParam11_0 finiteParam11_1 finiteParam11_2 finiteParam11_3 0) perm17.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 75) 0) 1)
  rw [he]
  exact Safe.framed (finiteRegion11_safe 0) perm17.symm

theorem finiteEdge75_2 : SafeCore (mutate (finiteNode 75) 2) := by
  have he := mutation_equal (finiteP 75) (preverse (prelabel (finiteP 70) perm6.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 75) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 70) perm6.symm)

theorem finiteEdge75_3 : SafeCore (mutate (finiteNode 75) 3) := by
  have he := mutation_equal (finiteP 75) (prelabel (finiteP 67) perm1.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 75) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 67) perm1.symm

theorem finiteEdge76_0 : SafeCore (mutate (finiteNode 76) 0) := by
  have he := mutation_equal (finiteP 76) (prelabel (fork [8] [3] [15] [23] [119] [2]) perm5.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (finite_safe 76)
  rw [show mutate (finiteNode 76) 0=(relabel (matrix (fork [8] [3] [15] [23] [119] [2]) 0) perm5.symm) from he]
  exact IsFork.relabelled (fork_sound [8] [3] [15] [23] [119] [2] 0 (by decide) (by decide)) perm5.symm

theorem finiteEdge76_1 : SafeCore (mutate (finiteNode 76) 1) := by
  have he := mutation_equal (finiteP 76) (prelabel (generic finiteParam12_0 finiteParam12_1 finiteParam12_2 finiteParam12_3 0) perm17.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 76) 0) 1)
  rw [he]
  exact Safe.framed (finiteRegion12_safe 0) perm17.symm

theorem finiteEdge76_2 : SafeCore (mutate (finiteNode 76) 2) := by
  have he := mutation_equal (finiteP 76) (preverse (prelabel (finiteP 69) perm6.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 76) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 69) perm6.symm)

theorem finiteEdge76_3 : SafeCore (mutate (finiteNode 76) 3) := by
  have he := mutation_equal (finiteP 76) (prelabel (finiteP 68) perm4.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 76) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 68) perm4.symm

theorem finiteEdge77_0 : SafeCore (mutate (finiteNode 77) 0) := by
  have he := mutation_equal (finiteP 77) (prelabel (fork [7] [9] [8] [61] [57] [3]) perm4.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (finite_safe 77)
  rw [show mutate (finiteNode 77) 0=(relabel (matrix (fork [7] [9] [8] [61] [57] [3]) 0) perm4.symm) from he]
  exact IsFork.relabelled (fork_sound [7] [9] [8] [61] [57] [3] 0 (by decide) (by decide)) perm4.symm

theorem finiteEdge77_1 : SafeCore (mutate (finiteNode 77) 1) := by
  have he := mutation_equal (finiteP 77) (preverse (prelabel (fork [2] [9] [3] [11] [5] [8]) perm10.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (finite_safe 77)
  rw [show mutate (finiteNode 77) 1=(reverse (relabel (matrix (fork [2] [9] [3] [11] [5] [8]) 0) perm10.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [2] [9] [3] [11] [5] [8] 0 (by decide) (by decide)) perm10.symm)

theorem finiteEdge77_2 : SafeCore (mutate (finiteNode 77) 2) := by
  have he := mutation_equal (finiteP 77) (preverse (prelabel (finiteP 88) perm7.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 77) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 88) perm7.symm)

theorem finiteEdge77_3 : SafeCore (mutate (finiteNode 77) 3) := by
  have he := mutation_equal (finiteP 77) (prelabel (finiteP 68) perm3.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 77) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 68) perm3.symm

theorem finiteEdge78_0 : SafeCore (mutate (finiteNode 78) 0) := by
  have he := mutation_equal (finiteP 78) (preverse (prelabel (root [38] [1557] [14278] [41] [376] [1]) perm5.symm)) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 78) 0
  rw [show mutate (finiteNode 78) 0=(reverse (relabel (matrix (root [38] [1557] [14278] [41] [376] [1]) 0) perm5.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [38] [1557] [14278] [41] [376] [1] 0 (by decide) (by decide)) perm5.symm)

theorem finiteEdge78_1 : SafeCore (mutate (finiteNode 78) 1) := by
  have he := mutation_equal (finiteP 78) (prelabel (finiteP 90) perm5.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 78) 0) 1)
  rw [he]
  exact Safe.framed (finite_safe 90) perm5.symm

theorem finiteEdge78_2 : SafeCore (mutate (finiteNode 78) 2) := by
  have he := mutation_equal (finiteP 78) (prelabel (finiteP 91) perm1.symm) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 78) 0) 2)
  rw [he]
  exact Safe.framed (finite_safe 91) perm1.symm

theorem finiteEdge78_3 : SafeCore (mutate (finiteNode 78) 3) := by
  have he := mutation_equal (finiteP 78) (prelabel (finiteP 70) perm5.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 78) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 70) perm5.symm

theorem finiteEdge79_0 : SafeCore (mutate (finiteNode 79) 0) := by
  have he := mutation_equal (finiteP 79) (prelabel (fork [16] [22] [11] [350] [177] [3]) perm4.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (finite_safe 79)
  rw [show mutate (finiteNode 79) 0=(relabel (matrix (fork [16] [22] [11] [350] [177] [3]) 0) perm4.symm) from he]
  exact IsFork.relabelled (fork_sound [16] [22] [11] [350] [177] [3] 0 (by decide) (by decide)) perm4.symm

theorem finiteEdge79_1 : SafeCore (mutate (finiteNode 79) 1) := by
  have he := mutation_equal (finiteP 79) (preverse (prelabel (fork [2] [22] [3] [28] [5] [11]) perm10.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (finite_safe 79)
  rw [show mutate (finiteNode 79) 1=(reverse (relabel (matrix (fork [2] [22] [3] [28] [5] [11]) 0) perm10.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [2] [22] [3] [28] [5] [11] 0 (by decide) (by decide)) perm10.symm)

theorem finiteEdge79_2 : SafeCore (mutate (finiteNode 79) 2) := by
  have he := mutation_equal (finiteP 79) (preverse (prelabel (finiteP 83) perm7.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 79) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 83) perm7.symm)

theorem finiteEdge79_3 : SafeCore (mutate (finiteNode 79) 3) := by
  have he := mutation_equal (finiteP 79) (prelabel (finiteP 71) perm5.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 79) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 71) perm5.symm

theorem finiteEdge80_0 : SafeCore (mutate (finiteNode 80) 0) := by
  have he := mutation_equal (finiteP 80) (prelabel (fork [267] [2643] [29] [705671] [7744] [11]) perm4.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (finite_safe 80)
  rw [show mutate (finiteNode 80) 0=(relabel (matrix (fork [267] [2643] [29] [705671] [7744] [11]) 0) perm4.symm) from he]
  exact IsFork.relabelled (fork_sound [267] [2643] [29] [705671] [7744] [11] 0 (by decide) (by decide)) perm4.symm

theorem finiteEdge80_1 : SafeCore (mutate (finiteNode 80) 1) := by
  have he := mutation_equal (finiteP 80) (preverse (prelabel (fork [10] [2643] [11] [26163] [109] [29]) perm10.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (finite_safe 80)
  rw [show mutate (finiteNode 80) 1=(reverse (relabel (matrix (fork [10] [2643] [11] [26163] [109] [29]) 0) perm10.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [10] [2643] [11] [26163] [109] [29] 0 (by decide) (by decide)) perm10.symm)

theorem finiteEdge80_2 : SafeCore (mutate (finiteNode 80) 2) := by
  have he := mutation_equal (finiteP 80) (preverse (prelabel (finiteP 92) perm7.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 80) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 92) perm7.symm)

theorem finiteEdge80_3 : SafeCore (mutate (finiteNode 80) 3) := by
  have he := mutation_equal (finiteP 80) (prelabel (finiteP 72) perm5.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 80) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 72) perm5.symm

theorem finiteEdge81_0 : SafeCore (mutate (finiteNode 81) 0) := by
  have he := mutation_equal (finiteP 81) (prelabel (fork [29] [2] [296] [57] [8583] [10]) perm5.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (finite_safe 81)
  rw [show mutate (finiteNode 81) 0=(relabel (matrix (fork [29] [2] [296] [57] [8583] [10]) 0) perm5.symm) from he]
  exact IsFork.relabelled (fork_sound [29] [2] [296] [57] [8583] [10] 0 (by decide) (by decide)) perm5.symm

theorem finiteEdge81_1 : SafeCore (mutate (finiteNode 81) 1) := by
  have he := mutation_equal (finiteP 81) (prelabel (generic finiteParam13_0 finiteParam13_1 finiteParam13_2 finiteParam13_3 0) perm17.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 81) 0) 1)
  rw [he]
  exact Safe.framed (finiteRegion13_safe 0) perm17.symm

theorem finiteEdge81_2 : SafeCore (mutate (finiteNode 81) 2) := by
  have he := mutation_equal (finiteP 81) (preverse (prelabel (finiteP 82) perm6.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 81) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 82) perm6.symm)

theorem finiteEdge81_3 : SafeCore (mutate (finiteNode 81) 3) := by
  have he := mutation_equal (finiteP 81) (prelabel (finiteP 72) perm1.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 81) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 72) perm1.symm

theorem finiteEdge82_0 : SafeCore (mutate (finiteNode 82) 0) := by
  have he := mutation_equal (finiteP 82) (prelabel (fork [11] [10] [296] [109] [3229] [2]) perm5.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (finite_safe 82)
  rw [show mutate (finiteNode 82) 0=(relabel (matrix (fork [11] [10] [296] [109] [3229] [2]) 0) perm5.symm) from he]
  exact IsFork.relabelled (fork_sound [11] [10] [296] [109] [3229] [2] 0 (by decide) (by decide)) perm5.symm

theorem finiteEdge82_1 : SafeCore (mutate (finiteNode 82) 1) := by
  have he := mutation_equal (finiteP 82) (preverse (prelabel (root [296] [602] [7981] [2] [27] [1]) perm6.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 82) 1
  rw [show mutate (finiteNode 82) 1=(reverse (relabel (matrix (root [296] [602] [7981] [2] [27] [1]) 0) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [296] [602] [7981] [2] [27] [1] 0 (by decide) (by decide)) perm6.symm)

theorem finiteEdge82_2 : SafeCore (mutate (finiteNode 82) 2) := by
  have he := mutation_equal (finiteP 82) (preverse (prelabel (finiteP 81) perm6.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 82) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 81) perm6.symm)

theorem finiteEdge82_3 : SafeCore (mutate (finiteNode 82) 3) := by
  have he := mutation_equal (finiteP 82) (prelabel (finiteP 73) perm21.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 82) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 73) perm21.symm

theorem finiteEdge83_0 : SafeCore (mutate (finiteNode 83) 0) := by
  have he := mutation_equal (finiteP 83) (prelabel (finiteP 84) perm21.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 83) 0) 0)
  rw [he]
  exact Safe.framed (finite_safe 84) perm21.symm

theorem finiteEdge83_1 : SafeCore (mutate (finiteNode 83) 1) := by
  have he := mutation_equal (finiteP 83) (preverse (prelabel (root [55] [881] [602] [16] [11] [1]) perm6.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 83) 1
  rw [show mutate (finiteNode 83) 1=(reverse (relabel (matrix (root [55] [881] [602] [16] [11] [1]) 0) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [55] [881] [602] [16] [11] [1] 0 (by decide) (by decide)) perm6.symm)

theorem finiteEdge83_2 : SafeCore (mutate (finiteNode 83) 2) := by
  have he := mutation_equal (finiteP 83) (preverse (prelabel (generic finiteParam10_0 finiteParam10_1 finiteParam10_2 finiteParam10_3 0) perm3.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 83) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finiteRegion10_safe 0) perm3.symm)

theorem finiteEdge83_3 : SafeCore (mutate (finiteNode 83) 3) := by
  have he := mutation_equal (finiteP 83) (preverse (prelabel (finiteP 79) perm7.symm)) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 83) 0) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 79) perm7.symm)

theorem finiteEdge84_0 : SafeCore (mutate (finiteNode 84) 0) := by
  have he := mutation_equal (finiteP 84) (prelabel (fork [3] [2] [154] [5] [407] [16]) perm5.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (finite_safe 84)
  rw [show mutate (finiteNode 84) 0=(relabel (matrix (fork [3] [2] [154] [5] [407] [16]) 0) perm5.symm) from he]
  exact IsFork.relabelled (fork_sound [3] [2] [154] [5] [407] [16] 0 (by decide) (by decide)) perm5.symm

theorem finiteEdge84_1 : SafeCore (mutate (finiteNode 84) 1) := by
  have he := mutation_equal (finiteP 84) (preverse (prelabel (root [154] [2466] [8467] [16] [55] [1]) perm6.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 84) 1
  rw [show mutate (finiteNode 84) 1=(reverse (relabel (matrix (root [154] [2466] [8467] [16] [55] [1]) 0) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [154] [2466] [8467] [16] [55] [1] 0 (by decide) (by decide)) perm6.symm)

theorem finiteEdge84_2 : SafeCore (mutate (finiteNode 84) 2) := by
  have he := mutation_equal (finiteP 84) (preverse (prelabel (generic finiteParam10_0 finiteParam10_1 finiteParam10_2 finiteParam10_3 2) perm16.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 84) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finiteRegion10_safe 2) perm16.symm)

theorem finiteEdge84_3 : SafeCore (mutate (finiteNode 84) 3) := by
  have he := mutation_equal (finiteP 84) (prelabel (finiteP 83) perm21.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 84) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 83) perm21.symm

theorem finiteEdge85_0 : SafeCore (mutate (finiteNode 85) 0) := by
  have he := mutation_equal (finiteP 85) (prelabel (finiteP 87) perm21.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 85) 0) 0)
  rw [he]
  exact Safe.framed (finite_safe 87) perm21.symm

theorem finiteEdge85_1 : SafeCore (mutate (finiteNode 85) 1) := by
  have he := mutation_equal (finiteP 85) (preverse (prelabel (root [115] [3106] [1261] [27] [11] [1]) perm6.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 85) 1
  rw [show mutate (finiteNode 85) 1=(reverse (relabel (matrix (root [115] [3106] [1261] [27] [11] [1]) 0) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [115] [3106] [1261] [27] [11] [1] 0 (by decide) (by decide)) perm6.symm)

theorem finiteEdge85_2 : SafeCore (mutate (finiteNode 85) 2) := by
  have he := mutation_equal (finiteP 85) (preverse (prelabel (generic finiteParam11_0 finiteParam11_1 finiteParam11_2 finiteParam11_3 0) perm3.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 85) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finiteRegion11_safe 0) perm3.symm)

theorem finiteEdge85_3 : SafeCore (mutate (finiteNode 85) 3) := by
  have he := mutation_equal (finiteP 85) (preverse (prelabel (finiteP 74) perm7.symm)) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 85) 0) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 74) perm7.symm)

theorem finiteEdge86_0 : SafeCore (mutate (finiteNode 86) 0) := by
  have he := mutation_equal (finiteP 86) (prelabel (fork [11] [10] [417] [109] [4549] [3]) perm5.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (finite_safe 86)
  rw [show mutate (finiteNode 86) 0=(relabel (matrix (fork [11] [10] [417] [109] [4549] [3]) 0) perm5.symm) from he]
  exact IsFork.relabelled (fork_sound [11] [10] [417] [109] [4549] [3] 0 (by decide) (by decide)) perm5.symm

theorem finiteEdge86_1 : SafeCore (mutate (finiteNode 86) 1) := by
  have he := mutation_equal (finiteP 86) (preverse (prelabel (root [417] [1261] [15835] [3] [38] [1]) perm6.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 86) 1
  rw [show mutate (finiteNode 86) 1=(reverse (relabel (matrix (root [417] [1261] [15835] [3] [38] [1]) 0) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [417] [1261] [15835] [3] [38] [1] 0 (by decide) (by decide)) perm6.symm)

theorem finiteEdge86_2 : SafeCore (mutate (finiteNode 86) 2) := by
  have he := mutation_equal (finiteP 86) (preverse (prelabel (finiteP 91) perm6.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 86) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 91) perm6.symm)

theorem finiteEdge86_3 : SafeCore (mutate (finiteNode 86) 3) := by
  have he := mutation_equal (finiteP 86) (prelabel (finiteP 75) perm21.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 86) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 75) perm21.symm

theorem finiteEdge87_0 : SafeCore (mutate (finiteNode 87) 0) := by
  have he := mutation_equal (finiteP 87) (prelabel (fork [4] [3] [449] [11] [1681] [27]) perm5.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (finite_safe 87)
  rw [show mutate (finiteNode 87) 0=(relabel (matrix (fork [4] [3] [449] [11] [1681] [27]) 0) perm5.symm) from he]
  exact IsFork.relabelled (fork_sound [4] [3] [449] [11] [1681] [27] 0 (by decide) (by decide)) perm5.symm

theorem finiteEdge87_1 : SafeCore (mutate (finiteNode 87) 1) := by
  have he := mutation_equal (finiteP 87) (preverse (prelabel (root [449] [12126] [51631] [27] [115] [1]) perm6.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 87) 1
  rw [show mutate (finiteNode 87) 1=(reverse (relabel (matrix (root [449] [12126] [51631] [27] [115] [1]) 0) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [449] [12126] [51631] [27] [115] [1] 0 (by decide) (by decide)) perm6.symm)

theorem finiteEdge87_2 : SafeCore (mutate (finiteNode 87) 2) := by
  have he := mutation_equal (finiteP 87) (preverse (prelabel (generic finiteParam11_0 finiteParam11_1 finiteParam11_2 finiteParam11_3 2) perm16.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 87) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finiteRegion11_safe 2) perm16.symm)

theorem finiteEdge87_3 : SafeCore (mutate (finiteNode 87) 3) := by
  have he := mutation_equal (finiteP 87) (prelabel (finiteP 85) perm21.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 87) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 85) perm21.symm

theorem finiteEdge88_0 : SafeCore (mutate (finiteNode 88) 0) := by
  have he := mutation_equal (finiteP 88) (prelabel (finiteP 89) perm21.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 88) 0) 0)
  rw [he]
  exact Safe.framed (finite_safe 89) perm21.symm

theorem finiteEdge88_1 : SafeCore (mutate (finiteNode 88) 1) := by
  have he := mutation_equal (finiteP 88) (preverse (prelabel (root [33] [232] [261] [7] [8] [1]) perm6.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 88) 1
  rw [show mutate (finiteNode 88) 1=(reverse (relabel (matrix (root [33] [232] [261] [7] [8] [1]) 0) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [33] [232] [261] [7] [8] [1] 0 (by decide) (by decide)) perm6.symm)

theorem finiteEdge88_2 : SafeCore (mutate (finiteNode 88) 2) := by
  have he := mutation_equal (finiteP 88) (preverse (prelabel (generic finiteParam12_0 finiteParam12_1 finiteParam12_2 finiteParam12_3 0) perm3.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 88) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finiteRegion12_safe 0) perm3.symm)

theorem finiteEdge88_3 : SafeCore (mutate (finiteNode 88) 3) := by
  have he := mutation_equal (finiteP 88) (preverse (prelabel (finiteP 77) perm7.symm)) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 88) 0) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 77) perm7.symm)

theorem finiteEdge89_0 : SafeCore (mutate (finiteNode 89) 0) := by
  have he := mutation_equal (finiteP 89) (prelabel (fork [3] [2] [91] [5] [240] [7]) perm5.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (finite_safe 89)
  rw [show mutate (finiteNode 89) 0=(relabel (matrix (fork [3] [2] [91] [5] [240] [7]) 0) perm5.symm) from he]
  exact IsFork.relabelled (fork_sound [3] [2] [91] [5] [240] [7] 0 (by decide) (by decide)) perm5.symm

theorem finiteEdge89_1 : SafeCore (mutate (finiteNode 89) 1) := by
  have he := mutation_equal (finiteP 89) (preverse (prelabel (root [91] [639] [3000] [7] [33] [1]) perm6.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 89) 1
  rw [show mutate (finiteNode 89) 1=(reverse (relabel (matrix (root [91] [639] [3000] [7] [33] [1]) 0) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [91] [639] [3000] [7] [33] [1] 0 (by decide) (by decide)) perm6.symm)

theorem finiteEdge89_2 : SafeCore (mutate (finiteNode 89) 2) := by
  have he := mutation_equal (finiteP 89) (preverse (prelabel (generic finiteParam12_0 finiteParam12_1 finiteParam12_2 finiteParam12_3 2) perm16.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 89) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finiteRegion12_safe 2) perm16.symm)

theorem finiteEdge89_3 : SafeCore (mutate (finiteNode 89) 3) := by
  have he := mutation_equal (finiteP 89) (prelabel (finiteP 88) perm21.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 89) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 88) perm21.symm

theorem finiteEdge90_0 : SafeCore (mutate (finiteNode 90) 0) := by
  have he := mutation_equal (finiteP 90) (prelabel (fork [376] [3722] [41] [1399462] [15417] [11]) perm4.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (finite_safe 90)
  rw [show mutate (finiteNode 90) 0=(relabel (matrix (fork [376] [3722] [41] [1399462] [15417] [11]) 0) perm4.symm) from he]
  exact IsFork.relabelled (fork_sound [376] [3722] [41] [1399462] [15417] [11] 0 (by decide) (by decide)) perm4.symm

theorem finiteEdge90_1 : SafeCore (mutate (finiteNode 90) 1) := by
  have he := mutation_equal (finiteP 90) (preverse (prelabel (fork [10] [3722] [11] [36844] [109] [41]) perm10.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (finite_safe 90)
  rw [show mutate (finiteNode 90) 1=(reverse (relabel (matrix (fork [10] [3722] [11] [36844] [109] [41]) 0) perm10.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [10] [3722] [11] [36844] [109] [41] 0 (by decide) (by decide)) perm10.symm)

theorem finiteEdge90_2 : SafeCore (mutate (finiteNode 90) 2) := by
  have he := mutation_equal (finiteP 90) (preverse (prelabel (finiteP 94) perm7.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 90) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 94) perm7.symm)

theorem finiteEdge90_3 : SafeCore (mutate (finiteNode 90) 3) := by
  have he := mutation_equal (finiteP 90) (prelabel (finiteP 78) perm5.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 90) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 78) perm5.symm

theorem finiteEdge91_0 : SafeCore (mutate (finiteNode 91) 0) := by
  have he := mutation_equal (finiteP 91) (prelabel (fork [41] [3] [417] [122] [17096] [10]) perm5.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (finite_safe 91)
  rw [show mutate (finiteNode 91) 0=(relabel (matrix (fork [41] [3] [417] [122] [17096] [10]) 0) perm5.symm) from he]
  exact IsFork.relabelled (fork_sound [41] [3] [417] [122] [17096] [10] 0 (by decide) (by decide)) perm5.symm

theorem finiteEdge91_1 : SafeCore (mutate (finiteNode 91) 1) := by
  have he := mutation_equal (finiteP 91) (prelabel (generic finiteParam14_0 finiteParam14_1 finiteParam14_2 finiteParam14_3 0) perm17.symm) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 91) 0) 1)
  rw [he]
  exact Safe.framed (finiteRegion14_safe 0) perm17.symm

theorem finiteEdge91_2 : SafeCore (mutate (finiteNode 91) 2) := by
  have he := mutation_equal (finiteP 91) (preverse (prelabel (finiteP 86) perm6.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 91) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 86) perm6.symm)

theorem finiteEdge91_3 : SafeCore (mutate (finiteNode 91) 3) := by
  have he := mutation_equal (finiteP 91) (prelabel (finiteP 78) perm1.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 91) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 78) perm1.symm

theorem finiteEdge92_0 : SafeCore (mutate (finiteNode 92) 0) := by
  have he := mutation_equal (finiteP 92) (prelabel (finiteP 93) perm21.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 92) 0) 0)
  rw [he]
  exact Safe.framed (finite_safe 93) perm21.symm

theorem finiteEdge92_1 : SafeCore (mutate (finiteNode 92) 1) := by
  have he := mutation_equal (finiteP 92) (preverse (prelabel (root [2962] [790855] [85887] [267] [29] [1]) perm6.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 92) 1
  rw [show mutate (finiteNode 92) 1=(reverse (relabel (matrix (root [2962] [790855] [85887] [267] [29] [1]) 0) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [2962] [790855] [85887] [267] [29] [1] 0 (by decide) (by decide)) perm6.symm)

theorem finiteEdge92_2 : SafeCore (mutate (finiteNode 92) 2) := by
  have he := mutation_equal (finiteP 92) (preverse (prelabel (generic finiteParam13_0 finiteParam13_1 finiteParam13_2 finiteParam13_3 0) perm3.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 92) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finiteRegion13_safe 0) perm3.symm)

theorem finiteEdge92_3 : SafeCore (mutate (finiteNode 92) 3) := by
  have he := mutation_equal (finiteP 92) (preverse (prelabel (finiteP 80) perm7.symm)) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 92) 0) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 80) perm7.symm)

theorem finiteEdge93_0 : SafeCore (mutate (finiteNode 93) 0) := by
  have he := mutation_equal (finiteP 93) (prelabel (fork [11] [10] [32553] [109] [355121] [267]) perm5.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (finite_safe 93)
  rw [show mutate (finiteNode 93) 0=(relabel (matrix (fork [11] [10] [32553] [109] [355121] [267]) 0) perm5.symm) from he]
  exact IsFork.relabelled (fork_sound [11] [10] [32553] [109] [355121] [267] 0 (by decide) (by decide)) perm5.symm

theorem finiteEdge93_1 : SafeCore (mutate (finiteNode 93) 1) := by
  have he := mutation_equal (finiteP 93) (preverse (prelabel (root [32553] [8691661] [96421975] [267] [2962] [1]) perm6.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 93) 1
  rw [show mutate (finiteNode 93) 1=(reverse (relabel (matrix (root [32553] [8691661] [96421975] [267] [2962] [1]) 0) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [32553] [8691661] [96421975] [267] [2962] [1] 0 (by decide) (by decide)) perm6.symm)

theorem finiteEdge93_2 : SafeCore (mutate (finiteNode 93) 2) := by
  have he := mutation_equal (finiteP 93) (preverse (prelabel (generic finiteParam13_0 finiteParam13_1 finiteParam13_2 finiteParam13_3 2) perm16.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 93) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finiteRegion13_safe 2) perm16.symm)

theorem finiteEdge93_3 : SafeCore (mutate (finiteNode 93) 3) := by
  have he := mutation_equal (finiteP 93) (prelabel (finiteP 92) perm21.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 93) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 92) perm21.symm

theorem finiteEdge94_0 : SafeCore (mutate (finiteNode 94) 0) := by
  have he := mutation_equal (finiteP 94) (prelabel (finiteP 95) perm21.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 94) 0) 0)
  rw [he]
  exact Safe.framed (finite_safe 95) perm21.symm

theorem finiteEdge94_1 : SafeCore (mutate (finiteNode 94) 1) := by
  have he := mutation_equal (finiteP 94) (preverse (prelabel (root [4173] [1569049] [171082] [376] [41] [1]) perm6.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 94) 1
  rw [show mutate (finiteNode 94) 1=(reverse (relabel (matrix (root [4173] [1569049] [171082] [376] [41] [1]) 0) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [4173] [1569049] [171082] [376] [41] [1] 0 (by decide) (by decide)) perm6.symm)

theorem finiteEdge94_2 : SafeCore (mutate (finiteNode 94) 2) := by
  have he := mutation_equal (finiteP 94) (preverse (prelabel (generic finiteParam14_0 finiteParam14_1 finiteParam14_2 finiteParam14_3 0) perm3.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 94) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finiteRegion14_safe 0) perm3.symm)

theorem finiteEdge94_3 : SafeCore (mutate (finiteNode 94) 3) := by
  have he := mutation_equal (finiteP 94) (preverse (prelabel (finiteP 90) perm7.symm)) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 94) 0) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (finite_safe 90) perm7.symm)

theorem finiteEdge95_0 : SafeCore (mutate (finiteNode 95) 0) := by
  have he := mutation_equal (finiteP 95) (prelabel (fork [11] [10] [45862] [109] [500309] [376]) perm5.symm) 0 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (finite_safe 95)
  rw [show mutate (finiteNode 95) 0=(relabel (matrix (fork [11] [10] [45862] [109] [500309] [376]) 0) perm5.symm) from he]
  exact IsFork.relabelled (fork_sound [11] [10] [45862] [109] [500309] [376] 0 (by decide) (by decide)) perm5.symm

theorem finiteEdge95_1 : SafeCore (mutate (finiteNode 95) 1) := by
  have he := mutation_equal (finiteP 95) (preverse (prelabel (root [45862] [17244122] [191382115] [376] [4173] [1]) perm6.symm)) 1 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (finite_safe 95) 1
  rw [show mutate (finiteNode 95) 1=(reverse (relabel (matrix (root [45862] [17244122] [191382115] [376] [4173] [1]) 0) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [45862] [17244122] [191382115] [376] [4173] [1] 0 (by decide) (by decide)) perm6.symm)

theorem finiteEdge95_2 : SafeCore (mutate (finiteNode 95) 2) := by
  have he := mutation_equal (finiteP 95) (preverse (prelabel (generic finiteParam14_0 finiteParam14_1 finiteParam14_2 finiteParam14_3 2) perm16.symm)) 2 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 95) 0) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (finiteRegion14_safe 2) perm16.symm)

theorem finiteEdge95_3 : SafeCore (mutate (finiteNode 95) 3) := by
  have he := mutation_equal (finiteP 95) (prelabel (finiteP 94) perm21.symm) 3 0 (by decide) (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (finiteP 95) 0) 3)
  rw [he]
  exact Safe.framed (finite_safe 94) perm21.symm

theorem finite_cyclic (i : Fin 96) : ¬ Acyclic (finiteNode i) := by
  rcases finiteFin i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
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
  · exact finiteCyclic60
  · exact finiteCyclic61
  · exact finiteCyclic62
  · exact finiteCyclic63
  · exact finiteCyclic64
  · exact finiteCyclic65
  · exact finiteCyclic66
  · exact finiteCyclic67
  · exact finiteCyclic68
  · exact finiteCyclic69
  · exact finiteCyclic70
  · exact finiteCyclic71
  · exact finiteCyclic72
  · exact finiteCyclic73
  · exact finiteCyclic74
  · exact finiteCyclic75
  · exact finiteCyclic76
  · exact finiteCyclic77
  · exact finiteCyclic78
  · exact finiteCyclic79
  · exact finiteCyclic80
  · exact finiteCyclic81
  · exact finiteCyclic82
  · exact finiteCyclic83
  · exact finiteCyclic84
  · exact finiteCyclic85
  · exact finiteCyclic86
  · exact finiteCyclic87
  · exact finiteCyclic88
  · exact finiteCyclic89
  · exact finiteCyclic90
  · exact finiteCyclic91
  · exact finiteCyclic92
  · exact finiteCyclic93
  · exact finiteCyclic94
  · exact finiteCyclic95
theorem finite_edges (i : Fin 96) (k : Fin 4) : SafeCore (mutate (finiteNode i) k) := by
  have hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
  rcases finiteFin i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rcases hk with rfl|rfl|rfl|rfl
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
  · exact finiteEdge60_0
  · exact finiteEdge60_1
  · exact finiteEdge60_2
  · exact finiteEdge60_3
  · exact finiteEdge61_0
  · exact finiteEdge61_1
  · exact finiteEdge61_2
  · exact finiteEdge61_3
  · exact finiteEdge62_0
  · exact finiteEdge62_1
  · exact finiteEdge62_2
  · exact finiteEdge62_3
  · exact finiteEdge63_0
  · exact finiteEdge63_1
  · exact finiteEdge63_2
  · exact finiteEdge63_3
  · exact finiteEdge64_0
  · exact finiteEdge64_1
  · exact finiteEdge64_2
  · exact finiteEdge64_3
  · exact finiteEdge65_0
  · exact finiteEdge65_1
  · exact finiteEdge65_2
  · exact finiteEdge65_3
  · exact finiteEdge66_0
  · exact finiteEdge66_1
  · exact finiteEdge66_2
  · exact finiteEdge66_3
  · exact finiteEdge67_0
  · exact finiteEdge67_1
  · exact finiteEdge67_2
  · exact finiteEdge67_3
  · exact finiteEdge68_0
  · exact finiteEdge68_1
  · exact finiteEdge68_2
  · exact finiteEdge68_3
  · exact finiteEdge69_0
  · exact finiteEdge69_1
  · exact finiteEdge69_2
  · exact finiteEdge69_3
  · exact finiteEdge70_0
  · exact finiteEdge70_1
  · exact finiteEdge70_2
  · exact finiteEdge70_3
  · exact finiteEdge71_0
  · exact finiteEdge71_1
  · exact finiteEdge71_2
  · exact finiteEdge71_3
  · exact finiteEdge72_0
  · exact finiteEdge72_1
  · exact finiteEdge72_2
  · exact finiteEdge72_3
  · exact finiteEdge73_0
  · exact finiteEdge73_1
  · exact finiteEdge73_2
  · exact finiteEdge73_3
  · exact finiteEdge74_0
  · exact finiteEdge74_1
  · exact finiteEdge74_2
  · exact finiteEdge74_3
  · exact finiteEdge75_0
  · exact finiteEdge75_1
  · exact finiteEdge75_2
  · exact finiteEdge75_3
  · exact finiteEdge76_0
  · exact finiteEdge76_1
  · exact finiteEdge76_2
  · exact finiteEdge76_3
  · exact finiteEdge77_0
  · exact finiteEdge77_1
  · exact finiteEdge77_2
  · exact finiteEdge77_3
  · exact finiteEdge78_0
  · exact finiteEdge78_1
  · exact finiteEdge78_2
  · exact finiteEdge78_3
  · exact finiteEdge79_0
  · exact finiteEdge79_1
  · exact finiteEdge79_2
  · exact finiteEdge79_3
  · exact finiteEdge80_0
  · exact finiteEdge80_1
  · exact finiteEdge80_2
  · exact finiteEdge80_3
  · exact finiteEdge81_0
  · exact finiteEdge81_1
  · exact finiteEdge81_2
  · exact finiteEdge81_3
  · exact finiteEdge82_0
  · exact finiteEdge82_1
  · exact finiteEdge82_2
  · exact finiteEdge82_3
  · exact finiteEdge83_0
  · exact finiteEdge83_1
  · exact finiteEdge83_2
  · exact finiteEdge83_3
  · exact finiteEdge84_0
  · exact finiteEdge84_1
  · exact finiteEdge84_2
  · exact finiteEdge84_3
  · exact finiteEdge85_0
  · exact finiteEdge85_1
  · exact finiteEdge85_2
  · exact finiteEdge85_3
  · exact finiteEdge86_0
  · exact finiteEdge86_1
  · exact finiteEdge86_2
  · exact finiteEdge86_3
  · exact finiteEdge87_0
  · exact finiteEdge87_1
  · exact finiteEdge87_2
  · exact finiteEdge87_3
  · exact finiteEdge88_0
  · exact finiteEdge88_1
  · exact finiteEdge88_2
  · exact finiteEdge88_3
  · exact finiteEdge89_0
  · exact finiteEdge89_1
  · exact finiteEdge89_2
  · exact finiteEdge89_3
  · exact finiteEdge90_0
  · exact finiteEdge90_1
  · exact finiteEdge90_2
  · exact finiteEdge90_3
  · exact finiteEdge91_0
  · exact finiteEdge91_1
  · exact finiteEdge91_2
  · exact finiteEdge91_3
  · exact finiteEdge92_0
  · exact finiteEdge92_1
  · exact finiteEdge92_2
  · exact finiteEdge92_3
  · exact finiteEdge93_0
  · exact finiteEdge93_1
  · exact finiteEdge93_2
  · exact finiteEdge93_3
  · exact finiteEdge94_0
  · exact finiteEdge94_1
  · exact finiteEdge94_2
  · exact finiteEdge94_3
  · exact finiteEdge95_0
  · exact finiteEdge95_1
  · exact finiteEdge95_2
  · exact finiteEdge95_3
def polyParam0_0 : P := [5,1]
def polyParam0_1 : P := [39,13,1]
def polyParam0_2 : P := [7,1]
def polyParam0_3 : P := [8,1]
theorem polyDomain0 (t : Int) (ht : 0≤t) : GenericStrip.Domain (eval polyParam0_0 t) (eval polyParam0_1 t) (eval polyParam0_2 t) (eval polyParam0_3 t) :=
  generic_domain polyParam0_0 polyParam0_1 polyParam0_2 polyParam0_3 t ht (by decide)
def polyRegion0 (t : Int) (ht : 0≤t) : Region := .inl (.inl ⟨eval polyParam0_0 t,⟨eval polyParam0_1 t,eval polyParam0_2 t,eval polyParam0_3 t⟩,polyDomain0 t ht⟩)
theorem polyParent0_0 (t : Int) (ht : 0≤t) : data.parent (polyRegion0 t ht) (0 : Fin 3)=(reverse (relabel (matrix (polyP 5) t) perm4.symm)) := by
  have he := mutation_equal (generic polyParam0_0 polyParam0_1 polyParam0_2 polyParam0_3 0) (preverse (prelabel (polyP 5) perm4.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem polyParent0_1 (t : Int) (ht : 0≤t) : data.parent (polyRegion0 t ht) (1 : Fin 3)=(relabel (matrix (tailP [8,1] 3) t) perm22.symm) := by
  have he := mutation_equal (generic polyParam0_0 polyParam0_1 polyParam0_2 polyParam0_3 0) (prelabel (tailP [8,1] 3) perm22.symm) 2 t ht (by decide) (by decide)
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
    exact Safe.framed (tailP_safe [8,1] 3 t ht (by decide)) perm22.symm
  · rw [polyParent0_2 t ht]
    exact Safe.reversed (Safe.framed (poly_safe t ht 6) perm16.symm)
theorem polyRegion0_safe (t : Int) (ht : 0≤t) (i : Fin 3) : SafeCore (matrix (generic polyParam0_0 polyParam0_1 polyParam0_2 polyParam0_3 i) t) := by
  rw [generic_eval]
  exact Safe.region (D:=data) (core:=Core) (polyRegion0 t ht) (polyParents0_safe t ht) (0,Fin.castLE (by decide) i)

def polyParam1_0 : P := [7,1]
def polyParam1_1 : P := [274,130,20,1]
def polyParam1_2 : P := [33,12,1]
def polyParam1_3 : P := [39,13,1]
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

def polyParam2_0 : P := [8,1]
def polyParam2_1 : P := [425,173,23,1]
def polyParam2_2 : P := [46,14,1]
def polyParam2_3 : P := [53,15,1]
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

def polyParam3_0 : P := [6,1]
def polyParam3_1 : P := [53,15,1]
def polyParam3_2 : P := [8,1]
def polyParam3_3 : P := [9,1]
theorem polyDomain3 (t : Int) (ht : 0≤t) : GenericStrip.Domain (eval polyParam3_0 t) (eval polyParam3_1 t) (eval polyParam3_2 t) (eval polyParam3_3 t) :=
  generic_domain polyParam3_0 polyParam3_1 polyParam3_2 polyParam3_3 t ht (by decide)
def polyRegion3 (t : Int) (ht : 0≤t) : Region := .inl (.inl ⟨eval polyParam3_0 t,⟨eval polyParam3_1 t,eval polyParam3_2 t,eval polyParam3_3 t⟩,polyDomain3 t ht⟩)
theorem polyParent3_0 (t : Int) (ht : 0≤t) : data.parent (polyRegion3 t ht) (0 : Fin 3)=(reverse (relabel (matrix (polyP 8) t) perm4.symm)) := by
  have he := mutation_equal (generic polyParam3_0 polyParam3_1 polyParam3_2 polyParam3_3 0) (preverse (prelabel (polyP 8) perm4.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse,generic_eval] at he
  exact he

theorem polyParent3_1 (t : Int) (ht : 0≤t) : data.parent (polyRegion3 t ht) (1 : Fin 3)=(relabel (matrix (tailP [9,1] 3) t) perm22.symm) := by
  have he := mutation_equal (generic polyParam3_0 polyParam3_1 polyParam3_2 polyParam3_3 0) (prelabel (tailP [9,1] 3) perm22.symm) 2 t ht (by decide) (by decide)
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
    exact Safe.framed (tailP_safe [9,1] 3 t ht (by decide)) perm22.symm
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
  have he := mutation_equal (polyP 0) (prelabel (tailP [10,1] 0) perm21.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (polyP 0) t) 0)
  rw [he]
  exact Safe.framed (tailP_safe [10,1] 0 t ht (by decide)) perm21.symm

theorem polyEdge0_1 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 0) 1) := by
  have he := mutation_equal (polyP 0) (preverse (prelabel (root [8,1] [25,3] [46,14,1] [3] [6,1] [1]) perm6.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (poly_safe t ht 0) 1
  rw [show mutate (polyNode t 0) 1=(reverse (relabel (matrix (root [8,1] [25,3] [46,14,1] [3] [6,1] [1]) t) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [8,1] [25,3] [46,14,1] [3] [6,1] [1] t ht (by decide)) perm6.symm)

theorem polyEdge0_2 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 0) 2) := by
  have he := mutation_equal (polyP 0) (preverse (prelabel (tailP [9,1] 2) perm20.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (polyP 0) t) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (tailP_safe [9,1] 2 t ht (by decide)) perm20.symm)

theorem polyEdge0_3 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 0) 3) := by
  have he := mutation_equal (polyP 0) (prelabel (tailP [6,1] 0) perm21.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (polyP 0) t) 3)
  rw [he]
  exact Safe.framed (tailP_safe [6,1] 0 t ht (by decide)) perm21.symm

theorem polyEdge1_0 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 1) 0) := by
  have he := mutation_equal (polyP 1) (prelabel (tailP [10,1] 1) perm21.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (polyP 1) t) 0)
  rw [he]
  exact Safe.framed (tailP_safe [10,1] 1 t ht (by decide)) perm21.symm

theorem polyEdge1_1 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 1) 1) := by
  have he := mutation_equal (polyP 1) (preverse (prelabel (polyP 4) perm19.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (polyP 1) t) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (poly_safe t ht 4) perm19.symm)

theorem polyEdge1_2 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 1) 2) := by
  have he := mutation_equal (polyP 1) (prelabel (tailP [9,1] 3) perm1.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (polyP 1) t) 2)
  rw [he]
  exact Safe.framed (tailP_safe [9,1] 3 t ht (by decide)) perm1.symm

theorem polyEdge1_3 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 1) 3) := by
  have he := mutation_equal (polyP 1) (prelabel (tailP [6,1] 1) perm21.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (polyP 1) t) 3)
  rw [he]
  exact Safe.framed (tailP_safe [6,1] 1 t ht (by decide)) perm21.symm

theorem polyEdge2_0 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 2) 0) := by
  have he := mutation_equal (polyP 2) (preverse (prelabel (tailP [8,1] 3) perm1.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (polyP 2) t) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (tailP_safe [8,1] 3 t ht (by decide)) perm1.symm)

theorem polyEdge2_1 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 2) 1) := by
  have he := mutation_equal (polyP 2) (preverse (prelabel (root [8,1] [55,15,1] [23,3] [7,1] [3] [1]) perm6.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (poly_safe t ht 2) 1
  rw [show mutate (polyNode t 2) 1=(reverse (relabel (matrix (root [8,1] [55,15,1] [23,3] [7,1] [3] [1]) t) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [8,1] [55,15,1] [23,3] [7,1] [3] [1] t ht (by decide)) perm6.symm)

theorem polyEdge2_2 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 2) 2) := by
  have he := mutation_equal (polyP 2) (preverse (prelabel (tailP [10,1] 3) perm21.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (polyP 2) t) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (tailP_safe [10,1] 3 t ht (by decide)) perm21.symm)

theorem polyEdge2_3 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 2) 3) := by
  have he := mutation_equal (polyP 2) (preverse (prelabel (tailP [7,1] 0) perm15.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (polyP 2) t) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (tailP_safe [7,1] 0 t ht (by decide)) perm15.symm)

theorem polyEdge3_0 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 3) 0) := by
  have he := mutation_equal (polyP 3) (preverse (prelabel (tailP [8,1] 2) perm1.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (polyP 3) t) 0)
  rw [he]
  exact Safe.reversed (Safe.framed (tailP_safe [8,1] 2 t ht (by decide)) perm1.symm)

theorem polyEdge3_1 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 3) 1) := by
  have he := mutation_equal (polyP 3) (prelabel (generic polyParam0_0 polyParam0_1 polyParam0_2 polyParam0_3 0) perm17.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (polyP 3) t) 1)
  rw [he]
  exact Safe.framed (polyRegion0_safe t ht 0) perm17.symm

theorem polyEdge3_2 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 3) 2) := by
  have he := mutation_equal (polyP 3) (preverse (prelabel (tailP [6,1] 2) perm21.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (polyP 3) t) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (tailP_safe [6,1] 2 t ht (by decide)) perm21.symm)

theorem polyEdge3_3 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 3) 3) := by
  have he := mutation_equal (polyP 3) (prelabel (tailP [7,1] 1) perm1.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (polyP 3) t) 3)
  rw [he]
  exact Safe.framed (tailP_safe [7,1] 1 t ht (by decide)) perm1.symm

theorem polyEdge4_0 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 4) 0) := by
  have he := mutation_equal (polyP 4) (preverse (prelabel (root [6,1] [41,13,1] [268,129,20,1] [7,1] [46,14,1] [1]) perm5.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (poly_safe t ht 4) 0
  rw [show mutate (polyNode t 4) 0=(reverse (relabel (matrix (root [6,1] [41,13,1] [268,129,20,1] [7,1] [46,14,1] [1]) t) perm5.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [6,1] [41,13,1] [268,129,20,1] [7,1] [46,14,1] [1] t ht (by decide)) perm5.symm)

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
  have he := mutation_equal (polyP 4) (preverse (prelabel (tailP [8,1] 1) perm11.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (polyP 4) t) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (tailP_safe [8,1] 1 t ht (by decide)) perm11.symm)

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
  have he := mutation_equal (polyP 6) (prelabel (fork [6,1] [5,1] [233,117,19,1] [29,11,1] [1359,922,230,25,1] [7,1]) perm5.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (poly_safe t ht 6)
  rw [show mutate (polyNode t 6) 0=(relabel (matrix (fork [6,1] [5,1] [233,117,19,1] [29,11,1] [1359,922,230,25,1] [7,1]) t) perm5.symm) from he]
  exact IsFork.relabelled (fork_sound [6,1] [5,1] [233,117,19,1] [29,11,1] [1359,922,230,25,1] [7,1] t ht (by decide)) perm5.symm

theorem polyEdge6_1 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 6) 1) := by
  have he := mutation_equal (polyP 6) (preverse (prelabel (root [233,117,19,1] [1636,1053,250,26,1] [9081,7591,2495,403,32,1] [7,1] [39,13,1] [1]) perm6.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (poly_safe t ht 6) 1
  rw [show mutate (polyNode t 6) 1=(reverse (relabel (matrix (root [233,117,19,1] [1636,1053,250,26,1] [9081,7591,2495,403,32,1] [7,1] [39,13,1] [1]) t) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [233,117,19,1] [1636,1053,250,26,1] [9081,7591,2495,403,32,1] [7,1] [39,13,1] [1] t ht (by decide)) perm6.symm)

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
  have he := mutation_equal (polyP 7) (prelabel (fork [8,1] [362,157,22,1] [9,1] [2850,1604,332,30,1] [71,17,1] [7,1]) perm4.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (poly_safe t ht 7)
  rw [show mutate (polyNode t 7) 0=(relabel (matrix (fork [8,1] [362,157,22,1] [9,1] [2850,1604,332,30,1] [71,17,1] [7,1]) t) perm4.symm) from he]
  exact IsFork.relabelled (fork_sound [8,1] [362,157,22,1] [9,1] [2850,1604,332,30,1] [71,17,1] [7,1] t ht (by decide)) perm4.symm

theorem polyEdge7_1 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 7) 1) := by
  have he := mutation_equal (polyP 7) (preverse (prelabel (fork [46,14,1] [362,157,22,1] [7,1] [16644,12289,3572,511,36,1] [323,144,21,1] [9,1]) perm10.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (poly_safe t ht 7)
  rw [show mutate (polyNode t 7) 1=(reverse (relabel (matrix (fork [46,14,1] [362,157,22,1] [7,1] [16644,12289,3572,511,36,1] [323,144,21,1] [9,1]) t) perm10.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [46,14,1] [362,157,22,1] [7,1] [16644,12289,3572,511,36,1] [323,144,21,1] [9,1] t ht (by decide)) perm10.symm)

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
  have he := mutation_equal (polyP 9) (preverse (prelabel (root [274,130,20,1] [9043,7578,2494,403,32,1] [1636,1053,250,26,1] [33,12,1] [6,1] [1]) perm6.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (poly_safe t ht 9) 1
  rw [show mutate (polyNode t 9) 1=(reverse (relabel (matrix (root [274,130,20,1] [9043,7578,2494,403,32,1] [1636,1053,250,26,1] [33,12,1] [6,1] [1]) t) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [274,130,20,1] [9043,7578,2494,403,32,1] [1636,1053,250,26,1] [33,12,1] [6,1] [1] t ht (by decide)) perm6.symm)

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
  have he := mutation_equal (polyP 10) (prelabel (fork [8,1] [7,1] [2186,1313,290,28,1] [55,15,1] [17214,12560,3613,513,36,1] [33,12,1]) perm5.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (poly_safe t ht 10)
  rw [show mutate (polyNode t 10) 0=(relabel (matrix (fork [8,1] [7,1] [2186,1313,290,28,1] [55,15,1] [17214,12560,3613,513,36,1] [33,12,1]) t) perm5.symm) from he]
  exact IsFork.relabelled (fork_sound [8,1] [7,1] [2186,1313,290,28,1] [55,15,1] [17214,12560,3613,513,36,1] [33,12,1] t ht (by decide)) perm5.symm

theorem polyEdge10_1 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 10) 1) := by
  have he := mutation_equal (polyP 10) (preverse (prelabel (root [2186,1313,290,28,1] [72145,69562,27512,5717,659,40,1] [598956,643941,293870,73818,11027,980,48,1] [33,12,1] [274,130,20,1] [1]) perm6.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (poly_safe t ht 10) 1
  rw [show mutate (polyNode t 10) 1=(reverse (relabel (matrix (root [2186,1313,290,28,1] [72145,69562,27512,5717,659,40,1] [598956,643941,293870,73818,11027,980,48,1] [33,12,1] [274,130,20,1] [1]) t) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [2186,1313,290,28,1] [72145,69562,27512,5717,659,40,1] [598956,643941,293870,73818,11027,980,48,1] [33,12,1] [274,130,20,1] [1] t ht (by decide)) perm6.symm)

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
  have he := mutation_equal (polyP 11) (preverse (prelabel (root [5,1] [29,11,1] [158,92,17,1] [6,1] [33,12,1] [1]) perm5.symm)) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (poly_safe t ht 11) 0
  rw [show mutate (polyNode t 11) 0=(reverse (relabel (matrix (root [5,1] [29,11,1] [158,92,17,1] [6,1] [33,12,1] [1]) t) perm5.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [5,1] [29,11,1] [158,92,17,1] [6,1] [33,12,1] [1] t ht (by decide)) perm5.symm)

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
  have he := mutation_equal (polyP 11) (preverse (prelabel (tailP [7,1] 1) perm11.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (polyP 11) t) 3)
  rw [he]
  exact Safe.reversed (Safe.framed (tailP_safe [7,1] 1 t ht (by decide)) perm11.symm)

theorem polyEdge12_0 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 12) 0) := by
  have he := mutation_equal (polyP 12) (prelabel (polyP 14) perm21.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore (mutate (matrix (polyP 12) t) 0)
  rw [he]
  exact Safe.framed (poly_safe t ht 14) perm21.symm

theorem polyEdge12_1 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 12) 1) := by
  have he := mutation_equal (polyP 12) (preverse (prelabel (root [425,173,23,1] [19551,13908,3905,541,37,1] [2966,1635,334,30,1] [46,14,1] [7,1] [1]) perm6.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (poly_safe t ht 12) 1
  rw [show mutate (polyNode t 12) 1=(reverse (relabel (matrix (root [425,173,23,1] [19551,13908,3905,541,37,1] [2966,1635,334,30,1] [46,14,1] [7,1] [1]) t) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [425,173,23,1] [19551,13908,3905,541,37,1] [2966,1635,334,30,1] [46,14,1] [7,1] [1] t ht (by decide)) perm6.symm)

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
  have he := mutation_equal (polyP 13) (prelabel (fork [7,1] [6,1] [370,158,22,1] [41,13,1] [2537,1461,311,29,1] [8,1]) perm5.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (poly_safe t ht 13)
  rw [show mutate (polyNode t 13) 0=(relabel (matrix (fork [7,1] [6,1] [370,158,22,1] [41,13,1] [2537,1461,311,29,1] [8,1]) t) perm5.symm) from he]
  exact IsFork.relabelled (fork_sound [7,1] [6,1] [370,158,22,1] [41,13,1] [2537,1461,311,29,1] [8,1] t ht (by decide)) perm5.symm

theorem polyEdge13_1 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 13) 1) := by
  have he := mutation_equal (polyP 13) (preverse (prelabel (root [370,158,22,1] [2966,1635,334,30,1] [19603,13923,3906,541,37,1] [8,1] [53,15,1] [1]) perm6.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (poly_safe t ht 13) 1
  rw [show mutate (polyNode t 13) 1=(reverse (relabel (matrix (root [370,158,22,1] [2966,1635,334,30,1] [19603,13923,3906,541,37,1] [8,1] [53,15,1] [1]) t) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [370,158,22,1] [2966,1635,334,30,1] [19603,13923,3906,541,37,1] [8,1] [53,15,1] [1] t ht (by decide)) perm6.symm)

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
  have he := mutation_equal (polyP 14) (prelabel (fork [9,1] [8,1] [3818,1981,380,32,1] [71,17,1] [33937,21474,5378,667,41,1] [46,14,1]) perm5.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (poly_safe t ht 14)
  rw [show mutate (polyNode t 14) 0=(relabel (matrix (fork [9,1] [8,1] [3818,1981,380,32,1] [71,17,1] [33937,21474,5378,667,41,1] [46,14,1]) t) perm5.symm) from he]
  exact IsFork.relabelled (fork_sound [9,1] [8,1] [3818,1981,380,32,1] [71,17,1] [33937,21474,5378,667,41,1] [46,14,1] t ht (by decide)) perm5.symm

theorem polyEdge14_1 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 14) 1) := by
  have he := mutation_equal (polyP 14) (preverse (prelabel (root [3818,1981,380,32,1] [175636,144579,49032,8773,874,46,1] [1622641,1502438,592027,128721,16682,1289,55,1] [46,14,1] [425,173,23,1] [1]) perm6.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data Core (poly_safe t ht 14) 1
  rw [show mutate (polyNode t 14) 1=(reverse (relabel (matrix (root [3818,1981,380,32,1] [175636,144579,49032,8773,874,46,1] [1622641,1502438,592027,128721,16682,1289,55,1] [46,14,1] [425,173,23,1] [1]) t) perm6.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [3818,1981,380,32,1] [175636,144579,49032,8773,874,46,1] [1622641,1502438,592027,128721,16682,1289,55,1] [46,14,1] [425,173,23,1] [1] t ht (by decide)) perm6.symm)

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
  have he := mutation_equal (polyP 15) (prelabel (fork [7,1] [226,116,19,1] [8,1] [1549,1026,248,26,1] [55,15,1] [6,1]) perm4.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 0 (poly_safe t ht 15)
  rw [show mutate (polyNode t 15) 0=(relabel (matrix (fork [7,1] [226,116,19,1] [8,1] [1549,1026,248,26,1] [55,15,1] [6,1]) t) perm4.symm) from he]
  exact IsFork.relabelled (fork_sound [7,1] [226,116,19,1] [8,1] [1549,1026,248,26,1] [55,15,1] [6,1] t ht (by decide)) perm4.symm

theorem polyEdge15_1 (t : Int) (ht : 0≤t) : SafeCore (mutate (polyNode t 15) 1) := by
  have he := mutation_equal (polyP 15) (preverse (prelabel (fork [33,12,1] [226,116,19,1] [6,1] [7451,6539,2245,377,31,1] [199,105,18,1] [8,1]) perm10.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply Safe.fork 1 (poly_safe t ht 15)
  rw [show mutate (polyNode t 15) 1=(reverse (relabel (matrix (fork [33,12,1] [226,116,19,1] [6,1] [7451,6539,2245,377,31,1] [199,105,18,1] [8,1]) t) perm10.symm)) from he]
  exact IsFork.reversed (IsFork.relabelled (fork_sound [33,12,1] [226,116,19,1] [6,1] [7451,6539,2245,377,31,1] [199,105,18,1] [8,1] t ht (by decide)) perm10.symm)

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



theorem frame_q207 : ofSix (-2) (-2) (1) (0) (-1) (1)=(reverse (relabel (finiteNode 0) perm14.symm)) := by
  funext i j
  exact (show ∀ a b, (ofSix (-2) (-2) (1) (0) (-1) (1)) a b=((reverse (relabel (finiteNode 0) perm14.symm))) a b from by decide) i j
theorem nma_q207 : ¬ MutationAcyclic (ofSix (-2) (-2) (1) (0) (-1) (1)) := by
  rw [frame_q207]
  exact safe_nma _ (Safe.reversed (Safe.framed (finite_safe 0) perm14.symm))

theorem frame_q285 : ofSix (-2) (-1) (-1) (-1) (1) (-1)=(relabel (finiteNode 12) perm0.symm) := by
  funext i j
  exact (show ∀ a b, (ofSix (-2) (-1) (-1) (-1) (1) (-1)) a b=((relabel (finiteNode 12) perm0.symm)) a b from by decide) i j
theorem nma_q285 : ¬ MutationAcyclic (ofSix (-2) (-1) (-1) (-1) (1) (-1)) := by
  rw [frame_q285]
  exact safe_nma _ (Safe.framed (finite_safe 12) perm0.symm)

theorem frame_q352 : ofSix (-2) (-1) (0) (-1) (2) (-1)=(relabel (finiteNode 0) perm4.symm) := by
  funext i j
  exact (show ∀ a b, (ofSix (-2) (-1) (0) (-1) (2) (-1)) a b=((relabel (finiteNode 0) perm4.symm)) a b from by decide) i j
theorem nma_q352 : ¬ MutationAcyclic (ofSix (-2) (-1) (0) (-1) (2) (-1)) := by
  rw [frame_q352]
  exact safe_nma _ (Safe.framed (finite_safe 0) perm4.symm)

theorem frame_q381 : ofSix (-2) (-1) (0) (1) (-2) (1)=(relabel (finiteNode 10) perm4.symm) := by
  funext i j
  exact (show ∀ a b, (ofSix (-2) (-1) (0) (1) (-2) (1)) a b=((relabel (finiteNode 10) perm4.symm)) a b from by decide) i j
theorem nma_q381 : ¬ MutationAcyclic (ofSix (-2) (-1) (0) (1) (-2) (1)) := by
  rw [frame_q381]
  exact safe_nma _ (Safe.framed (finite_safe 10) perm4.symm)

theorem frame_q484 : ofSix (-2) (-1) (1) (1) (1) (-1)=(reverse (relabel (finiteNode 12) perm7.symm)) := by
  funext i j
  exact (show ∀ a b, (ofSix (-2) (-1) (1) (1) (1) (-1)) a b=((reverse (relabel (finiteNode 12) perm7.symm))) a b from by decide) i j
theorem nma_q484 : ¬ MutationAcyclic (ofSix (-2) (-1) (1) (1) (1) (-1)) := by
  rw [frame_q484]
  exact safe_nma _ (Safe.reversed (Safe.framed (finite_safe 12) perm7.symm))

theorem frame_q527 : ofSix (-2) (-1) (2) (1) (0) (-1)=(reverse (relabel (finiteNode 10) perm10.symm)) := by
  funext i j
  exact (show ∀ a b, (ofSix (-2) (-1) (2) (1) (0) (-1)) a b=((reverse (relabel (finiteNode 10) perm10.symm))) a b from by decide) i j
theorem nma_q527 : ¬ MutationAcyclic (ofSix (-2) (-1) (2) (1) (0) (-1)) := by
  rw [frame_q527]
  exact safe_nma _ (Safe.reversed (Safe.framed (finite_safe 10) perm10.symm))

theorem frame_q440 : ofSix (-2) (-1) (1) (-1) (-1) (1)=(relabel (finiteNode 1) perm0.symm) := by
  funext i j
  exact (show ∀ a b, (ofSix (-2) (-1) (1) (-1) (-1) (1)) a b=((relabel (finiteNode 1) perm0.symm)) a b from by decide) i j
theorem nma_q440 : ¬ MutationAcyclic (ofSix (-2) (-1) (1) (-1) (-1) (1)) := by
  rw [frame_q440]
  exact safe_nma _ (Safe.framed (finite_safe 1) perm0.symm)

theorem frame_q477 : ofSix (-2) (-1) (1) (1) (-1) (-2)=(relabel (finiteNode 13) perm0.symm) := by
  funext i j
  exact (show ∀ a b, (ofSix (-2) (-1) (1) (1) (-1) (-2)) a b=((relabel (finiteNode 13) perm0.symm)) a b from by decide) i j
theorem nma_q477 : ¬ MutationAcyclic (ofSix (-2) (-1) (1) (1) (-1) (-2)) := by
  rw [frame_q477]
  exact safe_nma _ (Safe.framed (finite_safe 13) perm0.symm)

theorem frame_q624 : ofSix (-2) (1) (1) (-1) (1) (1)=(reverse (relabel (finiteNode 1) perm7.symm)) := by
  funext i j
  exact (show ∀ a b, (ofSix (-2) (1) (1) (-1) (1) (1)) a b=((reverse (relabel (finiteNode 1) perm7.symm))) a b from by decide) i j
theorem nma_q624 : ¬ MutationAcyclic (ofSix (-2) (1) (1) (-1) (1) (1)) := by
  rw [frame_q624]
  exact safe_nma _ (Safe.reversed (Safe.framed (finite_safe 1) perm7.symm))

end QuiverProofs.Q207Structural