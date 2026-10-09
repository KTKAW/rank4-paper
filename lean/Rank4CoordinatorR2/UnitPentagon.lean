import Rank4Round2.UnitDetour
import QuiverProofs.Invariants
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! The arbitrary-sign unit-pair pentagon, including the frozen-to-frozen
entry. Tropical row periodicity supplies the four other entries, and the
signed Pfaffian supplies the remaining entry. No scalar or MA premise. -/
namespace Rank4CoordinatorR2.UnitPentagon
open QuiverProofs Rank4Coordinator Rank4Round2

def row0 (p : Int×Int) : Int×Int := (-p.1,p.2+min p.1 0)
def row1 (p : Int×Int) : Int×Int := (p.1+min p.2 0,-p.2)

theorem tropical_five (x y : Int) :
    row0 (row1 (row0 (row1 (row0 (x,y)))))=(y,x) := by
  apply Prod.ext <;> simp only [row0,row1] <;> omega

theorem negative_unit_correction (x : Int) : correction (-1) x=min x 0 := by
  simp [correction,Int.max_def,Int.min_def]
  omega

def rowAt (B : Matrix 4) (r : Fin 4) : Int×Int := (B 0 r,B 1 r)

theorem row_zero (B : Matrix 4) (hs : SkewSymmetric B) (ha : B 0 1=1)
    (r : Fin 4) (hr0 : r≠0) (_hr1 : r≠1) :
    rowAt (mutate B 0) r=row0 (rowAt B r) := by
  have h10 : B 1 0= -1 := by have hh := hs 1 0; omega
  apply Prod.ext <;> simp [rowAt,row0,mutate,hr0,h10,negative_unit_correction]

theorem row_one (B : Matrix 4) (ha : B 0 1= -1)
    (r : Fin 4) (_hr0 : r≠0) (hr1 : r≠1) :
    rowAt (mutate B 1) r=row1 (rowAt B r) := by
  apply Prod.ext <;> simp [rowAt,row1,mutate,hr1,ha,negative_unit_correction]

theorem signed_pfaffian_mutation (B : Matrix 4) (hs : SkewSymmetric B) (k : Fin 4) :
    matrixPfaffian (mutate B k)= -matrixPfaffian B := by
  rw [←ofSix_reconstruct B hs]
  exact pfaffian_mutation _ _ _ _ _ _ k

theorem signed_pfaffian_word (B : Matrix 4) (hs : SkewSymmetric B) (w : List (Fin 4)) :
    matrixPfaffian (applyWord B w)=(-1:Int)^w.length*matrixPfaffian B := by
  induction w generalizing B with
  | nil => simp [applyWord]
  | cons k w ih =>
    simp only [applyWord,List.length_cons]
    rw [ih _ (mutation_preserves_skew B k hs),signed_pfaffian_mutation B hs k,pow_succ]
    ring

theorem five_rows (B : Matrix 4) (hs : SkewSymmetric B) (ha : B 0 1=1)
    (r : Fin 4) (hr0 : r≠0) (hr1 : r≠1) :
    rowAt (applyWord B [0,1,0,1,0]) r=(B 1 r,B 0 r) := by
  let B0 := mutate B 0
  let B1 := mutate B0 1
  let B2 := mutate B1 0
  let B3 := mutate B2 1
  have hs0 := mutation_preserves_skew B 0 hs
  have hs1 := mutation_preserves_skew B0 1 hs0
  have hs2 := mutation_preserves_skew B1 0 hs1
  have hs3 := mutation_preserves_skew B2 1 hs2
  have ha0 : B0 0 1= -1 := by simp [B0,mutate,ha]
  have ha1 : B1 0 1=1 := by simp [B1,mutate,ha0]
  have ha2 : B2 0 1= -1 := by simp [B2,mutate,ha1]
  have ha3 : B3 0 1=1 := by simp [B3,mutate,ha2]
  change rowAt (mutate B3 0) r=_
  rw [row_zero B3 hs3 ha3 r hr0 hr1,row_one B2 ha2 r hr0 hr1,
    row_zero B1 hs1 ha1 r hr0 hr1,row_one B0 ha0 r hr0 hr1,
    row_zero B hs ha r hr0 hr1]
  exact tropical_five _ _

theorem unit_five (B : Matrix 4) (hs : SkewSymmetric B) (ha : B 0 1=1) :
    applyWord B [0,1,0,1,0]=relabel B Forks.swap01 := by
  let C := applyWord B [0,1,0,1,0]
  have hsC : SkewSymmetric C := word_preserves_skew B _ hs
  have h01 : C 0 1= -1 := by simp [C,applyWord,mutate,ha]
  have h2 := five_rows B hs ha 2 (by decide) (by decide)
  have h3 := five_rows B hs ha 3 (by decide) (by decide)
  have h02 : C 0 2=B 1 2 := congrArg Prod.fst h2
  have h12 : C 1 2=B 0 2 := congrArg Prod.snd h2
  have h03 : C 0 3=B 1 3 := congrArg Prod.fst h3
  have h13 : C 1 3=B 0 3 := congrArg Prod.snd h3
  have hp := signed_pfaffian_word B hs [0,1,0,1,0]
  have h23 : C 2 3=B 2 3 := by
    change matrixPfaffian C=(-1:Int)^5*matrixPfaffian B at hp
    simp only [matrixPfaffian,h01,h02,h12,h03,h13,ha] at hp
    norm_num at hp
    nlinarith
  change C=relabel B Forks.swap01
  rw [←ofSix_reconstruct C hsC,h01,h02,h03,h12,h13,h23]
  rw [←ofSix_reconstruct (relabel B Forks.swap01) (relabel_skew B _ hs)]
  simp [relabel,Forks.swap01,ha,hs 1 0]

theorem unit_five_negative (B : Matrix 4) (hs : SkewSymmetric B) (ha : B 0 1= -1) :
    applyWord B [0,1,0,1,0]=relabel B Forks.swap01 := by
  have hp := unit_five (reverse B) (reverse_skew B hs)
    (show reverse B 0 1=1 by change -B 0 1=1; omega)
  rw [word_reverse] at hp
  have hh := congrArg reverse hp
  simp only [reverse_involutive] at hh
  have hr : reverse (relabel (reverse B) Forks.swap01)=relabel B Forks.swap01 := by
    funext i j
    simp [reverse,relabel]
  rw [hr] at hh
  exact hh

theorem unit_five_absolute (B : Matrix 4) (hs : SkewSymmetric B) (ha : |B 0 1|=1) :
    applyWord B [0,1,0,1,0]=relabel B Forks.swap01 := by
  have hc : B 0 1=1 ∨ B 0 1= -1 := by
    rcases le_total 0 (B 0 1) with h|h
    · rw [abs_of_nonneg h] at ha
      exact Or.inl ha
    · rw [abs_of_nonpos h] at ha
      exact Or.inr (by omega)
  rcases hc with h|h
  · exact unit_five B hs h
  · exact unit_five_negative B hs h

#print axioms tropical_five
#print axioms signed_pfaffian_word
#print axioms unit_five
#print axioms unit_five_absolute
end Rank4CoordinatorR2.UnitPentagon
