import Rank4CoordinatorR2.UnitCycle
import Rank4Round2.WordBounds

/-! A mixed-unit five-to-three replacement follows from two arbitrary-sign
unit pentagons. All three frozen entries are arbitrary integers. Literal
continuation words are transported by the actual endpoint permutation. -/
namespace Rank4Round2.MixedUnitRelation
open QuiverProofs Rank4Coordinator Rank4CoordinatorR2 Rank4Round2
open Rank4CoordinatorR2.UnitPentagon

def R (c e f : Int) : Matrix 4 := ofSix 1 (-2) c 1 e f
def old : List (Fin 4) := [0,1,2,0,2]
def new : List (Fin 4) := [1,0,2]

def cycle : Relabeling 4 :=
  ⟨fun i => match i.val with | 0=>1 | 1=>2 | 2=>0 | _=>3,
   fun i => match i.val with | 0=>2 | 1=>0 | 2=>1 | _=>3,by decide,by decide⟩
def swap12 : Relabeling 4 :=
  ⟨fun i => match i.val with | 0=>0 | 1=>2 | 2=>1 | _=>3,
   fun i => match i.val with | 0=>0 | 1=>2 | 2=>1 | _=>3,by decide,by decide⟩

private theorem four (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega

theorem unit_two_three (B : Matrix 4) (hs : SkewSymmetric B) (hu : abs (B 0 1)=1) :
    applyWord B [0,1]=relabel (applyWord B [1,0,1]) Forks.swap01 := by
  have hf := unit_five_absolute B hs hu
  have hh := congrArg (fun C => applyWord C [0,1,0]) hf
  dsimp only at hh
  rw [word_relabel] at hh
  simp only [List.map_cons,List.map_nil,show Forks.swap01.toFun 0=1 from rfl,
    show Forks.swap01.toFun 1=0 from rfl,applyWord,mutation_involutive] at hh
  exact hh

theorem conjugate_swap (B : Matrix 4) :
    relabel (relabel (relabel B cycle) Forks.swap01) cycle.symm=relabel B swap12 := by
  funext i j
  rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;> rfl

theorem unit_four12 (B : Matrix 4) (hs : SkewSymmetric B) (hu : abs (B 1 2)=1) :
    applyWord B [1,2,1,2]=relabel (mutate B 2) swap12 := by
  have hf := unit_five_absolute (relabel B cycle) (relabel_skew B cycle hs)
    (show abs (relabel B cycle 0 1)=1 from hu)
  have hh := congrArg (fun C => mutate C 0) hf
  simp only [applyWord,mutation_involutive,mutate_relabel,
    show cycle.toFun 0=1 from rfl,show cycle.toFun 1=2 from rfl,
    show Forks.swap01.toFun 0=1 from rfl] at hh
  have ht := congrArg (fun C => relabel C cycle.symm) hh
  dsimp only at ht
  rw [relabel_inverse,conjugate_swap] at ht
  exact ht

theorem triangle_unit_after_two (c e f : Int) : applyWord (R c e f) [1,0] 1 2= -1 := by
  simp [R,applyWord,mutate,ofSix,correction]

theorem mixed_endpoint (c e f : Int) :
    applyWord (R c e f) new=relabel (applyWord (R c e f) old) cycle := by
  let S := applyWord (R c e f) [1,0]
  have hS := word_preserves_skew (R c e f) [1,0] (ofSix_skew _ _ _ _ _ _)
  have huS : abs (S 1 2)=1 := by rw [show S 1 2= -1 from triangle_unit_after_two c e f];decide
  have h4 := unit_four12 S hS huS
  have hOld : applyWord (R c e f) old=
      relabel (applyWord S [1,2,1,2]) Forks.swap01 := by
    change applyWord (applyWord (R c e f) [0,1]) [2,0,2]=_
    rw [unit_two_three (R c e f) (ofSix_skew _ _ _ _ _ _)
      (by change abs (1:Int)=1;decide),word_relabel]
    rfl
  rw [h4] at hOld
  have hPerm : relabel (relabel (mutate S 2) swap12) Forks.swap01=
      relabel (mutate S 2) cycle.symm := by
    funext i j
    rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;> rfl
  rw [hPerm] at hOld
  have hh := congrArg (fun C => relabel C cycle) hOld
  dsimp only at hh
  have hinv : relabel (relabel (mutate S 2) cycle.symm) cycle=mutate S 2 := by
    funext i j
    rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;> rfl
  rw [hinv] at hh
  exact hh.symm

theorem literal_tail_endpoint (c e f : Int) (tail : List (Fin 4)) :
    applyWord (R c e f) (new++tail.map cycle.invFun)=
      relabel (applyWord (R c e f) (old++tail)) cycle :=
  reroute_endpoint _ old new tail cycle (mixed_endpoint c e f)

theorem literal_tail_count (c e f : Int) (H : Nat) (tail : List (Fin 4)) :
    overCount (R c e f) (new++tail.map cycle.invFun) H+overCount (R c e f) old H=
      overCount (R c e f) (old++tail) H+overCount (R c e f) new H := by
  rw [overCount_append,overCount_append,mixed_endpoint,overCount_relabel]
  omega

theorem literal_tail_prefix (c e f : Int) (K : Nat) (tail : List (Fin 4))
    (hNew : PrefixHeightLe (R c e f) new K)
    (hOld : PrefixHeightLe (R c e f) (old++tail) K) :
    PrefixHeightLe (R c e f) (new++tail.map cycle.invFun) K := by
  have ht := ((prefixHeight_append_iff (R c e f) old tail K).mp hOld).2
  exact reroute_prefixHeight _ old new tail cycle K (mixed_endpoint c e f) hNew ht

theorem literal_tail_acyclic (c e f : Int) (tail : List (Fin 4))
    (ha : Acyclic (applyWord (R c e f) (old++tail))) :
    Acyclic (applyWord (R c e f) (new++tail.map cycle.invFun)) := by
  rw [literal_tail_endpoint]
  exact (acyclic_relabel_iff _ cycle).mpr ha

#print axioms unit_two_three
#print axioms unit_four12
#print axioms mixed_endpoint
#print axioms literal_tail_count
#print axioms literal_tail_prefix
end Rank4Round2.MixedUnitRelation
