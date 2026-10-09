import Rank4Round2.MixedUnitActualEndpoint

/-! Exact three-to-five identity in the other unit triangle. This supplies
no general height guard: such a guard is false for arbitrary fourth rows. -/
namespace Rank4Round2.MixedUnitReverseRelation
open QuiverProofs Rank4Coordinator Rank4Round2 MixedUnitRelation

def R2 (c e f : Int) : Matrix 4 := ofSix 1 (-1) c 2 e f
def short : List (Fin 4) := [0,1,2]
def long : List (Fin 4) := [1,0,2,1,2]

private theorem four (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega

theorem unit_two_three12 (B : Matrix 4) (hs : SkewSymmetric B)
    (hu : abs (B 1 2)=1) :
    applyWord B [1,2]=relabel (applyWord B [2,1,2]) swap12 := by
  have hh := unit_two_three (relabel B cycle) (relabel_skew B cycle hs)
    (show abs (relabel B cycle 0 1)=1 from hu)
  rw [word_relabel,word_relabel] at hh
  have ht := congrArg (fun C => relabel C cycle.symm) hh
  dsimp only at ht
  rw [relabel_inverse,conjugate_swap] at ht
  exact ht

theorem triangle_unit_after_two (c e f : Int) :
    applyWord (R2 c e f) [1,0] 1 2= -1 := by
  simp [R2,applyWord,mutate,ofSix,correction]

theorem endpoint (c e f : Int) :
    applyWord (R2 c e f) long=relabel (applyWord (R2 c e f) short) cycle := by
  let S := applyWord (R2 c e f) [1,0]
  have hS := word_preserves_skew (R2 c e f) [1,0] (ofSix_skew _ _ _ _ _ _)
  have huS : abs (S 1 2)=1 := by
    rw [show S 1 2= -1 from triangle_unit_after_two c e f]
    decide
  have hShort : applyWord (R2 c e f) short=
      relabel (applyWord S [1,2]) Forks.swap01 := by
    change applyWord (applyWord (R2 c e f) [0,1]) [2]=_
    rw [unit_two_three (R2 c e f) (ofSix_skew _ _ _ _ _ _)
      (by change abs (1:Int)=1;decide),word_relabel]
    rfl
  rw [unit_two_three12 S hS huS] at hShort
  have hPerm : relabel (relabel (applyWord S [2,1,2]) swap12) Forks.swap01=
      relabel (applyWord (R2 c e f) long) cycle.symm := by
    funext i j
    rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;> rfl
  rw [hPerm] at hShort
  have hh := congrArg (fun C => relabel C cycle) hShort
  dsimp only at hh
  have hinv : relabel (relabel (applyWord (R2 c e f) long) cycle.symm) cycle=
      applyWord (R2 c e f) long := by
    funext i j
    rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;> rfl
  rw [hinv] at hh
  exact hh.symm

theorem tail_endpoint (c e f : Int) (tail : List (Fin 4)) :
    applyWord (R2 c e f) (long++tail.map cycle.invFun)=
      relabel (applyWord (R2 c e f) (short++tail)) cycle :=
  reroute_endpoint _ short long tail cycle (endpoint c e f)

theorem tail_count (c e f : Int) (H : Nat) (tail : List (Fin 4)) :
    overCount (R2 c e f) (long++tail.map cycle.invFun) H+overCount (R2 c e f) short H=
      overCount (R2 c e f) (short++tail) H+overCount (R2 c e f) long H := by
  rw [overCount_append,overCount_append,endpoint,overCount_relabel]
  omega

theorem tail_prefix (c e f : Int) (K : Nat) (tail : List (Fin 4))
    (hNew : PrefixHeightLe (R2 c e f) long K)
    (hOld : PrefixHeightLe (R2 c e f) (short++tail) K) :
    PrefixHeightLe (R2 c e f) (long++tail.map cycle.invFun) K := by
  have ht := ((prefixHeight_append_iff (R2 c e f) short tail K).mp hOld).2
  exact reroute_prefixHeight _ short long tail cycle K (endpoint c e f) hNew ht

theorem tail_acyclic (c e f : Int) (tail : List (Fin 4))
    (ha : Acyclic (applyWord (R2 c e f) (short++tail))) :
    Acyclic (applyWord (R2 c e f) (long++tail.map cycle.invFun)) := by
  rw [tail_endpoint]
  exact (acyclic_relabel_iff _ cycle).mpr ha

#print axioms unit_two_three12
#print axioms endpoint
#print axioms tail_count
#print axioms tail_prefix
end Rank4Round2.MixedUnitReverseRelation
