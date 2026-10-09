import QuiverProofs.WeakRegionCells
import QuiverProofs.ForkCertificates

/-! An infinite four-phase corridor with affine integer parameters.
Every tail transition is proved for all nonnegative indices. The seven finite
end states and the existing weak-region cells give closure under every mutation.
The discovery cutoff is absent from all theorem statements and proofs. -/

namespace QuiverProofs.AffineTwoCorridor
open WeakForks WeakRegions WeakRegionSemantics ForkCertificates
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

private theorem fin4 (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
private theorem fin7 (i : Fin 7) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 := by omega

def tail (n : Int) (i : Fin 4) : Matrix 4 := match i.val with
  | 0 => ofSix (-4*n-8) 1 1 (-4*n-6) (-6) (-1)
  | 1 => ofSix (-4*n-8) 1 1 (-4*n-2) (-2) (-1)
  | 2 => ofSix (-4*n-6) (-2) (4*n+2) 1 (-2) 1
  | _ => ofSix (-4*n-10) (-1) 2 (-6) (-4*n-6) (-1)

def base (i : Fin 7) : Matrix 4 := match i.val with
  | 0 => (ofSix (-6) (-2) (4) (1) (-1) (-1))
  | 1 => (ofSix (-6) (-2) (6) (-1) (1) (-2))
  | 2 => (ofSix (-6) (-1) (1) (-2) (-2) (-2))
  | 3 => (ofSix (-4) (-2) (2) (-1) (-1) (1))
  | 4 => (ofSix (-4) (-2) (2) (1) (-1) (2))
  | 5 => (ofSix (-4) (-1) (1) (-2) (-2) (1))
  | _ => (ofSix (-2) (-2) (-2) (-2) (1) (-1))

inductive Core : Matrix 4 → Prop
  | base (i : Fin 7) : Core (base i)
  | tail (n : Int) (hn : 0≤n) (i : Fin 4) : Core (tail n i)
  | framed {B : Matrix 4} : Core B → (p : Relabeling 4) → Core (relabel B p)
  | reversed {B : Matrix 4} : Core B → Core (reverse B)

def Edge (B : Matrix 4) (k : Fin 4) : Prop :=
  Core (mutate B k) ∨ IsWeakFork (mutate B k) k ∨ IsRoot (mutate B k) k

theorem base_edge_0_0 : Edge (base 0) 0 := by
  right; right
  have he : relabel (reverse (mutate (base 0) 0)) perm5 = root (4) (7) (23) (2) (6) (1) := by
    funext u v
    revert u v
    decide
  have hb : IsRoot (relabel (reverse (mutate (base 0) 0)) perm5) 0 := by
    rw [he]
    exact IsRoot.basic (4) (7) (23) (2) (6) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact root_of_reverse (root_of_relabel perm5 hb)

theorem base_edge_0_1 : Edge (base 0) 1 := by
  left
  have he : mutate (base 0) 1 = relabel (base 2) perm6 := by
    funext u v
    revert u v
    decide
  rw [he]
  exact Core.framed (Core.base 2) perm6

theorem base_edge_0_2 : Edge (base 0) 2 := by
  left
  have he : mutate (base 0) 2 = reverse (relabel (tail 0 1) perm6) := by
    funext u v
    revert u v
    decide
  rw [he]
  exact Core.reversed (Core.framed (Core.tail 0 (by omega) 1) perm6)

theorem base_edge_0_3 : Edge (base 0) 3 := by
  left
  have he : mutate (base 0) 3 = relabel (base 3) perm3 := by
    funext u v
    revert u v
    decide
  rw [he]
  exact Core.framed (Core.base 3) perm3

theorem base_edge_1_0 : Edge (base 1) 0 := by
  right; right
  have he : relabel (reverse (mutate (base 1) 0)) perm4 = root (6) (37) (10) (6) (2) (1) := by
    funext u v
    revert u v
    decide
  have hb : IsRoot (relabel (reverse (mutate (base 1) 0)) perm4) 0 := by
    rw [he]
    exact IsRoot.basic (6) (37) (10) (6) (2) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact root_of_reverse (root_of_relabel perm4 hb)

theorem base_edge_1_1 : Edge (base 1) 1 := by
  left
  have he : mutate (base 1) 1 = reverse (relabel (tail 0 0) perm10) := by
    funext u v
    revert u v
    decide
  rw [he]
  exact Core.reversed (Core.framed (Core.tail 0 (by omega) 0) perm10)

theorem base_edge_1_2 : Edge (base 1) 2 := by
  left
  have he : mutate (base 1) 2 = reverse (relabel (base 2) perm6) := by
    funext u v
    revert u v
    decide
  rw [he]
  exact Core.reversed (Core.framed (Core.base 2) perm6)

theorem base_edge_1_3 : Edge (base 1) 3 := by
  left
  have he : mutate (base 1) 3 = relabel (tail 0 3) perm8 := by
    funext u v
    revert u v
    decide
  rw [he]
  exact Core.framed (Core.tail 0 (by omega) 3) perm8

theorem base_edge_2_0 : Edge (base 2) 0 := by
  left
  have he : mutate (base 2) 0 = relabel (base 0) perm6 := by
    funext u v
    revert u v
    decide
  rw [he]
  exact Core.framed (Core.base 0) perm6

theorem base_edge_2_1 : Edge (base 2) 1 := by
  right; left
  have he : relabel (mutate (base 2) 1) perm7 = template (6) (2) (2) (11) (13) (2) := by
    funext u v
    revert u v
    decide
  have hb : IsWeakFork (relabel (mutate (base 2) 1) perm7) 0 := by
    rw [he]
    exact IsWeakFork.basic (6) (2) (2) (11) (13) (2) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm7 hb

theorem base_edge_2_2 : Edge (base 2) 2 := by
  left
  have he : mutate (base 2) 2 = reverse (relabel (base 1) perm6) := by
    funext u v
    revert u v
    decide
  rw [he]
  exact Core.reversed (Core.framed (Core.base 1) perm6)

theorem base_edge_2_3 : Edge (base 2) 3 := by
  left
  have he : mutate (base 2) 3 = reverse (relabel (base 4) perm7) := by
    funext u v
    revert u v
    decide
  rw [he]
  exact Core.reversed (Core.framed (Core.base 4) perm7)

theorem base_edge_3_0 : Edge (base 3) 0 := by
  right; right
  have he : relabel (reverse (mutate (base 3) 0)) perm4 = root (2) (7) (5) (4) (2) (1) := by
    funext u v
    revert u v
    decide
  have hb : IsRoot (relabel (reverse (mutate (base 3) 0)) perm4) 0 := by
    rw [he]
    exact IsRoot.basic (2) (7) (5) (4) (2) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact root_of_reverse (root_of_relabel perm4 hb)

theorem base_edge_3_1 : Edge (base 3) 1 := by
  left
  have he : mutate (base 3) 1 = relabel (base 0) perm4 := by
    funext u v
    revert u v
    decide
  rw [he]
  exact Core.framed (Core.base 0) perm4

theorem base_edge_3_2 : Edge (base 3) 2 := by
  left
  have he : mutate (base 3) 2 = reverse (relabel (base 5) perm6) := by
    funext u v
    revert u v
    decide
  rw [he]
  exact Core.reversed (Core.framed (Core.base 5) perm6)

theorem base_edge_3_3 : Edge (base 3) 3 := by
  left
  have he : mutate (base 3) 3 = relabel (base 6) perm0 := by
    funext u v
    revert u v
    decide
  rw [he]
  exact Core.framed (Core.base 6) perm0

theorem base_edge_4_0 : Edge (base 4) 0 := by
  right; right
  have he : relabel (reverse (mutate (base 4) 0)) perm5 = root (2) (6) (7) (2) (4) (1) := by
    funext u v
    revert u v
    decide
  have hb : IsRoot (relabel (reverse (mutate (base 4) 0)) perm5) 0 := by
    rw [he]
    exact IsRoot.basic (2) (6) (7) (2) (4) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact root_of_reverse (root_of_relabel perm5 hb)

theorem base_edge_4_1 : Edge (base 4) 1 := by
  left
  have he : mutate (base 4) 1 = relabel (base 5) perm6 := by
    funext u v
    revert u v
    decide
  rw [he]
  exact Core.framed (Core.base 5) perm6

theorem base_edge_4_2 : Edge (base 4) 2 := by
  left
  have he : mutate (base 4) 2 = reverse (relabel (base 2) perm7) := by
    funext u v
    revert u v
    decide
  rw [he]
  exact Core.reversed (Core.framed (Core.base 2) perm7)

theorem base_edge_4_3 : Edge (base 4) 3 := by
  left
  have he : mutate (base 4) 3 = relabel (base 6) perm4 := by
    funext u v
    revert u v
    decide
  rw [he]
  exact Core.framed (Core.base 6) perm4

theorem base_edge_5_0 : Edge (base 5) 0 := by
  left
  have he : mutate (base 5) 0 = relabel (base 4) perm6 := by
    funext u v
    revert u v
    decide
  rw [he]
  exact Core.framed (Core.base 4) perm6

theorem base_edge_5_1 : Edge (base 5) 1 := by
  right; right
  have he : relabel (reverse (mutate (base 5) 1)) perm7 = root (4) (7) (9) (2) (2) (1) := by
    funext u v
    revert u v
    decide
  have hb : IsRoot (relabel (reverse (mutate (base 5) 1)) perm7) 0 := by
    rw [he]
    exact IsRoot.basic (4) (7) (9) (2) (2) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact root_of_reverse (root_of_relabel perm7 hb)

theorem base_edge_5_2 : Edge (base 5) 2 := by
  left
  have he : mutate (base 5) 2 = reverse (relabel (base 3) perm6) := by
    funext u v
    revert u v
    decide
  rw [he]
  exact Core.reversed (Core.framed (Core.base 3) perm6)

theorem base_edge_5_3 : Edge (base 5) 3 := by
  left
  have he : mutate (base 5) 3 = reverse (relabel (base 5) perm14) := by
    funext u v
    revert u v
    decide
  rw [he]
  exact Core.reversed (Core.framed (Core.base 5) perm14)

theorem base_edge_6_0 : Edge (base 6) 0 := by
  left
  have he : mutate (base 6) 0 = reverse (relabel (base 6) perm2) := by
    funext u v
    revert u v
    decide
  rw [he]
  exact Core.reversed (Core.framed (Core.base 6) perm2)

theorem base_edge_6_1 : Edge (base 6) 1 := by
  left
  have he : mutate (base 6) 1 = relabel (tail 0 2) perm4 := by
    funext u v
    revert u v
    decide
  rw [he]
  exact Core.framed (Core.tail 0 (by omega) 2) perm4

theorem base_edge_6_2 : Edge (base 6) 2 := by
  left
  have he : mutate (base 6) 2 = relabel (base 4) perm3 := by
    funext u v
    revert u v
    decide
  rw [he]
  exact Core.framed (Core.base 4) perm3

theorem base_edge_6_3 : Edge (base 6) 3 := by
  left
  have he : mutate (base 6) 3 = relabel (base 3) perm0 := by
    funext u v
    revert u v
    decide
  rw [he]
  exact Core.framed (Core.base 3) perm0

theorem tail_edge_0_0 (n : Int) (hn : 0≤n) : Edge (tail n 0) 0 := by
  left
  have he : mutate (tail n 0) 0 = reverse (relabel (tail n 1) perm1) := by
    funext u v
    rcases fin4 u with rfl|rfl|rfl|rfl <;> rcases fin4 v with rfl|rfl|rfl|rfl <;>
      simp [tail,base,ofSix,mutate,correction,relabel,reverse,perm1] <;> grind
  rw [he]
  exact Core.reversed (Core.framed (Core.tail n (by omega) 1) perm1)

theorem tail_edge_0_1 (n : Int) (hn : 0≤n) : Edge (tail n 0) 1 := by
  right; right
  have he : relabel (reverse (mutate (tail n 0) 1)) perm6 = root (4*n + 8) (16*n*n + 56*n + 47) (24*n + 47) (4*n + 6) (6) (1) := by
    funext u v
    rcases fin4 u with rfl|rfl|rfl|rfl <;> rcases fin4 v with rfl|rfl|rfl|rfl <;>
      simp [tail,ofSix,mutate,correction,relabel,reverse,perm6,root] <;> grind
  have hb : IsRoot (relabel (reverse (mutate (tail n 0) 1)) perm6) 0 := by
    rw [he]
    have hnn := Int.mul_nonneg (show 0≤n by omega) (show 0≤n by omega)
    exact IsRoot.basic (4*n + 8) (16*n*n + 56*n + 47) (24*n + 47) (4*n + 6) (6) (1) (by unfold WeakRegions.Domain; grind) (by decide)
  exact root_of_reverse (root_of_relabel perm6 hb)

theorem tail_edge_0_2 (n : Int) (hn : 0≤n) : Edge (tail n 0) 2 := by
  left
  have he : mutate (tail n 0) 2 = reverse (relabel (tail (n+1) 1) perm21) := by
    funext u v
    rcases fin4 u with rfl|rfl|rfl|rfl <;> rcases fin4 v with rfl|rfl|rfl|rfl <;>
      simp [tail,base,ofSix,mutate,correction,relabel,reverse,perm21] <;> grind
  rw [he]
  exact Core.reversed (Core.framed (Core.tail (n+1) (by omega) 1) perm21)

theorem tail_edge_0_3_zero : Edge (tail 0 0) 3 := by
  left
  have he : mutate (tail 0 0) 3 = reverse (relabel (base 1) perm13) := by
    funext u v
    revert u v
    decide
  rw [he]
  exact Core.reversed (Core.framed (Core.base 1) perm13)

theorem tail_edge_0_3_pos (n : Int) (hn : 1≤n) : Edge (tail n 0) 3 := by
  left
  have he : mutate (tail n 0) 3 = reverse (relabel (tail (n-1) 3) perm20) := by
    funext u v
    rcases fin4 u with rfl|rfl|rfl|rfl <;> rcases fin4 v with rfl|rfl|rfl|rfl <;>
      simp [tail,base,ofSix,mutate,correction,relabel,reverse,perm20] <;> grind
  rw [he]
  exact Core.reversed (Core.framed (Core.tail (n-1) (by omega) 3) perm20)

theorem tail_edge_0_3 (n : Int) (hn : 0≤n) : Edge (tail n 0) 3 := by
  by_cases hzero : n=0
  · subst n; exact tail_edge_0_3_zero
  · exact tail_edge_0_3_pos n (by omega)

theorem tail_edge_1_0 (n : Int) (hn : 0≤n) : Edge (tail n 1) 0 := by
  left
  have he : mutate (tail n 1) 0 = reverse (relabel (tail n 0) perm1) := by
    funext u v
    rcases fin4 u with rfl|rfl|rfl|rfl <;> rcases fin4 v with rfl|rfl|rfl|rfl <;>
      simp [tail,base,ofSix,mutate,correction,relabel,reverse,perm1] <;> grind
  rw [he]
  exact Core.reversed (Core.framed (Core.tail n (by omega) 0) perm1)

theorem tail_edge_1_1 (n : Int) (hn : 0≤n) : Edge (tail n 1) 1 := by
  right; right
  have he : relabel (reverse (mutate (tail n 1) 1)) perm6 = root (4*n + 8) (16*n*n + 40*n + 15) (8*n + 15) (4*n + 2) (2) (1) := by
    funext u v
    rcases fin4 u with rfl|rfl|rfl|rfl <;> rcases fin4 v with rfl|rfl|rfl|rfl <;>
      simp [tail,ofSix,mutate,correction,relabel,reverse,perm6,root] <;> grind
  have hb : IsRoot (relabel (reverse (mutate (tail n 1) 1)) perm6) 0 := by
    rw [he]
    have hnn := Int.mul_nonneg (show 0≤n by omega) (show 0≤n by omega)
    exact IsRoot.basic (4*n + 8) (16*n*n + 40*n + 15) (8*n + 15) (4*n + 2) (2) (1) (by unfold WeakRegions.Domain; grind) (by decide)
  exact root_of_reverse (root_of_relabel perm6 hb)

theorem tail_edge_1_2_zero : Edge (tail 0 1) 2 := by
  left
  have he : mutate (tail 0 1) 2 = reverse (relabel (base 0) perm6) := by
    funext u v
    revert u v
    decide
  rw [he]
  exact Core.reversed (Core.framed (Core.base 0) perm6)

theorem tail_edge_1_2_pos (n : Int) (hn : 1≤n) : Edge (tail n 1) 2 := by
  left
  have he : mutate (tail n 1) 2 = reverse (relabel (tail (n-1) 0) perm21) := by
    funext u v
    rcases fin4 u with rfl|rfl|rfl|rfl <;> rcases fin4 v with rfl|rfl|rfl|rfl <;>
      simp [tail,base,ofSix,mutate,correction,relabel,reverse,perm21] <;> grind
  rw [he]
  exact Core.reversed (Core.framed (Core.tail (n-1) (by omega) 0) perm21)

theorem tail_edge_1_2 (n : Int) (hn : 0≤n) : Edge (tail n 1) 2 := by
  by_cases hzero : n=0
  · subst n; exact tail_edge_1_2_zero
  · exact tail_edge_1_2_pos n (by omega)

theorem tail_edge_1_3 (n : Int) (hn : 0≤n) : Edge (tail n 1) 3 := by
  left
  have he : mutate (tail n 1) 3 = reverse (relabel (tail n 2) perm7) := by
    funext u v
    rcases fin4 u with rfl|rfl|rfl|rfl <;> rcases fin4 v with rfl|rfl|rfl|rfl <;>
      simp [tail,base,ofSix,mutate,correction,relabel,reverse,perm7] <;> grind
  rw [he]
  exact Core.reversed (Core.framed (Core.tail n (by omega) 2) perm7)

theorem tail_edge_2_0 (n : Int) (hn : 0≤n) : Edge (tail n 2) 0 := by
  right; right
  have he : relabel (reverse (mutate (tail n 2) 0)) perm5 = root (4*n + 2) (8*n + 5) (16*n*n + 32*n + 10) (2) (4*n + 6) (1) := by
    funext u v
    rcases fin4 u with rfl|rfl|rfl|rfl <;> rcases fin4 v with rfl|rfl|rfl|rfl <;>
      simp [tail,ofSix,mutate,correction,relabel,reverse,perm5,root] <;> grind
  have hb : IsRoot (relabel (reverse (mutate (tail n 2) 0)) perm5) 0 := by
    rw [he]
    have hnn := Int.mul_nonneg (show 0≤n by omega) (show 0≤n by omega)
    exact IsRoot.basic (4*n + 2) (8*n + 5) (16*n*n + 32*n + 10) (2) (4*n + 6) (1) (by unfold WeakRegions.Domain; grind) (by decide)
  exact root_of_reverse (root_of_relabel perm5 hb)

theorem tail_edge_2_1 (n : Int) (hn : 0≤n) : Edge (tail n 2) 1 := by
  left
  have he : mutate (tail n 2) 1 = relabel (tail (n+1) 2) perm5 := by
    funext u v
    rcases fin4 u with rfl|rfl|rfl|rfl <;> rcases fin4 v with rfl|rfl|rfl|rfl <;>
      simp [tail,base,ofSix,mutate,correction,relabel,reverse,perm5] <;> grind
  rw [he]
  exact Core.framed (Core.tail (n+1) (by omega) 2) perm5

theorem tail_edge_2_2 (n : Int) (hn : 0≤n) : Edge (tail n 2) 2 := by
  left
  have he : mutate (tail n 2) 2 = reverse (relabel (tail n 1) perm7) := by
    funext u v
    rcases fin4 u with rfl|rfl|rfl|rfl <;> rcases fin4 v with rfl|rfl|rfl|rfl <;>
      simp [tail,base,ofSix,mutate,correction,relabel,reverse,perm7] <;> grind
  rw [he]
  exact Core.reversed (Core.framed (Core.tail n (by omega) 1) perm7)

theorem tail_edge_2_3_zero : Edge (tail 0 2) 3 := by
  left
  have he : mutate (tail 0 2) 3 = relabel (base 6) perm3 := by
    funext u v
    revert u v
    decide
  rw [he]
  exact Core.framed (Core.base 6) perm3

theorem tail_edge_2_3_pos (n : Int) (hn : 1≤n) : Edge (tail n 2) 3 := by
  left
  have he : mutate (tail n 2) 3 = relabel (tail (n-1) 2) perm5 := by
    funext u v
    rcases fin4 u with rfl|rfl|rfl|rfl <;> rcases fin4 v with rfl|rfl|rfl|rfl <;>
      simp [tail,base,ofSix,mutate,correction,relabel,reverse,perm5] <;> grind
  rw [he]
  exact Core.framed (Core.tail (n-1) (by omega) 2) perm5

theorem tail_edge_2_3 (n : Int) (hn : 0≤n) : Edge (tail n 2) 3 := by
  by_cases hzero : n=0
  · subst n; exact tail_edge_2_3_zero
  · exact tail_edge_2_3_pos n (by omega)

theorem tail_edge_3_0 (n : Int) (hn : 0≤n) : Edge (tail n 3) 0 := by
  left
  have he : mutate (tail n 3) 0 = relabel (tail (n+1) 3) perm21 := by
    funext u v
    rcases fin4 u with rfl|rfl|rfl|rfl <;> rcases fin4 v with rfl|rfl|rfl|rfl <;>
      simp [tail,base,ofSix,mutate,correction,relabel,reverse,perm21] <;> grind
  rw [he]
  exact Core.framed (Core.tail (n+1) (by omega) 3) perm21

theorem tail_edge_3_1 (n : Int) (hn : 0≤n) : Edge (tail n 3) 1 := by
  right; right
  have he : relabel (reverse (mutate (tail n 3) 1)) perm6 = root (4*n + 10) (24*n + 61) (16*n*n + 64*n + 58) (6) (4*n + 6) (1) := by
    funext u v
    rcases fin4 u with rfl|rfl|rfl|rfl <;> rcases fin4 v with rfl|rfl|rfl|rfl <;>
      simp [tail,ofSix,mutate,correction,relabel,reverse,perm6,root] <;> grind
  have hb : IsRoot (relabel (reverse (mutate (tail n 3) 1)) perm6) 0 := by
    rw [he]
    have hnn := Int.mul_nonneg (show 0≤n by omega) (show 0≤n by omega)
    exact IsRoot.basic (4*n + 10) (24*n + 61) (16*n*n + 64*n + 58) (6) (4*n + 6) (1) (by unfold WeakRegions.Domain; grind) (by decide)
  exact root_of_reverse (root_of_relabel perm6 hb)

theorem tail_edge_3_2 (n : Int) (hn : 0≤n) : Edge (tail n 3) 2 := by
  left
  have he : mutate (tail n 3) 2 = reverse (relabel (tail (n+1) 0) perm15) := by
    funext u v
    rcases fin4 u with rfl|rfl|rfl|rfl <;> rcases fin4 v with rfl|rfl|rfl|rfl <;>
      simp [tail,base,ofSix,mutate,correction,relabel,reverse,perm15] <;> grind
  rw [he]
  exact Core.reversed (Core.framed (Core.tail (n+1) (by omega) 0) perm15)

theorem tail_edge_3_3_zero : Edge (tail 0 3) 3 := by
  left
  have he : mutate (tail 0 3) 3 = relabel (base 1) perm12 := by
    funext u v
    revert u v
    decide
  rw [he]
  exact Core.framed (Core.base 1) perm12

theorem tail_edge_3_3_pos (n : Int) (hn : 1≤n) : Edge (tail n 3) 3 := by
  left
  have he : mutate (tail n 3) 3 = relabel (tail (n-1) 3) perm21 := by
    funext u v
    rcases fin4 u with rfl|rfl|rfl|rfl <;> rcases fin4 v with rfl|rfl|rfl|rfl <;>
      simp [tail,base,ofSix,mutate,correction,relabel,reverse,perm21] <;> grind
  rw [he]
  exact Core.framed (Core.tail (n-1) (by omega) 3) perm21

theorem tail_edge_3_3 (n : Int) (hn : 0≤n) : Edge (tail n 3) 3 := by
  by_cases hzero : n=0
  · subst n; exact tail_edge_3_3_zero
  · exact tail_edge_3_3_pos n (by omega)

theorem base_edges (i : Fin 7) (k : Fin 4) : Edge (base i) k := by
  rcases fin7 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rcases fin4 k with rfl|rfl|rfl|rfl
  · exact base_edge_0_0
  · exact base_edge_0_1
  · exact base_edge_0_2
  · exact base_edge_0_3
  · exact base_edge_1_0
  · exact base_edge_1_1
  · exact base_edge_1_2
  · exact base_edge_1_3
  · exact base_edge_2_0
  · exact base_edge_2_1
  · exact base_edge_2_2
  · exact base_edge_2_3
  · exact base_edge_3_0
  · exact base_edge_3_1
  · exact base_edge_3_2
  · exact base_edge_3_3
  · exact base_edge_4_0
  · exact base_edge_4_1
  · exact base_edge_4_2
  · exact base_edge_4_3
  · exact base_edge_5_0
  · exact base_edge_5_1
  · exact base_edge_5_2
  · exact base_edge_5_3
  · exact base_edge_6_0
  · exact base_edge_6_1
  · exact base_edge_6_2
  · exact base_edge_6_3

theorem tail_edges (n : Int) (hn : 0≤n) (i k : Fin 4) : Edge (tail n i) k := by
  rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 k with rfl|rfl|rfl|rfl
  · exact tail_edge_0_0 n hn
  · exact tail_edge_0_1 n hn
  · exact tail_edge_0_2 n hn
  · exact tail_edge_0_3 n hn
  · exact tail_edge_1_0 n hn
  · exact tail_edge_1_1 n hn
  · exact tail_edge_1_2 n hn
  · exact tail_edge_1_3 n hn
  · exact tail_edge_2_0 n hn
  · exact tail_edge_2_1 n hn
  · exact tail_edge_2_2 n hn
  · exact tail_edge_2_3 n hn
  · exact tail_edge_3_0 n hn
  · exact tail_edge_3_1 n hn
  · exact tail_edge_3_2 n hn
  · exact tail_edge_3_3 n hn

theorem base_cyclic_0 : ¬ Acyclic (base 0) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem base_cyclic_1 : ¬ Acyclic (base 1) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 2 (by decide)
  have h2 := hr 2 0 (by decide)
  omega

theorem base_cyclic_2 : ¬ Acyclic (base 2) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem base_cyclic_3 : ¬ Acyclic (base 3) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem base_cyclic_4 : ¬ Acyclic (base 4) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem base_cyclic_5 : ¬ Acyclic (base 5) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem base_cyclic_6 : ¬ Acyclic (base 6) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 1 3 (by decide)
  have h1 := hr 3 2 (by decide)
  have h2 := hr 2 1 (by decide)
  omega

theorem tail_cyclic_0 (n : Int) (hn : 0≤n) : ¬ Acyclic (tail n 0) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (by simp [tail,ofSix] <;> omega)
  have h1 := hr 2 1 (by simp [tail,ofSix] <;> omega)
  have h2 := hr 1 0 (by simp [tail,ofSix] <;> omega)
  omega

theorem tail_cyclic_1 (n : Int) (hn : 0≤n) : ¬ Acyclic (tail n 1) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (by simp [tail,ofSix] <;> omega)
  have h1 := hr 2 1 (by simp [tail,ofSix] <;> omega)
  have h2 := hr 1 0 (by simp [tail,ofSix] <;> omega)
  omega

theorem tail_cyclic_2 (n : Int) (hn : 0≤n) : ¬ Acyclic (tail n 2) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by simp [tail,ofSix] <;> omega)
  have h1 := hr 3 1 (by simp [tail,ofSix] <;> omega)
  have h2 := hr 1 0 (by simp [tail,ofSix] <;> omega)
  omega

theorem tail_cyclic_3 (n : Int) (hn : 0≤n) : ¬ Acyclic (tail n 3) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by simp [tail,ofSix] <;> omega)
  have h1 := hr 3 1 (by simp [tail,ofSix] <;> omega)
  have h2 := hr 1 0 (by simp [tail,ofSix] <;> omega)
  omega

theorem core_skew {B : Matrix 4} (h : Core B) : SkewSymmetric B := by
  induction h with
  | base i => rcases fin7 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact ofSix_skew _ _ _ _ _ _
  | tail n hn i => rcases fin4 i with rfl|rfl|rfl|rfl <;> exact ofSix_skew _ _ _ _ _ _
  | framed h p ih => exact relabel_skew _ p ih
  | reversed h ih => exact reverse_skew _ ih

theorem core_cyclic {B : Matrix 4} (h : Core B) : ¬ Acyclic B := by
  induction h with
  | base i =>
    rcases fin7 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact base_cyclic_0
    · exact base_cyclic_1
    · exact base_cyclic_2
    · exact base_cyclic_3
    · exact base_cyclic_4
    · exact base_cyclic_5
    · exact base_cyclic_6
  | tail n hn i =>
    rcases fin4 i with rfl|rfl|rfl|rfl
    · exact tail_cyclic_0 n hn
    · exact tail_cyclic_1 n hn
    · exact tail_cyclic_2 n hn
    · exact tail_cyclic_3 n hn
  | framed h p ih => exact fun ha => ih ((acyclic_relabel_iff _ p).mp ha)
  | reversed h ih => exact fun ha => ih ((acyclic_reverse_iff _ (core_skew h)).mp ha)

theorem core_edges {B : Matrix 4} (h : Core B) (k : Fin 4) : Edge B k := by
  induction h generalizing k with
  | base i => exact base_edges i k
  | tail n hn i => exact tail_edges n hn i k
  | framed h p ih =>
    unfold Edge at *
    rw [mutate_relabel]
    rcases ih (p.toFun k) with hc|hf|hr
    · exact Or.inl (Core.framed hc p)
    · exact Or.inr (Or.inl (by simpa only [p.left_inv] using IsWeakFork.relabelled hf p))
    · exact Or.inr (Or.inr (by simpa only [p.left_inv] using IsRoot.relabelled hr p))
  | reversed h ih =>
    unfold Edge at *
    rw [mutate_reverse]
    rcases ih k with hc|hf|hr
    · exact Or.inl (Core.reversed hc)
    · exact Or.inr (Or.inl (IsWeakFork.reversed hf))
    · exact Or.inr (Or.inr (IsRoot.reversed hr))

theorem core_NMA {B : Matrix 4} (h : Core B) : ¬ MutationAcyclic B :=
  region_NMA WeakRegionCells.root_cells_exist Core (fun _ => core_skew)
    (fun _ => core_cyclic) (fun _ h k => core_edges h k) B h

theorem nma_q014 : ¬ MutationAcyclic (ofSix (-2) (-2) (-2) (-2) 1 (-1)) :=
  core_NMA (Core.base 6)

theorem nma_q161 : ¬ MutationAcyclic (ofSix (-2) (-2) 1 (-2) (-1) 2) := by
  have he : mutate (ofSix (-2) (-2) 1 (-2) (-1) 2) 2 = relabel (base 6) perm8 := by
    funext u v; revert u v; decide
  intro h
  have hm := (mutationAcyclic_iff (ofSix (-2) (-2) 1 (-2) (-1) 2) 2).mpr h
  rw [he] at hm
  exact core_NMA (Core.framed (Core.base 6) perm8) hm

end QuiverProofs.AffineTwoCorridor
