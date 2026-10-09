import QuiverProofs.WeakRegionCells
import QuiverProofs.ForkCertificates

namespace QuiverProofs.AffineFourOddLocal
open WeakForks WeakRegions WeakRegionSemantics ForkCertificates
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

private theorem fin4 (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega

def tail (n : Int) (i : Fin 4) : Matrix 4 := match i.val with
  | 0 => ofSix (-2*n-7) 1 1 (-2*n-5) (-4) (-1)
  | 1 => ofSix (-2*n-7) 1 1 (-2*n-3) (-2) (-1)
  | 2 => ofSix (-2*n-5) (-2) (2*n+3) 1 (-2) 1
  | _ => ofSix (-2*n-7) (-1) 2 (-4) (-2*n-5) (-1)

def base (i : Fin 4) : Matrix 4 := match i.val with
  | 0 => (ofSix (-3) (2) (-1) (-5) (4) (1))
  | 1 => (ofSix (-4) (-1) (1) (3) (-5) (1))
  | 2 => (ofSix (1) (-2) (-3) (-1) (2) (-1))
  | _ => (ofSix (3) (1) (-2) (-4) (5) (1))

inductive Core : Matrix 4 → Prop
  | base (i : Fin 4) : Core (base i)
  | tail (n : Int) (hn : 0≤n) (i : Fin 4) : Core (tail n i)
  | framed {B : Matrix 4} : Core B → (p : Relabeling 4) → Core (relabel B p)
  | reversed {B : Matrix 4} : Core B → Core (reverse B)

def Edge (B : Matrix 4) (k : Fin 4) : Prop :=
  Core (mutate B k) ∨ IsWeakFork (mutate B k) k ∨ IsRoot (mutate B k) k

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
  have he : relabel (reverse (mutate (tail n 0) 1)) perm6 = root (2*n + 7) (4*n*n + 24*n + 34) (8*n + 27) (2*n + 5) (4) (1) := by
    funext u v
    rcases fin4 u with rfl|rfl|rfl|rfl <;> rcases fin4 v with rfl|rfl|rfl|rfl <;>
      simp [tail,ofSix,mutate,correction,relabel,reverse,perm6,root] <;> grind
  have hb : IsRoot (relabel (reverse (mutate (tail n 0) 1)) perm6) 0 := by
    rw [he]
    have hnn := Int.mul_nonneg (show 0≤n by omega) (show 0≤n by omega)
    exact IsRoot.basic (2*n + 7) (4*n*n + 24*n + 34) (8*n + 27) (2*n + 5) (4) (1) (by unfold WeakRegions.Domain; grind) (by decide)
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
  have he : mutate (tail 0 0) 3 = relabel (base 0) perm0 := by
    funext u v
    revert u v
    decide
  rw [he]
  exact Core.framed (Core.base 0) perm0

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
  have he : relabel (reverse (mutate (tail n 1) 1)) perm6 = root (2*n + 7) (4*n*n + 20*n + 20) (4*n + 13) (2*n + 3) (2) (1) := by
    funext u v
    rcases fin4 u with rfl|rfl|rfl|rfl <;> rcases fin4 v with rfl|rfl|rfl|rfl <;>
      simp [tail,ofSix,mutate,correction,relabel,reverse,perm6,root] <;> grind
  have hb : IsRoot (relabel (reverse (mutate (tail n 1) 1)) perm6) 0 := by
    rw [he]
    have hnn := Int.mul_nonneg (show 0≤n by omega) (show 0≤n by omega)
    exact IsRoot.basic (2*n + 7) (4*n*n + 20*n + 20) (4*n + 13) (2*n + 3) (2) (1) (by unfold WeakRegions.Domain; grind) (by decide)
  exact root_of_reverse (root_of_relabel perm6 hb)

theorem tail_edge_1_2_zero : Edge (tail 0 1) 2 := by
  left
  have he : mutate (tail 0 1) 2 = relabel (base 1) perm0 := by
    funext u v
    revert u v
    decide
  rw [he]
  exact Core.framed (Core.base 1) perm0

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
  have he : relabel (reverse (mutate (tail n 2) 0)) perm5 = root (2*n + 3) (4*n + 7) (4*n*n + 16*n + 13) (2) (2*n + 5) (1) := by
    funext u v
    rcases fin4 u with rfl|rfl|rfl|rfl <;> rcases fin4 v with rfl|rfl|rfl|rfl <;>
      simp [tail,ofSix,mutate,correction,relabel,reverse,perm5,root] <;> grind
  have hb : IsRoot (relabel (reverse (mutate (tail n 2) 0)) perm5) 0 := by
    rw [he]
    have hnn := Int.mul_nonneg (show 0≤n by omega) (show 0≤n by omega)
    exact IsRoot.basic (2*n + 3) (4*n + 7) (4*n*n + 16*n + 13) (2) (2*n + 5) (1) (by unfold WeakRegions.Domain; grind) (by decide)
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
  have he : mutate (tail 0 2) 3 = relabel (base 2) perm0 := by
    funext u v
    revert u v
    decide
  rw [he]
  exact Core.framed (Core.base 2) perm0

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
  have he : relabel (reverse (mutate (tail n 3) 1)) perm6 = root (2*n + 7) (8*n + 29) (4*n*n + 24*n + 33) (4) (2*n + 5) (1) := by
    funext u v
    rcases fin4 u with rfl|rfl|rfl|rfl <;> rcases fin4 v with rfl|rfl|rfl|rfl <;>
      simp [tail,ofSix,mutate,correction,relabel,reverse,perm6,root] <;> grind
  have hb : IsRoot (relabel (reverse (mutate (tail n 3) 1)) perm6) 0 := by
    rw [he]
    have hnn := Int.mul_nonneg (show 0≤n by omega) (show 0≤n by omega)
    exact IsRoot.basic (2*n + 7) (8*n + 29) (4*n*n + 24*n + 33) (4) (2*n + 5) (1) (by unfold WeakRegions.Domain; grind) (by decide)
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
  have he : mutate (tail 0 3) 3 = reverse (relabel (base 0) perm1) := by
    funext u v
    revert u v
    decide
  rw [he]
  exact Core.reversed (Core.framed (Core.base 0) perm1)

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

theorem tail_skew (n : Int) (i : Fin 4) : SkewSymmetric (tail n i) := by
  rcases fin4 i with rfl|rfl|rfl|rfl <;> exact ofSix_skew _ _ _ _ _ _

theorem tail_cyclic (n : Int) (hn : 0≤n) (i : Fin 4) : ¬ Acyclic (tail n i) := by
  rcases fin4 i with rfl|rfl|rfl|rfl
  · exact tail_cyclic_0 n hn
  · exact tail_cyclic_1 n hn
  · exact tail_cyclic_2 n hn
  · exact tail_cyclic_3 n hn

end QuiverProofs.AffineFourOddLocal
