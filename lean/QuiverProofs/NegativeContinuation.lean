import QuiverProofs.WeakRegionCells
import QuiverProofs.ForkCertificates

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace QuiverProofs.NegativeContinuation
open WeakForks WeakRegions WeakRegionSemantics ForkCertificates

namespace Core00
def node (i : Fin 2) : Matrix 4 := match i.val with
  | 0 => (ofSix (-2) (-2) (-2) (-2) (2) (-2))
  | _ => (ofSix (-2) (-2) (2) (-2) (-2) (2))

theorem cyclic0 : ¬ Acyclic (node 0) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 1 3 (by decide)
  have h1 := hr 3 2 (by decide)
  have h2 := hr 2 1 (by decide)
  omega

theorem edge0_0 : FramedCore node (mutate (node 0) 0) ∨
    IsWeakFork (mutate (node 0) 0) 0 ∨ IsRoot (mutate (node 0) 0) 0 := by
  left; refine ⟨1, perm12, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 0 u v =
    relabel (node 1) perm12 u v from by decide) u v

theorem edge0_1 : FramedCore node (mutate (node 0) 1) ∨
    IsWeakFork (mutate (node 0) 1) 1 ∨ IsRoot (mutate (node 0) 1) 1 := by
  right; left
  have he : relabel (reverse (mutate (node 0) 1)) perm8 = template (2) (2) (2) (6) (2) (2) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 0) 1)) perm8 u v =
      template (2) (2) (2) (6) (2) (2) u v from by decide) u v
  have hb : IsWeakFork (relabel (reverse (mutate (node 0) 1)) perm8) 0 := by
    rw [he]
    exact IsWeakFork.basic (2) (2) (2) (6) (2) (2) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_reverse (WeakForks.fork_of_relabel perm8 hb)

theorem edge0_2 : FramedCore node (mutate (node 0) 2) ∨
    IsWeakFork (mutate (node 0) 2) 2 ∨ IsRoot (mutate (node 0) 2) 2 := by
  right; left
  have he : relabel (reverse (mutate (node 0) 2)) perm16 = template (2) (2) (2) (6) (2) (2) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 0) 2)) perm16 u v =
      template (2) (2) (2) (6) (2) (2) u v from by decide) u v
  have hb : IsWeakFork (relabel (reverse (mutate (node 0) 2)) perm16) 0 := by
    rw [he]
    exact IsWeakFork.basic (2) (2) (2) (6) (2) (2) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_reverse (WeakForks.fork_of_relabel perm16 hb)

theorem edge0_3 : FramedCore node (mutate (node 0) 3) ∨
    IsWeakFork (mutate (node 0) 3) 3 ∨ IsRoot (mutate (node 0) 3) 3 := by
  right; left
  have he : relabel (reverse (mutate (node 0) 3)) perm20 = template (2) (2) (2) (6) (2) (2) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 0) 3)) perm20 u v =
      template (2) (2) (2) (6) (2) (2) u v from by decide) u v
  have hb : IsWeakFork (relabel (reverse (mutate (node 0) 3)) perm20) 0 := by
    rw [he]
    exact IsWeakFork.basic (2) (2) (2) (6) (2) (2) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_reverse (WeakForks.fork_of_relabel perm20 hb)

theorem cyclic1 : ¬ Acyclic (node 1) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge1_0 : FramedCore node (mutate (node 1) 0) ∨
    IsWeakFork (mutate (node 1) 0) 0 ∨ IsRoot (mutate (node 1) 0) 0 := by
  right; left
  have he : relabel (mutate (node 1) 0) perm5 = template (2) (2) (2) (6) (2) (2) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 1) 0) perm5 u v =
      template (2) (2) (2) (6) (2) (2) u v from by decide) u v
  have hb : IsWeakFork (relabel (mutate (node 1) 0) perm5) 0 := by
    rw [he]
    exact IsWeakFork.basic (2) (2) (2) (6) (2) (2) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm5 hb

theorem edge1_1 : FramedCore node (mutate (node 1) 1) ∨
    IsWeakFork (mutate (node 1) 1) 1 ∨ IsRoot (mutate (node 1) 1) 1 := by
  right; left
  have he : relabel (mutate (node 1) 1) perm6 = template (2) (2) (2) (6) (2) (2) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 1) 1) perm6 u v =
      template (2) (2) (2) (6) (2) (2) u v from by decide) u v
  have hb : IsWeakFork (relabel (mutate (node 1) 1) perm6) 0 := by
    rw [he]
    exact IsWeakFork.basic (2) (2) (2) (6) (2) (2) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm6 hb

theorem edge1_2 : FramedCore node (mutate (node 1) 2) ∨
    IsWeakFork (mutate (node 1) 2) 2 ∨ IsRoot (mutate (node 1) 2) 2 := by
  left; refine ⟨0, perm8, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 1) 2 u v =
    relabel (node 0) perm8 u v from by decide) u v

theorem edge1_3 : FramedCore node (mutate (node 1) 3) ∨
    IsWeakFork (mutate (node 1) 3) 3 ∨ IsRoot (mutate (node 1) 3) 3 := by
  right; left
  have he : relabel (mutate (node 1) 3) perm21 = template (2) (2) (2) (6) (2) (2) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 1) 3) perm21 u v =
      template (2) (2) (2) (6) (2) (2) u v from by decide) u v
  have hb : IsWeakFork (relabel (mutate (node 1) 3) perm21) 0 := by
    rw [he]
    exact IsWeakFork.basic (2) (2) (2) (6) (2) (2) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm21 hb

theorem all_skew : ∀ i, SkewSymmetric (node i) := by
  intro i
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl <;>
    exact ofSix_skew _ _ _ _ _ _

theorem all_cyclic : ∀ i, ¬ Acyclic (node i) := by
  intro i
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  · exact cyclic0
  · exact cyclic1

theorem all_edges : ∀ i k, FramedCore node (mutate (node i) k) ∨
    IsWeakFork (mutate (node i) k) k ∨ IsRoot (mutate (node i) k) k := by
  intro i k
  have hi : i = 0 ∨ i = 1 := by omega
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hi with rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl
  · exact edge0_0
  · exact edge0_1
  · exact edge0_2
  · exact edge0_3
  · exact edge1_0
  · exact edge1_1
  · exact edge1_2
  · exact edge1_3

end Core00

/-- Unconditional all-word NMA for source certificate `q017`. -/
theorem nma_q017 : ¬ MutationAcyclic (ofSix (-2) (-2) (-2) (-2) (2) (-2)) :=
  framed_region_NMA WeakRegionCells.root_cells_exist Core00.node
    Core00.all_skew Core00.all_cyclic Core00.all_edges 0

/-- Unconditional all-word NMA for source certificate `q218`. -/
theorem nma_q218 : ¬ MutationAcyclic (ofSix (-2) (-2) (2) (-2) (-2) (2)) :=
  framed_region_NMA WeakRegionCells.root_cells_exist Core00.node
    Core00.all_skew Core00.all_cyclic Core00.all_edges 1

namespace Core01
def node (i : Fin 5) : Matrix 4 := match i.val with
  | 0 => (ofSix (-4) (-2) (1) (-2) (-2) (-4))
  | 1 => (ofSix (-4) (-2) (1) (2) (-2) (2))
  | 2 => (ofSix (-4) (-2) (2) (2) (-1) (-2))
  | 3 => (ofSix (-2) (-2) (-1) (-2) (2) (-2))
  | _ => (ofSix (-2) (-2) (2) (-2) (-2) (1))

theorem cyclic0 : ¬ Acyclic (node 0) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge0_0 : FramedCore node (mutate (node 0) 0) ∨
    IsWeakFork (mutate (node 0) 0) 0 ∨ IsRoot (mutate (node 0) 0) 0 := by
  left; refine ⟨2, perm6, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 0 u v =
    relabel (node 2) perm6 u v from by decide) u v

theorem edge0_1 : FramedCore node (mutate (node 0) 1) ∨
    IsWeakFork (mutate (node 0) 1) 1 ∨ IsRoot (mutate (node 0) 1) 1 := by
  right; left
  have he : relabel (mutate (node 0) 1) perm7 = template (4) (2) (2) (7) (10) (4) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 0) 1) perm7 u v =
      template (4) (2) (2) (7) (10) (4) u v from by decide) u v
  have hb : IsWeakFork (relabel (mutate (node 0) 1) perm7) 0 := by
    rw [he]
    exact IsWeakFork.basic (4) (2) (2) (7) (10) (4) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm7 hb

theorem edge0_2 : FramedCore node (mutate (node 0) 2) ∨
    IsWeakFork (mutate (node 0) 2) 2 ∨ IsRoot (mutate (node 0) 2) 2 := by
  right; left
  have he : relabel (reverse (mutate (node 0) 2)) perm16 = template (4) (2) (2) (7) (10) (4) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 0) 2)) perm16 u v =
      template (4) (2) (2) (7) (10) (4) u v from by decide) u v
  have hb : IsWeakFork (relabel (reverse (mutate (node 0) 2)) perm16) 0 := by
    rw [he]
    exact IsWeakFork.basic (4) (2) (2) (7) (10) (4) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_reverse (WeakForks.fork_of_relabel perm16 hb)

theorem edge0_3 : FramedCore node (mutate (node 0) 3) ∨
    IsWeakFork (mutate (node 0) 3) 3 ∨ IsRoot (mutate (node 0) 3) 3 := by
  left; refine ⟨1, perm23, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 3 u v =
    relabel (node 1) perm23 u v from by decide) u v

theorem cyclic1 : ¬ Acyclic (node 1) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge1_0 : FramedCore node (mutate (node 1) 0) ∨
    IsWeakFork (mutate (node 1) 0) 0 ∨ IsRoot (mutate (node 1) 0) 0 := by
  left; refine ⟨0, perm23, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 1) 0 u v =
    relabel (node 0) perm23 u v from by decide) u v

theorem edge1_1 : FramedCore node (mutate (node 1) 1) ∨
    IsWeakFork (mutate (node 1) 1) 1 ∨ IsRoot (mutate (node 1) 1) 1 := by
  right; left
  have he : relabel (reverse (mutate (node 1) 1)) perm10 = template (2) (4) (2) (7) (2) (2) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 1) 1)) perm10 u v =
      template (2) (4) (2) (7) (2) (2) u v from by decide) u v
  have hb : IsWeakFork (relabel (reverse (mutate (node 1) 1)) perm10) 0 := by
    rw [he]
    exact IsWeakFork.basic (2) (4) (2) (7) (2) (2) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_reverse (WeakForks.fork_of_relabel perm10 hb)

theorem edge1_2 : FramedCore node (mutate (node 1) 2) ∨
    IsWeakFork (mutate (node 1) 2) 2 ∨ IsRoot (mutate (node 1) 2) 2 := by
  right; right
  have he : relabel (mutate (node 1) 2) perm14 = root (2) (8) (2) (2) (2) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 1) 2) perm14 u v =
      root (2) (8) (2) (2) (2) (1) u v from by decide) u v
  have hb : IsRoot (relabel (mutate (node 1) 2) perm14) 0 := by
    rw [he]
    exact IsRoot.basic (2) (8) (2) (2) (2) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact root_of_relabel perm14 hb

theorem edge1_3 : FramedCore node (mutate (node 1) 3) ∨
    IsWeakFork (mutate (node 1) 3) 3 ∨ IsRoot (mutate (node 1) 3) 3 := by
  left; refine ⟨3, perm0, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 1) 3 u v =
    relabel (node 3) perm0 u v from by decide) u v

theorem cyclic2 : ¬ Acyclic (node 2) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge2_0 : FramedCore node (mutate (node 2) 0) ∨
    IsWeakFork (mutate (node 2) 0) 0 ∨ IsRoot (mutate (node 2) 0) 0 := by
  right; left
  have he : relabel (mutate (node 2) 0) perm4 = template (2) (4) (2) (7) (2) (2) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 2) 0) perm4 u v =
      template (2) (4) (2) (7) (2) (2) u v from by decide) u v
  have hb : IsWeakFork (relabel (mutate (node 2) 0) perm4) 0 := by
    rw [he]
    exact IsWeakFork.basic (2) (4) (2) (7) (2) (2) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm4 hb

theorem edge2_1 : FramedCore node (mutate (node 2) 1) ∨
    IsWeakFork (mutate (node 2) 1) 1 ∨ IsRoot (mutate (node 2) 1) 1 := by
  left; refine ⟨0, perm6, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 2) 1 u v =
    relabel (node 0) perm6 u v from by decide) u v

theorem edge2_2 : FramedCore node (mutate (node 2) 2) ∨
    IsWeakFork (mutate (node 2) 2) 2 ∨ IsRoot (mutate (node 2) 2) 2 := by
  right; right
  have he : relabel (reverse (mutate (node 2) 2)) perm12 = root (2) (8) (2) (2) (2) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 2) 2)) perm12 u v =
      root (2) (8) (2) (2) (2) (1) u v from by decide) u v
  have hb : IsRoot (relabel (reverse (mutate (node 2) 2)) perm12) 0 := by
    rw [he]
    exact IsRoot.basic (2) (8) (2) (2) (2) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact root_of_reverse (root_of_relabel perm12 hb)

theorem edge2_3 : FramedCore node (mutate (node 2) 3) ∨
    IsWeakFork (mutate (node 2) 3) 3 ∨ IsRoot (mutate (node 2) 3) 3 := by
  left; refine ⟨4, perm8, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 2) 3 u v =
    relabel (node 4) perm8 u v from by decide) u v

theorem cyclic3 : ¬ Acyclic (node 3) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 1 3 (by decide)
  have h1 := hr 3 2 (by decide)
  have h2 := hr 2 1 (by decide)
  omega

theorem edge3_0 : FramedCore node (mutate (node 3) 0) ∨
    IsWeakFork (mutate (node 3) 0) 0 ∨ IsRoot (mutate (node 3) 0) 0 := by
  left; refine ⟨4, perm12, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 3) 0 u v =
    relabel (node 4) perm12 u v from by decide) u v

theorem edge3_1 : FramedCore node (mutate (node 3) 1) ∨
    IsWeakFork (mutate (node 3) 1) 1 ∨ IsRoot (mutate (node 3) 1) 1 := by
  right; right
  have he : relabel (mutate (node 3) 1) perm9 = root (2) (2) (6) (2) (2) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 3) 1) perm9 u v =
      root (2) (2) (6) (2) (2) (1) u v from by decide) u v
  have hb : IsRoot (relabel (mutate (node 3) 1) perm9) 0 := by
    rw [he]
    exact IsRoot.basic (2) (2) (6) (2) (2) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact root_of_relabel perm9 hb

theorem edge3_2 : FramedCore node (mutate (node 3) 2) ∨
    IsWeakFork (mutate (node 3) 2) 2 ∨ IsRoot (mutate (node 3) 2) 2 := by
  right; left
  have he : relabel (reverse (mutate (node 3) 2)) perm16 = template (2) (2) (2) (5) (2) (2) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 3) 2)) perm16 u v =
      template (2) (2) (2) (5) (2) (2) u v from by decide) u v
  have hb : IsWeakFork (relabel (reverse (mutate (node 3) 2)) perm16) 0 := by
    rw [he]
    exact IsWeakFork.basic (2) (2) (2) (5) (2) (2) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_reverse (WeakForks.fork_of_relabel perm16 hb)

theorem edge3_3 : FramedCore node (mutate (node 3) 3) ∨
    IsWeakFork (mutate (node 3) 3) 3 ∨ IsRoot (mutate (node 3) 3) 3 := by
  left; refine ⟨1, perm0, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 3) 3 u v =
    relabel (node 1) perm0 u v from by decide) u v

theorem cyclic4 : ¬ Acyclic (node 4) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge4_0 : FramedCore node (mutate (node 4) 0) ∨
    IsWeakFork (mutate (node 4) 0) 0 ∨ IsRoot (mutate (node 4) 0) 0 := by
  right; left
  have he : relabel (mutate (node 4) 0) perm5 = template (2) (2) (2) (5) (2) (2) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 4) 0) perm5 u v =
      template (2) (2) (2) (5) (2) (2) u v from by decide) u v
  have hb : IsWeakFork (relabel (mutate (node 4) 0) perm5) 0 := by
    rw [he]
    exact IsWeakFork.basic (2) (2) (2) (5) (2) (2) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm5 hb

theorem edge4_1 : FramedCore node (mutate (node 4) 1) ∨
    IsWeakFork (mutate (node 4) 1) 1 ∨ IsRoot (mutate (node 4) 1) 1 := by
  right; right
  have he : relabel (reverse (mutate (node 4) 1)) perm7 = root (2) (2) (6) (2) (2) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 4) 1)) perm7 u v =
      root (2) (2) (6) (2) (2) (1) u v from by decide) u v
  have hb : IsRoot (relabel (reverse (mutate (node 4) 1)) perm7) 0 := by
    rw [he]
    exact IsRoot.basic (2) (2) (6) (2) (2) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact root_of_reverse (root_of_relabel perm7 hb)

theorem edge4_2 : FramedCore node (mutate (node 4) 2) ∨
    IsWeakFork (mutate (node 4) 2) 2 ∨ IsRoot (mutate (node 4) 2) 2 := by
  left; refine ⟨3, perm8, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 4) 2 u v =
    relabel (node 3) perm8 u v from by decide) u v

theorem edge4_3 : FramedCore node (mutate (node 4) 3) ∨
    IsWeakFork (mutate (node 4) 3) 3 ∨ IsRoot (mutate (node 4) 3) 3 := by
  left; refine ⟨2, perm12, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 4) 3 u v =
    relabel (node 2) perm12 u v from by decide) u v

theorem all_skew : ∀ i, SkewSymmetric (node i) := by
  intro i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases hi with rfl | rfl | rfl | rfl | rfl <;>
    exact ofSix_skew _ _ _ _ _ _

theorem all_cyclic : ∀ i, ¬ Acyclic (node i) := by
  intro i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases hi with rfl | rfl | rfl | rfl | rfl
  · exact cyclic0
  · exact cyclic1
  · exact cyclic2
  · exact cyclic3
  · exact cyclic4

theorem all_edges : ∀ i k, FramedCore node (mutate (node i) k) ∨
    IsWeakFork (mutate (node i) k) k ∨ IsRoot (mutate (node i) k) k := by
  intro i k
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hi with rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl
  · exact edge0_0
  · exact edge0_1
  · exact edge0_2
  · exact edge0_3
  · exact edge1_0
  · exact edge1_1
  · exact edge1_2
  · exact edge1_3
  · exact edge2_0
  · exact edge2_1
  · exact edge2_2
  · exact edge2_3
  · exact edge3_0
  · exact edge3_1
  · exact edge3_2
  · exact edge3_3
  · exact edge4_0
  · exact edge4_1
  · exact edge4_2
  · exact edge4_3

end Core01

/-- Unconditional all-word NMA for source certificate `q045`. -/
theorem nma_q045 : ¬ MutationAcyclic (ofSix (-2) (-2) (-1) (-2) (2) (-2)) :=
  framed_region_NMA WeakRegionCells.root_cells_exist Core01.node
    Core01.all_skew Core01.all_cyclic Core01.all_edges 3

/-- Unconditional all-word NMA for source certificate `q217`. -/
theorem nma_q217 : ¬ MutationAcyclic (ofSix (-2) (-2) (2) (-2) (-2) (1)) :=
  framed_region_NMA WeakRegionCells.root_cells_exist Core01.node
    Core01.all_skew Core01.all_cyclic Core01.all_edges 4

namespace Core02
def node (i : Fin 2) : Matrix 4 := match i.val with
  | 0 => (ofSix (-2) (-2) (0) (-2) (2) (-2))
  | _ => (ofSix (-2) (-2) (2) (-2) (-2) (0))

theorem cyclic0 : ¬ Acyclic (node 0) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 1 3 (by decide)
  have h1 := hr 3 2 (by decide)
  have h2 := hr 2 1 (by decide)
  omega

theorem edge0_0 : FramedCore node (mutate (node 0) 0) ∨
    IsWeakFork (mutate (node 0) 0) 0 ∨ IsRoot (mutate (node 0) 0) 0 := by
  left; refine ⟨1, perm12, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 0 u v =
    relabel (node 1) perm12 u v from by decide) u v

theorem edge0_1 : FramedCore node (mutate (node 0) 1) ∨
    IsWeakFork (mutate (node 0) 1) 1 ∨ IsRoot (mutate (node 0) 1) 1 := by
  right; right
  have he : relabel (mutate (node 0) 1) perm8 = root (2) (6) (2) (2) (2) (0) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 0) 1) perm8 u v =
      root (2) (6) (2) (2) (2) (0) u v from by decide) u v
  have hb : IsRoot (relabel (mutate (node 0) 1) perm8) 0 := by
    rw [he]
    exact IsRoot.basic (2) (6) (2) (2) (2) (0) (by unfold WeakRegions.Domain; decide) (by decide)
  exact root_of_relabel perm8 hb

theorem edge0_2 : FramedCore node (mutate (node 0) 2) ∨
    IsWeakFork (mutate (node 0) 2) 2 ∨ IsRoot (mutate (node 0) 2) 2 := by
  right; left
  have he : relabel (reverse (mutate (node 0) 2)) perm16 = template (2) (2) (2) (4) (2) (2) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 0) 2)) perm16 u v =
      template (2) (2) (2) (4) (2) (2) u v from by decide) u v
  have hb : IsWeakFork (relabel (reverse (mutate (node 0) 2)) perm16) 0 := by
    rw [he]
    exact IsWeakFork.basic (2) (2) (2) (4) (2) (2) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_reverse (WeakForks.fork_of_relabel perm16 hb)

theorem edge0_3 : FramedCore node (mutate (node 0) 3) ∨
    IsWeakFork (mutate (node 0) 3) 3 ∨ IsRoot (mutate (node 0) 3) 3 := by
  left; refine ⟨0, perm2, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 3 u v =
    relabel (node 0) perm2 u v from by decide) u v

theorem cyclic1 : ¬ Acyclic (node 1) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge1_0 : FramedCore node (mutate (node 1) 0) ∨
    IsWeakFork (mutate (node 1) 0) 0 ∨ IsRoot (mutate (node 1) 0) 0 := by
  right; left
  have he : relabel (mutate (node 1) 0) perm5 = template (2) (2) (2) (4) (2) (2) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 1) 0) perm5 u v =
      template (2) (2) (2) (4) (2) (2) u v from by decide) u v
  have hb : IsWeakFork (relabel (mutate (node 1) 0) perm5) 0 := by
    rw [he]
    exact IsWeakFork.basic (2) (2) (2) (4) (2) (2) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm5 hb

theorem edge1_1 : FramedCore node (mutate (node 1) 1) ∨
    IsWeakFork (mutate (node 1) 1) 1 ∨ IsRoot (mutate (node 1) 1) 1 := by
  right; right
  have he : relabel (reverse (mutate (node 1) 1)) perm6 = root (2) (6) (2) (2) (2) (0) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 1) 1)) perm6 u v =
      root (2) (6) (2) (2) (2) (0) u v from by decide) u v
  have hb : IsRoot (relabel (reverse (mutate (node 1) 1)) perm6) 0 := by
    rw [he]
    exact IsRoot.basic (2) (6) (2) (2) (2) (0) (by unfold WeakRegions.Domain; decide) (by decide)
  exact root_of_reverse (root_of_relabel perm6 hb)

theorem edge1_2 : FramedCore node (mutate (node 1) 2) ∨
    IsWeakFork (mutate (node 1) 2) 2 ∨ IsRoot (mutate (node 1) 2) 2 := by
  left; refine ⟨0, perm8, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 1) 2 u v =
    relabel (node 0) perm8 u v from by decide) u v

theorem edge1_3 : FramedCore node (mutate (node 1) 3) ∨
    IsWeakFork (mutate (node 1) 3) 3 ∨ IsRoot (mutate (node 1) 3) 3 := by
  left; refine ⟨1, perm6, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 1) 3 u v =
    relabel (node 1) perm6 u v from by decide) u v

theorem all_skew : ∀ i, SkewSymmetric (node i) := by
  intro i
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl <;>
    exact ofSix_skew _ _ _ _ _ _

theorem all_cyclic : ∀ i, ¬ Acyclic (node i) := by
  intro i
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  · exact cyclic0
  · exact cyclic1

theorem all_edges : ∀ i k, FramedCore node (mutate (node i) k) ∨
    IsWeakFork (mutate (node i) k) k ∨ IsRoot (mutate (node i) k) k := by
  intro i k
  have hi : i = 0 ∨ i = 1 := by omega
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hi with rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl
  · exact edge0_0
  · exact edge0_1
  · exact edge0_2
  · exact edge0_3
  · exact edge1_0
  · exact edge1_1
  · exact edge1_2
  · exact edge1_3

end Core02

/-- Unconditional all-word NMA for source certificate `q109`. -/
theorem nma_q109 : ¬ MutationAcyclic (ofSix (-2) (-2) (0) (-2) (2) (-2)) :=
  framed_region_NMA WeakRegionCells.root_cells_exist Core02.node
    Core02.all_skew Core02.all_cyclic Core02.all_edges 0

/-- Unconditional all-word NMA for source certificate `q216`. -/
theorem nma_q216 : ¬ MutationAcyclic (ofSix (-2) (-2) (2) (-2) (-2) (0)) :=
  framed_region_NMA WeakRegionCells.root_cells_exist Core02.node
    Core02.all_skew Core02.all_cyclic Core02.all_edges 1

namespace Core03
def node (i : Fin 1) : Matrix 4 := match i.val with
  | _ => (ofSix (-2) (-2) (2) (-2) (-2) (-2))

theorem cyclic0 : ¬ Acyclic (node 0) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge0_0 : FramedCore node (mutate (node 0) 0) ∨
    IsWeakFork (mutate (node 0) 0) 0 ∨ IsRoot (mutate (node 0) 0) 0 := by
  left; refine ⟨0, perm21, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 0 u v =
    relabel (node 0) perm21 u v from by decide) u v

theorem edge0_1 : FramedCore node (mutate (node 0) 1) ∨
    IsWeakFork (mutate (node 0) 1) 1 ∨ IsRoot (mutate (node 0) 1) 1 := by
  right; left
  have he : relabel (mutate (node 0) 1) perm7 = template (2) (2) (2) (2) (6) (2) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 0) 1) perm7 u v =
      template (2) (2) (2) (2) (6) (2) u v from by decide) u v
  have hb : IsWeakFork (relabel (mutate (node 0) 1) perm7) 0 := by
    rw [he]
    exact IsWeakFork.basic (2) (2) (2) (2) (6) (2) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm7 hb

theorem edge0_2 : FramedCore node (mutate (node 0) 2) ∨
    IsWeakFork (mutate (node 0) 2) 2 ∨ IsRoot (mutate (node 0) 2) 2 := by
  right; left
  have he : relabel (reverse (mutate (node 0) 2)) perm16 = template (2) (2) (2) (2) (6) (2) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 0) 2)) perm16 u v =
      template (2) (2) (2) (2) (6) (2) u v from by decide) u v
  have hb : IsWeakFork (relabel (reverse (mutate (node 0) 2)) perm16) 0 := by
    rw [he]
    exact IsWeakFork.basic (2) (2) (2) (2) (6) (2) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_reverse (WeakForks.fork_of_relabel perm16 hb)

theorem edge0_3 : FramedCore node (mutate (node 0) 3) ∨
    IsWeakFork (mutate (node 0) 3) 3 ∨ IsRoot (mutate (node 0) 3) 3 := by
  left; refine ⟨0, perm21, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 3 u v =
    relabel (node 0) perm21 u v from by decide) u v

theorem all_skew : ∀ i, SkewSymmetric (node i) := by
  intro i
  have hi : i = 0 := by omega
  rcases hi with rfl <;>
    exact ofSix_skew _ _ _ _ _ _

theorem all_cyclic : ∀ i, ¬ Acyclic (node i) := by
  intro i
  have hi : i = 0 := by omega
  rcases hi with rfl
  · exact cyclic0

theorem all_edges : ∀ i k, FramedCore node (mutate (node i) k) ∨
    IsWeakFork (mutate (node i) k) k ∨ IsRoot (mutate (node i) k) k := by
  intro i k
  have hi : i = 0 := by omega
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hi with rfl <;>
    rcases hk with rfl | rfl | rfl | rfl
  · exact edge0_0
  · exact edge0_1
  · exact edge0_2
  · exact edge0_3

end Core03

/-- Unconditional all-word NMA for source certificate `q214`. -/
theorem nma_q214 : ¬ MutationAcyclic (ofSix (-2) (-2) (2) (-2) (-2) (-2)) :=
  framed_region_NMA WeakRegionCells.root_cells_exist Core03.node
    Core03.all_skew Core03.all_cyclic Core03.all_edges 0

namespace Core04
def node (i : Fin 3) : Matrix 4 := match i.val with
  | 0 => (ofSix (-6) (2) (2) (-2) (-2) (0))
  | 1 => (ofSix (-2) (-2) (2) (-2) (0) (-2))
  | _ => (ofSix (-2) (-2) (2) (0) (-2) (-2))

theorem cyclic0 : ¬ Acyclic (node 0) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 2 (by decide)
  have h1 := hr 2 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge0_0 : FramedCore node (mutate (node 0) 0) ∨
    IsWeakFork (mutate (node 0) 0) 0 ∨ IsRoot (mutate (node 0) 0) 0 := by
  right; right
  have he : relabel (mutate (node 0) 0) perm0 = root (6) (10) (10) (2) (2) (0) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 0) 0) perm0 u v =
      root (6) (10) (10) (2) (2) (0) u v from by decide) u v
  have hb : IsRoot (relabel (mutate (node 0) 0) perm0) 0 := by
    rw [he]
    exact IsRoot.basic (6) (10) (10) (2) (2) (0) (by unfold WeakRegions.Domain; decide) (by decide)
  exact root_of_relabel perm0 hb

theorem edge0_1 : FramedCore node (mutate (node 0) 1) ∨
    IsWeakFork (mutate (node 0) 1) 1 ∨ IsRoot (mutate (node 0) 1) 1 := by
  right; right
  have he : relabel (reverse (mutate (node 0) 1)) perm6 = root (6) (10) (10) (2) (2) (0) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 0) 1)) perm6 u v =
      root (6) (10) (10) (2) (2) (0) u v from by decide) u v
  have hb : IsRoot (relabel (reverse (mutate (node 0) 1)) perm6) 0 := by
    rw [he]
    exact IsRoot.basic (6) (10) (10) (2) (2) (0) (by unfold WeakRegions.Domain; decide) (by decide)
  exact root_of_reverse (root_of_relabel perm6 hb)

theorem edge0_2 : FramedCore node (mutate (node 0) 2) ∨
    IsWeakFork (mutate (node 0) 2) 2 ∨ IsRoot (mutate (node 0) 2) 2 := by
  left; refine ⟨1, perm2, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 2 u v =
    relabel (node 1) perm2 u v from by decide) u v

theorem edge0_3 : FramedCore node (mutate (node 0) 3) ∨
    IsWeakFork (mutate (node 0) 3) 3 ∨ IsRoot (mutate (node 0) 3) 3 := by
  left; refine ⟨1, perm3, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 3 u v =
    relabel (node 1) perm3 u v from by decide) u v

theorem cyclic1 : ¬ Acyclic (node 1) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 2 (by decide)
  have h2 := hr 2 0 (by decide)
  omega

theorem edge1_0 : FramedCore node (mutate (node 1) 0) ∨
    IsWeakFork (mutate (node 1) 0) 0 ∨ IsRoot (mutate (node 1) 0) 0 := by
  right; left
  have he : relabel (mutate (node 1) 0) perm5 = template (2) (2) (2) (2) (4) (2) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 1) 0) perm5 u v =
      template (2) (2) (2) (2) (4) (2) u v from by decide) u v
  have hb : IsWeakFork (relabel (mutate (node 1) 0) perm5) 0 := by
    rw [he]
    exact IsWeakFork.basic (2) (2) (2) (2) (4) (2) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm5 hb

theorem edge1_1 : FramedCore node (mutate (node 1) 1) ∨
    IsWeakFork (mutate (node 1) 1) 1 ∨ IsRoot (mutate (node 1) 1) 1 := by
  left; refine ⟨0, perm2, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 1) 1 u v =
    relabel (node 0) perm2 u v from by decide) u v

theorem edge1_2 : FramedCore node (mutate (node 1) 2) ∨
    IsWeakFork (mutate (node 1) 2) 2 ∨ IsRoot (mutate (node 1) 2) 2 := by
  right; left
  have he : relabel (reverse (mutate (node 1) 2)) perm16 = template (2) (2) (2) (2) (4) (2) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 1) 2)) perm16 u v =
      template (2) (2) (2) (2) (4) (2) u v from by decide) u v
  have hb : IsWeakFork (relabel (reverse (mutate (node 1) 2)) perm16) 0 := by
    rw [he]
    exact IsWeakFork.basic (2) (2) (2) (2) (4) (2) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_reverse (WeakForks.fork_of_relabel perm16 hb)

theorem edge1_3 : FramedCore node (mutate (node 1) 3) ∨
    IsWeakFork (mutate (node 1) 3) 3 ∨ IsRoot (mutate (node 1) 3) 3 := by
  left; refine ⟨2, perm1, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 1) 3 u v =
    relabel (node 2) perm1 u v from by decide) u v

theorem cyclic2 : ¬ Acyclic (node 2) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge2_0 : FramedCore node (mutate (node 2) 0) ∨
    IsWeakFork (mutate (node 2) 0) 0 ∨ IsRoot (mutate (node 2) 0) 0 := by
  left; refine ⟨2, perm21, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 2) 0 u v =
    relabel (node 2) perm21 u v from by decide) u v

theorem edge2_1 : FramedCore node (mutate (node 2) 1) ∨
    IsWeakFork (mutate (node 2) 1) 1 ∨ IsRoot (mutate (node 2) 1) 1 := by
  left; refine ⟨1, perm4, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 2) 1 u v =
    relabel (node 1) perm4 u v from by decide) u v

theorem edge2_2 : FramedCore node (mutate (node 2) 2) ∨
    IsWeakFork (mutate (node 2) 2) 2 ∨ IsRoot (mutate (node 2) 2) 2 := by
  left; refine ⟨1, perm1, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 2) 2 u v =
    relabel (node 1) perm1 u v from by decide) u v

theorem edge2_3 : FramedCore node (mutate (node 2) 3) ∨
    IsWeakFork (mutate (node 2) 3) 3 ∨ IsRoot (mutate (node 2) 3) 3 := by
  left; refine ⟨2, perm21, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 2) 3 u v =
    relabel (node 2) perm21 u v from by decide) u v

theorem all_skew : ∀ i, SkewSymmetric (node i) := by
  intro i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl <;>
    exact ofSix_skew _ _ _ _ _ _

theorem all_cyclic : ∀ i, ¬ Acyclic (node i) := by
  intro i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl
  · exact cyclic0
  · exact cyclic1
  · exact cyclic2

theorem all_edges : ∀ i k, FramedCore node (mutate (node i) k) ∨
    IsWeakFork (mutate (node i) k) k ∨ IsRoot (mutate (node i) k) k := by
  intro i k
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hi with rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl
  · exact edge0_0
  · exact edge0_1
  · exact edge0_2
  · exact edge0_3
  · exact edge1_0
  · exact edge1_1
  · exact edge1_2
  · exact edge1_3
  · exact edge2_0
  · exact edge2_1
  · exact edge2_2
  · exact edge2_3

end Core04

/-- Unconditional all-word NMA for source certificate `q223`. -/
theorem nma_q223 : ¬ MutationAcyclic (ofSix (-2) (-2) (2) (-2) (0) (-2)) :=
  framed_region_NMA WeakRegionCells.root_cells_exist Core04.node
    Core04.all_skew Core04.all_cyclic Core04.all_edges 1

/-- Unconditional all-word NMA for source certificate `q247`. -/
theorem nma_q247 : ¬ MutationAcyclic (ofSix (-2) (-2) (2) (0) (-2) (-2)) :=
  framed_region_NMA WeakRegionCells.root_cells_exist Core04.node
    Core04.all_skew Core04.all_cyclic Core04.all_edges 2

namespace Core05
def node (i : Fin 5) : Matrix 4 := match i.val with
  | 0 => (ofSix (-10) (-2) (4) (-2) (-2) (-1))
  | 1 => (ofSix (-10) (2) (2) (-4) (2) (-1))
  | 2 => (ofSix (-4) (-2) (2) (-2) (-1) (-2))
  | 3 => (ofSix (-4) (1) (2) (-2) (2) (-2))
  | _ => (ofSix (-2) (-2) (2) (-1) (-2) (-2))

theorem cyclic0 : ¬ Acyclic (node 0) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge0_0 : FramedCore node (mutate (node 0) 0) ∨
    IsWeakFork (mutate (node 0) 0) 0 ∨ IsRoot (mutate (node 0) 0) 0 := by
  right; left
  have he : relabel (mutate (node 0) 0) perm5 = template (4) (2) (10) (7) (38) (2) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 0) 0) perm5 u v =
      template (4) (2) (10) (7) (38) (2) u v from by decide) u v
  have hb : IsWeakFork (relabel (mutate (node 0) 0) perm5) 0 := by
    rw [he]
    exact IsWeakFork.basic (4) (2) (10) (7) (38) (2) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm5 hb

theorem edge0_1 : FramedCore node (mutate (node 0) 1) ∨
    IsWeakFork (mutate (node 0) 1) 1 ∨ IsRoot (mutate (node 0) 1) 1 := by
  right; right
  have he : relabel (reverse (mutate (node 0) 1)) perm6 = root (10) (22) (16) (2) (2) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 0) 1)) perm6 u v =
      root (10) (22) (16) (2) (2) (1) u v from by decide) u v
  have hb : IsRoot (relabel (reverse (mutate (node 0) 1)) perm6) 0 := by
    rw [he]
    exact IsRoot.basic (10) (22) (16) (2) (2) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact root_of_reverse (root_of_relabel perm6 hb)

theorem edge0_2 : FramedCore node (mutate (node 0) 2) ∨
    IsWeakFork (mutate (node 0) 2) 2 ∨ IsRoot (mutate (node 0) 2) 2 := by
  left; refine ⟨1, perm1, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 2 u v =
    relabel (node 1) perm1 u v from by decide) u v

theorem edge0_3 : FramedCore node (mutate (node 0) 3) ∨
    IsWeakFork (mutate (node 0) 3) 3 ∨ IsRoot (mutate (node 0) 3) 3 := by
  left; refine ⟨2, perm3, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 3 u v =
    relabel (node 2) perm3 u v from by decide) u v

theorem cyclic1 : ¬ Acyclic (node 1) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 2 (by decide)
  have h1 := hr 2 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge1_0 : FramedCore node (mutate (node 1) 0) ∨
    IsWeakFork (mutate (node 1) 0) 0 ∨ IsRoot (mutate (node 1) 0) 0 := by
  right; right
  have he : relabel (mutate (node 1) 0) perm1 = root (10) (22) (16) (2) (2) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 1) 0) perm1 u v =
      root (10) (22) (16) (2) (2) (1) u v from by decide) u v
  have hb : IsRoot (relabel (mutate (node 1) 0) perm1) 0 := by
    rw [he]
    exact IsRoot.basic (10) (22) (16) (2) (2) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact root_of_relabel perm1 hb

theorem edge1_1 : FramedCore node (mutate (node 1) 1) ∨
    IsWeakFork (mutate (node 1) 1) 1 ∨ IsRoot (mutate (node 1) 1) 1 := by
  right; left
  have he : relabel (reverse (mutate (node 1) 1)) perm9 = template (4) (2) (10) (7) (38) (2) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 1) 1)) perm9 u v =
      template (4) (2) (10) (7) (38) (2) u v from by decide) u v
  have hb : IsWeakFork (relabel (reverse (mutate (node 1) 1)) perm9) 0 := by
    rw [he]
    exact IsWeakFork.basic (4) (2) (10) (7) (38) (2) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_reverse (WeakForks.fork_of_relabel perm9 hb)

theorem edge1_2 : FramedCore node (mutate (node 1) 2) ∨
    IsWeakFork (mutate (node 1) 2) 2 ∨ IsRoot (mutate (node 1) 2) 2 := by
  left; refine ⟨3, perm20, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 1) 2 u v =
    relabel (node 3) perm20 u v from by decide) u v

theorem edge1_3 : FramedCore node (mutate (node 1) 3) ∨
    IsWeakFork (mutate (node 1) 3) 3 ∨ IsRoot (mutate (node 1) 3) 3 := by
  left; refine ⟨0, perm1, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 1) 3 u v =
    relabel (node 0) perm1 u v from by decide) u v

theorem cyclic2 : ¬ Acyclic (node 2) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge2_0 : FramedCore node (mutate (node 2) 0) ∨
    IsWeakFork (mutate (node 2) 0) 0 ∨ IsRoot (mutate (node 2) 0) 0 := by
  right; left
  have he : relabel (mutate (node 2) 0) perm5 = template (2) (2) (4) (2) (7) (2) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 2) 0) perm5 u v =
      template (2) (2) (4) (2) (7) (2) u v from by decide) u v
  have hb : IsWeakFork (relabel (mutate (node 2) 0) perm5) 0 := by
    rw [he]
    exact IsWeakFork.basic (2) (2) (4) (2) (7) (2) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm5 hb

theorem edge2_1 : FramedCore node (mutate (node 2) 1) ∨
    IsWeakFork (mutate (node 2) 1) 1 ∨ IsRoot (mutate (node 2) 1) 1 := by
  left; refine ⟨0, perm4, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 2) 1 u v =
    relabel (node 0) perm4 u v from by decide) u v

theorem edge2_2 : FramedCore node (mutate (node 2) 2) ∨
    IsWeakFork (mutate (node 2) 2) 2 ∨ IsRoot (mutate (node 2) 2) 2 := by
  right; left
  have he : relabel (reverse (mutate (node 2) 2)) perm16 = template (2) (2) (2) (2) (5) (4) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 2) 2)) perm16 u v =
      template (2) (2) (2) (2) (5) (4) u v from by decide) u v
  have hb : IsWeakFork (relabel (reverse (mutate (node 2) 2)) perm16) 0 := by
    rw [he]
    exact IsWeakFork.basic (2) (2) (2) (2) (5) (4) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_reverse (WeakForks.fork_of_relabel perm16 hb)

theorem edge2_3 : FramedCore node (mutate (node 2) 3) ∨
    IsWeakFork (mutate (node 2) 3) 3 ∨ IsRoot (mutate (node 2) 3) 3 := by
  left; refine ⟨4, perm3, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 2) 3 u v =
    relabel (node 4) perm3 u v from by decide) u v

theorem cyclic3 : ¬ Acyclic (node 3) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 2 (by decide)
  have h1 := hr 2 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge3_0 : FramedCore node (mutate (node 3) 0) ∨
    IsWeakFork (mutate (node 3) 0) 0 ∨ IsRoot (mutate (node 3) 0) 0 := by
  left; refine ⟨1, perm15, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 3) 0 u v =
    relabel (node 1) perm15 u v from by decide) u v

theorem edge3_1 : FramedCore node (mutate (node 3) 1) ∨
    IsWeakFork (mutate (node 3) 1) 1 ∨ IsRoot (mutate (node 3) 1) 1 := by
  right; left
  have he : relabel (reverse (mutate (node 3) 1)) perm9 = template (2) (2) (4) (2) (7) (2) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 3) 1)) perm9 u v =
      template (2) (2) (4) (2) (7) (2) u v from by decide) u v
  have hb : IsWeakFork (relabel (reverse (mutate (node 3) 1)) perm9) 0 := by
    rw [he]
    exact IsWeakFork.basic (2) (2) (4) (2) (7) (2) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_reverse (WeakForks.fork_of_relabel perm9 hb)

theorem edge3_2 : FramedCore node (mutate (node 3) 2) ∨
    IsWeakFork (mutate (node 3) 2) 2 ∨ IsRoot (mutate (node 3) 2) 2 := by
  left; refine ⟨4, perm11, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 3) 2 u v =
    relabel (node 4) perm11 u v from by decide) u v

theorem edge3_3 : FramedCore node (mutate (node 3) 3) ∨
    IsWeakFork (mutate (node 3) 3) 3 ∨ IsRoot (mutate (node 3) 3) 3 := by
  right; left
  have he : relabel (mutate (node 3) 3) perm23 = template (2) (2) (2) (2) (5) (4) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 3) 3) perm23 u v =
      template (2) (2) (2) (2) (5) (4) u v from by decide) u v
  have hb : IsWeakFork (relabel (mutate (node 3) 3) perm23) 0 := by
    rw [he]
    exact IsWeakFork.basic (2) (2) (2) (2) (5) (4) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm23 hb

theorem cyclic4 : ¬ Acyclic (node 4) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge4_0 : FramedCore node (mutate (node 4) 0) ∨
    IsWeakFork (mutate (node 4) 0) 0 ∨ IsRoot (mutate (node 4) 0) 0 := by
  left; refine ⟨4, perm21, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 4) 0 u v =
    relabel (node 4) perm21 u v from by decide) u v

theorem edge4_1 : FramedCore node (mutate (node 4) 1) ∨
    IsWeakFork (mutate (node 4) 1) 1 ∨ IsRoot (mutate (node 4) 1) 1 := by
  left; refine ⟨2, perm4, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 4) 1 u v =
    relabel (node 2) perm4 u v from by decide) u v

theorem edge4_2 : FramedCore node (mutate (node 4) 2) ∨
    IsWeakFork (mutate (node 4) 2) 2 ∨ IsRoot (mutate (node 4) 2) 2 := by
  left; refine ⟨3, perm19, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 4) 2 u v =
    relabel (node 3) perm19 u v from by decide) u v

theorem edge4_3 : FramedCore node (mutate (node 4) 3) ∨
    IsWeakFork (mutate (node 4) 3) 3 ∨ IsRoot (mutate (node 4) 3) 3 := by
  left; refine ⟨4, perm21, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 4) 3 u v =
    relabel (node 4) perm21 u v from by decide) u v

theorem all_skew : ∀ i, SkewSymmetric (node i) := by
  intro i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases hi with rfl | rfl | rfl | rfl | rfl <;>
    exact ofSix_skew _ _ _ _ _ _

theorem all_cyclic : ∀ i, ¬ Acyclic (node i) := by
  intro i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases hi with rfl | rfl | rfl | rfl | rfl
  · exact cyclic0
  · exact cyclic1
  · exact cyclic2
  · exact cyclic3
  · exact cyclic4

theorem all_edges : ∀ i k, FramedCore node (mutate (node i) k) ∨
    IsWeakFork (mutate (node i) k) k ∨ IsRoot (mutate (node i) k) k := by
  intro i k
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hi with rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl
  · exact edge0_0
  · exact edge0_1
  · exact edge0_2
  · exact edge0_3
  · exact edge1_0
  · exact edge1_1
  · exact edge1_2
  · exact edge1_3
  · exact edge2_0
  · exact edge2_1
  · exact edge2_2
  · exact edge2_3
  · exact edge3_0
  · exact edge3_1
  · exact edge3_2
  · exact edge3_3
  · exact edge4_0
  · exact edge4_1
  · exact edge4_2
  · exact edge4_3

end Core05

/-- Unconditional all-word NMA for source certificate `q231`. -/
theorem nma_q231 : ¬ MutationAcyclic (ofSix (-2) (-2) (2) (-1) (-2) (-2)) :=
  framed_region_NMA WeakRegionCells.root_cells_exist Core05.node
    Core05.all_skew Core05.all_cyclic Core05.all_edges 4

namespace Core06
def node (i : Fin 4) : Matrix 4 := match i.val with
  | 0 => (ofSix (-4) (1) (1) (-2) (-2) (-1))
  | 1 => (ofSix (-4) (2) (2) (-1) (-1) (-1))
  | 2 => (ofSix (-2) (-2) (2) (-1) (1) (-2))
  | _ => (ofSix (-2) (-1) (1) (-2) (2) (-2))

theorem cyclic0 : ¬ Acyclic (node 0) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 2 (by decide)
  have h1 := hr 2 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge0_0 : FramedCore node (mutate (node 0) 0) ∨
    IsWeakFork (mutate (node 0) 0) 0 ∨ IsRoot (mutate (node 0) 0) 0 := by
  left; refine ⟨1, perm6, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 0 u v =
    relabel (node 1) perm6 u v from by decide) u v

theorem edge0_1 : FramedCore node (mutate (node 0) 1) ∨
    IsWeakFork (mutate (node 0) 1) 1 ∨ IsRoot (mutate (node 0) 1) 1 := by
  right; right
  have he : relabel (reverse (mutate (node 0) 1)) perm6 = root (4) (7) (7) (2) (2) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 0) 1)) perm6 u v =
      root (4) (7) (7) (2) (2) (1) u v from by decide) u v
  have hb : IsRoot (relabel (reverse (mutate (node 0) 1)) perm6) 0 := by
    rw [he]
    exact IsRoot.basic (4) (7) (7) (2) (2) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact root_of_reverse (root_of_relabel perm6 hb)

theorem edge0_2 : FramedCore node (mutate (node 0) 2) ∨
    IsWeakFork (mutate (node 0) 2) 2 ∨ IsRoot (mutate (node 0) 2) 2 := by
  left; refine ⟨1, perm13, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 2 u v =
    relabel (node 1) perm13 u v from by decide) u v

theorem edge0_3 : FramedCore node (mutate (node 0) 3) ∨
    IsWeakFork (mutate (node 0) 3) 3 ∨ IsRoot (mutate (node 0) 3) 3 := by
  left; refine ⟨3, perm21, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 3 u v =
    relabel (node 3) perm21 u v from by decide) u v

theorem cyclic1 : ¬ Acyclic (node 1) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 2 (by decide)
  have h1 := hr 2 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge1_0 : FramedCore node (mutate (node 1) 0) ∨
    IsWeakFork (mutate (node 1) 0) 0 ∨ IsRoot (mutate (node 1) 0) 0 := by
  right; right
  have he : relabel (mutate (node 1) 0) perm1 = root (4) (7) (7) (2) (2) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 1) 0) perm1 u v =
      root (4) (7) (7) (2) (2) (1) u v from by decide) u v
  have hb : IsRoot (relabel (mutate (node 1) 0) perm1) 0 := by
    rw [he]
    exact IsRoot.basic (4) (7) (7) (2) (2) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact root_of_relabel perm1 hb

theorem edge1_1 : FramedCore node (mutate (node 1) 1) ∨
    IsWeakFork (mutate (node 1) 1) 1 ∨ IsRoot (mutate (node 1) 1) 1 := by
  left; refine ⟨0, perm6, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 1) 1 u v =
    relabel (node 0) perm6 u v from by decide) u v

theorem edge1_2 : FramedCore node (mutate (node 1) 2) ∨
    IsWeakFork (mutate (node 1) 2) 2 ∨ IsRoot (mutate (node 1) 2) 2 := by
  left; refine ⟨2, perm2, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 1) 2 u v =
    relabel (node 2) perm2 u v from by decide) u v

theorem edge1_3 : FramedCore node (mutate (node 1) 3) ∨
    IsWeakFork (mutate (node 1) 3) 3 ∨ IsRoot (mutate (node 1) 3) 3 := by
  left; refine ⟨0, perm10, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 1) 3 u v =
    relabel (node 0) perm10 u v from by decide) u v

theorem cyclic2 : ¬ Acyclic (node 2) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 2 (by decide)
  have h2 := hr 2 0 (by decide)
  omega

theorem edge2_0 : FramedCore node (mutate (node 2) 0) ∨
    IsWeakFork (mutate (node 2) 0) 0 ∨ IsRoot (mutate (node 2) 0) 0 := by
  right; right
  have he : relabel (reverse (mutate (node 2) 0)) perm4 = root (2) (5) (2) (2) (2) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 2) 0)) perm4 u v =
      root (2) (5) (2) (2) (2) (1) u v from by decide) u v
  have hb : IsRoot (relabel (reverse (mutate (node 2) 0)) perm4) 0 := by
    rw [he]
    exact IsRoot.basic (2) (5) (2) (2) (2) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact root_of_reverse (root_of_relabel perm4 hb)

theorem edge2_1 : FramedCore node (mutate (node 2) 1) ∨
    IsWeakFork (mutate (node 2) 1) 1 ∨ IsRoot (mutate (node 2) 1) 1 := by
  left; refine ⟨1, perm2, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 2) 1 u v =
    relabel (node 1) perm2 u v from by decide) u v

theorem edge2_2 : FramedCore node (mutate (node 2) 2) ∨
    IsWeakFork (mutate (node 2) 2) 2 ∨ IsRoot (mutate (node 2) 2) 2 := by
  left; refine ⟨2, perm1, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 2) 2 u v =
    relabel (node 2) perm1 u v from by decide) u v

theorem edge2_3 : FramedCore node (mutate (node 2) 3) ∨
    IsWeakFork (mutate (node 2) 3) 3 ∨ IsRoot (mutate (node 2) 3) 3 := by
  left; refine ⟨2, perm1, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 2) 3 u v =
    relabel (node 2) perm1 u v from by decide) u v

theorem cyclic3 : ¬ Acyclic (node 3) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 2 (by decide)
  have h2 := hr 2 0 (by decide)
  omega

theorem edge3_0 : FramedCore node (mutate (node 3) 0) ∨
    IsWeakFork (mutate (node 3) 0) 0 ∨ IsRoot (mutate (node 3) 0) 0 := by
  left; refine ⟨0, perm21, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 3) 0 u v =
    relabel (node 0) perm21 u v from by decide) u v

theorem edge3_1 : FramedCore node (mutate (node 3) 1) ∨
    IsWeakFork (mutate (node 3) 1) 1 ∨ IsRoot (mutate (node 3) 1) 1 := by
  right; right
  have he : relabel (mutate (node 3) 1) perm8 = root (2) (5) (2) (2) (2) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 3) 1) perm8 u v =
      root (2) (5) (2) (2) (2) (1) u v from by decide) u v
  have hb : IsRoot (relabel (mutate (node 3) 1) perm8) 0 := by
    rw [he]
    exact IsRoot.basic (2) (5) (2) (2) (2) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact root_of_relabel perm8 hb

theorem edge3_2 : FramedCore node (mutate (node 3) 2) ∨
    IsWeakFork (mutate (node 3) 2) 2 ∨ IsRoot (mutate (node 3) 2) 2 := by
  left; refine ⟨3, perm1, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 3) 2 u v =
    relabel (node 3) perm1 u v from by decide) u v

theorem edge3_3 : FramedCore node (mutate (node 3) 3) ∨
    IsWeakFork (mutate (node 3) 3) 3 ∨ IsRoot (mutate (node 3) 3) 3 := by
  left; refine ⟨3, perm1, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 3) 3 u v =
    relabel (node 3) perm1 u v from by decide) u v

theorem all_skew : ∀ i, SkewSymmetric (node i) := by
  intro i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases hi with rfl | rfl | rfl | rfl <;>
    exact ofSix_skew _ _ _ _ _ _

theorem all_cyclic : ∀ i, ¬ Acyclic (node i) := by
  intro i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases hi with rfl | rfl | rfl | rfl
  · exact cyclic0
  · exact cyclic1
  · exact cyclic2
  · exact cyclic3

theorem all_edges : ∀ i k, FramedCore node (mutate (node i) k) ∨
    IsWeakFork (mutate (node i) k) k ∨ IsRoot (mutate (node i) k) k := by
  intro i k
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hi with rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl
  · exact edge0_0
  · exact edge0_1
  · exact edge0_2
  · exact edge0_3
  · exact edge1_0
  · exact edge1_1
  · exact edge1_2
  · exact edge1_3
  · exact edge2_0
  · exact edge2_1
  · exact edge2_2
  · exact edge2_3
  · exact edge3_0
  · exact edge3_1
  · exact edge3_2
  · exact edge3_3

end Core06

/-- Unconditional all-word NMA for source certificate `q243`. -/
theorem nma_q243 : ¬ MutationAcyclic (ofSix (-2) (-2) (2) (-1) (1) (-2)) :=
  framed_region_NMA WeakRegionCells.root_cells_exist Core06.node
    Core06.all_skew Core06.all_cyclic Core06.all_edges 2

/-- Unconditional all-word NMA for source certificate `q430`. -/
theorem nma_q430 : ¬ MutationAcyclic (ofSix (-2) (-1) (1) (-2) (2) (-2)) :=
  framed_region_NMA WeakRegionCells.root_cells_exist Core06.node
    Core06.all_skew Core06.all_cyclic Core06.all_edges 3

namespace Core07
def node (i : Fin 2) : Matrix 4 := match i.val with
  | 0 => (ofSix (-2) (-2) (2) (0) (-2) (0))
  | _ => (ofSix (-2) (0) (0) (-2) (2) (-2))

theorem cyclic0 : ¬ Acyclic (node 0) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge0_0 : FramedCore node (mutate (node 0) 0) ∨
    IsWeakFork (mutate (node 0) 0) 0 ∨ IsRoot (mutate (node 0) 0) 0 := by
  right; right
  have he : relabel (reverse (mutate (node 0) 0)) perm4 = root (2) (2) (4) (2) (2) (0) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 0) 0)) perm4 u v =
      root (2) (2) (4) (2) (2) (0) u v from by decide) u v
  have hb : IsRoot (relabel (reverse (mutate (node 0) 0)) perm4) 0 := by
    rw [he]
    exact IsRoot.basic (2) (2) (4) (2) (2) (0) (by unfold WeakRegions.Domain; decide) (by decide)
  exact root_of_reverse (root_of_relabel perm4 hb)

theorem edge0_1 : FramedCore node (mutate (node 0) 1) ∨
    IsWeakFork (mutate (node 0) 1) 1 ∨ IsRoot (mutate (node 0) 1) 1 := by
  left; refine ⟨0, perm5, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 1 u v =
    relabel (node 0) perm5 u v from by decide) u v

theorem edge0_2 : FramedCore node (mutate (node 0) 2) ∨
    IsWeakFork (mutate (node 0) 2) 2 ∨ IsRoot (mutate (node 0) 2) 2 := by
  left; refine ⟨1, perm8, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 2 u v =
    relabel (node 1) perm8 u v from by decide) u v

theorem edge0_3 : FramedCore node (mutate (node 0) 3) ∨
    IsWeakFork (mutate (node 0) 3) 3 ∨ IsRoot (mutate (node 0) 3) 3 := by
  left; refine ⟨0, perm5, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 3 u v =
    relabel (node 0) perm5 u v from by decide) u v

theorem cyclic1 : ¬ Acyclic (node 1) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 1 3 (by decide)
  have h1 := hr 3 2 (by decide)
  have h2 := hr 2 1 (by decide)
  omega

theorem edge1_0 : FramedCore node (mutate (node 1) 0) ∨
    IsWeakFork (mutate (node 1) 0) 0 ∨ IsRoot (mutate (node 1) 0) 0 := by
  left; refine ⟨0, perm12, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 1) 0 u v =
    relabel (node 0) perm12 u v from by decide) u v

theorem edge1_1 : FramedCore node (mutate (node 1) 1) ∨
    IsWeakFork (mutate (node 1) 1) 1 ∨ IsRoot (mutate (node 1) 1) 1 := by
  right; right
  have he : relabel (mutate (node 1) 1) perm8 = root (2) (4) (2) (2) (2) (0) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 1) 1) perm8 u v =
      root (2) (4) (2) (2) (2) (0) u v from by decide) u v
  have hb : IsRoot (relabel (mutate (node 1) 1) perm8) 0 := by
    rw [he]
    exact IsRoot.basic (2) (4) (2) (2) (2) (0) (by unfold WeakRegions.Domain; decide) (by decide)
  exact root_of_relabel perm8 hb

theorem edge1_2 : FramedCore node (mutate (node 1) 2) ∨
    IsWeakFork (mutate (node 1) 2) 2 ∨ IsRoot (mutate (node 1) 2) 2 := by
  left; refine ⟨1, perm1, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 1) 2 u v =
    relabel (node 1) perm1 u v from by decide) u v

theorem edge1_3 : FramedCore node (mutate (node 1) 3) ∨
    IsWeakFork (mutate (node 1) 3) 3 ∨ IsRoot (mutate (node 1) 3) 3 := by
  left; refine ⟨1, perm1, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 1) 3 u v =
    relabel (node 1) perm1 u v from by decide) u v

theorem all_skew : ∀ i, SkewSymmetric (node i) := by
  intro i
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl <;>
    exact ofSix_skew _ _ _ _ _ _

theorem all_cyclic : ∀ i, ¬ Acyclic (node i) := by
  intro i
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  · exact cyclic0
  · exact cyclic1

theorem all_edges : ∀ i k, FramedCore node (mutate (node i) k) ∨
    IsWeakFork (mutate (node i) k) k ∨ IsRoot (mutate (node i) k) k := by
  intro i k
  have hi : i = 0 ∨ i = 1 := by omega
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hi with rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl
  · exact edge0_0
  · exact edge0_1
  · exact edge0_2
  · exact edge0_3
  · exact edge1_0
  · exact edge1_1
  · exact edge1_2
  · exact edge1_3

end Core07

/-- Unconditional all-word NMA for source certificate `q249`. -/
theorem nma_q249 : ¬ MutationAcyclic (ofSix (-2) (-2) (2) (0) (-2) (0)) :=
  framed_region_NMA WeakRegionCells.root_cells_exist Core07.node
    Core07.all_skew Core07.all_cyclic Core07.all_edges 0

/-- Unconditional all-word NMA for source certificate `q540`. -/
theorem nma_q540 : ¬ MutationAcyclic (ofSix (-2) (0) (0) (-2) (2) (-2)) :=
  framed_region_NMA WeakRegionCells.root_cells_exist Core07.node
    Core07.all_skew Core07.all_cyclic Core07.all_edges 1

end QuiverProofs.NegativeContinuation
