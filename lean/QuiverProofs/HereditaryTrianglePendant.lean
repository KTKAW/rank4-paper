import QuiverProofs.WeakRegionCells
import QuiverProofs.UnitZeroStrip
import QuiverProofs.ForkCertificates

/-! Unconditional NMA for the unit-pendant Markov boundary. The finite core
is joined to a previously proved unbounded unit-zero strip. All mutation words
are covered; no hereditary-MA or structural-existence hypothesis is used. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace QuiverProofs.HereditaryTrianglePendant
open ForkCertificates

def node (i : Fin 8) : Matrix 4 := match i.val with
  | 0 => (ofSix (-6) (-2) (4) (0) (-2) (-1))
  | 1 => (ofSix (-6) (0) (2) (-2) (-2) (-1))
  | 2 => (ofSix (-4) (1) (2) (-2) (-2) (0))
  | 3 => (ofSix (-2) (-2) (2) (-2) (-1) (-2))
  | 4 => (ofSix (-2) (-2) (2) (-1) (0) (-2))
  | 5 => (ofSix (-2) (-2) (2) (0) (-2) (-1))
  | 6 => (ofSix (-2) (-1) (2) (0) (-2) (0))
  | _ => (ofSix (-2) (0) (1) (-2) (0) (-2))

def stripParameters : UnitZeroStrip.Parameters := ⟨2,6,8⟩
theorem strip_domain : UnitZeroStrip.Domain 2 stripParameters.u stripParameters.v stripParameters.w := by unfold UnitZeroStrip.Domain stripParameters; decide

inductive Core : Matrix 4 → Prop
  | finite (i : Fin 8) : Core (node i)
  | strip (n : Nat) (i : Fin 10) : Core (UnitZeroStrip.strip 2 stripParameters n i)
  | framed {B : Matrix 4} : Core B → (p : Relabeling 4) → Core (relabel B p)
  | reversed {B : Matrix 4} : Core B → Core (reverse B)

theorem strict_fork_weak {B : Matrix 4} {r : Fin 4} (h : Forks.IsFork B r) :
    WeakForks.IsWeakFork B r := by
  induction h with
  | basic a b c d e f h =>
    apply WeakForks.IsWeakFork.basic a b c d e f
    unfold Forks.Domain at h
    unfold WeakForks.Domain
    omega
  | relabelled h p ih => exact .relabelled ih p
  | reversed h ih => exact .reversed ih

theorem strict_root_weak {B : Matrix 4} {r : Fin 4} (h : Regions.IsRoot B r) :
    WeakRegions.IsRoot B r := by
  induction h with
  | basic a b c d e eps h he =>
    apply WeakRegions.IsRoot.basic a b c d e eps _ he
    unfold Regions.Domain at h
    unfold WeakRegions.Domain
    omega
  | relabelled h p ih => exact .relabelled ih p
  | reversed h ih => exact .reversed ih

theorem cyclic0 : ¬ Acyclic (node 0) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge0_0 : Core (mutate (node 0) 0) ∨
    WeakForks.IsWeakFork (mutate (node 0) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 0) 0) 0 := by
  right; right
  have he : relabel (reverse (mutate (node 0) 0)) perm4 = WeakRegions.root (4) (22) (7) (6) (2) (0) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 0) 0)) perm4 u v =
      WeakRegions.root (4) (22) (7) (6) (2) (0) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 0) 0)) perm4) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (4) (22) (7) (6) (2) (0) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm4 hb)

theorem edge0_1 : Core (mutate (node 0) 1) ∨
    WeakForks.IsWeakFork (mutate (node 0) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 0) 1) 1 := by
  have he : mutate (node 0) 1 = reverse (relabel (UnitZeroStrip.strip 2 stripParameters 0 0) perm14) := by
    funext u v
    exact (show ∀ u v : Fin 4, mutate (node 0) 1 u v = (reverse (relabel (UnitZeroStrip.strip 2 stripParameters 0 0) perm14)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.strip 0 0) perm14))

theorem edge0_2 : Core (mutate (node 0) 2) ∨
    WeakForks.IsWeakFork (mutate (node 0) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 0) 2) 2 := by
  have he : mutate (node 0) 2 = reverse (relabel (node 1) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, mutate (node 0) 2 u v = (reverse (relabel (node 1) perm6)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 1) perm6))

theorem edge0_3 : Core (mutate (node 0) 3) ∨
    WeakForks.IsWeakFork (mutate (node 0) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 0) 3) 3 := by
  have he : mutate (node 0) 3 = reverse (relabel (node 2) perm11) := by
    funext u v
    exact (show ∀ u v : Fin 4, mutate (node 0) 3 u v = (reverse (relabel (node 2) perm11)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 2) perm11))

theorem cyclic1 : ¬ Acyclic (node 1) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge1_0 : Core (mutate (node 1) 0) ∨
    WeakForks.IsWeakFork (mutate (node 1) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 1) 0) 0 := by
  have he : mutate (node 1) 0 = relabel (UnitZeroStrip.strip 2 stripParameters 0 1) perm8 := by
    funext u v
    exact (show ∀ u v : Fin 4, mutate (node 1) 0 u v = (relabel (UnitZeroStrip.strip 2 stripParameters 0 1) perm8) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.strip 0 1) perm8)

theorem edge1_1 : Core (mutate (node 1) 1) ∨
    WeakForks.IsWeakFork (mutate (node 1) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 1) 1) 1 := by
  right; right
  have he : relabel (reverse (mutate (node 1) 1)) perm6 = WeakRegions.root (6) (12) (10) (2) (2) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 1) 1)) perm6 u v =
      WeakRegions.root (6) (12) (10) (2) (2) (1) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 1) 1)) perm6) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (6) (12) (10) (2) (2) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm6 hb)

theorem edge1_2 : Core (mutate (node 1) 2) ∨
    WeakForks.IsWeakFork (mutate (node 1) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 1) 2) 2 := by
  have he : mutate (node 1) 2 = reverse (relabel (node 0) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, mutate (node 1) 2 u v = (reverse (relabel (node 0) perm6)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 0) perm6))

theorem edge1_3 : Core (mutate (node 1) 3) ∨
    WeakForks.IsWeakFork (mutate (node 1) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 1) 3) 3 := by
  have he : mutate (node 1) 3 = relabel (node 3) perm3 := by
    funext u v
    exact (show ∀ u v : Fin 4, mutate (node 1) 3 u v = (relabel (node 3) perm3) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 3) perm3)

theorem cyclic2 : ¬ Acyclic (node 2) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (by decide)
  have h1 := hr 2 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge2_0 : Core (mutate (node 2) 0) ∨
    WeakForks.IsWeakFork (mutate (node 2) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 2) 0) 0 := by
  have he : mutate (node 2) 0 = reverse (relabel (node 0) perm19) := by
    funext u v
    exact (show ∀ u v : Fin 4, mutate (node 2) 0 u v = (reverse (relabel (node 0) perm19)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 0) perm19))

theorem edge2_1 : Core (mutate (node 2) 1) ∨
    WeakForks.IsWeakFork (mutate (node 2) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 2) 1) 1 := by
  right; right
  have he : relabel (reverse (mutate (node 2) 1)) perm6 = WeakRegions.root (4) (7) (6) (2) (2) (0) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 2) 1)) perm6 u v =
      WeakRegions.root (4) (7) (6) (2) (2) (0) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 2) 1)) perm6) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (4) (7) (6) (2) (2) (0) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm6 hb)

theorem edge2_2 : Core (mutate (node 2) 2) ∨
    WeakForks.IsWeakFork (mutate (node 2) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 2) 2) 2 := by
  have he : mutate (node 2) 2 = reverse (relabel (node 4) perm12) := by
    funext u v
    exact (show ∀ u v : Fin 4, mutate (node 2) 2 u v = (reverse (relabel (node 4) perm12)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 4) perm12))

theorem edge2_3 : Core (mutate (node 2) 3) ∨
    WeakForks.IsWeakFork (mutate (node 2) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 2) 3) 3 := by
  have he : mutate (node 2) 3 = relabel (node 7) perm3 := by
    funext u v
    exact (show ∀ u v : Fin 4, mutate (node 2) 3 u v = (relabel (node 7) perm3) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 7) perm3)

theorem cyclic3 : ¬ Acyclic (node 3) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge3_0 : Core (mutate (node 3) 0) ∨
    WeakForks.IsWeakFork (mutate (node 3) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 3) 0) 0 := by
  right; left
  have he : relabel (mutate (node 3) 0) perm5 = WeakForks.template (2) (2) (2) (2) (3) (2) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 3) 0) perm5 u v =
      WeakForks.template (2) (2) (2) (2) (3) (2) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (mutate (node 3) 0) perm5) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (2) (2) (2) (2) (3) (2) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm5 hb

theorem edge3_1 : Core (mutate (node 3) 1) ∨
    WeakForks.IsWeakFork (mutate (node 3) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 3) 1) 1 := by
  have he : mutate (node 3) 1 = relabel (node 1) perm4 := by
    funext u v
    exact (show ∀ u v : Fin 4, mutate (node 3) 1 u v = (relabel (node 1) perm4) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 1) perm4)

theorem edge3_2 : Core (mutate (node 3) 2) ∨
    WeakForks.IsWeakFork (mutate (node 3) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 3) 2) 2 := by
  right; left
  have he : relabel (reverse (mutate (node 3) 2)) perm16 = WeakForks.template (2) (2) (2) (2) (5) (2) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 3) 2)) perm16 u v =
      WeakForks.template (2) (2) (2) (2) (5) (2) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (reverse (mutate (node 3) 2)) perm16) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (2) (2) (2) (2) (5) (2) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_reverse (WeakForks.fork_of_relabel perm16 hb)

theorem edge3_3 : Core (mutate (node 3) 3) ∨
    WeakForks.IsWeakFork (mutate (node 3) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 3) 3) 3 := by
  have he : mutate (node 3) 3 = reverse (relabel (node 4) perm20) := by
    funext u v
    exact (show ∀ u v : Fin 4, mutate (node 3) 3 u v = (reverse (relabel (node 4) perm20)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 4) perm20))

theorem cyclic4 : ¬ Acyclic (node 4) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 2 (by decide)
  have h2 := hr 2 0 (by decide)
  omega

theorem edge4_0 : Core (mutate (node 4) 0) ∨
    WeakForks.IsWeakFork (mutate (node 4) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 4) 0) 0 := by
  right; right
  have he : relabel (reverse (mutate (node 4) 0)) perm4 = WeakRegions.root (2) (4) (2) (2) (2) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 4) 0)) perm4 u v =
      WeakRegions.root (2) (4) (2) (2) (2) (1) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 4) 0)) perm4) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (2) (4) (2) (2) (2) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm4 hb)

theorem edge4_1 : Core (mutate (node 4) 1) ∨
    WeakForks.IsWeakFork (mutate (node 4) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 4) 1) 1 := by
  have he : mutate (node 4) 1 = reverse (relabel (node 2) perm8) := by
    funext u v
    exact (show ∀ u v : Fin 4, mutate (node 4) 1 u v = (reverse (relabel (node 2) perm8)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 2) perm8))

theorem edge4_2 : Core (mutate (node 4) 2) ∨
    WeakForks.IsWeakFork (mutate (node 4) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 4) 2) 2 := by
  have he : mutate (node 4) 2 = reverse (relabel (node 3) perm15) := by
    funext u v
    exact (show ∀ u v : Fin 4, mutate (node 4) 2 u v = (reverse (relabel (node 3) perm15)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 3) perm15))

theorem edge4_3 : Core (mutate (node 4) 3) ∨
    WeakForks.IsWeakFork (mutate (node 4) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 4) 3) 3 := by
  have he : mutate (node 4) 3 = relabel (node 5) perm3 := by
    funext u v
    exact (show ∀ u v : Fin 4, mutate (node 4) 3 u v = (relabel (node 5) perm3) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 5) perm3)

theorem cyclic5 : ¬ Acyclic (node 5) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge5_0 : Core (mutate (node 5) 0) ∨
    WeakForks.IsWeakFork (mutate (node 5) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 5) 0) 0 := by
  right; right
  have he : relabel (reverse (mutate (node 5) 0)) perm4 = WeakRegions.root (2) (2) (3) (2) (2) (0) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 5) 0)) perm4 u v =
      WeakRegions.root (2) (2) (3) (2) (2) (0) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 5) 0)) perm4) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (2) (2) (3) (2) (2) (0) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm4 hb)

theorem edge5_1 : Core (mutate (node 5) 1) ∨
    WeakForks.IsWeakFork (mutate (node 5) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 5) 1) 1 := by
  have he : mutate (node 5) 1 = relabel (node 4) perm4 := by
    funext u v
    exact (show ∀ u v : Fin 4, mutate (node 5) 1 u v = (relabel (node 4) perm4) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 4) perm4)

theorem edge5_2 : Core (mutate (node 5) 2) ∨
    WeakForks.IsWeakFork (mutate (node 5) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 5) 2) 2 := by
  have he : mutate (node 5) 2 = relabel (node 7) perm8 := by
    funext u v
    exact (show ∀ u v : Fin 4, mutate (node 5) 2 u v = (relabel (node 7) perm8) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 7) perm8)

theorem edge5_3 : Core (mutate (node 5) 3) ∨
    WeakForks.IsWeakFork (mutate (node 5) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 5) 3) 3 := by
  have he : mutate (node 5) 3 = relabel (node 6) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, mutate (node 5) 3 u v = (relabel (node 6) perm21) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 6) perm21)

theorem cyclic6 : ¬ Acyclic (node 6) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge6_0 : Core (mutate (node 6) 0) ∨
    WeakForks.IsWeakFork (mutate (node 6) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 6) 0) 0 := by
  have he : mutate (node 6) 0 = relabel (node 5) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, mutate (node 6) 0 u v = (relabel (node 5) perm21) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 5) perm21)

theorem edge6_1 : Core (mutate (node 6) 1) ∨
    WeakForks.IsWeakFork (mutate (node 6) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 6) 1) 1 := by
  have he : mutate (node 6) 1 = relabel (node 6) perm5 := by
    funext u v
    exact (show ∀ u v : Fin 4, mutate (node 6) 1 u v = (relabel (node 6) perm5) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 6) perm5)

theorem edge6_2 : Core (mutate (node 6) 2) ∨
    WeakForks.IsWeakFork (mutate (node 6) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 6) 2) 2 := by
  have he : mutate (node 6) 2 = reverse (relabel (node 6) perm5) := by
    funext u v
    exact (show ∀ u v : Fin 4, mutate (node 6) 2 u v = (reverse (relabel (node 6) perm5)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 6) perm5))

theorem edge6_3 : Core (mutate (node 6) 3) ∨
    WeakForks.IsWeakFork (mutate (node 6) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 6) 3) 3 := by
  have he : mutate (node 6) 3 = relabel (node 6) perm5 := by
    funext u v
    exact (show ∀ u v : Fin 4, mutate (node 6) 3 u v = (relabel (node 6) perm5) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 6) perm5)

theorem cyclic7 : ¬ Acyclic (node 7) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 2 (by decide)
  have h2 := hr 2 1 (by decide)
  have h3 := hr 1 0 (by decide)
  omega

theorem edge7_0 : Core (mutate (node 7) 0) ∨
    WeakForks.IsWeakFork (mutate (node 7) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 7) 0) 0 := by
  have he : mutate (node 7) 0 = relabel (node 5) perm12 := by
    funext u v
    exact (show ∀ u v : Fin 4, mutate (node 7) 0 u v = (relabel (node 5) perm12) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 5) perm12)

theorem edge7_1 : Core (mutate (node 7) 1) ∨
    WeakForks.IsWeakFork (mutate (node 7) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 7) 1) 1 := by
  have he : mutate (node 7) 1 = relabel (node 2) perm4 := by
    funext u v
    exact (show ∀ u v : Fin 4, mutate (node 7) 1 u v = (relabel (node 2) perm4) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 2) perm4)

theorem edge7_2 : Core (mutate (node 7) 2) ∨
    WeakForks.IsWeakFork (mutate (node 7) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 7) 2) 2 := by
  have he : mutate (node 7) 2 = reverse (relabel (node 2) perm15) := by
    funext u v
    exact (show ∀ u v : Fin 4, mutate (node 7) 2 u v = (reverse (relabel (node 2) perm15)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 2) perm15))

theorem edge7_3 : Core (mutate (node 7) 3) ∨
    WeakForks.IsWeakFork (mutate (node 7) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 7) 3) 3 := by
  have he : mutate (node 7) 3 = reverse (relabel (node 5) perm20) := by
    funext u v
    exact (show ∀ u v : Fin 4, mutate (node 7) 3 u v = (reverse (relabel (node 5) perm20)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 5) perm20))

theorem finite_skew (i : Fin 8) : SkewSymmetric (node i) := by
  have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 := by omega
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ofSix_skew _ _ _ _ _ _

theorem finite_cyclic (i : Fin 8) : ¬ Acyclic (node i) := by
  have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 := by omega
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact cyclic0
  · exact cyclic1
  · exact cyclic2
  · exact cyclic3
  · exact cyclic4
  · exact cyclic5
  · exact cyclic6
  · exact cyclic7

theorem finite_edges (i : Fin 8) (k : Fin 4) : Core (mutate (node i) k) ∨
    WeakForks.IsWeakFork (mutate (node i) k) k ∨ WeakRegions.IsRoot (mutate (node i) k) k := by
  have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 := by omega
  have hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hk with rfl|rfl|rfl|rfl
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
  · exact edge5_0
  · exact edge5_1
  · exact edge5_2
  · exact edge5_3
  · exact edge6_0
  · exact edge6_1
  · exact edge6_2
  · exact edge6_3
  · exact edge7_0
  · exact edge7_1
  · exact edge7_2
  · exact edge7_3

theorem parent0_core : Core (UnitZeroStrip.parent 2 stripParameters 0) := by
  have he : UnitZeroStrip.parent 2 stripParameters 0 = reverse (relabel (node 0) perm14) := by
    funext u v
    exact (show ∀ u v : Fin 4, UnitZeroStrip.parent 2 stripParameters 0 u v = (reverse (relabel (node 0) perm14)) u v from by decide) u v
  rw [he]
  exact Core.reversed (Core.framed (Core.finite 0) perm14)

theorem parent1_core : Core (UnitZeroStrip.parent 2 stripParameters 1) := by
  have he : UnitZeroStrip.parent 2 stripParameters 1 = relabel (node 1) perm12 := by
    funext u v
    exact (show ∀ u v : Fin 4, UnitZeroStrip.parent 2 stripParameters 1 u v = (relabel (node 1) perm12) u v from by decide) u v
  rw [he]
  exact Core.framed (Core.finite 1) perm12

theorem parents_core (j : Fin 2) : Core (UnitZeroStrip.parent 2 stripParameters j) := by
  have hj : j=0 ∨ j=1 := by omega
  rcases hj with rfl|rfl
  · exact parent0_core
  · exact parent1_core

theorem core_skew {B : Matrix 4} (h : Core B) : SkewSymmetric B := by
  induction h with
  | finite i => exact finite_skew i
  | strip n i => exact UnitZeroStrip.strip_skew _ _ _ _
  | framed h p ih => exact relabel_skew _ p ih
  | reversed h ih => exact reverse_skew _ ih

theorem core_cyclic {B : Matrix 4} (h : Core B) : ¬ Acyclic B := by
  induction h with
  | finite i => exact finite_cyclic i
  | strip n i => exact UnitZeroStrip.strip_cyclic _ _ strip_domain _ _
  | framed h p ih => exact fun ha => ih ((acyclic_relabel_iff _ p).mp ha)
  | reversed h ih => exact fun ha => ih ((acyclic_reverse_iff _ (core_skew h)).mp ha)

theorem core_edges {B : Matrix 4} (h : Core B) (k : Fin 4) :
    Core (mutate B k) ∨ WeakForks.IsWeakFork (mutate B k) k ∨ WeakRegions.IsRoot (mutate B k) k := by
  induction h generalizing k with
  | finite i => exact finite_edges i k
  | strip n i =>
    rcases UnitZeroStrip.all_edges 2 stripParameters strip_domain n i k with
      ⟨n2,i2,p,he⟩ | ⟨j,p,he⟩ | hf | hr
    · rw [he]; exact Or.inl (.framed (.strip n2 i2) p)
    · rw [he]; exact Or.inl (.framed (parents_core j) p)
    · exact Or.inr (Or.inl (strict_fork_weak hf))
    · exact Or.inr (Or.inr (strict_root_weak hr))
  | framed h p ih =>
    rw [mutate_relabel]
    rcases ih (p.toFun k) with hc|hf|hr
    · exact Or.inl (.framed hc p)
    · exact Or.inr (Or.inl (by simpa only [p.left_inv] using WeakForks.IsWeakFork.relabelled hf p))
    · exact Or.inr (Or.inr (by simpa only [p.left_inv] using WeakRegions.IsRoot.relabelled hr p))
  | reversed h ih =>
    rw [mutate_reverse]
    rcases ih k with hc|hf|hr
    · exact Or.inl (.reversed hc)
    · exact Or.inr (Or.inl (.reversed hf))
    · exact Or.inr (Or.inr (.reversed hr))

theorem core_NMA {B : Matrix 4} (h : Core B) : ¬ MutationAcyclic B :=
  WeakRegionSemantics.region_NMA WeakRegionCells.root_cells_exist Core
    (fun _ h => core_skew h) (fun _ h => core_cyclic h) (fun _ h k => core_edges h k) B h

theorem node_NMA (i : Fin 8) : ¬ MutationAcyclic (node i) := core_NMA (.finite i)

/-- Exact source q219: unconditional NMA for every finite mutation word. -/
theorem nma_q219 : ¬ MutationAcyclic (ofSix (-2) (-2) (2) (-2) (-1) (-2)) := by
  have he : (ofSix (-2) (-2) (2) (-2) (-1) (-2)) = relabel (node 3) perm0 := by
    funext u v
    exact (show ∀ u v : Fin 4, (ofSix (-2) (-2) (2) (-2) (-1) (-2)) u v = (relabel (node 3) perm0) u v from by decide) u v
  rw [he]
  exact core_NMA (Core.framed (Core.finite 3) perm0)

/-- Exact source q227: unconditional NMA for every finite mutation word. -/
theorem nma_q227 : ¬ MutationAcyclic (ofSix (-2) (-2) (2) (-2) (1) (-2)) := by
  have he : (ofSix (-2) (-2) (2) (-2) (1) (-2)) = reverse (relabel (node 3) perm14) := by
    funext u v
    exact (show ∀ u v : Fin 4, (ofSix (-2) (-2) (2) (-2) (1) (-2)) u v = (reverse (relabel (node 3) perm14)) u v from by decide) u v
  rw [he]
  exact core_NMA (Core.reversed (Core.framed (Core.finite 3) perm14))

/-- Exact source q239: unconditional NMA for every finite mutation word. -/
theorem nma_q239 : ¬ MutationAcyclic (ofSix (-2) (-2) (2) (-1) (0) (-2)) := by
  have he : (ofSix (-2) (-2) (2) (-1) (0) (-2)) = relabel (node 4) perm0 := by
    funext u v
    exact (show ∀ u v : Fin 4, (ofSix (-2) (-2) (2) (-1) (0) (-2)) u v = (relabel (node 4) perm0) u v from by decide) u v
  rw [he]
  exact core_NMA (Core.framed (Core.finite 4) perm0)

/-- Exact source q248: unconditional NMA for every finite mutation word. -/
theorem nma_q248 : ¬ MutationAcyclic (ofSix (-2) (-2) (2) (0) (-2) (-1)) := by
  have he : (ofSix (-2) (-2) (2) (0) (-2) (-1)) = relabel (node 5) perm0 := by
    funext u v
    exact (show ∀ u v : Fin 4, (ofSix (-2) (-2) (2) (0) (-2) (-1)) u v = (relabel (node 5) perm0) u v from by decide) u v
  rw [he]
  exact core_NMA (Core.framed (Core.finite 5) perm0)

/-- Exact source q514: unconditional NMA for every finite mutation word. -/
theorem nma_q514 : ¬ MutationAcyclic (ofSix (-2) (-1) (2) (0) (-2) (-2)) := by
  have he : (ofSix (-2) (-1) (2) (0) (-2) (-2)) = reverse (relabel (node 5) perm21) := by
    funext u v
    exact (show ∀ u v : Fin 4, (ofSix (-2) (-1) (2) (0) (-2) (-2)) u v = (reverse (relabel (node 5) perm21)) u v from by decide) u v
  rw [he]
  exact core_NMA (Core.reversed (Core.framed (Core.finite 5) perm21))

/-- Exact source q516: unconditional NMA for every finite mutation word. -/
theorem nma_q516 : ¬ MutationAcyclic (ofSix (-2) (-1) (2) (0) (-2) (0)) := by
  have he : (ofSix (-2) (-1) (2) (0) (-2) (0)) = relabel (node 6) perm0 := by
    funext u v
    exact (show ∀ u v : Fin 4, (ofSix (-2) (-1) (2) (0) (-2) (0)) u v = (relabel (node 6) perm0) u v from by decide) u v
  rw [he]
  exact core_NMA (Core.framed (Core.finite 6) perm0)

/-- Exact source q529: unconditional NMA for every finite mutation word. -/
theorem nma_q529 : ¬ MutationAcyclic (ofSix (-2) (-1) (2) (2) (-2) (0)) := by
  have he : (ofSix (-2) (-1) (2) (2) (-2) (0)) = reverse (relabel (node 4) perm12) := by
    funext u v
    exact (show ∀ u v : Fin 4, (ofSix (-2) (-1) (2) (2) (-2) (0)) u v = (reverse (relabel (node 4) perm12)) u v from by decide) u v
  rw [he]
  exact core_NMA (Core.reversed (Core.framed (Core.finite 4) perm12))

/-- Exact source q565: unconditional NMA for every finite mutation word. -/
theorem nma_q565 : ¬ MutationAcyclic (ofSix (-2) (0) (1) (-2) (0) (-2)) := by
  have he : (ofSix (-2) (0) (1) (-2) (0) (-2)) = relabel (node 7) perm0 := by
    funext u v
    exact (show ∀ u v : Fin 4, (ofSix (-2) (0) (1) (-2) (0) (-2)) u v = (relabel (node 7) perm0) u v from by decide) u v
  rw [he]
  exact core_NMA (Core.framed (Core.finite 7) perm0)

/-- Exact source q610: unconditional NMA for every finite mutation word. -/
theorem nma_q610 : ¬ MutationAcyclic (ofSix (-2) (0) (2) (0) (-2) (-1)) := by
  have he : (ofSix (-2) (0) (2) (0) (-2) (-1)) = reverse (relabel (node 6) perm21) := by
    funext u v
    exact (show ∀ u v : Fin 4, (ofSix (-2) (0) (2) (0) (-2) (-1)) u v = (reverse (relabel (node 6) perm21)) u v from by decide) u v
  rw [he]
  exact core_NMA (Core.reversed (Core.framed (Core.finite 6) perm21))

end QuiverProofs.HereditaryTrianglePendant
