import QuiverProofs.HereditaryTrianglePendant
import QuiverProofs.StripSemantics
import QuiverProofs.AbundantPendantStrip

/-! Exact finite core joined to unbounded G/N/D strips. Every entrance parent is checked. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace QuiverProofs.ProperPendantRegions00
open ForkCertificates HereditaryTrianglePendant

def node (i : Fin 11) : Matrix 4 := match i.val with
  | 0 => (ofSix (-8) (-8) (6) (0) (-2) (-1))
  | 1 => (ofSix (-8) (-2) (2) (-2) (-6) (-1))
  | 2 => (ofSix (-8) (-2) (8) (-2) (0) (-1))
  | 3 => (ofSix (-6) (-2) (4) (-1) (-2) (0))
  | 4 => (ofSix (-6) (-1) (2) (-2) (-4) (0))
  | 5 => (ofSix (-4) (-2) (2) (0) (-2) (1))
  | 6 => (ofSix (-4) (0) (1) (0) (-2) (-2))
  | 7 => (ofSix (-4) (0) (1) (0) (-2) (2))
  | 8 => (ofSix (-4) (0) (2) (-2) (-2) (1))
  | 9 => (ofSix (-3) (-2) (2) (-2) (-2) (0))
  | _ => (ofSix (-2) (-2) (0) (-1) (2) (-2))

def seed0 : AbundantPendantStrip.Parameters := ⟨2,7⟩
theorem domain0 : PendantSquare.Domain 2 4 seed0.x seed0.y := by unfold PendantSquare.Domain seed0; decide
def strip0 (n : Nat) (i : Fin 2) : Matrix 4 := AbundantPendantStrip.strip 2 4 seed0 n i
def seed1 : UnitZeroStrip.Parameters := ⟨8,8,10⟩
theorem domain1 : UnitZeroStrip.Domain 2 seed1.u seed1.v seed1.w := by unfold UnitZeroStrip.Domain seed1; decide
def strip1 (n : Nat) (i : Fin 10) : Matrix 4 := UnitZeroStrip.strip 2 seed1 n i

inductive Core : Matrix 4 → Prop
  | finite (i : Fin 11) : Core (node i)
  | strip0 (n : Nat) (i : Fin 2) : Core (strip0 n i)
  | strip1 (n : Nat) (i : Fin 10) : Core (strip1 n i)
  | framed {B : Matrix 4} : Core B → (p : Relabeling 4) → Core (relabel B p)
  | reversed {B : Matrix 4} : Core B → Core (reverse B)

theorem cyclic0 : ¬ Acyclic (node 0) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge0_0 : Core (mutate (node 0) 0) ∨
    WeakForks.IsWeakFork (mutate (node 0) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 0) 0) 0 := by
  right; right
  have he : relabel (reverse (mutate (node 0) 0)) perm4 = WeakRegions.root (6) (46) (47) (8) (8) (0) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 0) 0)) perm4) u v = (WeakRegions.root (6) (46) (47) (8) (8) (0)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 0) 0)) perm4) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (6) (46) (47) (8) (8) (0) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm4 hb)

theorem edge0_1 : Core (mutate (node 0) 1) ∨
    WeakForks.IsWeakFork (mutate (node 0) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 0) 1) 1 := by
  have he : mutate (node 0) 1 = reverse (relabel (strip1 0 0) perm14) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 0) 1) u v = (reverse (relabel (strip1 0 0) perm14)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.strip1 0 0) perm14))

theorem edge0_2 : Core (mutate (node 0) 2) ∨
    WeakForks.IsWeakFork (mutate (node 0) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 0) 2) 2 := by
  have he : mutate (node 0) 2 = relabel (node 2) perm1 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 0) 2) u v = (relabel (node 2) perm1) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 2) perm1)

theorem edge0_3 : Core (mutate (node 0) 3) ∨
    WeakForks.IsWeakFork (mutate (node 0) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 0) 3) 3 := by
  have he : mutate (node 0) 3 = relabel (node 3) perm5 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 0) 3) u v = (relabel (node 3) perm5) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 3) perm5)

theorem cyclic1 : ¬ Acyclic (node 1) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge1_0 : Core (mutate (node 1) 0) ∨
    WeakForks.IsWeakFork (mutate (node 1) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 1) 0) 0 := by
  right; left
  have he : relabel (mutate (node 1) 0) perm5 = WeakForks.template (2) (2) (8) (3) (10) (2) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 1) 0) perm5) u v = (WeakForks.template (2) (2) (8) (3) (10) (2)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (mutate (node 1) 0) perm5) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (2) (2) (8) (3) (10) (2) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm5 hb

theorem edge1_1 : Core (mutate (node 1) 1) ∨
    WeakForks.IsWeakFork (mutate (node 1) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 1) 1) 1 := by
  right; right
  have he : relabel (reverse (mutate (node 1) 1)) perm6 = WeakRegions.root (8) (18) (46) (2) (6) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 1) 1)) perm6) u v = (WeakRegions.root (8) (18) (46) (2) (6) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 1) 1)) perm6) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (8) (18) (46) (2) (6) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm6 hb)

theorem edge1_2 : Core (mutate (node 1) 2) ∨
    WeakForks.IsWeakFork (mutate (node 1) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 1) 2) 2 := by
  have he : mutate (node 1) 2 = reverse (relabel (node 2) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 1) 2) u v = (reverse (relabel (node 2) perm6)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 2) perm6))

theorem edge1_3 : Core (mutate (node 1) 3) ∨
    WeakForks.IsWeakFork (mutate (node 1) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 1) 3) 3 := by
  have he : mutate (node 1) 3 = relabel (node 4) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 1) 3) u v = (relabel (node 4) perm21) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 4) perm21)

theorem cyclic2 : ¬ Acyclic (node 2) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 2 (by decide)
  have h2 := hr 2 0 (by decide)
  omega

theorem edge2_0 : Core (mutate (node 2) 0) ∨
    WeakForks.IsWeakFork (mutate (node 2) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 2) 0) 0 := by
  right; left
  have he : relabel (mutate (node 2) 0) perm5 = WeakForks.template (8) (2) (8) (15) (64) (2) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 2) 0) perm5) u v = (WeakForks.template (8) (2) (8) (15) (64) (2)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (mutate (node 2) 0) perm5) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (8) (2) (8) (15) (64) (2) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm5 hb

theorem edge2_1 : Core (mutate (node 2) 1) ∨
    WeakForks.IsWeakFork (mutate (node 2) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 2) 1) 1 := by
  have he : mutate (node 2) 1 = reverse (relabel (strip1 0 1) perm15) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 2) 1) u v = (reverse (relabel (strip1 0 1) perm15)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.strip1 0 1) perm15))

theorem edge2_2 : Core (mutate (node 2) 2) ∨
    WeakForks.IsWeakFork (mutate (node 2) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 2) 2) 2 := by
  have he : mutate (node 2) 2 = reverse (relabel (node 1) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 2) 2) u v = (reverse (relabel (node 1) perm6)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 1) perm6))

theorem edge2_3 : Core (mutate (node 2) 3) ∨
    WeakForks.IsWeakFork (mutate (node 2) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 2) 3) 3 := by
  have he : mutate (node 2) 3 = relabel (node 0) perm1 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 2) 3) u v = (relabel (node 0) perm1) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 0) perm1)

theorem cyclic3 : ¬ Acyclic (node 3) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge3_0 : Core (mutate (node 3) 0) ∨
    WeakForks.IsWeakFork (mutate (node 3) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 3) 0) 0 := by
  right; right
  have he : relabel (reverse (mutate (node 3) 0)) perm4 = WeakRegions.root (4) (22) (8) (6) (2) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 3) 0)) perm4) u v = (WeakRegions.root (4) (22) (8) (6) (2) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 3) 0)) perm4) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (4) (22) (8) (6) (2) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm4 hb)

theorem edge3_1 : Core (mutate (node 3) 1) ∨
    WeakForks.IsWeakFork (mutate (node 3) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 3) 1) 1 := by
  have he : mutate (node 3) 1 = relabel (node 0) perm5 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 3) 1) u v = (relabel (node 0) perm5) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 0) perm5)

theorem edge3_2 : Core (mutate (node 3) 2) ∨
    WeakForks.IsWeakFork (mutate (node 3) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 3) 2) 2 := by
  have he : mutate (node 3) 2 = reverse (relabel (node 4) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 3) 2) u v = (reverse (relabel (node 4) perm6)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 4) perm6))

theorem edge3_3 : Core (mutate (node 3) 3) ∨
    WeakForks.IsWeakFork (mutate (node 3) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 3) 3) 3 := by
  have he : mutate (node 3) 3 = relabel (node 5) perm5 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 3) 3) u v = (relabel (node 5) perm5) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 5) perm5)

theorem cyclic4 : ¬ Acyclic (node 4) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge4_0 : Core (mutate (node 4) 0) ∨
    WeakForks.IsWeakFork (mutate (node 4) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 4) 0) 0 := by
  have he : mutate (node 4) 0 = relabel (node 1) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 4) 0) u v = (relabel (node 1) perm21) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 1) perm21)

theorem edge4_1 : Core (mutate (node 4) 1) ∨
    WeakForks.IsWeakFork (mutate (node 4) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 4) 1) 1 := by
  right; right
  have he : relabel (reverse (mutate (node 4) 1)) perm6 = WeakRegions.root (6) (13) (22) (2) (4) (0) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 4) 1)) perm6) u v = (WeakRegions.root (6) (13) (22) (2) (4) (0)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 4) 1)) perm6) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (6) (13) (22) (2) (4) (0) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm6 hb)

theorem edge4_2 : Core (mutate (node 4) 2) ∨
    WeakForks.IsWeakFork (mutate (node 4) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 4) 2) 2 := by
  have he : mutate (node 4) 2 = reverse (relabel (node 3) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 4) 2) u v = (reverse (relabel (node 3) perm6)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 3) perm6))

theorem edge4_3 : Core (mutate (node 4) 3) ∨
    WeakForks.IsWeakFork (mutate (node 4) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 4) 3) 3 := by
  have he : mutate (node 4) 3 = relabel (node 8) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 4) 3) u v = (relabel (node 8) perm21) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 8) perm21)

theorem cyclic5 : ¬ Acyclic (node 5) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge5_0 : Core (mutate (node 5) 0) ∨
    WeakForks.IsWeakFork (mutate (node 5) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 5) 0) 0 := by
  right; right
  have he : relabel (reverse (mutate (node 5) 0)) perm4 = WeakRegions.root (2) (6) (5) (4) (2) (0) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 5) 0)) perm4) u v = (WeakRegions.root (2) (6) (5) (4) (2) (0)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 5) 0)) perm4) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (2) (6) (5) (4) (2) (0) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm4 hb)

theorem edge5_1 : Core (mutate (node 5) 1) ∨
    WeakForks.IsWeakFork (mutate (node 5) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 5) 1) 1 := by
  have he : mutate (node 5) 1 = relabel (node 3) perm5 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 5) 1) u v = (relabel (node 3) perm5) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 3) perm5)

theorem edge5_2 : Core (mutate (node 5) 2) ∨
    WeakForks.IsWeakFork (mutate (node 5) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 5) 2) 2 := by
  have he : mutate (node 5) 2 = reverse (relabel (node 8) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 5) 2) u v = (reverse (relabel (node 8) perm6)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 8) perm6))

theorem edge5_3 : Core (mutate (node 5) 3) ∨
    WeakForks.IsWeakFork (mutate (node 5) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 5) 3) 3 := by
  have he : mutate (node 5) 3 = relabel (node 10) perm4 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 5) 3) u v = (relabel (node 10) perm4) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 10) perm4)

theorem cyclic6 : ¬ Acyclic (node 6) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge6_0 : Core (mutate (node 6) 0) ∨
    WeakForks.IsWeakFork (mutate (node 6) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 6) 0) 0 := by
  have he : mutate (node 6) 0 = reverse (relabel (node 7) perm0) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 6) 0) u v = (reverse (relabel (node 7) perm0)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 7) perm0))

theorem edge6_1 : Core (mutate (node 6) 1) ∨
    WeakForks.IsWeakFork (mutate (node 6) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 6) 1) 1 := by
  have he : mutate (node 6) 1 = reverse (relabel (strip0 0 0) perm14) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 6) 1) u v = (reverse (relabel (strip0 0 0) perm14)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.strip0 0 0) perm14))

theorem edge6_2 : Core (mutate (node 6) 2) ∨
    WeakForks.IsWeakFork (mutate (node 6) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 6) 2) 2 := by
  have he : mutate (node 6) 2 = relabel (node 7) perm0 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 6) 2) u v = (relabel (node 7) perm0) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 7) perm0)

theorem edge6_3 : Core (mutate (node 6) 3) ∨
    WeakForks.IsWeakFork (mutate (node 6) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 6) 3) 3 := by
  have he : mutate (node 6) 3 = reverse (relabel (node 10) perm13) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 6) 3) u v = (reverse (relabel (node 10) perm13)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 10) perm13))

theorem cyclic7 : ¬ Acyclic (node 7) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge7_0 : Core (mutate (node 7) 0) ∨
    WeakForks.IsWeakFork (mutate (node 7) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 7) 0) 0 := by
  have he : mutate (node 7) 0 = reverse (relabel (node 6) perm0) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 7) 0) u v = (reverse (relabel (node 6) perm0)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 6) perm0))

theorem edge7_1 : Core (mutate (node 7) 1) ∨
    WeakForks.IsWeakFork (mutate (node 7) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 7) 1) 1 := by
  have he : mutate (node 7) 1 = reverse (relabel (strip0 0 1) perm14) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 7) 1) u v = (reverse (relabel (strip0 0 1) perm14)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.strip0 0 1) perm14))

theorem edge7_2 : Core (mutate (node 7) 2) ∨
    WeakForks.IsWeakFork (mutate (node 7) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 7) 2) 2 := by
  have he : mutate (node 7) 2 = relabel (node 6) perm0 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 7) 2) u v = (relabel (node 6) perm0) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 6) perm0)

theorem edge7_3 : Core (mutate (node 7) 3) ∨
    WeakForks.IsWeakFork (mutate (node 7) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 7) 3) 3 := by
  have he : mutate (node 7) 3 = reverse (relabel (node 8) perm14) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 7) 3) u v = (reverse (relabel (node 8) perm14)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 8) perm14))

theorem cyclic8 : ¬ Acyclic (node 8) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge8_0 : Core (mutate (node 8) 0) ∨
    WeakForks.IsWeakFork (mutate (node 8) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 8) 0) 0 := by
  have he : mutate (node 8) 0 = relabel (node 4) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 8) 0) u v = (relabel (node 4) perm21) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 4) perm21)

theorem edge8_1 : Core (mutate (node 8) 1) ∨
    WeakForks.IsWeakFork (mutate (node 8) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 8) 1) 1 := by
  right; right
  have he : relabel (reverse (mutate (node 8) 1)) perm7 = WeakRegions.root (4) (6) (8) (2) (2) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 8) 1)) perm7) u v = (WeakRegions.root (4) (6) (8) (2) (2) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 8) 1)) perm7) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (4) (6) (8) (2) (2) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm7 hb)

theorem edge8_2 : Core (mutate (node 8) 2) ∨
    WeakForks.IsWeakFork (mutate (node 8) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 8) 2) 2 := by
  have he : mutate (node 8) 2 = reverse (relabel (node 5) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 8) 2) u v = (reverse (relabel (node 5) perm6)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 5) perm6))

theorem edge8_3 : Core (mutate (node 8) 3) ∨
    WeakForks.IsWeakFork (mutate (node 8) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 8) 3) 3 := by
  have he : mutate (node 8) 3 = reverse (relabel (node 7) perm14) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 8) 3) u v = (reverse (relabel (node 7) perm14)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 7) perm14))

theorem cyclic9 : ¬ Acyclic (node 9) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge9_0 : Core (mutate (node 9) 0) ∨
    WeakForks.IsWeakFork (mutate (node 9) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 9) 0) 0 := by
  right; left
  have he : relabel (mutate (node 9) 0) perm5 = WeakForks.template (2) (2) (3) (4) (4) (2) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 9) 0) perm5) u v = (WeakForks.template (2) (2) (3) (4) (4) (2)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (mutate (node 9) 0) perm5) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (2) (2) (3) (4) (4) (2) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm5 hb

theorem edge9_1 : Core (mutate (node 9) 1) ∨
    WeakForks.IsWeakFork (mutate (node 9) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 9) 1) 1 := by
  right; right
  have he : relabel (reverse (mutate (node 9) 1)) perm6 = WeakRegions.root (3) (8) (4) (2) (2) (0) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 9) 1)) perm6) u v = (WeakRegions.root (3) (8) (4) (2) (2) (0)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 9) 1)) perm6) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (3) (8) (4) (2) (2) (0) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm6 hb)

theorem edge9_2 : Core (mutate (node 9) 2) ∨
    WeakForks.IsWeakFork (mutate (node 9) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 9) 2) 2 := by
  have he : mutate (node 9) 2 = reverse (relabel (node 9) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 9) 2) u v = (reverse (relabel (node 9) perm6)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 9) perm6))

theorem edge9_3 : Core (mutate (node 9) 3) ∨
    WeakForks.IsWeakFork (mutate (node 9) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 9) 3) 3 := by
  have he : mutate (node 9) 3 = reverse (relabel (node 10) perm8) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 9) 3) u v = (reverse (relabel (node 10) perm8)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 10) perm8))

theorem cyclic10 : ¬ Acyclic (node 10) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 1 3 (by decide)
  have h1 := hr 3 2 (by decide)
  have h2 := hr 2 1 (by decide)
  omega

theorem edge10_0 : Core (mutate (node 10) 0) ∨
    WeakForks.IsWeakFork (mutate (node 10) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 10) 0) 0 := by
  have he : mutate (node 10) 0 = reverse (relabel (node 10) perm2) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 10) 0) u v = (reverse (relabel (node 10) perm2)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 10) perm2))

theorem edge10_1 : Core (mutate (node 10) 1) ∨
    WeakForks.IsWeakFork (mutate (node 10) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 10) 1) 1 := by
  have he : mutate (node 10) 1 = reverse (relabel (node 6) perm10) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 10) 1) u v = (reverse (relabel (node 6) perm10)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 6) perm10))

theorem edge10_2 : Core (mutate (node 10) 2) ∨
    WeakForks.IsWeakFork (mutate (node 10) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 10) 2) 2 := by
  have he : mutate (node 10) 2 = relabel (node 5) perm3 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 10) 2) u v = (relabel (node 5) perm3) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 5) perm3)

theorem edge10_3 : Core (mutate (node 10) 3) ∨
    WeakForks.IsWeakFork (mutate (node 10) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 10) 3) 3 := by
  have he : mutate (node 10) 3 = reverse (relabel (node 9) perm12) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 10) 3) u v = (reverse (relabel (node 9) perm12)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 9) perm12))

theorem finite_skew (i : Fin 11) : SkewSymmetric (node i) := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 := by omega
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ofSix_skew _ _ _ _ _ _

theorem finite_cyclic (i : Fin 11) : ¬ Acyclic (node i) := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 := by omega
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact cyclic0
  · exact cyclic1
  · exact cyclic2
  · exact cyclic3
  · exact cyclic4
  · exact cyclic5
  · exact cyclic6
  · exact cyclic7
  · exact cyclic8
  · exact cyclic9
  · exact cyclic10

theorem finite_edges (i : Fin 11) (k : Fin 4) : Core (mutate (node i) k) ∨
    WeakForks.IsWeakFork (mutate (node i) k) k ∨ WeakRegions.IsRoot (mutate (node i) k) k := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 := by omega
  have hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hk with rfl|rfl|rfl|rfl
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
  · exact edge8_0
  · exact edge8_1
  · exact edge8_2
  · exact edge8_3
  · exact edge9_0
  · exact edge9_1
  · exact edge9_2
  · exact edge9_3
  · exact edge10_0
  · exact edge10_1
  · exact edge10_2
  · exact edge10_3

theorem parent0_0 : Core (AbundantPendantStrip.parent 2 4 seed0 0) := by
  have he : AbundantPendantStrip.parent 2 4 seed0 0 = reverse (relabel (node 6) perm14) := by
    funext u v
    exact (show ∀ u v : Fin 4, (AbundantPendantStrip.parent 2 4 seed0 0) u v = (reverse (relabel (node 6) perm14)) u v from by decide) u v
  rw [he]
  exact Core.reversed (Core.framed (Core.finite 6) perm14)

theorem parent0_1 : Core (AbundantPendantStrip.parent 2 4 seed0 1) := by
  have he : AbundantPendantStrip.parent 2 4 seed0 1 = reverse (relabel (node 7) perm14) := by
    funext u v
    exact (show ∀ u v : Fin 4, (AbundantPendantStrip.parent 2 4 seed0 1) u v = (reverse (relabel (node 7) perm14)) u v from by decide) u v
  rw [he]
  exact Core.reversed (Core.framed (Core.finite 7) perm14)

theorem parents0 (p : Fin 2) : Core (AbundantPendantStrip.parent 2 4 seed0 p) := by
  have hp : p=0 ∨ p=1 := by omega
  rcases hp with rfl|rfl
  · exact parent0_0
  · exact parent0_1

theorem parent1_0 : Core (UnitZeroStrip.parent 2 seed1 0) := by
  have he : UnitZeroStrip.parent 2 seed1 0 = reverse (relabel (node 0) perm14) := by
    funext u v
    exact (show ∀ u v : Fin 4, (UnitZeroStrip.parent 2 seed1 0) u v = (reverse (relabel (node 0) perm14)) u v from by decide) u v
  rw [he]
  exact Core.reversed (Core.framed (Core.finite 0) perm14)

theorem parent1_1 : Core (UnitZeroStrip.parent 2 seed1 1) := by
  have he : UnitZeroStrip.parent 2 seed1 1 = reverse (relabel (node 2) perm20) := by
    funext u v
    exact (show ∀ u v : Fin 4, (UnitZeroStrip.parent 2 seed1 1) u v = (reverse (relabel (node 2) perm20)) u v from by decide) u v
  rw [he]
  exact Core.reversed (Core.framed (Core.finite 2) perm20)

theorem parents1 (p : Fin 2) : Core (UnitZeroStrip.parent 2 seed1 p) := by
  have hp : p=0 ∨ p=1 := by omega
  rcases hp with rfl|rfl
  · exact parent1_0
  · exact parent1_1

theorem core_skew {B : Matrix 4} (h : Core B) : SkewSymmetric B := by
  induction h with
  | finite i => exact finite_skew i
  | strip0 n i => exact AbundantPendantStrip.strip_skew _ _ _ _ _
  | strip1 n i => exact UnitZeroStrip.strip_skew _ _ _ _
  | framed h p ih => exact relabel_skew _ p ih
  | reversed h ih => exact reverse_skew _ ih

theorem core_cyclic {B : Matrix 4} (h : Core B) : ¬ Acyclic B := by
  induction h with
  | finite i => exact finite_cyclic i
  | strip0 n i => exact AbundantPendantStrip.strip_cyclic _ _ _ domain0 _ _
  | strip1 n i => exact UnitZeroStrip.strip_cyclic _ _ domain1 _ _
  | framed h p ih => exact fun ha => ih ((acyclic_relabel_iff _ p).mp ha)
  | reversed h ih => exact fun ha => ih ((acyclic_reverse_iff _ (core_skew h)).mp ha)

theorem core_edges {B : Matrix 4} (h : Core B) (k : Fin 4) :
    Core (mutate B k) ∨ WeakForks.IsWeakFork (mutate B k) k ∨ WeakRegions.IsRoot (mutate B k) k := by
  induction h generalizing k with
  | finite i => exact finite_edges i k
  | strip0 n i =>
    rcases AbundantPendantStrip.all_edges 2 4 seed0 domain0 n i k with
      ⟨n2,i2,p,he⟩ | ⟨p2,p,he⟩ | hr
    · rw [show strip0 n i = AbundantPendantStrip.strip 2 4 seed0 n i from rfl, he]
      exact Or.inl (.framed (.strip0 n2 i2) p)
    · rw [show strip0 n i = AbundantPendantStrip.strip 2 4 seed0 n i from rfl, he]
      exact Or.inl (.framed (parents0 p2) p)
    · exact Or.inr (Or.inr (strict_root_weak hr))
  | strip1 n i =>
    rcases UnitZeroStrip.all_edges 2 seed1 domain1 n i k with
      ⟨n2,i2,p,he⟩ | ⟨p2,p,he⟩ | hf | hr
    · rw [show strip1 n i = UnitZeroStrip.strip 2 seed1 n i from rfl, he]
      exact Or.inl (.framed (.strip1 n2 i2) p)
    · rw [show strip1 n i = UnitZeroStrip.strip 2 seed1 n i from rfl, he]
      exact Or.inl (.framed (parents1 p2) p)
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

/-- Exact source q133: unconditional NMA for every finite mutation word. -/
theorem nma_q133 : ¬ MutationAcyclic (ofSix (-2) (-2) (0) (-1) (2) (-2)) := by
  have he : (ofSix (-2) (-2) (0) (-1) (2) (-2)) = relabel (node 10) perm0 := by
    funext u v
    exact (show ∀ u v : Fin 4, ((ofSix (-2) (-2) (0) (-1) (2) (-2))) u v = (relabel (node 10) perm0) u v from by decide) u v
  rw [he]
  exact core_NMA (Core.framed (Core.finite 10) perm0)

/-- Exact source q204: unconditional NMA for every finite mutation word. -/
theorem nma_q204 : ¬ MutationAcyclic (ofSix (-2) (-2) (1) (0) (-2) (2)) := by
  have he : (ofSix (-2) (-2) (1) (0) (-2) (2)) = reverse (relabel (node 10) perm10) := by
    funext u v
    exact (show ∀ u v : Fin 4, ((ofSix (-2) (-2) (1) (0) (-2) (2))) u v = (reverse (relabel (node 10) perm10)) u v from by decide) u v
  rw [he]
  exact core_NMA (Core.reversed (Core.framed (Core.finite 10) perm10))

end QuiverProofs.ProperPendantRegions00
