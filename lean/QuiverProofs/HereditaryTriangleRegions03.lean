import QuiverProofs.HereditaryTrianglePendant
import QuiverProofs.StripSemantics

/-! Exact finite core joined to unbounded G/N strips. Every entrance parent is checked. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace QuiverProofs.HereditaryTriangleRegions03
open ForkCertificates HereditaryTrianglePendant

def node (i : Fin 16) : Matrix 4 := match i.val with
  | 0 => (ofSix (-128) (-2) (3) (-12) (-46) (-1))
  | 1 => (ofSix (-46) (-1) (3) (-12) (-10) (-1))
  | 2 => (ofSix (-22) (-2) (3) (-2) (-8) (-1))
  | 3 => (ofSix (-22) (-2) (10) (-2) (-1) (-1))
  | 4 => (ofSix (-16) (-10) (12) (3) (-2) (1))
  | 5 => (ofSix (-12) (-10) (8) (1) (-2) (-1))
  | 6 => (ofSix (-8) (-2) (4) (-1) (-2) (-1))
  | 7 => (ofSix (-8) (-1) (3) (-2) (-2) (-1))
  | 8 => (ofSix (-4) (-2) (3) (0) (-2) (-1))
  | 9 => (ofSix (-4) (0) (2) (-2) (-1) (-1))
  | 10 => (ofSix (-3) (-2) (2) (-2) (-1) (-2))
  | 11 => (ofSix (-3) (1) (2) (-1) (-2) (0))
  | 12 => (ofSix (-2) (-2) (2) (-1) (-1) (-2))
  | 13 => (ofSix (-2) (-1) (2) (0) (-2) (-1))
  | 14 => (ofSix (-2) (-1) (2) (1) (-2) (0))
  | _ => (ofSix (-2) (0) (2) (-1) (-1) (-1))

def seed0 : Cone.State := ⟨46,12,22⟩
theorem domain0 : GenericStrip.Domain 2 seed0.A seed0.H seed0.Z := by unfold GenericStrip.Domain seed0; decide
def strip0 (n : Nat) (i : Fin 6) : Matrix 4 :=
  GenericStrip.phase 2 (GenericStrip.orbit 2 seed0 n).A (GenericStrip.orbit 2 seed0 n).H (GenericStrip.orbit 2 seed0 n).Z i
def seed1 : UnitZeroStrip.Parameters := ⟨2,4,5⟩
theorem domain1 : UnitZeroStrip.Domain 2 seed1.u seed1.v seed1.w := by unfold UnitZeroStrip.Domain seed1; decide
def strip1 (n : Nat) (i : Fin 10) : Matrix 4 := UnitZeroStrip.strip 2 seed1 n i

inductive Core : Matrix 4 → Prop
  | finite (i : Fin 16) : Core (node i)
  | strip0 (n : Nat) (i : Fin 6) : Core (strip0 n i)
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
  right; left
  have he : relabel (mutate (node 0) 0) perm5 = WeakForks.template (3) (2) (128) (5) (338) (12) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 0) 0) perm5) u v = (WeakForks.template (3) (2) (128) (5) (338) (12)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (mutate (node 0) 0) perm5) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (3) (2) (128) (5) (338) (12) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm5 hb

theorem edge0_1 : Core (mutate (node 0) 1) ∨
    WeakForks.IsWeakFork (mutate (node 0) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 0) 1) 1 := by
  right; right
  have he : relabel (reverse (mutate (node 0) 1)) perm6 = WeakRegions.root (128) (1538) (5885) (12) (46) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 0) 1)) perm6) u v = (WeakRegions.root (128) (1538) (5885) (12) (46) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 0) 1)) perm6) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (128) (1538) (5885) (12) (46) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm6 hb)

theorem edge0_2 : Core (mutate (node 0) 2) ∨
    WeakForks.IsWeakFork (mutate (node 0) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 0) 2) 2 := by
  have he : mutate (node 0) 2 = reverse (relabel (strip0 0 2) perm16) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 0) 2) u v = (reverse (relabel (strip0 0 2) perm16)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.strip0 0 2) perm16))

theorem edge0_3 : Core (mutate (node 0) 3) ∨
    WeakForks.IsWeakFork (mutate (node 0) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 0) 3) 3 := by
  have he : mutate (node 0) 3 = relabel (node 1) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 0) 3) u v = (relabel (node 1) perm21) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 1) perm21)

theorem cyclic1 : ¬ Acyclic (node 1) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge1_0 : Core (mutate (node 1) 0) ∨
    WeakForks.IsWeakFork (mutate (node 1) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 1) 0) 0 := by
  have he : mutate (node 1) 0 = relabel (node 0) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 1) 0) u v = (relabel (node 0) perm21) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 0) perm21)

theorem edge1_1 : Core (mutate (node 1) 1) ∨
    WeakForks.IsWeakFork (mutate (node 1) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 1) 1) 1 := by
  right; right
  have he : relabel (reverse (mutate (node 1) 1)) perm6 = WeakRegions.root (46) (553) (457) (12) (10) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 1) 1)) perm6) u v = (WeakRegions.root (46) (553) (457) (12) (10) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 1) 1)) perm6) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (46) (553) (457) (12) (10) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm6 hb)

theorem edge1_2 : Core (mutate (node 1) 2) ∨
    WeakForks.IsWeakFork (mutate (node 1) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 1) 2) 2 := by
  have he : mutate (node 1) 2 = reverse (relabel (strip0 0 0) perm4) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 1) 2) u v = (reverse (relabel (strip0 0 0) perm4)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.strip0 0 0) perm4))

theorem edge1_3 : Core (mutate (node 1) 3) ∨
    WeakForks.IsWeakFork (mutate (node 1) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 1) 3) 3 := by
  have he : mutate (node 1) 3 = reverse (relabel (node 4) perm7) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 1) 3) u v = (reverse (relabel (node 4) perm7)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 4) perm7))

theorem cyclic2 : ¬ Acyclic (node 2) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge2_0 : Core (mutate (node 2) 0) ∨
    WeakForks.IsWeakFork (mutate (node 2) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 2) 0) 0 := by
  right; left
  have he : relabel (mutate (node 2) 0) perm5 = WeakForks.template (3) (2) (22) (5) (58) (2) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 2) 0) perm5) u v = (WeakForks.template (3) (2) (22) (5) (58) (2)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (mutate (node 2) 0) perm5) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (3) (2) (22) (5) (58) (2) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm5 hb

theorem edge2_1 : Core (mutate (node 2) 1) ∨
    WeakForks.IsWeakFork (mutate (node 2) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 2) 1) 1 := by
  right; right
  have he : relabel (reverse (mutate (node 2) 1)) perm6 = WeakRegions.root (22) (46) (173) (2) (8) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 2) 1)) perm6) u v = (WeakRegions.root (22) (46) (173) (2) (8) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 2) 1)) perm6) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (22) (46) (173) (2) (8) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm6 hb)

theorem edge2_2 : Core (mutate (node 2) 2) ∨
    WeakForks.IsWeakFork (mutate (node 2) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 2) 2) 2 := by
  have he : mutate (node 2) 2 = reverse (relabel (node 3) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 2) 2) u v = (reverse (relabel (node 3) perm6)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 3) perm6))

theorem edge2_3 : Core (mutate (node 2) 3) ∨
    WeakForks.IsWeakFork (mutate (node 2) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 2) 3) 3 := by
  have he : mutate (node 2) 3 = relabel (node 7) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 2) 3) u v = (relabel (node 7) perm21) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 7) perm21)

theorem cyclic3 : ¬ Acyclic (node 3) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge3_0 : Core (mutate (node 3) 0) ∨
    WeakForks.IsWeakFork (mutate (node 3) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 3) 0) 0 := by
  right; left
  have he : relabel (mutate (node 3) 0) perm5 = WeakForks.template (10) (2) (22) (19) (219) (2) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 3) 0) perm5) u v = (WeakForks.template (10) (2) (22) (19) (219) (2)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (mutate (node 3) 0) perm5) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (10) (2) (22) (19) (219) (2) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm5 hb

theorem edge3_1 : Core (mutate (node 3) 1) ∨
    WeakForks.IsWeakFork (mutate (node 3) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 3) 1) 1 := by
  have he : mutate (node 3) 1 = relabel (strip0 0 0) perm22 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 3) 1) u v = (relabel (strip0 0 0) perm22) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.strip0 0 0) perm22)

theorem edge3_2 : Core (mutate (node 3) 2) ∨
    WeakForks.IsWeakFork (mutate (node 3) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 3) 2) 2 := by
  have he : mutate (node 3) 2 = reverse (relabel (node 2) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 3) 2) u v = (reverse (relabel (node 2) perm6)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 2) perm6))

theorem edge3_3 : Core (mutate (node 3) 3) ∨
    WeakForks.IsWeakFork (mutate (node 3) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 3) 3) 3 := by
  have he : mutate (node 3) 3 = relabel (node 5) perm1 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 3) 3) u v = (relabel (node 5) perm1) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 5) perm1)

theorem cyclic4 : ¬ Acyclic (node 4) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge4_0 : Core (mutate (node 4) 0) ∨
    WeakForks.IsWeakFork (mutate (node 4) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 4) 0) 0 := by
  right; left
  have he : relabel (mutate (node 4) 0) perm4 = WeakForks.template (12) (16) (10) (190) (121) (3) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 4) 0) perm4) u v = (WeakForks.template (12) (16) (10) (190) (121) (3)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (mutate (node 4) 0) perm4) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (12) (16) (10) (190) (121) (3) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm4 hb

theorem edge4_1 : Core (mutate (node 4) 1) ∨
    WeakForks.IsWeakFork (mutate (node 4) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 4) 1) 1 := by
  right; left
  have he : relabel (reverse (mutate (node 4) 1)) perm10 = WeakForks.template (2) (16) (3) (20) (5) (10) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 4) 1)) perm10) u v = (WeakForks.template (2) (16) (3) (20) (5) (10)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (reverse (mutate (node 4) 1)) perm10) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (2) (16) (3) (20) (5) (10) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_reverse (WeakForks.fork_of_relabel perm10 hb)

theorem edge4_2 : Core (mutate (node 4) 2) ∨
    WeakForks.IsWeakFork (mutate (node 4) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 4) 2) 2 := by
  have he : mutate (node 4) 2 = reverse (relabel (node 1) perm7) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 4) 2) u v = (reverse (relabel (node 1) perm7)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 1) perm7))

theorem edge4_3 : Core (mutate (node 4) 3) ∨
    WeakForks.IsWeakFork (mutate (node 4) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 4) 3) 3 := by
  have he : mutate (node 4) 3 = relabel (node 5) perm5 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 4) 3) u v = (relabel (node 5) perm5) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 5) perm5)

theorem cyclic5 : ¬ Acyclic (node 5) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge5_0 : Core (mutate (node 5) 0) ∨
    WeakForks.IsWeakFork (mutate (node 5) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 5) 0) 0 := by
  right; right
  have he : relabel (reverse (mutate (node 5) 0)) perm5 = WeakRegions.root (8) (79) (94) (10) (12) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 5) 0)) perm5) u v = (WeakRegions.root (8) (79) (94) (10) (12) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 5) 0)) perm5) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (8) (79) (94) (10) (12) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm5 hb)

theorem edge5_1 : Core (mutate (node 5) 1) ∨
    WeakForks.IsWeakFork (mutate (node 5) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 5) 1) 1 := by
  have he : mutate (node 5) 1 = relabel (node 4) perm5 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 5) 1) u v = (relabel (node 4) perm5) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 4) perm5)

theorem edge5_2 : Core (mutate (node 5) 2) ∨
    WeakForks.IsWeakFork (mutate (node 5) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 5) 2) 2 := by
  have he : mutate (node 5) 2 = relabel (node 3) perm1 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 5) 2) u v = (relabel (node 3) perm1) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 3) perm1)

theorem edge5_3 : Core (mutate (node 5) 3) ∨
    WeakForks.IsWeakFork (mutate (node 5) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 5) 3) 3 := by
  have he : mutate (node 5) 3 = relabel (node 6) perm5 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 5) 3) u v = (relabel (node 6) perm5) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 6) perm5)

theorem cyclic6 : ¬ Acyclic (node 6) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge6_0 : Core (mutate (node 6) 0) ∨
    WeakForks.IsWeakFork (mutate (node 6) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 6) 0) 0 := by
  right; right
  have he : relabel (reverse (mutate (node 6) 0)) perm4 = WeakRegions.root (4) (30) (7) (8) (2) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 6) 0)) perm4) u v = (WeakRegions.root (4) (30) (7) (8) (2) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 6) 0)) perm4) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (4) (30) (7) (8) (2) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm4 hb)

theorem edge6_1 : Core (mutate (node 6) 1) ∨
    WeakForks.IsWeakFork (mutate (node 6) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 6) 1) 1 := by
  have he : mutate (node 6) 1 = relabel (node 5) perm5 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 6) 1) u v = (relabel (node 5) perm5) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 5) perm5)

theorem edge6_2 : Core (mutate (node 6) 2) ∨
    WeakForks.IsWeakFork (mutate (node 6) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 6) 2) 2 := by
  have he : mutate (node 6) 2 = reverse (relabel (node 7) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 6) 2) u v = (reverse (relabel (node 7) perm6)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 7) perm6))

theorem edge6_3 : Core (mutate (node 6) 3) ∨
    WeakForks.IsWeakFork (mutate (node 6) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 6) 3) 3 := by
  have he : mutate (node 6) 3 = relabel (node 9) perm3 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 6) 3) u v = (relabel (node 9) perm3) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 9) perm3)

theorem cyclic7 : ¬ Acyclic (node 7) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge7_0 : Core (mutate (node 7) 0) ∨
    WeakForks.IsWeakFork (mutate (node 7) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 7) 0) 0 := by
  have he : mutate (node 7) 0 = relabel (node 2) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 7) 0) u v = (relabel (node 2) perm21) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 2) perm21)

theorem edge7_1 : Core (mutate (node 7) 1) ∨
    WeakForks.IsWeakFork (mutate (node 7) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 7) 1) 1 := by
  right; right
  have he : relabel (reverse (mutate (node 7) 1)) perm6 = WeakRegions.root (8) (17) (13) (2) (2) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 7) 1)) perm6) u v = (WeakRegions.root (8) (17) (13) (2) (2) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 7) 1)) perm6) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (8) (17) (13) (2) (2) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm6 hb)

theorem edge7_2 : Core (mutate (node 7) 2) ∨
    WeakForks.IsWeakFork (mutate (node 7) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 7) 2) 2 := by
  have he : mutate (node 7) 2 = reverse (relabel (node 6) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 7) 2) u v = (reverse (relabel (node 6) perm6)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 6) perm6))

theorem edge7_3 : Core (mutate (node 7) 3) ∨
    WeakForks.IsWeakFork (mutate (node 7) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 7) 3) 3 := by
  have he : mutate (node 7) 3 = relabel (node 10) perm3 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 7) 3) u v = (relabel (node 10) perm3) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 10) perm3)

theorem cyclic8 : ¬ Acyclic (node 8) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge8_0 : Core (mutate (node 8) 0) ∨
    WeakForks.IsWeakFork (mutate (node 8) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 8) 0) 0 := by
  right; right
  have he : relabel (reverse (mutate (node 8) 0)) perm4 = WeakRegions.root (3) (10) (5) (4) (2) (0) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 8) 0)) perm4) u v = (WeakRegions.root (3) (10) (5) (4) (2) (0)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 8) 0)) perm4) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (3) (10) (5) (4) (2) (0) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm4 hb)

theorem edge8_1 : Core (mutate (node 8) 1) ∨
    WeakForks.IsWeakFork (mutate (node 8) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 8) 1) 1 := by
  have he : mutate (node 8) 1 = reverse (relabel (strip1 0 0) perm14) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 8) 1) u v = (reverse (relabel (strip1 0 0) perm14)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.strip1 0 0) perm14))

theorem edge8_2 : Core (mutate (node 8) 2) ∨
    WeakForks.IsWeakFork (mutate (node 8) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 8) 2) 2 := by
  have he : mutate (node 8) 2 = reverse (relabel (node 9) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 8) 2) u v = (reverse (relabel (node 9) perm6)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 9) perm6))

theorem edge8_3 : Core (mutate (node 8) 3) ∨
    WeakForks.IsWeakFork (mutate (node 8) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 8) 3) 3 := by
  have he : mutate (node 8) 3 = relabel (node 11) perm5 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 8) 3) u v = (relabel (node 11) perm5) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 11) perm5)

theorem cyclic9 : ¬ Acyclic (node 9) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge9_0 : Core (mutate (node 9) 0) ∨
    WeakForks.IsWeakFork (mutate (node 9) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 9) 0) 0 := by
  have he : mutate (node 9) 0 = relabel (strip1 0 1) perm8 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 9) 0) u v = (relabel (strip1 0 1) perm8) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.strip1 0 1) perm8)

theorem edge9_1 : Core (mutate (node 9) 1) ∨
    WeakForks.IsWeakFork (mutate (node 9) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 9) 1) 1 := by
  have he : mutate (node 9) 1 = relabel (node 6) perm4 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 9) 1) u v = (relabel (node 6) perm4) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 6) perm4)

theorem edge9_2 : Core (mutate (node 9) 2) ∨
    WeakForks.IsWeakFork (mutate (node 9) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 9) 2) 2 := by
  have he : mutate (node 9) 2 = reverse (relabel (node 8) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 9) 2) u v = (reverse (relabel (node 8) perm6)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 8) perm6))

theorem edge9_3 : Core (mutate (node 9) 3) ∨
    WeakForks.IsWeakFork (mutate (node 9) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 9) 3) 3 := by
  have he : mutate (node 9) 3 = relabel (node 12) perm3 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 9) 3) u v = (relabel (node 12) perm3) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 12) perm3)

theorem cyclic10 : ¬ Acyclic (node 10) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge10_0 : Core (mutate (node 10) 0) ∨
    WeakForks.IsWeakFork (mutate (node 10) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 10) 0) 0 := by
  right; left
  have he : relabel (mutate (node 10) 0) perm5 = WeakForks.template (2) (2) (3) (2) (5) (2) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 10) 0) perm5) u v = (WeakForks.template (2) (2) (3) (2) (5) (2)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (mutate (node 10) 0) perm5) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (2) (2) (3) (2) (5) (2) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm5 hb

theorem edge10_1 : Core (mutate (node 10) 1) ∨
    WeakForks.IsWeakFork (mutate (node 10) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 10) 1) 1 := by
  have he : mutate (node 10) 1 = relabel (node 7) perm4 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 10) 1) u v = (relabel (node 7) perm4) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 7) perm4)

theorem edge10_2 : Core (mutate (node 10) 2) ∨
    WeakForks.IsWeakFork (mutate (node 10) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 10) 2) 2 := by
  right; left
  have he : relabel (reverse (mutate (node 10) 2)) perm16 = WeakForks.template (2) (2) (2) (2) (5) (3) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 10) 2)) perm16) u v = (WeakForks.template (2) (2) (2) (2) (5) (3)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (reverse (mutate (node 10) 2)) perm16) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (2) (2) (2) (2) (5) (3) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_reverse (WeakForks.fork_of_relabel perm16 hb)

theorem edge10_3 : Core (mutate (node 10) 3) ∨
    WeakForks.IsWeakFork (mutate (node 10) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 10) 3) 3 := by
  have he : mutate (node 10) 3 = reverse (relabel (node 12) perm20) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 10) 3) u v = (reverse (relabel (node 12) perm20)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 12) perm20))

theorem cyclic11 : ¬ Acyclic (node 11) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (by decide)
  have h1 := hr 2 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge11_0 : Core (mutate (node 11) 0) ∨
    WeakForks.IsWeakFork (mutate (node 11) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 11) 0) 0 := by
  have he : mutate (node 11) 0 = reverse (relabel (node 8) perm19) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 11) 0) u v = (reverse (relabel (node 8) perm19)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 8) perm19))

theorem edge11_1 : Core (mutate (node 11) 1) ∨
    WeakForks.IsWeakFork (mutate (node 11) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 11) 1) 1 := by
  have he : mutate (node 11) 1 = relabel (node 8) perm5 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 11) 1) u v = (relabel (node 8) perm5) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 8) perm5)

theorem edge11_2 : Core (mutate (node 11) 2) ∨
    WeakForks.IsWeakFork (mutate (node 11) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 11) 2) 2 := by
  have he : mutate (node 11) 2 = relabel (node 14) perm0 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 11) 2) u v = (relabel (node 14) perm0) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 14) perm0)

theorem edge11_3 : Core (mutate (node 11) 3) ∨
    WeakForks.IsWeakFork (mutate (node 11) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 11) 3) 3 := by
  have he : mutate (node 11) 3 = relabel (node 15) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 11) 3) u v = (relabel (node 15) perm21) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 15) perm21)

theorem cyclic12 : ¬ Acyclic (node 12) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge12_0 : Core (mutate (node 12) 0) ∨
    WeakForks.IsWeakFork (mutate (node 12) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 12) 0) 0 := by
  right; right
  have he : relabel (reverse (mutate (node 12) 0)) perm4 = WeakRegions.root (2) (3) (2) (2) (2) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 12) 0)) perm4) u v = (WeakRegions.root (2) (3) (2) (2) (2) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 12) 0)) perm4) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (2) (3) (2) (2) (2) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm4 hb)

theorem edge12_1 : Core (mutate (node 12) 1) ∨
    WeakForks.IsWeakFork (mutate (node 12) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 12) 1) 1 := by
  have he : mutate (node 12) 1 = relabel (node 9) perm4 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 12) 1) u v = (relabel (node 9) perm4) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 9) perm4)

theorem edge12_2 : Core (mutate (node 12) 2) ∨
    WeakForks.IsWeakFork (mutate (node 12) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 12) 2) 2 := by
  have he : mutate (node 12) 2 = reverse (relabel (node 10) perm15) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 12) 2) u v = (reverse (relabel (node 10) perm15)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 10) perm15))

theorem edge12_3 : Core (mutate (node 12) 3) ∨
    WeakForks.IsWeakFork (mutate (node 12) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 12) 3) 3 := by
  have he : mutate (node 12) 3 = relabel (node 14) perm23 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 12) 3) u v = (relabel (node 14) perm23) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 14) perm23)

theorem cyclic13 : ¬ Acyclic (node 13) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge13_0 : Core (mutate (node 13) 0) ∨
    WeakForks.IsWeakFork (mutate (node 13) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 13) 0) 0 := by
  have he : mutate (node 13) 0 = relabel (node 13) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 13) 0) u v = (relabel (node 13) perm21) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 13) perm21)

theorem edge13_1 : Core (mutate (node 13) 1) ∨
    WeakForks.IsWeakFork (mutate (node 13) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 13) 1) 1 := by
  have he : mutate (node 13) 1 = relabel (node 14) perm5 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 13) 1) u v = (relabel (node 14) perm5) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 14) perm5)

theorem edge13_2 : Core (mutate (node 13) 2) ∨
    WeakForks.IsWeakFork (mutate (node 13) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 13) 2) 2 := by
  have he : mutate (node 13) 2 = relabel (node 15) perm19 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 13) 2) u v = (relabel (node 15) perm19) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 15) perm19)

theorem edge13_3 : Core (mutate (node 13) 3) ∨
    WeakForks.IsWeakFork (mutate (node 13) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 13) 3) 3 := by
  have he : mutate (node 13) 3 = relabel (node 13) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 13) 3) u v = (relabel (node 13) perm21) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 13) perm21)

theorem cyclic14 : ¬ Acyclic (node 14) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge14_0 : Core (mutate (node 14) 0) ∨
    WeakForks.IsWeakFork (mutate (node 14) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 14) 0) 0 := by
  have he : mutate (node 14) 0 = relabel (node 12) perm23 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 14) 0) u v = (relabel (node 12) perm23) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 12) perm23)

theorem edge14_1 : Core (mutate (node 14) 1) ∨
    WeakForks.IsWeakFork (mutate (node 14) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 14) 1) 1 := by
  have he : mutate (node 14) 1 = reverse (relabel (node 12) perm17) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 14) 1) u v = (reverse (relabel (node 12) perm17)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 12) perm17))

theorem edge14_2 : Core (mutate (node 14) 2) ∨
    WeakForks.IsWeakFork (mutate (node 14) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 14) 2) 2 := by
  have he : mutate (node 14) 2 = relabel (node 11) perm0 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 14) 2) u v = (relabel (node 11) perm0) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 11) perm0)

theorem edge14_3 : Core (mutate (node 14) 3) ∨
    WeakForks.IsWeakFork (mutate (node 14) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 14) 3) 3 := by
  have he : mutate (node 14) 3 = relabel (node 13) perm5 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 14) 3) u v = (relabel (node 13) perm5) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 13) perm5)

theorem cyclic15 : ¬ Acyclic (node 15) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge15_0 : Core (mutate (node 15) 0) ∨
    WeakForks.IsWeakFork (mutate (node 15) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 15) 0) 0 := by
  have he : mutate (node 15) 0 = relabel (node 11) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 15) 0) u v = (relabel (node 11) perm21) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 11) perm21)

theorem edge15_1 : Core (mutate (node 15) 1) ∨
    WeakForks.IsWeakFork (mutate (node 15) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 15) 1) 1 := by
  have he : mutate (node 15) 1 = relabel (node 15) perm4 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 15) 1) u v = (relabel (node 15) perm4) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 15) perm4)

theorem edge15_2 : Core (mutate (node 15) 2) ∨
    WeakForks.IsWeakFork (mutate (node 15) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 15) 2) 2 := by
  have he : mutate (node 15) 2 = relabel (node 13) perm11 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 15) 2) u v = (relabel (node 13) perm11) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 13) perm11)

theorem edge15_3 : Core (mutate (node 15) 3) ∨
    WeakForks.IsWeakFork (mutate (node 15) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 15) 3) 3 := by
  have he : mutate (node 15) 3 = relabel (node 15) perm3 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 15) 3) u v = (relabel (node 15) perm3) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 15) perm3)

theorem finite_skew (i : Fin 16) : SkewSymmetric (node i) := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 := by omega
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ofSix_skew _ _ _ _ _ _

theorem finite_cyclic (i : Fin 16) : ¬ Acyclic (node i) := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 := by omega
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · exact cyclic11
  · exact cyclic12
  · exact cyclic13
  · exact cyclic14
  · exact cyclic15

theorem finite_edges (i : Fin 16) (k : Fin 4) : Core (mutate (node i) k) ∨
    WeakForks.IsWeakFork (mutate (node i) k) k ∨ WeakRegions.IsRoot (mutate (node i) k) k := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 := by omega
  have hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hk with rfl|rfl|rfl|rfl
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
  · exact edge11_0
  · exact edge11_1
  · exact edge11_2
  · exact edge11_3
  · exact edge12_0
  · exact edge12_1
  · exact edge12_2
  · exact edge12_3
  · exact edge13_0
  · exact edge13_1
  · exact edge13_2
  · exact edge13_3
  · exact edge14_0
  · exact edge14_1
  · exact edge14_2
  · exact edge14_3
  · exact edge15_0
  · exact edge15_1
  · exact edge15_2
  · exact edge15_3

theorem parent0_0 : Core (mutate (GenericStrip.root 2 seed0.A seed0.H seed0.Z) 1) := by
  have he : mutate (GenericStrip.root 2 seed0.A seed0.H seed0.Z) 1 = reverse (relabel (node 1) perm3) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (GenericStrip.root 2 seed0.A seed0.H seed0.Z) 1) u v = (reverse (relabel (node 1) perm3)) u v from by decide) u v
  rw [he]
  exact Core.reversed (Core.framed (Core.finite 1) perm3)

theorem parent0_1 : Core (mutate (GenericStrip.root 2 seed0.A seed0.H seed0.Z) 2) := by
  have he : mutate (GenericStrip.root 2 seed0.A seed0.H seed0.Z) 2 = relabel (node 3) perm17 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (GenericStrip.root 2 seed0.A seed0.H seed0.Z) 2) u v = (relabel (node 3) perm17) u v from by decide) u v
  rw [he]
  exact Core.framed (Core.finite 3) perm17

theorem parent0_2 : Core (mutate (GenericStrip.phaseQ 2 seed0.A seed0.H seed0.Z) 0) := by
  have he : mutate (GenericStrip.phaseQ 2 seed0.A seed0.H seed0.Z) 0 = reverse (relabel (node 0) perm16) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (GenericStrip.phaseQ 2 seed0.A seed0.H seed0.Z) 0) u v = (reverse (relabel (node 0) perm16)) u v from by decide) u v
  rw [he]
  exact Core.reversed (Core.framed (Core.finite 0) perm16)

theorem address0 {B : Matrix 4} (h : StripSemantics.Core 2 seed0 Core B) : Core B := by
  induction h with
  | base h => exact h
  | strip n i => exact Core.strip0 n i
  | framed h p ih => exact Core.framed ih p
  | reversed h ih => exact Core.reversed ih

theorem parent1_0 : Core (UnitZeroStrip.parent 2 seed1 0) := by
  have he : UnitZeroStrip.parent 2 seed1 0 = reverse (relabel (node 8) perm14) := by
    funext u v
    exact (show ∀ u v : Fin 4, (UnitZeroStrip.parent 2 seed1 0) u v = (reverse (relabel (node 8) perm14)) u v from by decide) u v
  rw [he]
  exact Core.reversed (Core.framed (Core.finite 8) perm14)

theorem parent1_1 : Core (UnitZeroStrip.parent 2 seed1 1) := by
  have he : UnitZeroStrip.parent 2 seed1 1 = relabel (node 9) perm12 := by
    funext u v
    exact (show ∀ u v : Fin 4, (UnitZeroStrip.parent 2 seed1 1) u v = (relabel (node 9) perm12) u v from by decide) u v
  rw [he]
  exact Core.framed (Core.finite 9) perm12

theorem parents1 (p : Fin 2) : Core (UnitZeroStrip.parent 2 seed1 p) := by
  have hp : p=0 ∨ p=1 := by omega
  rcases hp with rfl|rfl
  · exact parent1_0
  · exact parent1_1

theorem core_skew {B : Matrix 4} (h : Core B) : SkewSymmetric B := by
  induction h with
  | finite i => exact finite_skew i
  | strip0 n i => exact GenericStrip.phase_skew _ _ _ _ _
  | strip1 n i => exact UnitZeroStrip.strip_skew _ _ _ _
  | framed h p ih => exact relabel_skew _ p ih
  | reversed h ih => exact reverse_skew _ ih

theorem core_cyclic {B : Matrix 4} (h : Core B) : ¬ Acyclic B := by
  induction h with
  | finite i => exact finite_cyclic i
  | strip0 n i => exact GenericStrip.phase_cyclic _ _ _ _ (GenericStrip.orbit_domain 2 seed0 domain0 n) i
  | strip1 n i => exact UnitZeroStrip.strip_cyclic _ _ domain1 _ _
  | framed h p ih => exact fun ha => ih ((acyclic_relabel_iff _ p).mp ha)
  | reversed h ih => exact fun ha => ih ((acyclic_reverse_iff _ (core_skew h)).mp ha)

theorem core_edges {B : Matrix 4} (h : Core B) (k : Fin 4) :
    Core (mutate B k) ∨ WeakForks.IsWeakFork (mutate B k) k ∨ WeakRegions.IsRoot (mutate B k) k := by
  induction h generalizing k with
  | finite i => exact finite_edges i k
  | strip0 n i =>
    rcases StripSemantics.strip_edges 2 seed0 Core domain0
      (.base parent0_0) (.base parent0_1) (.base parent0_2) n i k with hc|hf|hr
    · exact Or.inl (address0 hc)
    · exact Or.inr (Or.inl (strict_fork_weak hf))
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

/-- Exact source q235: unconditional NMA for every finite mutation word. -/
theorem nma_q235 : ¬ MutationAcyclic (ofSix (-2) (-2) (2) (-1) (-1) (-2)) := by
  have he : (ofSix (-2) (-2) (2) (-1) (-1) (-2)) = relabel (node 12) perm0 := by
    funext u v
    exact (show ∀ u v : Fin 4, ((ofSix (-2) (-2) (2) (-1) (-1) (-2))) u v = (relabel (node 12) perm0) u v from by decide) u v
  rw [he]
  exact core_NMA (Core.framed (Core.finite 12) perm0)

/-- Exact source q504: unconditional NMA for every finite mutation word. -/
theorem nma_q504 : ¬ MutationAcyclic (ofSix (-2) (-1) (2) (-1) (-2) (-2)) := by
  have he : (ofSix (-2) (-1) (2) (-1) (-2) (-2)) = reverse (relabel (node 12) perm23) := by
    funext u v
    exact (show ∀ u v : Fin 4, ((ofSix (-2) (-1) (2) (-1) (-2) (-2))) u v = (reverse (relabel (node 12) perm23)) u v from by decide) u v
  rw [he]
  exact core_NMA (Core.reversed (Core.framed (Core.finite 12) perm23))

/-- Exact source q515: unconditional NMA for every finite mutation word. -/
theorem nma_q515 : ¬ MutationAcyclic (ofSix (-2) (-1) (2) (0) (-2) (-1)) := by
  have he : (ofSix (-2) (-1) (2) (0) (-2) (-1)) = relabel (node 13) perm0 := by
    funext u v
    exact (show ∀ u v : Fin 4, ((ofSix (-2) (-1) (2) (0) (-2) (-1))) u v = (relabel (node 13) perm0) u v from by decide) u v
  rw [he]
  exact core_NMA (Core.framed (Core.finite 13) perm0)

/-- Exact source q524: unconditional NMA for every finite mutation word. -/
theorem nma_q524 : ¬ MutationAcyclic (ofSix (-2) (-1) (2) (1) (-2) (0)) := by
  have he : (ofSix (-2) (-1) (2) (1) (-2) (0)) = relabel (node 14) perm0 := by
    funext u v
    exact (show ∀ u v : Fin 4, ((ofSix (-2) (-1) (2) (1) (-2) (0))) u v = (relabel (node 14) perm0) u v from by decide) u v
  rw [he]
  exact core_NMA (Core.framed (Core.finite 14) perm0)

/-- Exact source q609: unconditional NMA for every finite mutation word. -/
theorem nma_q609 : ¬ MutationAcyclic (ofSix (-2) (0) (2) (-1) (-1) (-1)) := by
  have he : (ofSix (-2) (0) (2) (-1) (-1) (-1)) = relabel (node 15) perm0 := by
    funext u v
    exact (show ∀ u v : Fin 4, ((ofSix (-2) (0) (2) (-1) (-1) (-1))) u v = (relabel (node 15) perm0) u v from by decide) u v
  rw [he]
  exact core_NMA (Core.framed (Core.finite 15) perm0)

end QuiverProofs.HereditaryTriangleRegions03
