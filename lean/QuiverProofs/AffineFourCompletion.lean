import QuiverProofs.AffineFourLocal
import QuiverProofs.HereditaryTrianglePendant
import QuiverProofs.StripSemantics

/-! Exact finite core joined to unbounded G/N strips. Every entrance parent is checked. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace QuiverProofs.AffineFourCompletion
open ForkCertificates HereditaryTrianglePendant

def node (i : Fin 34) : Matrix 4 := match i.val with
  | 0 => (ofSix (-11650) (-7) (8) (-178) (-1460) (-1))
  | 1 => (ofSix (-4484) (-7) (8) (-68) (-562) (-1))
  | 2 => (ofSix (-1460) (-1) (8) (-178) (-30) (-1))
  | 3 => (ofSix (-1220) (-30) (178) (8) (-7) (1))
  | 4 => (ofSix (-562) (-1) (8) (-68) (-12) (-1))
  | 5 => (ofSix (-466) (-12) (68) (8) (-7) (1))
  | 6 => (ofSix (-208) (-7) (8) (-4) (-26) (-1))
  | 7 => (ofSix (-208) (-4) (30) (-7) (-1) (-1))
  | 8 => (ofSix (-178) (-30) (26) (1) (-7) (-1))
  | 9 => (ofSix (-80) (-7) (8) (-2) (-10) (-1))
  | 10 => (ofSix (-80) (-2) (12) (-7) (-1) (-1))
  | 11 => (ofSix (-68) (-12) (10) (1) (-7) (-1))
  | 12 => (ofSix (-34) (-7) (9) (0) (-4) (-1))
  | 13 => (ofSix (-34) (0) (4) (-7) (-2) (-1))
  | 14 => (ofSix (-26) (-8) (7) (0) (-4) (-1))
  | 15 => (ofSix (-26) (-4) (4) (-1) (-7) (-1))
  | 16 => (ofSix (-26) (-4) (4) (2) (-7) (-1))
  | 17 => (ofSix (-26) (-1) (8) (-4) (0) (-1))
  | 18 => (ofSix (-10) (-8) (7) (0) (-2) (-1))
  | 19 => (ofSix (-10) (-2) (2) (-1) (-7) (-1))
  | 20 => (ofSix (-10) (-1) (8) (-2) (0) (-1))
  | 21 => (ofSix (-9) (1) (4) (-2) (-2) (0))
  | 22 => (ofSix (-7) (-2) (2) (1) (-4) (0))
  | 23 => (ofSix (-7) (-1) (2) (-1) (-4) (0))
  | 24 => (ofSix (-7) (-1) (4) (-1) (-2) (0))
  | 25 => (ofSix (-4) (-2) (4) (-1) (1) (-2))
  | 26 => (ofSix (-4) (-2) (4) (1) (-1) (-1))
  | 27 => (ofSix (-4) (-1) (1) (-2) (0) (-2))
  | 28 => (ofSix (-4) (-1) (1) (0) (-2) (-2))
  | 29 => (ofSix (-4) (-1) (1) (0) (-2) (1))
  | 30 => (ofSix (-4) (0) (2) (-1) (-1) (1))
  | 31 => (ofSix (-2) (-2) (0) (-1) (1) (-2))
  | 32 => (ofSix (-2) (-2) (0) (-1) (2) (-1))
  | _ => (ofSix (-2) (-2) (2) (-1) (-1) (1))

def seed0 : Cone.State := ⟨562,68,80⟩
theorem domain0 : GenericStrip.Domain 7 seed0.A seed0.H seed0.Z := by unfold GenericStrip.Domain seed0; decide
def strip0 (n : Nat) (i : Fin 6) : Matrix 4 :=
  GenericStrip.phase 7 (GenericStrip.orbit 7 seed0 n).A (GenericStrip.orbit 7 seed0 n).H (GenericStrip.orbit 7 seed0 n).Z i
def seed1 : Cone.State := ⟨1460,178,208⟩
theorem domain1 : GenericStrip.Domain 7 seed1.A seed1.H seed1.Z := by unfold GenericStrip.Domain seed1; decide
def strip1 (n : Nat) (i : Fin 6) : Matrix 4 :=
  GenericStrip.phase 7 (GenericStrip.orbit 7 seed1 n).A (GenericStrip.orbit 7 seed1 n).H (GenericStrip.orbit 7 seed1 n).Z i
def seed2 : UnitZeroStrip.Parameters := ⟨8,10,13⟩
theorem domain2 : UnitZeroStrip.Domain 2 seed2.u seed2.v seed2.w := by unfold UnitZeroStrip.Domain seed2; decide
def strip2 (n : Nat) (i : Fin 10) : Matrix 4 := UnitZeroStrip.strip 2 seed2 n i
def seed3 : UnitZeroStrip.Parameters := ⟨7,34,127⟩
theorem domain3 : UnitZeroStrip.Domain 4 seed3.u seed3.v seed3.w := by unfold UnitZeroStrip.Domain seed3; decide
def strip3 (n : Nat) (i : Fin 10) : Matrix 4 := UnitZeroStrip.strip 4 seed3 n i
def seed4 : UnitZeroStrip.Parameters := ⟨8,26,97⟩
theorem domain4 : UnitZeroStrip.Domain 4 seed4.u seed4.v seed4.w := by unfold UnitZeroStrip.Domain seed4; decide
def strip4 (n : Nat) (i : Fin 10) : Matrix 4 := UnitZeroStrip.strip 4 seed4 n i

inductive Core : Matrix 4 → Prop
  | finite (i : Fin 34) : Core (node i)
  | affine (n : Int) (hn : 0≤n) (i : Fin 4) : Core (AffineFourLocal.tail n i)
  | strip0 (n : Nat) (i : Fin 6) : Core (strip0 n i)
  | strip1 (n : Nat) (i : Fin 6) : Core (strip1 n i)
  | strip2 (n : Nat) (i : Fin 10) : Core (strip2 n i)
  | strip3 (n : Nat) (i : Fin 10) : Core (strip3 n i)
  | strip4 (n : Nat) (i : Fin 10) : Core (strip4 n i)
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
  have he : relabel (mutate (node 0) 0) perm5 = WeakForks.template (8) (7) (11650) (55) (91740) (178) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 0) 0) perm5) u v = (WeakForks.template (8) (7) (11650) (55) (91740) (178)) u v from by decide +kernel) u v
  have hb : WeakForks.IsWeakFork (relabel (mutate (node 0) 0) perm5) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (8) (7) (11650) (55) (91740) (178) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm5 hb

theorem edge0_1 : Core (mutate (node 0) 1) ∨
    WeakForks.IsWeakFork (mutate (node 0) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 0) 1) 1 := by
  right; right
  have he : relabel (reverse (mutate (node 0) 1)) perm6 = WeakRegions.root (11650) (2073707) (17008992) (178) (1460) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 0) 1)) perm6) u v = (WeakRegions.root (11650) (2073707) (17008992) (178) (1460) (1)) u v from by decide +kernel) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 0) 1)) perm6) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (11650) (2073707) (17008992) (178) (1460) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm6 hb)

theorem edge0_2 : Core (mutate (node 0) 2) ∨
    WeakForks.IsWeakFork (mutate (node 0) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 0) 2) 2 := by
  have he : mutate (node 0) 2 = reverse (relabel (strip1 0 2) perm16) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 0) 2) u v = (reverse (relabel (strip1 0 2) perm16)) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.strip1 0 2) perm16))

theorem edge0_3 : Core (mutate (node 0) 3) ∨
    WeakForks.IsWeakFork (mutate (node 0) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 0) 3) 3 := by
  have he : mutate (node 0) 3 = relabel (node 2) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 0) 3) u v = (relabel (node 2) perm21) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 2) perm21)

theorem cyclic1 : ¬ Acyclic (node 1) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge1_0 : Core (mutate (node 1) 0) ∨
    WeakForks.IsWeakFork (mutate (node 1) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 1) 0) 0 := by
  right; left
  have he : relabel (mutate (node 1) 0) perm5 = WeakForks.template (8) (7) (4484) (55) (35310) (68) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 1) 0) perm5) u v = (WeakForks.template (8) (7) (4484) (55) (35310) (68)) u v from by decide +kernel) u v
  have hb : WeakForks.IsWeakFork (relabel (mutate (node 1) 0) perm5) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (8) (7) (4484) (55) (35310) (68) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm5 hb

theorem edge1_1 : Core (mutate (node 1) 1) ∨
    WeakForks.IsWeakFork (mutate (node 1) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 1) 1) 1 := by
  right; right
  have he : relabel (reverse (mutate (node 1) 1)) perm6 = WeakRegions.root (4484) (304919) (2520000) (68) (562) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 1) 1)) perm6) u v = (WeakRegions.root (4484) (304919) (2520000) (68) (562) (1)) u v from by decide +kernel) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 1) 1)) perm6) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (4484) (304919) (2520000) (68) (562) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm6 hb)

theorem edge1_2 : Core (mutate (node 1) 2) ∨
    WeakForks.IsWeakFork (mutate (node 1) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 1) 2) 2 := by
  have he : mutate (node 1) 2 = reverse (relabel (strip0 0 2) perm16) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 1) 2) u v = (reverse (relabel (strip0 0 2) perm16)) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.strip0 0 2) perm16))

theorem edge1_3 : Core (mutate (node 1) 3) ∨
    WeakForks.IsWeakFork (mutate (node 1) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 1) 3) 3 := by
  have he : mutate (node 1) 3 = relabel (node 4) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 1) 3) u v = (relabel (node 4) perm21) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 4) perm21)

theorem cyclic2 : ¬ Acyclic (node 2) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge2_0 : Core (mutate (node 2) 0) ∨
    WeakForks.IsWeakFork (mutate (node 2) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 2) 0) 0 := by
  have he : mutate (node 2) 0 = relabel (node 0) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 2) 0) u v = (relabel (node 0) perm21) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 0) perm21)

theorem edge2_1 : Core (mutate (node 2) 1) ∨
    WeakForks.IsWeakFork (mutate (node 2) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 2) 1) 1 := by
  right; right
  have he : relabel (reverse (mutate (node 2) 1)) perm6 = WeakRegions.root (1460) (259881) (43792) (178) (30) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 2) 1)) perm6) u v = (WeakRegions.root (1460) (259881) (43792) (178) (30) (1)) u v from by decide +kernel) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 2) 1)) perm6) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (1460) (259881) (43792) (178) (30) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm6 hb)

theorem edge2_2 : Core (mutate (node 2) 2) ∨
    WeakForks.IsWeakFork (mutate (node 2) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 2) 2) 2 := by
  have he : mutate (node 2) 2 = reverse (relabel (strip1 0 0) perm4) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 2) 2) u v = (reverse (relabel (strip1 0 0) perm4)) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.strip1 0 0) perm4))

theorem edge2_3 : Core (mutate (node 2) 3) ∨
    WeakForks.IsWeakFork (mutate (node 2) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 2) 3) 3 := by
  have he : mutate (node 2) 3 = reverse (relabel (node 3) perm7) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 2) 3) u v = (reverse (relabel (node 3) perm7)) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 3) perm7))

theorem cyclic3 : ¬ Acyclic (node 3) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge3_0 : Core (mutate (node 3) 0) ∨
    WeakForks.IsWeakFork (mutate (node 3) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 3) 0) 0 := by
  right; left
  have he : relabel (mutate (node 3) 0) perm4 = WeakForks.template (178) (1220) (30) (217153) (5341) (8) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 3) 0) perm4) u v = (WeakForks.template (178) (1220) (30) (217153) (5341) (8)) u v from by decide +kernel) u v
  have hb : WeakForks.IsWeakFork (relabel (mutate (node 3) 0) perm4) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (178) (1220) (30) (217153) (5341) (8) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm4 hb

theorem edge3_1 : Core (mutate (node 3) 1) ∨
    WeakForks.IsWeakFork (mutate (node 3) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 3) 1) 1 := by
  right; left
  have he : relabel (reverse (mutate (node 3) 1)) perm10 = WeakForks.template (7) (1220) (8) (8362) (55) (30) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 3) 1)) perm10) u v = (WeakForks.template (7) (1220) (8) (8362) (55) (30)) u v from by decide +kernel) u v
  have hb : WeakForks.IsWeakFork (relabel (reverse (mutate (node 3) 1)) perm10) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (7) (1220) (8) (8362) (55) (30) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_reverse (WeakForks.fork_of_relabel perm10 hb)

theorem edge3_2 : Core (mutate (node 3) 2) ∨
    WeakForks.IsWeakFork (mutate (node 3) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 3) 2) 2 := by
  have he : mutate (node 3) 2 = reverse (relabel (node 2) perm7) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 3) 2) u v = (reverse (relabel (node 2) perm7)) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 2) perm7))

theorem edge3_3 : Core (mutate (node 3) 3) ∨
    WeakForks.IsWeakFork (mutate (node 3) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 3) 3) 3 := by
  have he : mutate (node 3) 3 = relabel (node 8) perm5 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 3) 3) u v = (relabel (node 8) perm5) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 8) perm5)

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
    exact (show ∀ u v : Fin 4, (mutate (node 4) 0) u v = (relabel (node 1) perm21) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 1) perm21)

theorem edge4_1 : Core (mutate (node 4) 1) ∨
    WeakForks.IsWeakFork (mutate (node 4) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 4) 1) 1 := by
  right; right
  have he : relabel (reverse (mutate (node 4) 1)) perm6 = WeakRegions.root (562) (38217) (6736) (68) (12) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 4) 1)) perm6) u v = (WeakRegions.root (562) (38217) (6736) (68) (12) (1)) u v from by decide +kernel) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 4) 1)) perm6) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (562) (38217) (6736) (68) (12) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm6 hb)

theorem edge4_2 : Core (mutate (node 4) 2) ∨
    WeakForks.IsWeakFork (mutate (node 4) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 4) 2) 2 := by
  have he : mutate (node 4) 2 = reverse (relabel (strip0 0 0) perm4) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 4) 2) u v = (reverse (relabel (strip0 0 0) perm4)) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.strip0 0 0) perm4))

theorem edge4_3 : Core (mutate (node 4) 3) ∨
    WeakForks.IsWeakFork (mutate (node 4) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 4) 3) 3 := by
  have he : mutate (node 4) 3 = reverse (relabel (node 5) perm7) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 4) 3) u v = (reverse (relabel (node 5) perm7)) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 5) perm7))

theorem cyclic5 : ¬ Acyclic (node 5) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge5_0 : Core (mutate (node 5) 0) ∨
    WeakForks.IsWeakFork (mutate (node 5) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 5) 0) 0 := by
  right; left
  have he : relabel (mutate (node 5) 0) perm4 = WeakForks.template (68) (466) (12) (31681) (817) (8) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 5) 0) perm4) u v = (WeakForks.template (68) (466) (12) (31681) (817) (8)) u v from by decide +kernel) u v
  have hb : WeakForks.IsWeakFork (relabel (mutate (node 5) 0) perm4) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (68) (466) (12) (31681) (817) (8) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm4 hb

theorem edge5_1 : Core (mutate (node 5) 1) ∨
    WeakForks.IsWeakFork (mutate (node 5) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 5) 1) 1 := by
  right; left
  have he : relabel (reverse (mutate (node 5) 1)) perm10 = WeakForks.template (7) (466) (8) (3194) (55) (12) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 5) 1)) perm10) u v = (WeakForks.template (7) (466) (8) (3194) (55) (12)) u v from by decide +kernel) u v
  have hb : WeakForks.IsWeakFork (relabel (reverse (mutate (node 5) 1)) perm10) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (7) (466) (8) (3194) (55) (12) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_reverse (WeakForks.fork_of_relabel perm10 hb)

theorem edge5_2 : Core (mutate (node 5) 2) ∨
    WeakForks.IsWeakFork (mutate (node 5) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 5) 2) 2 := by
  have he : mutate (node 5) 2 = reverse (relabel (node 4) perm7) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 5) 2) u v = (reverse (relabel (node 4) perm7)) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 4) perm7))

theorem edge5_3 : Core (mutate (node 5) 3) ∨
    WeakForks.IsWeakFork (mutate (node 5) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 5) 3) 3 := by
  have he : mutate (node 5) 3 = relabel (node 11) perm5 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 5) 3) u v = (relabel (node 11) perm5) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 11) perm5)

theorem cyclic6 : ¬ Acyclic (node 6) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge6_0 : Core (mutate (node 6) 0) ∨
    WeakForks.IsWeakFork (mutate (node 6) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 6) 0) 0 := by
  right; left
  have he : relabel (mutate (node 6) 0) perm5 = WeakForks.template (8) (7) (208) (55) (1638) (4) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 6) 0) perm5) u v = (WeakForks.template (8) (7) (208) (55) (1638) (4)) u v from by decide +kernel) u v
  have hb : WeakForks.IsWeakFork (relabel (mutate (node 6) 0) perm5) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (8) (7) (208) (55) (1638) (4) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm5 hb

theorem edge6_1 : Core (mutate (node 6) 1) ∨
    WeakForks.IsWeakFork (mutate (node 6) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 6) 1) 1 := by
  right; right
  have he : relabel (reverse (mutate (node 6) 1)) perm6 = WeakRegions.root (208) (839) (5400) (4) (26) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 6) 1)) perm6) u v = (WeakRegions.root (208) (839) (5400) (4) (26) (1)) u v from by decide +kernel) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 6) 1)) perm6) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (208) (839) (5400) (4) (26) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm6 hb)

theorem edge6_2 : Core (mutate (node 6) 2) ∨
    WeakForks.IsWeakFork (mutate (node 6) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 6) 2) 2 := by
  have he : mutate (node 6) 2 = reverse (relabel (node 7) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 6) 2) u v = (reverse (relabel (node 7) perm6)) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 7) perm6))

theorem edge6_3 : Core (mutate (node 6) 3) ∨
    WeakForks.IsWeakFork (mutate (node 6) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 6) 3) 3 := by
  have he : mutate (node 6) 3 = relabel (node 17) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 6) 3) u v = (relabel (node 17) perm21) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 17) perm21)

theorem cyclic7 : ¬ Acyclic (node 7) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge7_0 : Core (mutate (node 7) 0) ∨
    WeakForks.IsWeakFork (mutate (node 7) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 7) 0) 0 := by
  right; left
  have he : relabel (mutate (node 7) 0) perm5 = WeakForks.template (30) (4) (208) (119) (6239) (7) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 7) 0) perm5) u v = (WeakForks.template (30) (4) (208) (119) (6239) (7)) u v from by decide +kernel) u v
  have hb : WeakForks.IsWeakFork (relabel (mutate (node 7) 0) perm5) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (30) (4) (208) (119) (6239) (7) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm5 hb

theorem edge7_1 : Core (mutate (node 7) 1) ∨
    WeakForks.IsWeakFork (mutate (node 7) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 7) 1) 1 := by
  have he : mutate (node 7) 1 = relabel (strip1 0 0) perm22 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 7) 1) u v = (relabel (strip1 0 0) perm22) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.framed (Core.strip1 0 0) perm22)

theorem edge7_2 : Core (mutate (node 7) 2) ∨
    WeakForks.IsWeakFork (mutate (node 7) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 7) 2) 2 := by
  have he : mutate (node 7) 2 = reverse (relabel (node 6) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 7) 2) u v = (reverse (relabel (node 6) perm6)) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 6) perm6))

theorem edge7_3 : Core (mutate (node 7) 3) ∨
    WeakForks.IsWeakFork (mutate (node 7) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 7) 3) 3 := by
  have he : mutate (node 7) 3 = relabel (node 8) perm1 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 7) 3) u v = (relabel (node 8) perm1) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 8) perm1)

theorem cyclic8 : ¬ Acyclic (node 8) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge8_0 : Core (mutate (node 8) 0) ∨
    WeakForks.IsWeakFork (mutate (node 8) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 8) 0) 0 := by
  right; right
  have he : relabel (reverse (mutate (node 8) 0)) perm5 = WeakRegions.root (26) (779) (4621) (30) (178) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 8) 0)) perm5) u v = (WeakRegions.root (26) (779) (4621) (30) (178) (1)) u v from by decide +kernel) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 8) 0)) perm5) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (26) (779) (4621) (30) (178) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm5 hb)

theorem edge8_1 : Core (mutate (node 8) 1) ∨
    WeakForks.IsWeakFork (mutate (node 8) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 8) 1) 1 := by
  have he : mutate (node 8) 1 = relabel (node 3) perm5 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 8) 1) u v = (relabel (node 3) perm5) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 3) perm5)

theorem edge8_2 : Core (mutate (node 8) 2) ∨
    WeakForks.IsWeakFork (mutate (node 8) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 8) 2) 2 := by
  have he : mutate (node 8) 2 = relabel (node 7) perm1 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 8) 2) u v = (relabel (node 7) perm1) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 7) perm1)

theorem edge8_3 : Core (mutate (node 8) 3) ∨
    WeakForks.IsWeakFork (mutate (node 8) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 8) 3) 3 := by
  have he : mutate (node 8) 3 = relabel (node 15) perm5 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 8) 3) u v = (relabel (node 15) perm5) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 15) perm5)

theorem cyclic9 : ¬ Acyclic (node 9) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge9_0 : Core (mutate (node 9) 0) ∨
    WeakForks.IsWeakFork (mutate (node 9) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 9) 0) 0 := by
  right; left
  have he : relabel (mutate (node 9) 0) perm5 = WeakForks.template (8) (7) (80) (55) (630) (2) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 9) 0) perm5) u v = (WeakForks.template (8) (7) (80) (55) (630) (2)) u v from by decide +kernel) u v
  have hb : WeakForks.IsWeakFork (relabel (mutate (node 9) 0) perm5) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (8) (7) (80) (55) (630) (2) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm5 hb

theorem edge9_1 : Core (mutate (node 9) 1) ∨
    WeakForks.IsWeakFork (mutate (node 9) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 9) 1) 1 := by
  right; right
  have he : relabel (reverse (mutate (node 9) 1)) perm6 = WeakRegions.root (80) (167) (792) (2) (10) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 9) 1)) perm6) u v = (WeakRegions.root (80) (167) (792) (2) (10) (1)) u v from by decide +kernel) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 9) 1)) perm6) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (80) (167) (792) (2) (10) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm6 hb)

theorem edge9_2 : Core (mutate (node 9) 2) ∨
    WeakForks.IsWeakFork (mutate (node 9) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 9) 2) 2 := by
  have he : mutate (node 9) 2 = reverse (relabel (node 10) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 9) 2) u v = (reverse (relabel (node 10) perm6)) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 10) perm6))

theorem edge9_3 : Core (mutate (node 9) 3) ∨
    WeakForks.IsWeakFork (mutate (node 9) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 9) 3) 3 := by
  have he : mutate (node 9) 3 = relabel (node 20) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 9) 3) u v = (relabel (node 20) perm21) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 20) perm21)

theorem cyclic10 : ¬ Acyclic (node 10) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge10_0 : Core (mutate (node 10) 0) ∨
    WeakForks.IsWeakFork (mutate (node 10) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 10) 0) 0 := by
  right; left
  have he : relabel (mutate (node 10) 0) perm5 = WeakForks.template (12) (2) (80) (23) (959) (7) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 10) 0) perm5) u v = (WeakForks.template (12) (2) (80) (23) (959) (7)) u v from by decide +kernel) u v
  have hb : WeakForks.IsWeakFork (relabel (mutate (node 10) 0) perm5) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (12) (2) (80) (23) (959) (7) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm5 hb

theorem edge10_1 : Core (mutate (node 10) 1) ∨
    WeakForks.IsWeakFork (mutate (node 10) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 10) 1) 1 := by
  have he : mutate (node 10) 1 = relabel (strip0 0 0) perm22 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 10) 1) u v = (relabel (strip0 0 0) perm22) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.framed (Core.strip0 0 0) perm22)

theorem edge10_2 : Core (mutate (node 10) 2) ∨
    WeakForks.IsWeakFork (mutate (node 10) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 10) 2) 2 := by
  have he : mutate (node 10) 2 = reverse (relabel (node 9) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 10) 2) u v = (reverse (relabel (node 9) perm6)) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 9) perm6))

theorem edge10_3 : Core (mutate (node 10) 3) ∨
    WeakForks.IsWeakFork (mutate (node 10) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 10) 3) 3 := by
  have he : mutate (node 10) 3 = relabel (node 11) perm1 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 10) 3) u v = (relabel (node 11) perm1) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 11) perm1)

theorem cyclic11 : ¬ Acyclic (node 11) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge11_0 : Core (mutate (node 11) 0) ∨
    WeakForks.IsWeakFork (mutate (node 11) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 11) 0) 0 := by
  right; right
  have he : relabel (reverse (mutate (node 11) 0)) perm5 = WeakRegions.root (10) (119) (673) (12) (68) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 11) 0)) perm5) u v = (WeakRegions.root (10) (119) (673) (12) (68) (1)) u v from by decide +kernel) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 11) 0)) perm5) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (10) (119) (673) (12) (68) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm5 hb)

theorem edge11_1 : Core (mutate (node 11) 1) ∨
    WeakForks.IsWeakFork (mutate (node 11) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 11) 1) 1 := by
  have he : mutate (node 11) 1 = relabel (node 5) perm5 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 11) 1) u v = (relabel (node 5) perm5) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 5) perm5)

theorem edge11_2 : Core (mutate (node 11) 2) ∨
    WeakForks.IsWeakFork (mutate (node 11) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 11) 2) 2 := by
  have he : mutate (node 11) 2 = relabel (node 10) perm1 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 11) 2) u v = (relabel (node 10) perm1) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 10) perm1)

theorem edge11_3 : Core (mutate (node 11) 3) ∨
    WeakForks.IsWeakFork (mutate (node 11) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 11) 3) 3 := by
  have he : mutate (node 11) 3 = relabel (node 19) perm5 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 11) 3) u v = (relabel (node 19) perm5) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 19) perm5)

theorem cyclic12 : ¬ Acyclic (node 12) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge12_0 : Core (mutate (node 12) 0) ∨
    WeakForks.IsWeakFork (mutate (node 12) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 12) 0) 0 := by
  right; right
  have he : relabel (reverse (mutate (node 12) 0)) perm4 = WeakRegions.root (9) (302) (62) (34) (7) (0) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 12) 0)) perm4) u v = (WeakRegions.root (9) (302) (62) (34) (7) (0)) u v from by decide +kernel) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 12) 0)) perm4) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (9) (302) (62) (34) (7) (0) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm4 hb)

theorem edge12_1 : Core (mutate (node 12) 1) ∨
    WeakForks.IsWeakFork (mutate (node 12) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 12) 1) 1 := by
  have he : mutate (node 12) 1 = reverse (relabel (strip3 0 0) perm14) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 12) 1) u v = (reverse (relabel (strip3 0 0) perm14)) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.strip3 0 0) perm14))

theorem edge12_2 : Core (mutate (node 12) 2) ∨
    WeakForks.IsWeakFork (mutate (node 12) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 12) 2) 2 := by
  have he : mutate (node 12) 2 = reverse (relabel (node 13) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 12) 2) u v = (reverse (relabel (node 13) perm6)) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 13) perm6))

theorem edge12_3 : Core (mutate (node 12) 3) ∨
    WeakForks.IsWeakFork (mutate (node 12) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 12) 3) 3 := by
  have he : mutate (node 12) 3 = reverse (relabel (node 21) perm11) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 12) 3) u v = (reverse (relabel (node 21) perm11)) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 21) perm11))

theorem cyclic13 : ¬ Acyclic (node 13) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge13_0 : Core (mutate (node 13) 0) ∨
    WeakForks.IsWeakFork (mutate (node 13) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 13) 0) 0 := by
  have he : mutate (node 13) 0 = relabel (strip3 0 1) perm8 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 13) 0) u v = (relabel (strip3 0 1) perm8) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.framed (Core.strip3 0 1) perm8)

theorem edge13_1 : Core (mutate (node 13) 1) ∨
    WeakForks.IsWeakFork (mutate (node 13) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 13) 1) 1 := by
  right; right
  have he : relabel (reverse (mutate (node 13) 1)) perm6 = WeakRegions.root (34) (238) (64) (7) (2) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 13) 1)) perm6) u v = (WeakRegions.root (34) (238) (64) (7) (2) (1)) u v from by decide +kernel) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 13) 1)) perm6) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (34) (238) (64) (7) (2) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm6 hb)

theorem edge13_2 : Core (mutate (node 13) 2) ∨
    WeakForks.IsWeakFork (mutate (node 13) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 13) 2) 2 := by
  have he : mutate (node 13) 2 = reverse (relabel (node 12) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 13) 2) u v = (reverse (relabel (node 12) perm6)) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 12) perm6))

theorem edge13_3 : Core (mutate (node 13) 3) ∨
    WeakForks.IsWeakFork (mutate (node 13) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 13) 3) 3 := by
  have he : mutate (node 13) 3 = relabel (node 16) perm1 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 13) 3) u v = (relabel (node 16) perm1) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 16) perm1)

theorem cyclic14 : ¬ Acyclic (node 14) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge14_0 : Core (mutate (node 14) 0) ∨
    WeakForks.IsWeakFork (mutate (node 14) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 14) 0) 0 := by
  right; right
  have he : relabel (reverse (mutate (node 14) 0)) perm4 = WeakRegions.root (7) (178) (55) (26) (8) (0) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 14) 0)) perm4) u v = (WeakRegions.root (7) (178) (55) (26) (8) (0)) u v from by decide +kernel) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 14) 0)) perm4) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (7) (178) (55) (26) (8) (0) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm4 hb)

theorem edge14_1 : Core (mutate (node 14) 1) ∨
    WeakForks.IsWeakFork (mutate (node 14) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 14) 1) 1 := by
  have he : mutate (node 14) 1 = reverse (relabel (strip4 0 0) perm14) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 14) 1) u v = (reverse (relabel (strip4 0 0) perm14)) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.strip4 0 0) perm14))

theorem edge14_2 : Core (mutate (node 14) 2) ∨
    WeakForks.IsWeakFork (mutate (node 14) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 14) 2) 2 := by
  have he : mutate (node 14) 2 = relabel (node 17) perm1 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 14) 2) u v = (relabel (node 17) perm1) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 17) perm1)

theorem edge14_3 : Core (mutate (node 14) 3) ∨
    WeakForks.IsWeakFork (mutate (node 14) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 14) 3) 3 := by
  have he : mutate (node 14) 3 = relabel (node 23) perm5 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 14) 3) u v = (relabel (node 23) perm5) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 23) perm5)

theorem cyclic15 : ¬ Acyclic (node 15) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge15_0 : Core (mutate (node 15) 0) ∨
    WeakForks.IsWeakFork (mutate (node 15) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 15) 0) 0 := by
  right; right
  have he : relabel (reverse (mutate (node 15) 0)) perm4 = WeakRegions.root (4) (97) (15) (26) (4) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 15) 0)) perm4) u v = (WeakRegions.root (4) (97) (15) (26) (4) (1)) u v from by decide +kernel) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 15) 0)) perm4) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (4) (97) (15) (26) (4) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm4 hb)

theorem edge15_1 : Core (mutate (node 15) 1) ∨
    WeakForks.IsWeakFork (mutate (node 15) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 15) 1) 1 := by
  have he : mutate (node 15) 1 = relabel (node 8) perm5 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 15) 1) u v = (relabel (node 8) perm5) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 8) perm5)

theorem edge15_2 : Core (mutate (node 15) 2) ∨
    WeakForks.IsWeakFork (mutate (node 15) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 15) 2) 2 := by
  have he : mutate (node 15) 2 = reverse (relabel (node 17) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 15) 2) u v = (reverse (relabel (node 17) perm6)) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 17) perm6))

theorem edge15_3 : Core (mutate (node 15) 3) ∨
    WeakForks.IsWeakFork (mutate (node 15) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 15) 3) 3 := by
  have he : mutate (node 15) 3 = relabel (node 24) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 15) 3) u v = (relabel (node 24) perm21) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 24) perm21)

theorem cyclic16 : ¬ Acyclic (node 16) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge16_0 : Core (mutate (node 16) 0) ∨
    WeakForks.IsWeakFork (mutate (node 16) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 16) 0) 0 := by
  right; left
  have he : relabel (mutate (node 16) 0) perm4 = WeakForks.template (4) (26) (4) (97) (15) (2) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 16) 0) perm4) u v = (WeakForks.template (4) (26) (4) (97) (15) (2)) u v from by decide +kernel) u v
  have hb : WeakForks.IsWeakFork (relabel (mutate (node 16) 0) perm4) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (4) (26) (4) (97) (15) (2) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm4 hb

theorem edge16_1 : Core (mutate (node 16) 1) ∨
    WeakForks.IsWeakFork (mutate (node 16) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 16) 1) 1 := by
  right; left
  have he : relabel (reverse (mutate (node 16) 1)) perm10 = WeakForks.template (7) (26) (2) (178) (15) (4) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 16) 1)) perm10) u v = (WeakForks.template (7) (26) (2) (178) (15) (4)) u v from by decide +kernel) u v
  have hb : WeakForks.IsWeakFork (relabel (reverse (mutate (node 16) 1)) perm10) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (7) (26) (2) (178) (15) (4) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_reverse (WeakForks.fork_of_relabel perm10 hb)

theorem edge16_2 : Core (mutate (node 16) 2) ∨
    WeakForks.IsWeakFork (mutate (node 16) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 16) 2) 2 := by
  have he : mutate (node 16) 2 = relabel (node 13) perm1 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 16) 2) u v = (relabel (node 13) perm1) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 13) perm1)

theorem edge16_3 : Core (mutate (node 16) 3) ∨
    WeakForks.IsWeakFork (mutate (node 16) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 16) 3) 3 := by
  have he : mutate (node 16) 3 = reverse (relabel (node 22) perm19) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 16) 3) u v = (reverse (relabel (node 22) perm19)) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 22) perm19))

theorem cyclic17 : ¬ Acyclic (node 17) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 2 (by decide)
  have h2 := hr 2 0 (by decide)
  omega

theorem edge17_0 : Core (mutate (node 17) 0) ∨
    WeakForks.IsWeakFork (mutate (node 17) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 17) 0) 0 := by
  have he : mutate (node 17) 0 = relabel (node 6) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 17) 0) u v = (relabel (node 6) perm21) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 6) perm21)

theorem edge17_1 : Core (mutate (node 17) 1) ∨
    WeakForks.IsWeakFork (mutate (node 17) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 17) 1) 1 := by
  have he : mutate (node 17) 1 = reverse (relabel (strip4 0 1) perm15) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 17) 1) u v = (reverse (relabel (strip4 0 1) perm15)) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.strip4 0 1) perm15))

theorem edge17_2 : Core (mutate (node 17) 2) ∨
    WeakForks.IsWeakFork (mutate (node 17) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 17) 2) 2 := by
  have he : mutate (node 17) 2 = reverse (relabel (node 15) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 17) 2) u v = (reverse (relabel (node 15) perm6)) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 15) perm6))

theorem edge17_3 : Core (mutate (node 17) 3) ∨
    WeakForks.IsWeakFork (mutate (node 17) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 17) 3) 3 := by
  have he : mutate (node 17) 3 = relabel (node 14) perm1 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 17) 3) u v = (relabel (node 14) perm1) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 14) perm1)

theorem cyclic18 : ¬ Acyclic (node 18) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge18_0 : Core (mutate (node 18) 0) ∨
    WeakForks.IsWeakFork (mutate (node 18) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 18) 0) 0 := by
  right; right
  have he : relabel (reverse (mutate (node 18) 0)) perm4 = WeakRegions.root (7) (68) (55) (10) (8) (0) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 18) 0)) perm4) u v = (WeakRegions.root (7) (68) (55) (10) (8) (0)) u v from by decide +kernel) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 18) 0)) perm4) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (7) (68) (55) (10) (8) (0) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm4 hb)

theorem edge18_1 : Core (mutate (node 18) 1) ∨
    WeakForks.IsWeakFork (mutate (node 18) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 18) 1) 1 := by
  have he : mutate (node 18) 1 = reverse (relabel (strip2 0 0) perm14) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 18) 1) u v = (reverse (relabel (strip2 0 0) perm14)) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.strip2 0 0) perm14))

theorem edge18_2 : Core (mutate (node 18) 2) ∨
    WeakForks.IsWeakFork (mutate (node 18) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 18) 2) 2 := by
  have he : mutate (node 18) 2 = relabel (node 20) perm1 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 18) 2) u v = (relabel (node 20) perm1) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 20) perm1)

theorem edge18_3 : Core (mutate (node 18) 3) ∨
    WeakForks.IsWeakFork (mutate (node 18) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 18) 3) 3 := by
  have he : mutate (node 18) 3 = relabel (node 24) perm5 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 18) 3) u v = (relabel (node 24) perm5) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 24) perm5)

theorem cyclic19 : ¬ Acyclic (node 19) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge19_0 : Core (mutate (node 19) 0) ∨
    WeakForks.IsWeakFork (mutate (node 19) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 19) 0) 0 := by
  right; right
  have he : relabel (reverse (mutate (node 19) 0)) perm4 = WeakRegions.root (2) (13) (3) (10) (2) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 19) 0)) perm4) u v = (WeakRegions.root (2) (13) (3) (10) (2) (1)) u v from by decide +kernel) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 19) 0)) perm4) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (2) (13) (3) (10) (2) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm4 hb)

theorem edge19_1 : Core (mutate (node 19) 1) ∨
    WeakForks.IsWeakFork (mutate (node 19) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 19) 1) 1 := by
  have he : mutate (node 19) 1 = relabel (node 11) perm5 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 19) 1) u v = (relabel (node 11) perm5) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 11) perm5)

theorem edge19_2 : Core (mutate (node 19) 2) ∨
    WeakForks.IsWeakFork (mutate (node 19) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 19) 2) 2 := by
  have he : mutate (node 19) 2 = reverse (relabel (node 20) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 19) 2) u v = (reverse (relabel (node 20) perm6)) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 20) perm6))

theorem edge19_3 : Core (mutate (node 19) 3) ∨
    WeakForks.IsWeakFork (mutate (node 19) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 19) 3) 3 := by
  have he : mutate (node 19) 3 = relabel (node 23) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 19) 3) u v = (relabel (node 23) perm21) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 23) perm21)

theorem cyclic20 : ¬ Acyclic (node 20) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 2 (by decide)
  have h2 := hr 2 0 (by decide)
  omega

theorem edge20_0 : Core (mutate (node 20) 0) ∨
    WeakForks.IsWeakFork (mutate (node 20) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 20) 0) 0 := by
  have he : mutate (node 20) 0 = relabel (node 9) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 20) 0) u v = (relabel (node 9) perm21) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 9) perm21)

theorem edge20_1 : Core (mutate (node 20) 1) ∨
    WeakForks.IsWeakFork (mutate (node 20) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 20) 1) 1 := by
  have he : mutate (node 20) 1 = reverse (relabel (strip2 0 1) perm15) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 20) 1) u v = (reverse (relabel (strip2 0 1) perm15)) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.strip2 0 1) perm15))

theorem edge20_2 : Core (mutate (node 20) 2) ∨
    WeakForks.IsWeakFork (mutate (node 20) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 20) 2) 2 := by
  have he : mutate (node 20) 2 = reverse (relabel (node 19) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 20) 2) u v = (reverse (relabel (node 19) perm6)) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 19) perm6))

theorem edge20_3 : Core (mutate (node 20) 3) ∨
    WeakForks.IsWeakFork (mutate (node 20) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 20) 3) 3 := by
  have he : mutate (node 20) 3 = relabel (node 18) perm1 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 20) 3) u v = (relabel (node 18) perm1) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 18) perm1)

theorem cyclic21 : ¬ Acyclic (node 21) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (by decide)
  have h1 := hr 2 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge21_0 : Core (mutate (node 21) 0) ∨
    WeakForks.IsWeakFork (mutate (node 21) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 21) 0) 0 := by
  have he : mutate (node 21) 0 = reverse (relabel (node 12) perm19) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 21) 0) u v = (reverse (relabel (node 12) perm19)) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 12) perm19))

theorem edge21_1 : Core (mutate (node 21) 1) ∨
    WeakForks.IsWeakFork (mutate (node 21) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 21) 1) 1 := by
  right; right
  have he : relabel (reverse (mutate (node 21) 1)) perm6 = WeakRegions.root (9) (17) (14) (2) (2) (0) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 21) 1)) perm6) u v = (WeakRegions.root (9) (17) (14) (2) (2) (0)) u v from by decide +kernel) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 21) 1)) perm6) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (9) (17) (14) (2) (2) (0) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm6 hb)

theorem edge21_2 : Core (mutate (node 21) 2) ∨
    WeakForks.IsWeakFork (mutate (node 21) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 21) 2) 2 := by
  have he : mutate (node 21) 2 = reverse (relabel (node 22) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 21) 2) u v = (reverse (relabel (node 22) perm6)) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 22) perm6))

theorem edge21_3 : Core (mutate (node 21) 3) ∨
    WeakForks.IsWeakFork (mutate (node 21) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 21) 3) 3 := by
  have he : mutate (node 21) 3 = relabel (node 27) perm3 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 21) 3) u v = (relabel (node 27) perm3) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 27) perm3)

theorem cyclic22 : ¬ Acyclic (node 22) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge22_0 : Core (mutate (node 22) 0) ∨
    WeakForks.IsWeakFork (mutate (node 22) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 22) 0) 0 := by
  right; right
  have he : relabel (reverse (mutate (node 22) 0)) perm5 = WeakRegions.root (2) (4) (10) (2) (7) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 22) 0)) perm5) u v = (WeakRegions.root (2) (4) (10) (2) (7) (1)) u v from by decide +kernel) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 22) 0)) perm5) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (2) (4) (10) (2) (7) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm5 hb)

theorem edge22_1 : Core (mutate (node 22) 1) ∨
    WeakForks.IsWeakFork (mutate (node 22) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 22) 1) 1 := by
  have he : mutate (node 22) 1 = reverse (relabel (node 16) perm11) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 22) 1) u v = (reverse (relabel (node 16) perm11)) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 16) perm11))

theorem edge22_2 : Core (mutate (node 22) 2) ∨
    WeakForks.IsWeakFork (mutate (node 22) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 22) 2) 2 := by
  have he : mutate (node 22) 2 = reverse (relabel (node 21) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 22) 2) u v = (reverse (relabel (node 21) perm6)) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 21) perm6))

theorem edge22_3 : Core (mutate (node 22) 3) ∨
    WeakForks.IsWeakFork (mutate (node 22) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 22) 3) 3 := by
  have he : mutate (node 22) 3 = reverse (relabel (node 28) perm19) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 22) 3) u v = (reverse (relabel (node 28) perm19)) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 28) perm19))

theorem cyclic23 : ¬ Acyclic (node 23) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge23_0 : Core (mutate (node 23) 0) ∨
    WeakForks.IsWeakFork (mutate (node 23) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 23) 0) 0 := by
  have he : mutate (node 23) 0 = relabel (node 19) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 23) 0) u v = (relabel (node 19) perm21) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 19) perm21)

theorem edge23_1 : Core (mutate (node 23) 1) ∨
    WeakForks.IsWeakFork (mutate (node 23) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 23) 1) 1 := by
  have he : mutate (node 23) 1 = relabel (node 14) perm5 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 23) 1) u v = (relabel (node 14) perm5) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 14) perm5)

theorem edge23_2 : Core (mutate (node 23) 2) ∨
    WeakForks.IsWeakFork (mutate (node 23) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 23) 2) 2 := by
  have he : mutate (node 23) 2 = reverse (relabel (node 24) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 23) 2) u v = (reverse (relabel (node 24) perm6)) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 24) perm6))

theorem edge23_3 : Core (mutate (node 23) 3) ∨
    WeakForks.IsWeakFork (mutate (node 23) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 23) 3) 3 := by
  have he : mutate (node 23) 3 = relabel (node 30) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 23) 3) u v = (relabel (node 30) perm21) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 30) perm21)

theorem cyclic24 : ¬ Acyclic (node 24) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge24_0 : Core (mutate (node 24) 0) ∨
    WeakForks.IsWeakFork (mutate (node 24) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 24) 0) 0 := by
  have he : mutate (node 24) 0 = relabel (node 15) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 24) 0) u v = (relabel (node 15) perm21) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 15) perm21)

theorem edge24_1 : Core (mutate (node 24) 1) ∨
    WeakForks.IsWeakFork (mutate (node 24) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 24) 1) 1 := by
  have he : mutate (node 24) 1 = relabel (node 18) perm5 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 24) 1) u v = (relabel (node 18) perm5) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 18) perm5)

theorem edge24_2 : Core (mutate (node 24) 2) ∨
    WeakForks.IsWeakFork (mutate (node 24) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 24) 2) 2 := by
  have he : mutate (node 24) 2 = reverse (relabel (node 23) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 24) 2) u v = (reverse (relabel (node 23) perm6)) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 23) perm6))

theorem edge24_3 : Core (mutate (node 24) 3) ∨
    WeakForks.IsWeakFork (mutate (node 24) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 24) 3) 3 := by
  have he : mutate (node 24) 3 = relabel (node 29) perm5 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 24) 3) u v = (relabel (node 29) perm5) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 29) perm5)

theorem cyclic25 : ¬ Acyclic (node 25) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 2 (by decide)
  have h2 := hr 2 0 (by decide)
  omega

theorem edge25_0 : Core (mutate (node 25) 0) ∨
    WeakForks.IsWeakFork (mutate (node 25) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 25) 0) 0 := by
  right; right
  have he : relabel (reverse (mutate (node 25) 0)) perm4 = WeakRegions.root (4) (17) (6) (4) (2) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 25) 0)) perm4) u v = (WeakRegions.root (4) (17) (6) (4) (2) (1)) u v from by decide +kernel) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 25) 0)) perm4) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (4) (17) (6) (4) (2) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm4 hb)

theorem edge25_1 : Core (mutate (node 25) 1) ∨
    WeakForks.IsWeakFork (mutate (node 25) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 25) 1) 1 := by
  have he : mutate (node 25) 1 = reverse (relabel (AffineFourLocal.tail 0 0) perm10) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 25) 1) u v = (reverse (relabel (AffineFourLocal.tail 0 0) perm10)) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.affine 0 (by omega) 0) perm10))

theorem edge25_2 : Core (mutate (node 25) 2) ∨
    WeakForks.IsWeakFork (mutate (node 25) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 25) 2) 2 := by
  have he : mutate (node 25) 2 = reverse (relabel (node 27) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 25) 2) u v = (reverse (relabel (node 27) perm6)) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 27) perm6))

theorem edge25_3 : Core (mutate (node 25) 3) ∨
    WeakForks.IsWeakFork (mutate (node 25) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 25) 3) 3 := by
  have he : mutate (node 25) 3 = relabel (AffineFourLocal.tail 0 3) perm8 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 25) 3) u v = (relabel (AffineFourLocal.tail 0 3) perm8) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.framed (Core.affine 0 (by omega) 3) perm8)

theorem cyclic26 : ¬ Acyclic (node 26) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge26_0 : Core (mutate (node 26) 0) ∨
    WeakForks.IsWeakFork (mutate (node 26) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 26) 0) 0 := by
  right; right
  have he : relabel (reverse (mutate (node 26) 0)) perm5 = WeakRegions.root (4) (7) (15) (2) (4) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 26) 0)) perm5) u v = (WeakRegions.root (4) (7) (15) (2) (4) (1)) u v from by decide +kernel) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 26) 0)) perm5) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (4) (7) (15) (2) (4) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm5 hb)

theorem edge26_1 : Core (mutate (node 26) 1) ∨
    WeakForks.IsWeakFork (mutate (node 26) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 26) 1) 1 := by
  have he : mutate (node 26) 1 = relabel (node 27) perm6 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 26) 1) u v = (relabel (node 27) perm6) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 27) perm6)

theorem edge26_2 : Core (mutate (node 26) 2) ∨
    WeakForks.IsWeakFork (mutate (node 26) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 26) 2) 2 := by
  have he : mutate (node 26) 2 = reverse (relabel (AffineFourLocal.tail 0 1) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 26) 2) u v = (reverse (relabel (AffineFourLocal.tail 0 1) perm6)) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.affine 0 (by omega) 1) perm6))

theorem edge26_3 : Core (mutate (node 26) 3) ∨
    WeakForks.IsWeakFork (mutate (node 26) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 26) 3) 3 := by
  have he : mutate (node 26) 3 = relabel (node 30) perm3 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 26) 3) u v = (relabel (node 30) perm3) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 30) perm3)

theorem cyclic27 : ¬ Acyclic (node 27) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 2 (by decide)
  have h2 := hr 2 0 (by decide)
  omega

theorem edge27_0 : Core (mutate (node 27) 0) ∨
    WeakForks.IsWeakFork (mutate (node 27) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 27) 0) 0 := by
  have he : mutate (node 27) 0 = relabel (node 26) perm6 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 27) 0) u v = (relabel (node 26) perm6) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 26) perm6)

theorem edge27_1 : Core (mutate (node 27) 1) ∨
    WeakForks.IsWeakFork (mutate (node 27) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 27) 1) 1 := by
  have he : mutate (node 27) 1 = relabel (node 21) perm4 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 27) 1) u v = (relabel (node 21) perm4) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 21) perm4)

theorem edge27_2 : Core (mutate (node 27) 2) ∨
    WeakForks.IsWeakFork (mutate (node 27) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 27) 2) 2 := by
  have he : mutate (node 27) 2 = reverse (relabel (node 25) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 27) 2) u v = (reverse (relabel (node 25) perm6)) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 25) perm6))

theorem edge27_3 : Core (mutate (node 27) 3) ∨
    WeakForks.IsWeakFork (mutate (node 27) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 27) 3) 3 := by
  have he : mutate (node 27) 3 = relabel (node 28) perm1 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 27) 3) u v = (relabel (node 28) perm1) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 28) perm1)

theorem cyclic28 : ¬ Acyclic (node 28) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge28_0 : Core (mutate (node 28) 0) ∨
    WeakForks.IsWeakFork (mutate (node 28) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 28) 0) 0 := by
  have he : mutate (node 28) 0 = reverse (relabel (node 29) perm0) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 28) 0) u v = (reverse (relabel (node 29) perm0)) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 29) perm0))

theorem edge28_1 : Core (mutate (node 28) 1) ∨
    WeakForks.IsWeakFork (mutate (node 28) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 28) 1) 1 := by
  have he : mutate (node 28) 1 = reverse (relabel (node 22) perm11) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 28) 1) u v = (reverse (relabel (node 22) perm11)) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 22) perm11))

theorem edge28_2 : Core (mutate (node 28) 2) ∨
    WeakForks.IsWeakFork (mutate (node 28) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 28) 2) 2 := by
  have he : mutate (node 28) 2 = relabel (node 27) perm1 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 28) 2) u v = (relabel (node 27) perm1) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 27) perm1)

theorem edge28_3 : Core (mutate (node 28) 3) ∨
    WeakForks.IsWeakFork (mutate (node 28) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 28) 3) 3 := by
  have he : mutate (node 28) 3 = reverse (relabel (node 32) perm13) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 28) 3) u v = (reverse (relabel (node 32) perm13)) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 32) perm13))

theorem cyclic29 : ¬ Acyclic (node 29) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge29_0 : Core (mutate (node 29) 0) ∨
    WeakForks.IsWeakFork (mutate (node 29) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 29) 0) 0 := by
  have he : mutate (node 29) 0 = reverse (relabel (node 28) perm0) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 29) 0) u v = (reverse (relabel (node 28) perm0)) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 28) perm0))

theorem edge29_1 : Core (mutate (node 29) 1) ∨
    WeakForks.IsWeakFork (mutate (node 29) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 29) 1) 1 := by
  have he : mutate (node 29) 1 = relabel (node 24) perm5 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 29) 1) u v = (relabel (node 24) perm5) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 24) perm5)

theorem edge29_2 : Core (mutate (node 29) 2) ∨
    WeakForks.IsWeakFork (mutate (node 29) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 29) 2) 2 := by
  have he : mutate (node 29) 2 = reverse (relabel (node 30) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 29) 2) u v = (reverse (relabel (node 30) perm6)) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 30) perm6))

theorem edge29_3 : Core (mutate (node 29) 3) ∨
    WeakForks.IsWeakFork (mutate (node 29) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 29) 3) 3 := by
  have he : mutate (node 29) 3 = reverse (relabel (node 33) perm13) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 29) 3) u v = (reverse (relabel (node 33) perm13)) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 33) perm13))

theorem cyclic30 : ¬ Acyclic (node 30) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge30_0 : Core (mutate (node 30) 0) ∨
    WeakForks.IsWeakFork (mutate (node 30) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 30) 0) 0 := by
  have he : mutate (node 30) 0 = relabel (node 23) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 30) 0) u v = (relabel (node 23) perm21) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 23) perm21)

theorem edge30_1 : Core (mutate (node 30) 1) ∨
    WeakForks.IsWeakFork (mutate (node 30) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 30) 1) 1 := by
  have he : mutate (node 30) 1 = relabel (node 26) perm4 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 30) 1) u v = (relabel (node 26) perm4) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 26) perm4)

theorem edge30_2 : Core (mutate (node 30) 2) ∨
    WeakForks.IsWeakFork (mutate (node 30) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 30) 2) 2 := by
  have he : mutate (node 30) 2 = reverse (relabel (node 29) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 30) 2) u v = (reverse (relabel (node 29) perm6)) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 29) perm6))

theorem edge30_3 : Core (mutate (node 30) 3) ∨
    WeakForks.IsWeakFork (mutate (node 30) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 30) 3) 3 := by
  have he : mutate (node 30) 3 = relabel (node 31) perm3 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 30) 3) u v = (relabel (node 31) perm3) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 31) perm3)

theorem cyclic31 : ¬ Acyclic (node 31) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 1 3 (by decide)
  have h1 := hr 3 2 (by decide)
  have h2 := hr 2 1 (by decide)
  omega

theorem edge31_0 : Core (mutate (node 31) 0) ∨
    WeakForks.IsWeakFork (mutate (node 31) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 31) 0) 0 := by
  have he : mutate (node 31) 0 = reverse (relabel (node 32) perm2) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 31) 0) u v = (reverse (relabel (node 32) perm2)) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 32) perm2))

theorem edge31_1 : Core (mutate (node 31) 1) ∨
    WeakForks.IsWeakFork (mutate (node 31) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 31) 1) 1 := by
  have he : mutate (node 31) 1 = relabel (node 30) perm4 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 31) 1) u v = (relabel (node 30) perm4) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 30) perm4)

theorem edge31_2 : Core (mutate (node 31) 2) ∨
    WeakForks.IsWeakFork (mutate (node 31) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 31) 2) 2 := by
  have he : mutate (node 31) 2 = relabel (AffineFourLocal.tail 0 2) perm3 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 31) 2) u v = (relabel (AffineFourLocal.tail 0 2) perm3) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.framed (Core.affine 0 (by omega) 2) perm3)

theorem edge31_3 : Core (mutate (node 31) 3) ∨
    WeakForks.IsWeakFork (mutate (node 31) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 31) 3) 3 := by
  have he : mutate (node 31) 3 = relabel (node 32) perm2 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 31) 3) u v = (relabel (node 32) perm2) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 32) perm2)

theorem cyclic32 : ¬ Acyclic (node 32) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 1 3 (by decide)
  have h1 := hr 3 2 (by decide)
  have h2 := hr 2 1 (by decide)
  omega

theorem edge32_0 : Core (mutate (node 32) 0) ∨
    WeakForks.IsWeakFork (mutate (node 32) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 32) 0) 0 := by
  have he : mutate (node 32) 0 = reverse (relabel (node 31) perm2) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 32) 0) u v = (reverse (relabel (node 31) perm2)) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 31) perm2))

theorem edge32_1 : Core (mutate (node 32) 1) ∨
    WeakForks.IsWeakFork (mutate (node 32) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 32) 1) 1 := by
  have he : mutate (node 32) 1 = reverse (relabel (node 28) perm10) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 32) 1) u v = (reverse (relabel (node 28) perm10)) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 28) perm10))

theorem edge32_2 : Core (mutate (node 32) 2) ∨
    WeakForks.IsWeakFork (mutate (node 32) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 32) 2) 2 := by
  have he : mutate (node 32) 2 = relabel (node 33) perm3 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 32) 2) u v = (relabel (node 33) perm3) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 33) perm3)

theorem edge32_3 : Core (mutate (node 32) 3) ∨
    WeakForks.IsWeakFork (mutate (node 32) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 32) 3) 3 := by
  have he : mutate (node 32) 3 = relabel (node 31) perm2 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 32) 3) u v = (relabel (node 31) perm2) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 31) perm2)

theorem cyclic33 : ¬ Acyclic (node 33) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge33_0 : Core (mutate (node 33) 0) ∨
    WeakForks.IsWeakFork (mutate (node 33) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 33) 0) 0 := by
  right; right
  have he : relabel (reverse (mutate (node 33) 0)) perm4 = WeakRegions.root (2) (3) (5) (2) (2) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 33) 0)) perm4) u v = (WeakRegions.root (2) (3) (5) (2) (2) (1)) u v from by decide +kernel) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 33) 0)) perm4) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (2) (3) (5) (2) (2) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm4 hb)

theorem edge33_1 : Core (mutate (node 33) 1) ∨
    WeakForks.IsWeakFork (mutate (node 33) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 33) 1) 1 := by
  have he : mutate (node 33) 1 = reverse (relabel (node 29) perm10) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 33) 1) u v = (reverse (relabel (node 29) perm10)) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 29) perm10))

theorem edge33_2 : Core (mutate (node 33) 2) ∨
    WeakForks.IsWeakFork (mutate (node 33) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 33) 2) 2 := by
  have he : mutate (node 33) 2 = reverse (relabel (node 33) perm5) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 33) 2) u v = (reverse (relabel (node 33) perm5)) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 33) perm5))

theorem edge33_3 : Core (mutate (node 33) 3) ∨
    WeakForks.IsWeakFork (mutate (node 33) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 33) 3) 3 := by
  have he : mutate (node 33) 3 = relabel (node 32) perm4 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 33) 3) u v = (relabel (node 32) perm4) u v from by decide +kernel) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 32) perm4)

theorem finite_skew (i : Fin 34) : SkewSymmetric (node i) := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 ∨ i = 32 ∨ i = 33 := by omega
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ofSix_skew _ _ _ _ _ _

theorem finite_cyclic (i : Fin 34) : ¬ Acyclic (node i) := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 ∨ i = 32 ∨ i = 33 := by omega
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · exact cyclic16
  · exact cyclic17
  · exact cyclic18
  · exact cyclic19
  · exact cyclic20
  · exact cyclic21
  · exact cyclic22
  · exact cyclic23
  · exact cyclic24
  · exact cyclic25
  · exact cyclic26
  · exact cyclic27
  · exact cyclic28
  · exact cyclic29
  · exact cyclic30
  · exact cyclic31
  · exact cyclic32
  · exact cyclic33

theorem finite_edges (i : Fin 34) (k : Fin 4) : Core (mutate (node i) k) ∨
    WeakForks.IsWeakFork (mutate (node i) k) k ∨ WeakRegions.IsRoot (mutate (node i) k) k := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 ∨ i = 32 ∨ i = 33 := by omega
  have hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hk with rfl|rfl|rfl|rfl
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
  · exact edge16_0
  · exact edge16_1
  · exact edge16_2
  · exact edge16_3
  · exact edge17_0
  · exact edge17_1
  · exact edge17_2
  · exact edge17_3
  · exact edge18_0
  · exact edge18_1
  · exact edge18_2
  · exact edge18_3
  · exact edge19_0
  · exact edge19_1
  · exact edge19_2
  · exact edge19_3
  · exact edge20_0
  · exact edge20_1
  · exact edge20_2
  · exact edge20_3
  · exact edge21_0
  · exact edge21_1
  · exact edge21_2
  · exact edge21_3
  · exact edge22_0
  · exact edge22_1
  · exact edge22_2
  · exact edge22_3
  · exact edge23_0
  · exact edge23_1
  · exact edge23_2
  · exact edge23_3
  · exact edge24_0
  · exact edge24_1
  · exact edge24_2
  · exact edge24_3
  · exact edge25_0
  · exact edge25_1
  · exact edge25_2
  · exact edge25_3
  · exact edge26_0
  · exact edge26_1
  · exact edge26_2
  · exact edge26_3
  · exact edge27_0
  · exact edge27_1
  · exact edge27_2
  · exact edge27_3
  · exact edge28_0
  · exact edge28_1
  · exact edge28_2
  · exact edge28_3
  · exact edge29_0
  · exact edge29_1
  · exact edge29_2
  · exact edge29_3
  · exact edge30_0
  · exact edge30_1
  · exact edge30_2
  · exact edge30_3
  · exact edge31_0
  · exact edge31_1
  · exact edge31_2
  · exact edge31_3
  · exact edge32_0
  · exact edge32_1
  · exact edge32_2
  · exact edge32_3
  · exact edge33_0
  · exact edge33_1
  · exact edge33_2
  · exact edge33_3

theorem affine_parent0 : Core (AffineFourLocal.base 0) := by
  have he : AffineFourLocal.base 0 = reverse (relabel (node 25) perm13) := by
    funext u v
    exact (show ∀ u v : Fin 4, (AffineFourLocal.base 0) u v = (reverse (relabel (node 25) perm13)) u v from by decide +kernel) u v
  rw [he]
  exact Core.reversed (Core.framed (Core.finite 25) perm13)

theorem affine_parent1 : Core (AffineFourLocal.base 1) := by
  have he : AffineFourLocal.base 1 = reverse (relabel (node 26) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (AffineFourLocal.base 1) u v = (reverse (relabel (node 26) perm6)) u v from by decide +kernel) u v
  rw [he]
  exact Core.reversed (Core.framed (Core.finite 26) perm6)

theorem affine_parent2 : Core (AffineFourLocal.base 2) := by
  have he : AffineFourLocal.base 2 = relabel (node 31) perm4 := by
    funext u v
    exact (show ∀ u v : Fin 4, (AffineFourLocal.base 2) u v = (relabel (node 31) perm4) u v from by decide +kernel) u v
  rw [he]
  exact Core.framed (Core.finite 31) perm4

theorem affine_parent3 : Core (AffineFourLocal.base 3) := by
  have he : AffineFourLocal.base 3 = relabel (node 25) perm12 := by
    funext u v
    exact (show ∀ u v : Fin 4, (AffineFourLocal.base 3) u v = (relabel (node 25) perm12) u v from by decide +kernel) u v
  rw [he]
  exact Core.framed (Core.finite 25) perm12

theorem affine_address {B : Matrix 4} (h : AffineFourLocal.Core B) : Core B := by
  induction h with
  | base i =>
    have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
    rcases hi with rfl|rfl|rfl|rfl
    · exact affine_parent0
    · exact affine_parent1
    · exact affine_parent2
    · exact affine_parent3
  | tail n hn i => exact Core.affine n hn i
  | framed h p ih => exact Core.framed ih p
  | reversed h ih => exact Core.reversed ih

theorem parent0_0 : Core (mutate (GenericStrip.root 7 seed0.A seed0.H seed0.Z) 1) := by
  have he : mutate (GenericStrip.root 7 seed0.A seed0.H seed0.Z) 1 = reverse (relabel (node 4) perm3) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (GenericStrip.root 7 seed0.A seed0.H seed0.Z) 1) u v = (reverse (relabel (node 4) perm3)) u v from by decide +kernel) u v
  rw [he]
  exact Core.reversed (Core.framed (Core.finite 4) perm3)

theorem parent0_1 : Core (mutate (GenericStrip.root 7 seed0.A seed0.H seed0.Z) 2) := by
  have he : mutate (GenericStrip.root 7 seed0.A seed0.H seed0.Z) 2 = relabel (node 10) perm17 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (GenericStrip.root 7 seed0.A seed0.H seed0.Z) 2) u v = (relabel (node 10) perm17) u v from by decide +kernel) u v
  rw [he]
  exact Core.framed (Core.finite 10) perm17

theorem parent0_2 : Core (mutate (GenericStrip.phaseQ 7 seed0.A seed0.H seed0.Z) 0) := by
  have he : mutate (GenericStrip.phaseQ 7 seed0.A seed0.H seed0.Z) 0 = reverse (relabel (node 1) perm16) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (GenericStrip.phaseQ 7 seed0.A seed0.H seed0.Z) 0) u v = (reverse (relabel (node 1) perm16)) u v from by decide +kernel) u v
  rw [he]
  exact Core.reversed (Core.framed (Core.finite 1) perm16)

theorem address0 {B : Matrix 4} (h : StripSemantics.Core 7 seed0 Core B) : Core B := by
  induction h with
  | base h => exact h
  | strip n i => exact Core.strip0 n i
  | framed h p ih => exact Core.framed ih p
  | reversed h ih => exact Core.reversed ih

theorem parent1_0 : Core (mutate (GenericStrip.root 7 seed1.A seed1.H seed1.Z) 1) := by
  have he : mutate (GenericStrip.root 7 seed1.A seed1.H seed1.Z) 1 = reverse (relabel (node 2) perm3) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (GenericStrip.root 7 seed1.A seed1.H seed1.Z) 1) u v = (reverse (relabel (node 2) perm3)) u v from by decide +kernel) u v
  rw [he]
  exact Core.reversed (Core.framed (Core.finite 2) perm3)

theorem parent1_1 : Core (mutate (GenericStrip.root 7 seed1.A seed1.H seed1.Z) 2) := by
  have he : mutate (GenericStrip.root 7 seed1.A seed1.H seed1.Z) 2 = relabel (node 7) perm17 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (GenericStrip.root 7 seed1.A seed1.H seed1.Z) 2) u v = (relabel (node 7) perm17) u v from by decide +kernel) u v
  rw [he]
  exact Core.framed (Core.finite 7) perm17

theorem parent1_2 : Core (mutate (GenericStrip.phaseQ 7 seed1.A seed1.H seed1.Z) 0) := by
  have he : mutate (GenericStrip.phaseQ 7 seed1.A seed1.H seed1.Z) 0 = reverse (relabel (node 0) perm16) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (GenericStrip.phaseQ 7 seed1.A seed1.H seed1.Z) 0) u v = (reverse (relabel (node 0) perm16)) u v from by decide +kernel) u v
  rw [he]
  exact Core.reversed (Core.framed (Core.finite 0) perm16)

theorem address1 {B : Matrix 4} (h : StripSemantics.Core 7 seed1 Core B) : Core B := by
  induction h with
  | base h => exact h
  | strip n i => exact Core.strip1 n i
  | framed h p ih => exact Core.framed ih p
  | reversed h ih => exact Core.reversed ih

theorem parent2_0 : Core (UnitZeroStrip.parent 2 seed2 0) := by
  have he : UnitZeroStrip.parent 2 seed2 0 = reverse (relabel (node 18) perm14) := by
    funext u v
    exact (show ∀ u v : Fin 4, (UnitZeroStrip.parent 2 seed2 0) u v = (reverse (relabel (node 18) perm14)) u v from by decide +kernel) u v
  rw [he]
  exact Core.reversed (Core.framed (Core.finite 18) perm14)

theorem parent2_1 : Core (UnitZeroStrip.parent 2 seed2 1) := by
  have he : UnitZeroStrip.parent 2 seed2 1 = reverse (relabel (node 20) perm20) := by
    funext u v
    exact (show ∀ u v : Fin 4, (UnitZeroStrip.parent 2 seed2 1) u v = (reverse (relabel (node 20) perm20)) u v from by decide +kernel) u v
  rw [he]
  exact Core.reversed (Core.framed (Core.finite 20) perm20)

theorem parents2 (p : Fin 2) : Core (UnitZeroStrip.parent 2 seed2 p) := by
  have hp : p=0 ∨ p=1 := by omega
  rcases hp with rfl|rfl
  · exact parent2_0
  · exact parent2_1

theorem parent3_0 : Core (UnitZeroStrip.parent 4 seed3 0) := by
  have he : UnitZeroStrip.parent 4 seed3 0 = reverse (relabel (node 12) perm14) := by
    funext u v
    exact (show ∀ u v : Fin 4, (UnitZeroStrip.parent 4 seed3 0) u v = (reverse (relabel (node 12) perm14)) u v from by decide +kernel) u v
  rw [he]
  exact Core.reversed (Core.framed (Core.finite 12) perm14)

theorem parent3_1 : Core (UnitZeroStrip.parent 4 seed3 1) := by
  have he : UnitZeroStrip.parent 4 seed3 1 = relabel (node 13) perm12 := by
    funext u v
    exact (show ∀ u v : Fin 4, (UnitZeroStrip.parent 4 seed3 1) u v = (relabel (node 13) perm12) u v from by decide +kernel) u v
  rw [he]
  exact Core.framed (Core.finite 13) perm12

theorem parents3 (p : Fin 2) : Core (UnitZeroStrip.parent 4 seed3 p) := by
  have hp : p=0 ∨ p=1 := by omega
  rcases hp with rfl|rfl
  · exact parent3_0
  · exact parent3_1

theorem parent4_0 : Core (UnitZeroStrip.parent 4 seed4 0) := by
  have he : UnitZeroStrip.parent 4 seed4 0 = reverse (relabel (node 14) perm14) := by
    funext u v
    exact (show ∀ u v : Fin 4, (UnitZeroStrip.parent 4 seed4 0) u v = (reverse (relabel (node 14) perm14)) u v from by decide +kernel) u v
  rw [he]
  exact Core.reversed (Core.framed (Core.finite 14) perm14)

theorem parent4_1 : Core (UnitZeroStrip.parent 4 seed4 1) := by
  have he : UnitZeroStrip.parent 4 seed4 1 = reverse (relabel (node 17) perm20) := by
    funext u v
    exact (show ∀ u v : Fin 4, (UnitZeroStrip.parent 4 seed4 1) u v = (reverse (relabel (node 17) perm20)) u v from by decide +kernel) u v
  rw [he]
  exact Core.reversed (Core.framed (Core.finite 17) perm20)

theorem parents4 (p : Fin 2) : Core (UnitZeroStrip.parent 4 seed4 p) := by
  have hp : p=0 ∨ p=1 := by omega
  rcases hp with rfl|rfl
  · exact parent4_0
  · exact parent4_1

theorem core_skew {B : Matrix 4} (h : Core B) : SkewSymmetric B := by
  induction h with
  | finite i => exact finite_skew i
  | affine n hn i => exact AffineFourLocal.tail_skew n i
  | strip0 n i => exact GenericStrip.phase_skew _ _ _ _ _
  | strip1 n i => exact GenericStrip.phase_skew _ _ _ _ _
  | strip2 n i => exact UnitZeroStrip.strip_skew _ _ _ _
  | strip3 n i => exact UnitZeroStrip.strip_skew _ _ _ _
  | strip4 n i => exact UnitZeroStrip.strip_skew _ _ _ _
  | framed h p ih => exact relabel_skew _ p ih
  | reversed h ih => exact reverse_skew _ ih

theorem core_cyclic {B : Matrix 4} (h : Core B) : ¬ Acyclic B := by
  induction h with
  | finite i => exact finite_cyclic i
  | affine n hn i => exact AffineFourLocal.tail_cyclic n hn i
  | strip0 n i => exact GenericStrip.phase_cyclic _ _ _ _ (GenericStrip.orbit_domain 7 seed0 domain0 n) i
  | strip1 n i => exact GenericStrip.phase_cyclic _ _ _ _ (GenericStrip.orbit_domain 7 seed1 domain1 n) i
  | strip2 n i => exact UnitZeroStrip.strip_cyclic _ _ domain2 _ _
  | strip3 n i => exact UnitZeroStrip.strip_cyclic _ _ domain3 _ _
  | strip4 n i => exact UnitZeroStrip.strip_cyclic _ _ domain4 _ _
  | framed h p ih => exact fun ha => ih ((acyclic_relabel_iff _ p).mp ha)
  | reversed h ih => exact fun ha => ih ((acyclic_reverse_iff _ (core_skew h)).mp ha)

theorem core_edges {B : Matrix 4} (h : Core B) (k : Fin 4) :
    Core (mutate B k) ∨ WeakForks.IsWeakFork (mutate B k) k ∨ WeakRegions.IsRoot (mutate B k) k := by
  induction h generalizing k with
  | finite i => exact finite_edges i k
  | affine n hn i =>
    rcases AffineFourLocal.tail_edges n hn i k with hc|hf|hr
    · exact Or.inl (affine_address hc)
    · exact Or.inr (Or.inl hf)
    · exact Or.inr (Or.inr hr)
  | strip0 n i =>
    rcases StripSemantics.strip_edges 7 seed0 Core domain0
      (.base parent0_0) (.base parent0_1) (.base parent0_2) n i k with hc|hf|hr
    · exact Or.inl (address0 hc)
    · exact Or.inr (Or.inl (strict_fork_weak hf))
    · exact Or.inr (Or.inr (strict_root_weak hr))
  | strip1 n i =>
    rcases StripSemantics.strip_edges 7 seed1 Core domain1
      (.base parent1_0) (.base parent1_1) (.base parent1_2) n i k with hc|hf|hr
    · exact Or.inl (address1 hc)
    · exact Or.inr (Or.inl (strict_fork_weak hf))
    · exact Or.inr (Or.inr (strict_root_weak hr))
  | strip2 n i =>
    rcases UnitZeroStrip.all_edges 2 seed2 domain2 n i k with
      ⟨n2,i2,p,he⟩ | ⟨p2,p,he⟩ | hf | hr
    · rw [show strip2 n i = UnitZeroStrip.strip 2 seed2 n i from rfl, he]
      exact Or.inl (.framed (.strip2 n2 i2) p)
    · rw [show strip2 n i = UnitZeroStrip.strip 2 seed2 n i from rfl, he]
      exact Or.inl (.framed (parents2 p2) p)
    · exact Or.inr (Or.inl (strict_fork_weak hf))
    · exact Or.inr (Or.inr (strict_root_weak hr))
  | strip3 n i =>
    rcases UnitZeroStrip.all_edges 4 seed3 domain3 n i k with
      ⟨n2,i2,p,he⟩ | ⟨p2,p,he⟩ | hf | hr
    · rw [show strip3 n i = UnitZeroStrip.strip 4 seed3 n i from rfl, he]
      exact Or.inl (.framed (.strip3 n2 i2) p)
    · rw [show strip3 n i = UnitZeroStrip.strip 4 seed3 n i from rfl, he]
      exact Or.inl (.framed (parents3 p2) p)
    · exact Or.inr (Or.inl (strict_fork_weak hf))
    · exact Or.inr (Or.inr (strict_root_weak hr))
  | strip4 n i =>
    rcases UnitZeroStrip.all_edges 4 seed4 domain4 n i k with
      ⟨n2,i2,p,he⟩ | ⟨p2,p,he⟩ | hf | hr
    · rw [show strip4 n i = UnitZeroStrip.strip 4 seed4 n i from rfl, he]
      exact Or.inl (.framed (.strip4 n2 i2) p)
    · rw [show strip4 n i = UnitZeroStrip.strip 4 seed4 n i from rfl, he]
      exact Or.inl (.framed (parents4 p2) p)
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

/-- Exact source q128: unconditional NMA for every finite mutation word. -/
theorem nma_q128 : ¬ MutationAcyclic (ofSix (-2) (-2) (0) (-1) (1) (-2)) := by
  have he : (ofSix (-2) (-2) (0) (-1) (1) (-2)) = relabel (node 31) perm0 := by
    funext u v
    exact (show ∀ u v : Fin 4, ((ofSix (-2) (-2) (0) (-1) (1) (-2))) u v = (relabel (node 31) perm0) u v from by decide +kernel) u v
  rw [he]
  exact core_NMA (Core.framed (Core.finite 31) perm0)

/-- Exact source q134: unconditional NMA for every finite mutation word. -/
theorem nma_q134 : ¬ MutationAcyclic (ofSix (-2) (-2) (0) (-1) (2) (-1)) := by
  have he : (ofSix (-2) (-2) (0) (-1) (2) (-1)) = relabel (node 32) perm0 := by
    funext u v
    exact (show ∀ u v : Fin 4, ((ofSix (-2) (-2) (0) (-1) (2) (-1))) u v = (relabel (node 32) perm0) u v from by decide +kernel) u v
  rw [he]
  exact core_NMA (Core.framed (Core.finite 32) perm0)

/-- Exact source q208: unconditional NMA for every finite mutation word. -/
theorem nma_q208 : ¬ MutationAcyclic (ofSix (-2) (-2) (1) (0) (-1) (2)) := by
  have he : (ofSix (-2) (-2) (1) (0) (-1) (2)) = reverse (relabel (node 32) perm10) := by
    funext u v
    exact (show ∀ u v : Fin 4, ((ofSix (-2) (-2) (1) (0) (-1) (2))) u v = (reverse (relabel (node 32) perm10)) u v from by decide +kernel) u v
  rw [he]
  exact core_NMA (Core.reversed (Core.framed (Core.finite 32) perm10))

/-- Exact source q238: unconditional NMA for every finite mutation word. -/
theorem nma_q238 : ¬ MutationAcyclic (ofSix (-2) (-2) (2) (-1) (-1) (1)) := by
  have he : (ofSix (-2) (-2) (2) (-1) (-1) (1)) = relabel (node 33) perm0 := by
    funext u v
    exact (show ∀ u v : Fin 4, ((ofSix (-2) (-2) (2) (-1) (-1) (1))) u v = (relabel (node 33) perm0) u v from by decide +kernel) u v
  rw [he]
  exact core_NMA (Core.framed (Core.finite 33) perm0)

/-- Exact source q273: unconditional NMA for every finite mutation word. -/
theorem nma_q273 : ¬ MutationAcyclic (ofSix (-2) (-1) (-1) (-2) (2) (-1)) := by
  have he : (ofSix (-2) (-1) (-1) (-2) (2) (-1)) = reverse (relabel (node 33) perm13) := by
    funext u v
    exact (show ∀ u v : Fin 4, ((ofSix (-2) (-1) (-1) (-2) (2) (-1))) u v = (reverse (relabel (node 33) perm13)) u v from by decide +kernel) u v
  rw [he]
  exact core_NMA (Core.reversed (Core.framed (Core.finite 33) perm13))

/-- Exact source q470: unconditional NMA for every finite mutation word. -/
theorem nma_q470 : ¬ MutationAcyclic (ofSix (-2) (-1) (1) (0) (2) (-2)) := by
  have he : (ofSix (-2) (-1) (1) (0) (2) (-2)) = reverse (relabel (node 31) perm7) := by
    funext u v
    exact (show ∀ u v : Fin 4, ((ofSix (-2) (-1) (1) (0) (2) (-2))) u v = (reverse (relabel (node 31) perm7)) u v from by decide +kernel) u v
  rw [he]
  exact core_NMA (Core.reversed (Core.framed (Core.finite 31) perm7))

end QuiverProofs.AffineFourCompletion
