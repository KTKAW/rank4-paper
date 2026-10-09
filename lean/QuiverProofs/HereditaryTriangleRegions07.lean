import QuiverProofs.HereditaryTrianglePendant
import QuiverProofs.StripSemantics

/-! Exact finite core joined to unbounded G/N strips. Every entrance parent is checked. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace QuiverProofs.HereditaryTriangleRegions07
open ForkCertificates HereditaryTrianglePendant

def node (i : Fin 49) : Matrix 4 := match i.val with
  | 0 => (ofSix (-4658) (-6) (7) (-93) (-668) (-1))
  | 1 => (ofSix (-690) (-3) (4) (-40) (-177) (-1))
  | 2 => (ofSix (-668) (-1) (7) (-93) (-18) (-1))
  | 3 => (ofSix (-542) (-18) (93) (7) (-6) (1))
  | 4 => (ofSix (-177) (-1) (4) (-40) (-18) (-1))
  | 5 => (ofSix (-117) (-3) (4) (-7) (-30) (-1))
  | 6 => (ofSix (-111) (-6) (7) (-2) (-16) (-1))
  | 7 => (ofSix (-111) (-2) (18) (-6) (-1) (-1))
  | 8 => (ofSix (-105) (-18) (40) (4) (-3) (1))
  | 9 => (ofSix (-93) (-18) (16) (1) (-6) (-1))
  | 10 => (ofSix (-92) (-2) (3) (-9) (-33) (-1))
  | 11 => (ofSix (-58) (-3) (4) (-3) (-15) (-1))
  | 12 => (ofSix (-58) (-3) (18) (-3) (-1) (-1))
  | 13 => (ofSix (-40) (-18) (15) (1) (-3) (-1))
  | 14 => (ofSix (-39) (-2) (3) (-4) (-14) (-1))
  | 15 => (ofSix (-33) (-1) (3) (-9) (-7) (-1))
  | 16 => (ofSix (-30) (-1) (4) (-7) (-3) (-1))
  | 17 => (ofSix (-18) (-4) (3) (3) (-7) (-1))
  | 18 => (ofSix (-16) (-2) (3) (-1) (-6) (-1))
  | 19 => (ofSix (-16) (-1) (7) (-2) (-1) (-1))
  | 20 => (ofSix (-15) (-3) (5) (-1) (-3) (-1))
  | 21 => (ofSix (-15) (-1) (4) (-3) (-2) (-1))
  | 22 => (ofSix (-14) (-1) (3) (-4) (-3) (-1))
  | 23 => (ofSix (-12) (-7) (9) (3) (-2) (1))
  | 24 => (ofSix (-10) (-3) (4) (0) (-3) (-1))
  | 25 => (ofSix (-10) (0) (3) (-3) (-1) (-1))
  | 26 => (ofSix (-9) (-7) (6) (1) (-2) (-1))
  | 27 => (ofSix (-7) (-4) (3) (2) (-3) (-1))
  | 28 => (ofSix (-7) (-3) (3) (1) (-3) (-1))
  | 29 => (ofSix (-7) (-3) (5) (0) (-2) (-1))
  | 30 => (ofSix (-7) (-2) (3) (0) (-3) (-1))
  | 31 => (ofSix (-7) (0) (2) (-3) (-2) (-1))
  | 32 => (ofSix (-7) (0) (3) (-2) (-1) (-1))
  | 33 => (ofSix (-6) (-1) (3) (-1) (-2) (-1))
  | 34 => (ofSix (-5) (-3) (2) (3) (-4) (-1))
  | 35 => (ofSix (-5) (-3) (4) (0) (-2) (-1))
  | 36 => (ofSix (-5) (0) (2) (-3) (-1) (-1))
  | 37 => (ofSix (-5) (1) (2) (-2) (-3) (0))
  | 38 => (ofSix (-4) (-3) (3) (1) (-2) (-1))
  | 39 => (ofSix (-4) (1) (2) (-1) (-3) (0))
  | 40 => (ofSix (-3) (-2) (2) (1) (-3) (-1))
  | 41 => (ofSix (-3) (-2) (2) (2) (-3) (-1))
  | 42 => (ofSix (-3) (-2) (3) (0) (-2) (-1))
  | 43 => (ofSix (-3) (-2) (3) (1) (-2) (0))
  | 44 => (ofSix (-3) (-1) (2) (1) (-3) (0))
  | 45 => (ofSix (-3) (-1) (3) (0) (-2) (-1))
  | 46 => (ofSix (-3) (0) (2) (-2) (-1) (-1))
  | 47 => (ofSix (-3) (0) (2) (-1) (-2) (-1))
  | _ => (ofSix (-2) (-1) (2) (-1) (-1) (-2))

def seed0 : Cone.State := ⟨14,4,7⟩
theorem domain0 : GenericStrip.Domain 2 seed0.A seed0.H seed0.Z := by unfold GenericStrip.Domain seed0; decide
def strip0 (n : Nat) (i : Fin 6) : Matrix 4 :=
  GenericStrip.phase 2 (GenericStrip.orbit 2 seed0 n).A (GenericStrip.orbit 2 seed0 n).H (GenericStrip.orbit 2 seed0 n).Z i
def seed1 : Cone.State := ⟨33,9,16⟩
theorem domain1 : GenericStrip.Domain 2 seed1.A seed1.H seed1.Z := by unfold GenericStrip.Domain seed1; decide
def strip1 (n : Nat) (i : Fin 6) : Matrix 4 :=
  GenericStrip.phase 2 (GenericStrip.orbit 2 seed1 n).A (GenericStrip.orbit 2 seed1 n).H (GenericStrip.orbit 2 seed1 n).Z i
def seed2 : Cone.State := ⟨30,7,10⟩
theorem domain2 : GenericStrip.Domain 3 seed2.A seed2.H seed2.Z := by unfold GenericStrip.Domain seed2; decide
def strip2 (n : Nat) (i : Fin 6) : Matrix 4 :=
  GenericStrip.phase 3 (GenericStrip.orbit 3 seed2 n).A (GenericStrip.orbit 3 seed2 n).H (GenericStrip.orbit 3 seed2 n).Z i
def seed3 : Cone.State := ⟨177,40,58⟩
theorem domain3 : GenericStrip.Domain 3 seed3.A seed3.H seed3.Z := by unfold GenericStrip.Domain seed3; decide
def strip3 (n : Nat) (i : Fin 6) : Matrix 4 :=
  GenericStrip.phase 3 (GenericStrip.orbit 3 seed3 n).A (GenericStrip.orbit 3 seed3 n).H (GenericStrip.orbit 3 seed3 n).Z i
def seed4 : Cone.State := ⟨668,93,111⟩
theorem domain4 : GenericStrip.Domain 6 seed4.A seed4.H seed4.Z := by unfold GenericStrip.Domain seed4; decide
def strip4 (n : Nat) (i : Fin 6) : Matrix 4 :=
  GenericStrip.phase 6 (GenericStrip.orbit 6 seed4 n).A (GenericStrip.orbit 6 seed4 n).H (GenericStrip.orbit 6 seed4 n).Z i
def seed5 : UnitZeroStrip.Parameters := ⟨3,5,6⟩
theorem domain5 : UnitZeroStrip.Domain 2 seed5.u seed5.v seed5.w := by unfold UnitZeroStrip.Domain seed5; decide
def strip5 (n : Nat) (i : Fin 10) : Matrix 4 := UnitZeroStrip.strip 2 seed5 n i
def seed6 : UnitZeroStrip.Parameters := ⟨3,7,9⟩
theorem domain6 : UnitZeroStrip.Domain 2 seed6.u seed6.v seed6.w := by unfold UnitZeroStrip.Domain seed6; decide
def strip6 (n : Nat) (i : Fin 10) : Matrix 4 := UnitZeroStrip.strip 2 seed6 n i
def seed7 : UnitZeroStrip.Parameters := ⟨2,7,18⟩
theorem domain7 : UnitZeroStrip.Domain 3 seed7.u seed7.v seed7.w := by unfold UnitZeroStrip.Domain seed7; decide
def strip7 (n : Nat) (i : Fin 10) : Matrix 4 := UnitZeroStrip.strip 3 seed7 n i
def seed8 : UnitZeroStrip.Parameters := ⟨3,10,26⟩
theorem domain8 : UnitZeroStrip.Domain 3 seed8.u seed8.v seed8.w := by unfold UnitZeroStrip.Domain seed8; decide
def strip8 (n : Nat) (i : Fin 10) : Matrix 4 := UnitZeroStrip.strip 3 seed8 n i

inductive Core : Matrix 4 → Prop
  | finite (i : Fin 49) : Core (node i)
  | strip0 (n : Nat) (i : Fin 6) : Core (strip0 n i)
  | strip1 (n : Nat) (i : Fin 6) : Core (strip1 n i)
  | strip2 (n : Nat) (i : Fin 6) : Core (strip2 n i)
  | strip3 (n : Nat) (i : Fin 6) : Core (strip3 n i)
  | strip4 (n : Nat) (i : Fin 6) : Core (strip4 n i)
  | strip5 (n : Nat) (i : Fin 10) : Core (strip5 n i)
  | strip6 (n : Nat) (i : Fin 10) : Core (strip6 n i)
  | strip7 (n : Nat) (i : Fin 10) : Core (strip7 n i)
  | strip8 (n : Nat) (i : Fin 10) : Core (strip8 n i)
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
  have he : relabel (mutate (node 0) 0) perm5 = WeakForks.template (7) (6) (4658) (41) (31938) (93) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 0) 0) perm5) u v = (WeakForks.template (7) (6) (4658) (41) (31938) (93)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (mutate (node 0) 0) perm5) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (7) (6) (4658) (41) (31938) (93) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm5 hb

theorem edge0_1 : Core (mutate (node 0) 1) ∨
    WeakForks.IsWeakFork (mutate (node 0) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 0) 1) 1 := by
  right; right
  have he : relabel (reverse (mutate (node 0) 1)) perm6 = WeakRegions.root (4658) (433200) (3111537) (93) (668) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 0) 1)) perm6) u v = (WeakRegions.root (4658) (433200) (3111537) (93) (668) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 0) 1)) perm6) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (4658) (433200) (3111537) (93) (668) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm6 hb)

theorem edge0_2 : Core (mutate (node 0) 2) ∨
    WeakForks.IsWeakFork (mutate (node 0) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 0) 2) 2 := by
  have he : mutate (node 0) 2 = reverse (relabel (strip4 0 2) perm16) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 0) 2) u v = (reverse (relabel (strip4 0 2) perm16)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.strip4 0 2) perm16))

theorem edge0_3 : Core (mutate (node 0) 3) ∨
    WeakForks.IsWeakFork (mutate (node 0) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 0) 3) 3 := by
  have he : mutate (node 0) 3 = relabel (node 2) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 0) 3) u v = (relabel (node 2) perm21) u v from by decide) u v
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
  have he : relabel (mutate (node 1) 0) perm5 = WeakForks.template (4) (3) (690) (11) (2583) (40) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 1) 0) perm5) u v = (WeakForks.template (4) (3) (690) (11) (2583) (40)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (mutate (node 1) 0) perm5) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (4) (3) (690) (11) (2583) (40) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm5 hb

theorem edge1_1 : Core (mutate (node 1) 1) ∨
    WeakForks.IsWeakFork (mutate (node 1) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 1) 1) 1 := by
  right; right
  have he : relabel (reverse (mutate (node 1) 1)) perm6 = WeakRegions.root (690) (27603) (122126) (40) (177) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 1) 1)) perm6) u v = (WeakRegions.root (690) (27603) (122126) (40) (177) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 1) 1)) perm6) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (690) (27603) (122126) (40) (177) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm6 hb)

theorem edge1_2 : Core (mutate (node 1) 2) ∨
    WeakForks.IsWeakFork (mutate (node 1) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 1) 2) 2 := by
  have he : mutate (node 1) 2 = reverse (relabel (strip3 0 2) perm16) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 1) 2) u v = (reverse (relabel (strip3 0 2) perm16)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.strip3 0 2) perm16))

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
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge2_0 : Core (mutate (node 2) 0) ∨
    WeakForks.IsWeakFork (mutate (node 2) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 2) 0) 0 := by
  have he : mutate (node 2) 0 = relabel (node 0) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 2) 0) u v = (relabel (node 0) perm21) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 0) perm21)

theorem edge2_1 : Core (mutate (node 2) 1) ∨
    WeakForks.IsWeakFork (mutate (node 2) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 2) 1) 1 := by
  right; right
  have he : relabel (reverse (mutate (node 2) 1)) perm6 = WeakRegions.root (668) (62125) (12017) (93) (18) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 2) 1)) perm6) u v = (WeakRegions.root (668) (62125) (12017) (93) (18) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 2) 1)) perm6) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (668) (62125) (12017) (93) (18) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm6 hb)

theorem edge2_2 : Core (mutate (node 2) 2) ∨
    WeakForks.IsWeakFork (mutate (node 2) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 2) 2) 2 := by
  have he : mutate (node 2) 2 = reverse (relabel (strip4 0 0) perm4) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 2) 2) u v = (reverse (relabel (strip4 0 0) perm4)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.strip4 0 0) perm4))

theorem edge2_3 : Core (mutate (node 2) 3) ∨
    WeakForks.IsWeakFork (mutate (node 2) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 2) 3) 3 := by
  have he : mutate (node 2) 3 = reverse (relabel (node 3) perm7) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 2) 3) u v = (reverse (relabel (node 3) perm7)) u v from by decide) u v
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
  have he : relabel (mutate (node 3) 0) perm4 = WeakForks.template (93) (542) (18) (50400) (1675) (7) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 3) 0) perm4) u v = (WeakForks.template (93) (542) (18) (50400) (1675) (7)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (mutate (node 3) 0) perm4) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (93) (542) (18) (50400) (1675) (7) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm4 hb

theorem edge3_1 : Core (mutate (node 3) 1) ∨
    WeakForks.IsWeakFork (mutate (node 3) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 3) 1) 1 := by
  right; left
  have he : relabel (reverse (mutate (node 3) 1)) perm10 = WeakForks.template (6) (542) (7) (3159) (41) (18) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 3) 1)) perm10) u v = (WeakForks.template (6) (542) (7) (3159) (41) (18)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (reverse (mutate (node 3) 1)) perm10) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (6) (542) (7) (3159) (41) (18) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_reverse (WeakForks.fork_of_relabel perm10 hb)

theorem edge3_2 : Core (mutate (node 3) 2) ∨
    WeakForks.IsWeakFork (mutate (node 3) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 3) 2) 2 := by
  have he : mutate (node 3) 2 = reverse (relabel (node 2) perm7) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 3) 2) u v = (reverse (relabel (node 2) perm7)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 2) perm7))

theorem edge3_3 : Core (mutate (node 3) 3) ∨
    WeakForks.IsWeakFork (mutate (node 3) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 3) 3) 3 := by
  have he : mutate (node 3) 3 = relabel (node 9) perm5 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 3) 3) u v = (relabel (node 9) perm5) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 9) perm5)

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
  have he : relabel (reverse (mutate (node 4) 1)) perm6 = WeakRegions.root (177) (7081) (3182) (40) (18) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 4) 1)) perm6) u v = (WeakRegions.root (177) (7081) (3182) (40) (18) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 4) 1)) perm6) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (177) (7081) (3182) (40) (18) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm6 hb)

theorem edge4_2 : Core (mutate (node 4) 2) ∨
    WeakForks.IsWeakFork (mutate (node 4) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 4) 2) 2 := by
  have he : mutate (node 4) 2 = reverse (relabel (strip3 0 0) perm4) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 4) 2) u v = (reverse (relabel (strip3 0 0) perm4)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.strip3 0 0) perm4))

theorem edge4_3 : Core (mutate (node 4) 3) ∨
    WeakForks.IsWeakFork (mutate (node 4) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 4) 3) 3 := by
  have he : mutate (node 4) 3 = reverse (relabel (node 8) perm7) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 4) 3) u v = (reverse (relabel (node 8) perm7)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 8) perm7))

theorem cyclic5 : ¬ Acyclic (node 5) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge5_0 : Core (mutate (node 5) 0) ∨
    WeakForks.IsWeakFork (mutate (node 5) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 5) 0) 0 := by
  right; left
  have he : relabel (mutate (node 5) 0) perm5 = WeakForks.template (4) (3) (117) (11) (438) (7) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 5) 0) perm5) u v = (WeakForks.template (4) (3) (117) (11) (438) (7)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (mutate (node 5) 0) perm5) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (4) (3) (117) (11) (438) (7) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm5 hb

theorem edge5_1 : Core (mutate (node 5) 1) ∨
    WeakForks.IsWeakFork (mutate (node 5) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 5) 1) 1 := by
  right; right
  have he : relabel (reverse (mutate (node 5) 1)) perm6 = WeakRegions.root (117) (822) (3506) (7) (30) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 5) 1)) perm6) u v = (WeakRegions.root (117) (822) (3506) (7) (30) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 5) 1)) perm6) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (117) (822) (3506) (7) (30) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm6 hb)

theorem edge5_2 : Core (mutate (node 5) 2) ∨
    WeakForks.IsWeakFork (mutate (node 5) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 5) 2) 2 := by
  have he : mutate (node 5) 2 = reverse (relabel (strip2 0 2) perm16) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 5) 2) u v = (reverse (relabel (strip2 0 2) perm16)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.strip2 0 2) perm16))

theorem edge5_3 : Core (mutate (node 5) 3) ∨
    WeakForks.IsWeakFork (mutate (node 5) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 5) 3) 3 := by
  have he : mutate (node 5) 3 = relabel (node 16) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 5) 3) u v = (relabel (node 16) perm21) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 16) perm21)

theorem cyclic6 : ¬ Acyclic (node 6) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge6_0 : Core (mutate (node 6) 0) ∨
    WeakForks.IsWeakFork (mutate (node 6) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 6) 0) 0 := by
  right; left
  have he : relabel (mutate (node 6) 0) perm5 = WeakForks.template (7) (6) (111) (41) (761) (2) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 6) 0) perm5) u v = (WeakForks.template (7) (6) (111) (41) (761) (2)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (mutate (node 6) 0) perm5) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (7) (6) (111) (41) (761) (2) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm5 hb

theorem edge6_1 : Core (mutate (node 6) 1) ∨
    WeakForks.IsWeakFork (mutate (node 6) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 6) 1) 1 := by
  right; right
  have he : relabel (reverse (mutate (node 6) 1)) perm6 = WeakRegions.root (111) (228) (1769) (2) (16) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 6) 1)) perm6) u v = (WeakRegions.root (111) (228) (1769) (2) (16) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 6) 1)) perm6) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (111) (228) (1769) (2) (16) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm6 hb)

theorem edge6_2 : Core (mutate (node 6) 2) ∨
    WeakForks.IsWeakFork (mutate (node 6) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 6) 2) 2 := by
  have he : mutate (node 6) 2 = reverse (relabel (node 7) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 6) 2) u v = (reverse (relabel (node 7) perm6)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 7) perm6))

theorem edge6_3 : Core (mutate (node 6) 3) ∨
    WeakForks.IsWeakFork (mutate (node 6) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 6) 3) 3 := by
  have he : mutate (node 6) 3 = relabel (node 19) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 6) 3) u v = (relabel (node 19) perm21) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 19) perm21)

theorem cyclic7 : ¬ Acyclic (node 7) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge7_0 : Core (mutate (node 7) 0) ∨
    WeakForks.IsWeakFork (mutate (node 7) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 7) 0) 0 := by
  right; left
  have he : relabel (mutate (node 7) 0) perm5 = WeakForks.template (18) (2) (111) (35) (1997) (6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 7) 0) perm5) u v = (WeakForks.template (18) (2) (111) (35) (1997) (6)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (mutate (node 7) 0) perm5) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (18) (2) (111) (35) (1997) (6) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm5 hb

theorem edge7_1 : Core (mutate (node 7) 1) ∨
    WeakForks.IsWeakFork (mutate (node 7) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 7) 1) 1 := by
  have he : mutate (node 7) 1 = relabel (strip4 0 0) perm22 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 7) 1) u v = (relabel (strip4 0 0) perm22) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.strip4 0 0) perm22)

theorem edge7_2 : Core (mutate (node 7) 2) ∨
    WeakForks.IsWeakFork (mutate (node 7) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 7) 2) 2 := by
  have he : mutate (node 7) 2 = reverse (relabel (node 6) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 7) 2) u v = (reverse (relabel (node 6) perm6)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 6) perm6))

theorem edge7_3 : Core (mutate (node 7) 3) ∨
    WeakForks.IsWeakFork (mutate (node 7) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 7) 3) 3 := by
  have he : mutate (node 7) 3 = relabel (node 9) perm1 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 7) 3) u v = (relabel (node 9) perm1) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 9) perm1)

theorem cyclic8 : ¬ Acyclic (node 8) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge8_0 : Core (mutate (node 8) 0) ∨
    WeakForks.IsWeakFork (mutate (node 8) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 8) 0) 0 := by
  right; left
  have he : relabel (mutate (node 8) 0) perm4 = WeakForks.template (40) (105) (18) (4197) (721) (4) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 8) 0) perm4) u v = (WeakForks.template (40) (105) (18) (4197) (721) (4)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (mutate (node 8) 0) perm4) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (40) (105) (18) (4197) (721) (4) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm4 hb

theorem edge8_1 : Core (mutate (node 8) 1) ∨
    WeakForks.IsWeakFork (mutate (node 8) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 8) 1) 1 := by
  right; left
  have he : relabel (reverse (mutate (node 8) 1)) perm10 = WeakForks.template (3) (105) (4) (275) (11) (18) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 8) 1)) perm10) u v = (WeakForks.template (3) (105) (4) (275) (11) (18)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (reverse (mutate (node 8) 1)) perm10) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (3) (105) (4) (275) (11) (18) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_reverse (WeakForks.fork_of_relabel perm10 hb)

theorem edge8_2 : Core (mutate (node 8) 2) ∨
    WeakForks.IsWeakFork (mutate (node 8) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 8) 2) 2 := by
  have he : mutate (node 8) 2 = reverse (relabel (node 4) perm7) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 8) 2) u v = (reverse (relabel (node 4) perm7)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 4) perm7))

theorem edge8_3 : Core (mutate (node 8) 3) ∨
    WeakForks.IsWeakFork (mutate (node 8) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 8) 3) 3 := by
  have he : mutate (node 8) 3 = relabel (node 13) perm5 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 8) 3) u v = (relabel (node 13) perm5) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 13) perm5)

theorem cyclic9 : ¬ Acyclic (node 9) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge9_0 : Core (mutate (node 9) 0) ∨
    WeakForks.IsWeakFork (mutate (node 9) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 9) 0) 0 := by
  right; right
  have he : relabel (reverse (mutate (node 9) 0)) perm5 = WeakRegions.root (16) (287) (1482) (18) (93) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 9) 0)) perm5) u v = (WeakRegions.root (16) (287) (1482) (18) (93) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 9) 0)) perm5) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (16) (287) (1482) (18) (93) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm5 hb)

theorem edge9_1 : Core (mutate (node 9) 1) ∨
    WeakForks.IsWeakFork (mutate (node 9) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 9) 1) 1 := by
  have he : mutate (node 9) 1 = relabel (node 3) perm5 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 9) 1) u v = (relabel (node 3) perm5) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 3) perm5)

theorem edge9_2 : Core (mutate (node 9) 2) ∨
    WeakForks.IsWeakFork (mutate (node 9) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 9) 2) 2 := by
  have he : mutate (node 9) 2 = relabel (node 7) perm1 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 9) 2) u v = (relabel (node 7) perm1) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 7) perm1)

theorem edge9_3 : Core (mutate (node 9) 3) ∨
    WeakForks.IsWeakFork (mutate (node 9) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 9) 3) 3 := by
  have he : mutate (node 9) 3 = relabel (node 18) perm5 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 9) 3) u v = (relabel (node 18) perm5) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 18) perm5)

theorem cyclic10 : ¬ Acyclic (node 10) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge10_0 : Core (mutate (node 10) 0) ∨
    WeakForks.IsWeakFork (mutate (node 10) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 10) 0) 0 := by
  right; left
  have he : relabel (mutate (node 10) 0) perm5 = WeakForks.template (3) (2) (92) (5) (243) (9) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 10) 0) perm5) u v = (WeakForks.template (3) (2) (92) (5) (243) (9)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (mutate (node 10) 0) perm5) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (3) (2) (92) (5) (243) (9) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm5 hb

theorem edge10_1 : Core (mutate (node 10) 1) ∨
    WeakForks.IsWeakFork (mutate (node 10) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 10) 1) 1 := by
  right; right
  have he : relabel (reverse (mutate (node 10) 1)) perm6 = WeakRegions.root (92) (830) (3033) (9) (33) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 10) 1)) perm6) u v = (WeakRegions.root (92) (830) (3033) (9) (33) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 10) 1)) perm6) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (92) (830) (3033) (9) (33) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm6 hb)

theorem edge10_2 : Core (mutate (node 10) 2) ∨
    WeakForks.IsWeakFork (mutate (node 10) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 10) 2) 2 := by
  have he : mutate (node 10) 2 = reverse (relabel (strip1 0 2) perm16) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 10) 2) u v = (reverse (relabel (strip1 0 2) perm16)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.strip1 0 2) perm16))

theorem edge10_3 : Core (mutate (node 10) 3) ∨
    WeakForks.IsWeakFork (mutate (node 10) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 10) 3) 3 := by
  have he : mutate (node 10) 3 = relabel (node 15) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 10) 3) u v = (relabel (node 15) perm21) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 15) perm21)

theorem cyclic11 : ¬ Acyclic (node 11) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge11_0 : Core (mutate (node 11) 0) ∨
    WeakForks.IsWeakFork (mutate (node 11) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 11) 0) 0 := by
  right; left
  have he : relabel (mutate (node 11) 0) perm5 = WeakForks.template (4) (3) (58) (11) (217) (3) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 11) 0) perm5) u v = (WeakForks.template (4) (3) (58) (11) (217) (3)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (mutate (node 11) 0) perm5) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (4) (3) (58) (11) (217) (3) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm5 hb

theorem edge11_1 : Core (mutate (node 11) 1) ∨
    WeakForks.IsWeakFork (mutate (node 11) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 11) 1) 1 := by
  right; right
  have he : relabel (reverse (mutate (node 11) 1)) perm6 = WeakRegions.root (58) (177) (866) (3) (15) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 11) 1)) perm6) u v = (WeakRegions.root (58) (177) (866) (3) (15) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 11) 1)) perm6) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (58) (177) (866) (3) (15) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm6 hb)

theorem edge11_2 : Core (mutate (node 11) 2) ∨
    WeakForks.IsWeakFork (mutate (node 11) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 11) 2) 2 := by
  have he : mutate (node 11) 2 = reverse (relabel (node 12) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 11) 2) u v = (reverse (relabel (node 12) perm6)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 12) perm6))

theorem edge11_3 : Core (mutate (node 11) 3) ∨
    WeakForks.IsWeakFork (mutate (node 11) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 11) 3) 3 := by
  have he : mutate (node 11) 3 = relabel (node 21) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 11) 3) u v = (relabel (node 21) perm21) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 21) perm21)

theorem cyclic12 : ¬ Acyclic (node 12) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge12_0 : Core (mutate (node 12) 0) ∨
    WeakForks.IsWeakFork (mutate (node 12) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 12) 0) 0 := by
  right; left
  have he : relabel (mutate (node 12) 0) perm5 = WeakForks.template (18) (3) (58) (53) (1043) (3) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 12) 0) perm5) u v = (WeakForks.template (18) (3) (58) (53) (1043) (3)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (mutate (node 12) 0) perm5) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (18) (3) (58) (53) (1043) (3) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm5 hb

theorem edge12_1 : Core (mutate (node 12) 1) ∨
    WeakForks.IsWeakFork (mutate (node 12) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 12) 1) 1 := by
  have he : mutate (node 12) 1 = relabel (strip3 0 0) perm22 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 12) 1) u v = (relabel (strip3 0 0) perm22) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.strip3 0 0) perm22)

theorem edge12_2 : Core (mutate (node 12) 2) ∨
    WeakForks.IsWeakFork (mutate (node 12) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 12) 2) 2 := by
  have he : mutate (node 12) 2 = reverse (relabel (node 11) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 12) 2) u v = (reverse (relabel (node 11) perm6)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 11) perm6))

theorem edge12_3 : Core (mutate (node 12) 3) ∨
    WeakForks.IsWeakFork (mutate (node 12) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 12) 3) 3 := by
  have he : mutate (node 12) 3 = relabel (node 13) perm1 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 12) 3) u v = (relabel (node 13) perm1) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 13) perm1)

theorem cyclic13 : ¬ Acyclic (node 13) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge13_0 : Core (mutate (node 13) 0) ∨
    WeakForks.IsWeakFork (mutate (node 13) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 13) 0) 0 := by
  right; right
  have he : relabel (reverse (mutate (node 13) 0)) perm5 = WeakRegions.root (15) (269) (597) (18) (40) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 13) 0)) perm5) u v = (WeakRegions.root (15) (269) (597) (18) (40) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 13) 0)) perm5) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (15) (269) (597) (18) (40) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm5 hb)

theorem edge13_1 : Core (mutate (node 13) 1) ∨
    WeakForks.IsWeakFork (mutate (node 13) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 13) 1) 1 := by
  have he : mutate (node 13) 1 = relabel (node 8) perm5 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 13) 1) u v = (relabel (node 8) perm5) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 8) perm5)

theorem edge13_2 : Core (mutate (node 13) 2) ∨
    WeakForks.IsWeakFork (mutate (node 13) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 13) 2) 2 := by
  have he : mutate (node 13) 2 = relabel (node 12) perm1 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 13) 2) u v = (relabel (node 12) perm1) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 12) perm1)

theorem edge13_3 : Core (mutate (node 13) 3) ∨
    WeakForks.IsWeakFork (mutate (node 13) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 13) 3) 3 := by
  have he : mutate (node 13) 3 = relabel (node 20) perm5 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 13) 3) u v = (relabel (node 20) perm5) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 20) perm5)

theorem cyclic14 : ¬ Acyclic (node 14) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge14_0 : Core (mutate (node 14) 0) ∨
    WeakForks.IsWeakFork (mutate (node 14) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 14) 0) 0 := by
  right; left
  have he : relabel (mutate (node 14) 0) perm5 = WeakForks.template (3) (2) (39) (5) (103) (4) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 14) 0) perm5) u v = (WeakForks.template (3) (2) (39) (5) (103) (4)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (mutate (node 14) 0) perm5) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (3) (2) (39) (5) (103) (4) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm5 hb

theorem edge14_1 : Core (mutate (node 14) 1) ∨
    WeakForks.IsWeakFork (mutate (node 14) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 14) 1) 1 := by
  right; right
  have he : relabel (reverse (mutate (node 14) 1)) perm6 = WeakRegions.root (39) (158) (543) (4) (14) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 14) 1)) perm6) u v = (WeakRegions.root (39) (158) (543) (4) (14) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 14) 1)) perm6) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (39) (158) (543) (4) (14) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm6 hb)

theorem edge14_2 : Core (mutate (node 14) 2) ∨
    WeakForks.IsWeakFork (mutate (node 14) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 14) 2) 2 := by
  have he : mutate (node 14) 2 = reverse (relabel (strip0 0 2) perm16) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 14) 2) u v = (reverse (relabel (strip0 0 2) perm16)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.strip0 0 2) perm16))

theorem edge14_3 : Core (mutate (node 14) 3) ∨
    WeakForks.IsWeakFork (mutate (node 14) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 14) 3) 3 := by
  have he : mutate (node 14) 3 = relabel (node 22) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 14) 3) u v = (relabel (node 22) perm21) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 22) perm21)

theorem cyclic15 : ¬ Acyclic (node 15) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge15_0 : Core (mutate (node 15) 0) ∨
    WeakForks.IsWeakFork (mutate (node 15) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 15) 0) 0 := by
  have he : mutate (node 15) 0 = relabel (node 10) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 15) 0) u v = (relabel (node 10) perm21) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 10) perm21)

theorem edge15_1 : Core (mutate (node 15) 1) ∨
    WeakForks.IsWeakFork (mutate (node 15) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 15) 1) 1 := by
  right; right
  have he : relabel (reverse (mutate (node 15) 1)) perm6 = WeakRegions.root (33) (298) (228) (9) (7) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 15) 1)) perm6) u v = (WeakRegions.root (33) (298) (228) (9) (7) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 15) 1)) perm6) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (33) (298) (228) (9) (7) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm6 hb)

theorem edge15_2 : Core (mutate (node 15) 2) ∨
    WeakForks.IsWeakFork (mutate (node 15) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 15) 2) 2 := by
  have he : mutate (node 15) 2 = reverse (relabel (strip1 0 0) perm4) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 15) 2) u v = (reverse (relabel (strip1 0 0) perm4)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.strip1 0 0) perm4))

theorem edge15_3 : Core (mutate (node 15) 3) ∨
    WeakForks.IsWeakFork (mutate (node 15) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 15) 3) 3 := by
  have he : mutate (node 15) 3 = reverse (relabel (node 23) perm7) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 15) 3) u v = (reverse (relabel (node 23) perm7)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 23) perm7))

theorem cyclic16 : ¬ Acyclic (node 16) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge16_0 : Core (mutate (node 16) 0) ∨
    WeakForks.IsWeakFork (mutate (node 16) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 16) 0) 0 := by
  have he : mutate (node 16) 0 = relabel (node 5) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 16) 0) u v = (relabel (node 5) perm21) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 5) perm21)

theorem edge16_1 : Core (mutate (node 16) 1) ∨
    WeakForks.IsWeakFork (mutate (node 16) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 16) 1) 1 := by
  right; right
  have he : relabel (reverse (mutate (node 16) 1)) perm6 = WeakRegions.root (30) (211) (86) (7) (3) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 16) 1)) perm6) u v = (WeakRegions.root (30) (211) (86) (7) (3) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 16) 1)) perm6) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (30) (211) (86) (7) (3) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm6 hb)

theorem edge16_2 : Core (mutate (node 16) 2) ∨
    WeakForks.IsWeakFork (mutate (node 16) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 16) 2) 2 := by
  have he : mutate (node 16) 2 = reverse (relabel (strip2 0 0) perm4) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 16) 2) u v = (reverse (relabel (strip2 0 0) perm4)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.strip2 0 0) perm4))

theorem edge16_3 : Core (mutate (node 16) 3) ∨
    WeakForks.IsWeakFork (mutate (node 16) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 16) 3) 3 := by
  have he : mutate (node 16) 3 = relabel (node 17) perm1 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 16) 3) u v = (relabel (node 17) perm1) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 17) perm1)

theorem cyclic17 : ¬ Acyclic (node 17) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge17_0 : Core (mutate (node 17) 0) ∨
    WeakForks.IsWeakFork (mutate (node 17) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 17) 0) 0 := by
  right; left
  have he : relabel (mutate (node 17) 0) perm4 = WeakForks.template (3) (18) (4) (47) (11) (3) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 17) 0) perm4) u v = (WeakForks.template (3) (18) (4) (47) (11) (3)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (mutate (node 17) 0) perm4) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (3) (18) (4) (47) (11) (3) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm4 hb

theorem edge17_1 : Core (mutate (node 17) 1) ∨
    WeakForks.IsWeakFork (mutate (node 17) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 17) 1) 1 := by
  right; left
  have he : relabel (reverse (mutate (node 17) 1)) perm10 = WeakForks.template (7) (18) (3) (123) (22) (4) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 17) 1)) perm10) u v = (WeakForks.template (7) (18) (3) (123) (22) (4)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (reverse (mutate (node 17) 1)) perm10) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (7) (18) (3) (123) (22) (4) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_reverse (WeakForks.fork_of_relabel perm10 hb)

theorem edge17_2 : Core (mutate (node 17) 2) ∨
    WeakForks.IsWeakFork (mutate (node 17) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 17) 2) 2 := by
  have he : mutate (node 17) 2 = relabel (node 16) perm1 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 17) 2) u v = (relabel (node 16) perm1) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 16) perm1)

theorem edge17_3 : Core (mutate (node 17) 3) ∨
    WeakForks.IsWeakFork (mutate (node 17) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 17) 3) 3 := by
  have he : mutate (node 17) 3 = reverse (relabel (node 28) perm19) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 17) 3) u v = (reverse (relabel (node 28) perm19)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 28) perm19))

theorem cyclic18 : ¬ Acyclic (node 18) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge18_0 : Core (mutate (node 18) 0) ∨
    WeakForks.IsWeakFork (mutate (node 18) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 18) 0) 0 := by
  right; right
  have he : relabel (reverse (mutate (node 18) 0)) perm4 = WeakRegions.root (3) (42) (5) (16) (2) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 18) 0)) perm4) u v = (WeakRegions.root (3) (42) (5) (16) (2) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 18) 0)) perm4) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (3) (42) (5) (16) (2) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm4 hb)

theorem edge18_1 : Core (mutate (node 18) 1) ∨
    WeakForks.IsWeakFork (mutate (node 18) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 18) 1) 1 := by
  have he : mutate (node 18) 1 = relabel (node 9) perm5 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 18) 1) u v = (relabel (node 9) perm5) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 9) perm5)

theorem edge18_2 : Core (mutate (node 18) 2) ∨
    WeakForks.IsWeakFork (mutate (node 18) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 18) 2) 2 := by
  have he : mutate (node 18) 2 = reverse (relabel (node 19) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 18) 2) u v = (reverse (relabel (node 19) perm6)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 19) perm6))

theorem edge18_3 : Core (mutate (node 18) 3) ∨
    WeakForks.IsWeakFork (mutate (node 18) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 18) 3) 3 := by
  have he : mutate (node 18) 3 = relabel (node 33) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 18) 3) u v = (relabel (node 33) perm21) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 33) perm21)

theorem cyclic19 : ¬ Acyclic (node 19) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge19_0 : Core (mutate (node 19) 0) ∨
    WeakForks.IsWeakFork (mutate (node 19) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 19) 0) 0 := by
  have he : mutate (node 19) 0 = relabel (node 6) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 19) 0) u v = (relabel (node 6) perm21) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 6) perm21)

theorem edge19_1 : Core (mutate (node 19) 1) ∨
    WeakForks.IsWeakFork (mutate (node 19) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 19) 1) 1 := by
  have he : mutate (node 19) 1 = relabel (strip1 0 0) perm22 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 19) 1) u v = (relabel (strip1 0 0) perm22) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.strip1 0 0) perm22)

theorem edge19_2 : Core (mutate (node 19) 2) ∨
    WeakForks.IsWeakFork (mutate (node 19) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 19) 2) 2 := by
  have he : mutate (node 19) 2 = reverse (relabel (node 18) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 19) 2) u v = (reverse (relabel (node 18) perm6)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 18) perm6))

theorem edge19_3 : Core (mutate (node 19) 3) ∨
    WeakForks.IsWeakFork (mutate (node 19) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 19) 3) 3 := by
  have he : mutate (node 19) 3 = relabel (node 26) perm1 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 19) 3) u v = (relabel (node 26) perm1) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 26) perm1)

theorem cyclic20 : ¬ Acyclic (node 20) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge20_0 : Core (mutate (node 20) 0) ∨
    WeakForks.IsWeakFork (mutate (node 20) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 20) 0) 0 := by
  right; right
  have he : relabel (reverse (mutate (node 20) 0)) perm4 = WeakRegions.root (5) (72) (14) (15) (3) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 20) 0)) perm4) u v = (WeakRegions.root (5) (72) (14) (15) (3) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 20) 0)) perm4) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (5) (72) (14) (15) (3) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm4 hb)

theorem edge20_1 : Core (mutate (node 20) 1) ∨
    WeakForks.IsWeakFork (mutate (node 20) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 20) 1) 1 := by
  have he : mutate (node 20) 1 = relabel (node 13) perm5 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 20) 1) u v = (relabel (node 13) perm5) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 13) perm5)

theorem edge20_2 : Core (mutate (node 20) 2) ∨
    WeakForks.IsWeakFork (mutate (node 20) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 20) 2) 2 := by
  have he : mutate (node 20) 2 = reverse (relabel (node 21) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 20) 2) u v = (reverse (relabel (node 21) perm6)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 21) perm6))

theorem edge20_3 : Core (mutate (node 20) 3) ∨
    WeakForks.IsWeakFork (mutate (node 20) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 20) 3) 3 := by
  have he : mutate (node 20) 3 = relabel (node 36) perm3 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 20) 3) u v = (relabel (node 36) perm3) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 36) perm3)

theorem cyclic21 : ¬ Acyclic (node 21) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge21_0 : Core (mutate (node 21) 0) ∨
    WeakForks.IsWeakFork (mutate (node 21) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 21) 0) 0 := by
  have he : mutate (node 21) 0 = relabel (node 11) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 21) 0) u v = (relabel (node 11) perm21) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 11) perm21)

theorem edge21_1 : Core (mutate (node 21) 1) ∨
    WeakForks.IsWeakFork (mutate (node 21) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 21) 1) 1 := by
  right; right
  have he : relabel (reverse (mutate (node 21) 1)) perm6 = WeakRegions.root (15) (46) (26) (3) (2) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 21) 1)) perm6) u v = (WeakRegions.root (15) (46) (26) (3) (2) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 21) 1)) perm6) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (15) (46) (26) (3) (2) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm6 hb)

theorem edge21_2 : Core (mutate (node 21) 2) ∨
    WeakForks.IsWeakFork (mutate (node 21) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 21) 2) 2 := by
  have he : mutate (node 21) 2 = reverse (relabel (node 20) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 21) 2) u v = (reverse (relabel (node 20) perm6)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 20) perm6))

theorem edge21_3 : Core (mutate (node 21) 3) ∨
    WeakForks.IsWeakFork (mutate (node 21) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 21) 3) 3 := by
  have he : mutate (node 21) 3 = relabel (node 27) perm1 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 21) 3) u v = (relabel (node 27) perm1) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 27) perm1)

theorem cyclic22 : ¬ Acyclic (node 22) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge22_0 : Core (mutate (node 22) 0) ∨
    WeakForks.IsWeakFork (mutate (node 22) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 22) 0) 0 := by
  have he : mutate (node 22) 0 = relabel (node 14) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 22) 0) u v = (relabel (node 14) perm21) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 14) perm21)

theorem edge22_1 : Core (mutate (node 22) 1) ∨
    WeakForks.IsWeakFork (mutate (node 22) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 22) 1) 1 := by
  right; right
  have he : relabel (reverse (mutate (node 22) 1)) perm6 = WeakRegions.root (14) (57) (39) (4) (3) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 22) 1)) perm6) u v = (WeakRegions.root (14) (57) (39) (4) (3) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 22) 1)) perm6) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (14) (57) (39) (4) (3) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm6 hb)

theorem edge22_2 : Core (mutate (node 22) 2) ∨
    WeakForks.IsWeakFork (mutate (node 22) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 22) 2) 2 := by
  have he : mutate (node 22) 2 = reverse (relabel (strip0 0 0) perm4) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 22) 2) u v = (reverse (relabel (strip0 0 0) perm4)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.strip0 0 0) perm4))

theorem edge22_3 : Core (mutate (node 22) 3) ∨
    WeakForks.IsWeakFork (mutate (node 22) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 22) 3) 3 := by
  have he : mutate (node 22) 3 = relabel (node 34) perm1 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 22) 3) u v = (relabel (node 34) perm1) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 34) perm1)

theorem cyclic23 : ¬ Acyclic (node 23) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge23_0 : Core (mutate (node 23) 0) ∨
    WeakForks.IsWeakFork (mutate (node 23) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 23) 0) 0 := by
  right; left
  have he : relabel (mutate (node 23) 0) perm4 = WeakForks.template (9) (12) (7) (106) (64) (3) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 23) 0) perm4) u v = (WeakForks.template (9) (12) (7) (106) (64) (3)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (mutate (node 23) 0) perm4) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (9) (12) (7) (106) (64) (3) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm4 hb

theorem edge23_1 : Core (mutate (node 23) 1) ∨
    WeakForks.IsWeakFork (mutate (node 23) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 23) 1) 1 := by
  right; left
  have he : relabel (reverse (mutate (node 23) 1)) perm10 = WeakForks.template (2) (12) (3) (15) (5) (7) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 23) 1)) perm10) u v = (WeakForks.template (2) (12) (3) (15) (5) (7)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (reverse (mutate (node 23) 1)) perm10) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (2) (12) (3) (15) (5) (7) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_reverse (WeakForks.fork_of_relabel perm10 hb)

theorem edge23_2 : Core (mutate (node 23) 2) ∨
    WeakForks.IsWeakFork (mutate (node 23) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 23) 2) 2 := by
  have he : mutate (node 23) 2 = reverse (relabel (node 15) perm7) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 23) 2) u v = (reverse (relabel (node 15) perm7)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 15) perm7))

theorem edge23_3 : Core (mutate (node 23) 3) ∨
    WeakForks.IsWeakFork (mutate (node 23) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 23) 3) 3 := by
  have he : mutate (node 23) 3 = relabel (node 26) perm5 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 23) 3) u v = (relabel (node 26) perm5) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 26) perm5)

theorem cyclic24 : ¬ Acyclic (node 24) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge24_0 : Core (mutate (node 24) 0) ∨
    WeakForks.IsWeakFork (mutate (node 24) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 24) 0) 0 := by
  right; right
  have he : relabel (reverse (mutate (node 24) 0)) perm4 = WeakRegions.root (4) (37) (11) (10) (3) (0) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 24) 0)) perm4) u v = (WeakRegions.root (4) (37) (11) (10) (3) (0)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 24) 0)) perm4) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (4) (37) (11) (10) (3) (0) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm4 hb)

theorem edge24_1 : Core (mutate (node 24) 1) ∨
    WeakForks.IsWeakFork (mutate (node 24) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 24) 1) 1 := by
  have he : mutate (node 24) 1 = reverse (relabel (strip8 0 0) perm14) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 24) 1) u v = (reverse (relabel (strip8 0 0) perm14)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.strip8 0 0) perm14))

theorem edge24_2 : Core (mutate (node 24) 2) ∨
    WeakForks.IsWeakFork (mutate (node 24) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 24) 2) 2 := by
  have he : mutate (node 24) 2 = reverse (relabel (node 25) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 24) 2) u v = (reverse (relabel (node 25) perm6)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 25) perm6))

theorem edge24_3 : Core (mutate (node 24) 3) ∨
    WeakForks.IsWeakFork (mutate (node 24) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 24) 3) 3 := by
  have he : mutate (node 24) 3 = relabel (node 39) perm5 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 24) 3) u v = (relabel (node 39) perm5) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 39) perm5)

theorem cyclic25 : ¬ Acyclic (node 25) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge25_0 : Core (mutate (node 25) 0) ∨
    WeakForks.IsWeakFork (mutate (node 25) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 25) 0) 0 := by
  have he : mutate (node 25) 0 = relabel (strip8 0 1) perm8 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 25) 0) u v = (relabel (strip8 0 1) perm8) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.strip8 0 1) perm8)

theorem edge25_1 : Core (mutate (node 25) 1) ∨
    WeakForks.IsWeakFork (mutate (node 25) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 25) 1) 1 := by
  have he : mutate (node 25) 1 = relabel (strip2 0 0) perm22 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 25) 1) u v = (relabel (strip2 0 0) perm22) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.strip2 0 0) perm22)

theorem edge25_2 : Core (mutate (node 25) 2) ∨
    WeakForks.IsWeakFork (mutate (node 25) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 25) 2) 2 := by
  have he : mutate (node 25) 2 = reverse (relabel (node 24) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 25) 2) u v = (reverse (relabel (node 24) perm6)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 24) perm6))

theorem edge25_3 : Core (mutate (node 25) 3) ∨
    WeakForks.IsWeakFork (mutate (node 25) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 25) 3) 3 := by
  have he : mutate (node 25) 3 = relabel (node 28) perm1 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 25) 3) u v = (relabel (node 28) perm1) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 28) perm1)

theorem cyclic26 : ¬ Acyclic (node 26) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge26_0 : Core (mutate (node 26) 0) ∨
    WeakForks.IsWeakFork (mutate (node 26) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 26) 0) 0 := by
  right; right
  have he : relabel (reverse (mutate (node 26) 0)) perm5 = WeakRegions.root (6) (41) (52) (7) (9) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 26) 0)) perm5) u v = (WeakRegions.root (6) (41) (52) (7) (9) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 26) 0)) perm5) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (6) (41) (52) (7) (9) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm5 hb)

theorem edge26_1 : Core (mutate (node 26) 1) ∨
    WeakForks.IsWeakFork (mutate (node 26) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 26) 1) 1 := by
  have he : mutate (node 26) 1 = relabel (node 23) perm5 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 26) 1) u v = (relabel (node 23) perm5) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 23) perm5)

theorem edge26_2 : Core (mutate (node 26) 2) ∨
    WeakForks.IsWeakFork (mutate (node 26) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 26) 2) 2 := by
  have he : mutate (node 26) 2 = relabel (node 19) perm1 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 26) 2) u v = (relabel (node 19) perm1) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 19) perm1)

theorem edge26_3 : Core (mutate (node 26) 3) ∨
    WeakForks.IsWeakFork (mutate (node 26) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 26) 3) 3 := by
  have he : mutate (node 26) 3 = relabel (node 33) perm5 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 26) 3) u v = (relabel (node 33) perm5) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 33) perm5)

theorem cyclic27 : ¬ Acyclic (node 27) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge27_0 : Core (mutate (node 27) 0) ∨
    WeakForks.IsWeakFork (mutate (node 27) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 27) 0) 0 := by
  right; left
  have he : relabel (mutate (node 27) 0) perm4 = WeakForks.template (3) (7) (4) (18) (11) (2) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 27) 0) perm4) u v = (WeakForks.template (3) (7) (4) (18) (11) (2)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (mutate (node 27) 0) perm4) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (3) (7) (4) (18) (11) (2) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm4 hb

theorem edge27_1 : Core (mutate (node 27) 1) ∨
    WeakForks.IsWeakFork (mutate (node 27) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 27) 1) 1 := by
  right; left
  have he : relabel (reverse (mutate (node 27) 1)) perm10 = WeakForks.template (3) (7) (2) (18) (7) (4) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 27) 1)) perm10) u v = (WeakForks.template (3) (7) (2) (18) (7) (4)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (reverse (mutate (node 27) 1)) perm10) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (3) (7) (2) (18) (7) (4) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_reverse (WeakForks.fork_of_relabel perm10 hb)

theorem edge27_2 : Core (mutate (node 27) 2) ∨
    WeakForks.IsWeakFork (mutate (node 27) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 27) 2) 2 := by
  have he : mutate (node 27) 2 = relabel (node 21) perm1 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 27) 2) u v = (relabel (node 21) perm1) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 21) perm1)

theorem edge27_3 : Core (mutate (node 27) 3) ∨
    WeakForks.IsWeakFork (mutate (node 27) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 27) 3) 3 := by
  have he : mutate (node 27) 3 = reverse (relabel (node 40) perm19) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 27) 3) u v = (reverse (relabel (node 40) perm19)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 40) perm19))

theorem cyclic28 : ¬ Acyclic (node 28) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge28_0 : Core (mutate (node 28) 0) ∨
    WeakForks.IsWeakFork (mutate (node 28) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 28) 0) 0 := by
  right; right
  have he : relabel (reverse (mutate (node 28) 0)) perm5 = WeakRegions.root (3) (8) (18) (3) (7) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 28) 0)) perm5) u v = (WeakRegions.root (3) (8) (18) (3) (7) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 28) 0)) perm5) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (3) (8) (18) (3) (7) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm5 hb)

theorem edge28_1 : Core (mutate (node 28) 1) ∨
    WeakForks.IsWeakFork (mutate (node 28) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 28) 1) 1 := by
  have he : mutate (node 28) 1 = reverse (relabel (node 17) perm11) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 28) 1) u v = (reverse (relabel (node 17) perm11)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 17) perm11))

theorem edge28_2 : Core (mutate (node 28) 2) ∨
    WeakForks.IsWeakFork (mutate (node 28) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 28) 2) 2 := by
  have he : mutate (node 28) 2 = relabel (node 25) perm1 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 28) 2) u v = (relabel (node 25) perm1) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 25) perm1)

theorem edge28_3 : Core (mutate (node 28) 3) ∨
    WeakForks.IsWeakFork (mutate (node 28) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 28) 3) 3 := by
  have he : mutate (node 28) 3 = reverse (relabel (node 44) perm19) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 28) 3) u v = (reverse (relabel (node 44) perm19)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 44) perm19))

theorem cyclic29 : ¬ Acyclic (node 29) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge29_0 : Core (mutate (node 29) 0) ∨
    WeakForks.IsWeakFork (mutate (node 29) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 29) 0) 0 := by
  right; right
  have he : relabel (reverse (mutate (node 29) 0)) perm4 = WeakRegions.root (5) (33) (14) (7) (3) (0) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 29) 0)) perm4) u v = (WeakRegions.root (5) (33) (14) (7) (3) (0)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 29) 0)) perm4) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (5) (33) (14) (7) (3) (0) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm4 hb)

theorem edge29_1 : Core (mutate (node 29) 1) ∨
    WeakForks.IsWeakFork (mutate (node 29) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 29) 1) 1 := by
  have he : mutate (node 29) 1 = reverse (relabel (strip6 0 0) perm14) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 29) 1) u v = (reverse (relabel (strip6 0 0) perm14)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.strip6 0 0) perm14))

theorem edge29_2 : Core (mutate (node 29) 2) ∨
    WeakForks.IsWeakFork (mutate (node 29) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 29) 2) 2 := by
  have he : mutate (node 29) 2 = reverse (relabel (node 31) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 29) 2) u v = (reverse (relabel (node 31) perm6)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 31) perm6))

theorem edge29_3 : Core (mutate (node 29) 3) ∨
    WeakForks.IsWeakFork (mutate (node 29) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 29) 3) 3 := by
  have he : mutate (node 29) 3 = reverse (relabel (node 37) perm11) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 29) 3) u v = (reverse (relabel (node 37) perm11)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 37) perm11))

theorem cyclic30 : ¬ Acyclic (node 30) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge30_0 : Core (mutate (node 30) 0) ∨
    WeakForks.IsWeakFork (mutate (node 30) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 30) 0) 0 := by
  right; right
  have he : relabel (reverse (mutate (node 30) 0)) perm4 = WeakRegions.root (3) (18) (5) (7) (2) (0) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 30) 0)) perm4) u v = (WeakRegions.root (3) (18) (5) (7) (2) (0)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 30) 0)) perm4) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (3) (18) (5) (7) (2) (0) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm4 hb)

theorem edge30_1 : Core (mutate (node 30) 1) ∨
    WeakForks.IsWeakFork (mutate (node 30) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 30) 1) 1 := by
  have he : mutate (node 30) 1 = reverse (relabel (strip7 0 0) perm14) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 30) 1) u v = (reverse (relabel (strip7 0 0) perm14)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.strip7 0 0) perm14))

theorem edge30_2 : Core (mutate (node 30) 2) ∨
    WeakForks.IsWeakFork (mutate (node 30) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 30) 2) 2 := by
  have he : mutate (node 30) 2 = reverse (relabel (node 32) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 30) 2) u v = (reverse (relabel (node 32) perm6)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 32) perm6))

theorem edge30_3 : Core (mutate (node 30) 3) ∨
    WeakForks.IsWeakFork (mutate (node 30) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 30) 3) 3 := by
  have he : mutate (node 30) 3 = relabel (node 45) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 30) 3) u v = (relabel (node 45) perm21) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 45) perm21)

theorem cyclic31 : ¬ Acyclic (node 31) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge31_0 : Core (mutate (node 31) 0) ∨
    WeakForks.IsWeakFork (mutate (node 31) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 31) 0) 0 := by
  have he : mutate (node 31) 0 = relabel (strip6 0 1) perm8 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 31) 0) u v = (relabel (strip6 0 1) perm8) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.strip6 0 1) perm8)

theorem edge31_1 : Core (mutate (node 31) 1) ∨
    WeakForks.IsWeakFork (mutate (node 31) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 31) 1) 1 := by
  right; right
  have he : relabel (reverse (mutate (node 31) 1)) perm6 = WeakRegions.root (7) (21) (12) (3) (2) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 31) 1)) perm6) u v = (WeakRegions.root (7) (21) (12) (3) (2) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 31) 1)) perm6) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (7) (21) (12) (3) (2) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm6 hb)

theorem edge31_2 : Core (mutate (node 31) 2) ∨
    WeakForks.IsWeakFork (mutate (node 31) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 31) 2) 2 := by
  have he : mutate (node 31) 2 = reverse (relabel (node 29) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 31) 2) u v = (reverse (relabel (node 29) perm6)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 29) perm6))

theorem edge31_3 : Core (mutate (node 31) 3) ∨
    WeakForks.IsWeakFork (mutate (node 31) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 31) 3) 3 := by
  have he : mutate (node 31) 3 = relabel (node 41) perm1 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 31) 3) u v = (relabel (node 41) perm1) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 41) perm1)

theorem cyclic32 : ¬ Acyclic (node 32) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge32_0 : Core (mutate (node 32) 0) ∨
    WeakForks.IsWeakFork (mutate (node 32) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 32) 0) 0 := by
  have he : mutate (node 32) 0 = relabel (strip7 0 1) perm8 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 32) 0) u v = (relabel (strip7 0 1) perm8) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.strip7 0 1) perm8)

theorem edge32_1 : Core (mutate (node 32) 1) ∨
    WeakForks.IsWeakFork (mutate (node 32) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 32) 1) 1 := by
  have he : mutate (node 32) 1 = relabel (strip0 0 0) perm22 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 32) 1) u v = (relabel (strip0 0 0) perm22) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.strip0 0 0) perm22)

theorem edge32_2 : Core (mutate (node 32) 2) ∨
    WeakForks.IsWeakFork (mutate (node 32) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 32) 2) 2 := by
  have he : mutate (node 32) 2 = reverse (relabel (node 30) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 32) 2) u v = (reverse (relabel (node 30) perm6)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 30) perm6))

theorem edge32_3 : Core (mutate (node 32) 3) ∨
    WeakForks.IsWeakFork (mutate (node 32) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 32) 3) 3 := by
  have he : mutate (node 32) 3 = relabel (node 38) perm1 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 32) 3) u v = (relabel (node 38) perm1) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 38) perm1)

theorem cyclic33 : ¬ Acyclic (node 33) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge33_0 : Core (mutate (node 33) 0) ∨
    WeakForks.IsWeakFork (mutate (node 33) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 33) 0) 0 := by
  have he : mutate (node 33) 0 = relabel (node 18) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 33) 0) u v = (relabel (node 18) perm21) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 18) perm21)

theorem edge33_1 : Core (mutate (node 33) 1) ∨
    WeakForks.IsWeakFork (mutate (node 33) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 33) 1) 1 := by
  have he : mutate (node 33) 1 = relabel (node 26) perm5 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 33) 1) u v = (relabel (node 26) perm5) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 26) perm5)

theorem edge33_2 : Core (mutate (node 33) 2) ∨
    WeakForks.IsWeakFork (mutate (node 33) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 33) 2) 2 := by
  have he : mutate (node 33) 2 = reverse (relabel (node 33) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 33) 2) u v = (reverse (relabel (node 33) perm6)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 33) perm6))

theorem edge33_3 : Core (mutate (node 33) 3) ∨
    WeakForks.IsWeakFork (mutate (node 33) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 33) 3) 3 := by
  have he : mutate (node 33) 3 = relabel (node 46) perm3 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 33) 3) u v = (relabel (node 46) perm3) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 46) perm3)

theorem cyclic34 : ¬ Acyclic (node 34) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge34_0 : Core (mutate (node 34) 0) ∨
    WeakForks.IsWeakFork (mutate (node 34) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 34) 0) 0 := by
  right; left
  have he : relabel (mutate (node 34) 0) perm4 = WeakForks.template (2) (5) (3) (6) (5) (3) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 34) 0) perm4) u v = (WeakForks.template (2) (5) (3) (6) (5) (3)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (mutate (node 34) 0) perm4) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (2) (5) (3) (6) (5) (3) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm4 hb

theorem edge34_1 : Core (mutate (node 34) 1) ∨
    WeakForks.IsWeakFork (mutate (node 34) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 34) 1) 1 := by
  right; left
  have he : relabel (reverse (mutate (node 34) 1)) perm10 = WeakForks.template (4) (5) (3) (18) (13) (3) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 34) 1)) perm10) u v = (WeakForks.template (4) (5) (3) (18) (13) (3)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (reverse (mutate (node 34) 1)) perm10) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (4) (5) (3) (18) (13) (3) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_reverse (WeakForks.fork_of_relabel perm10 hb)

theorem edge34_2 : Core (mutate (node 34) 2) ∨
    WeakForks.IsWeakFork (mutate (node 34) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 34) 2) 2 := by
  have he : mutate (node 34) 2 = relabel (node 22) perm1 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 34) 2) u v = (relabel (node 22) perm1) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 22) perm1)

theorem edge34_3 : Core (mutate (node 34) 3) ∨
    WeakForks.IsWeakFork (mutate (node 34) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 34) 3) 3 := by
  have he : mutate (node 34) 3 = reverse (relabel (node 38) perm19) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 34) 3) u v = (reverse (relabel (node 38) perm19)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 38) perm19))

theorem cyclic35 : ¬ Acyclic (node 35) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge35_0 : Core (mutate (node 35) 0) ∨
    WeakForks.IsWeakFork (mutate (node 35) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 35) 0) 0 := by
  right; right
  have he : relabel (reverse (mutate (node 35) 0)) perm4 = WeakRegions.root (4) (18) (11) (5) (3) (0) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 35) 0)) perm4) u v = (WeakRegions.root (4) (18) (11) (5) (3) (0)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 35) 0)) perm4) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (4) (18) (11) (5) (3) (0) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm4 hb)

theorem edge35_1 : Core (mutate (node 35) 1) ∨
    WeakForks.IsWeakFork (mutate (node 35) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 35) 1) 1 := by
  have he : mutate (node 35) 1 = reverse (relabel (strip5 0 0) perm14) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 35) 1) u v = (reverse (relabel (strip5 0 0) perm14)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.strip5 0 0) perm14))

theorem edge35_2 : Core (mutate (node 35) 2) ∨
    WeakForks.IsWeakFork (mutate (node 35) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 35) 2) 2 := by
  have he : mutate (node 35) 2 = reverse (relabel (node 36) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 35) 2) u v = (reverse (relabel (node 36) perm6)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 36) perm6))

theorem edge35_3 : Core (mutate (node 35) 3) ∨
    WeakForks.IsWeakFork (mutate (node 35) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 35) 3) 3 := by
  have he : mutate (node 35) 3 = reverse (relabel (node 39) perm11) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 35) 3) u v = (reverse (relabel (node 39) perm11)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 39) perm11))

theorem cyclic36 : ¬ Acyclic (node 36) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge36_0 : Core (mutate (node 36) 0) ∨
    WeakForks.IsWeakFork (mutate (node 36) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 36) 0) 0 := by
  have he : mutate (node 36) 0 = relabel (strip5 0 1) perm8 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 36) 0) u v = (relabel (strip5 0 1) perm8) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.strip5 0 1) perm8)

theorem edge36_1 : Core (mutate (node 36) 1) ∨
    WeakForks.IsWeakFork (mutate (node 36) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 36) 1) 1 := by
  have he : mutate (node 36) 1 = relabel (node 20) perm4 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 36) 1) u v = (relabel (node 20) perm4) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 20) perm4)

theorem edge36_2 : Core (mutate (node 36) 2) ∨
    WeakForks.IsWeakFork (mutate (node 36) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 36) 2) 2 := by
  have he : mutate (node 36) 2 = reverse (relabel (node 35) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 36) 2) u v = (reverse (relabel (node 35) perm6)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 35) perm6))

theorem edge36_3 : Core (mutate (node 36) 3) ∨
    WeakForks.IsWeakFork (mutate (node 36) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 36) 3) 3 := by
  have he : mutate (node 36) 3 = relabel (node 40) perm1 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 36) 3) u v = (relabel (node 40) perm1) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 40) perm1)

theorem cyclic37 : ¬ Acyclic (node 37) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (by decide)
  have h1 := hr 2 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge37_0 : Core (mutate (node 37) 0) ∨
    WeakForks.IsWeakFork (mutate (node 37) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 37) 0) 0 := by
  have he : mutate (node 37) 0 = reverse (relabel (node 29) perm19) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 37) 0) u v = (reverse (relabel (node 29) perm19)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 29) perm19))

theorem edge37_1 : Core (mutate (node 37) 1) ∨
    WeakForks.IsWeakFork (mutate (node 37) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 37) 1) 1 := by
  right; right
  have he : relabel (reverse (mutate (node 37) 1)) perm6 = WeakRegions.root (5) (9) (13) (2) (3) (0) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 37) 1)) perm6) u v = (WeakRegions.root (5) (9) (13) (2) (3) (0)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 37) 1)) perm6) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (5) (9) (13) (2) (3) (0) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm6 hb)

theorem edge37_2 : Core (mutate (node 37) 2) ∨
    WeakForks.IsWeakFork (mutate (node 37) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 37) 2) 2 := by
  have he : mutate (node 37) 2 = reverse (relabel (node 43) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 37) 2) u v = (reverse (relabel (node 43) perm6)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 43) perm6))

theorem edge37_3 : Core (mutate (node 37) 3) ∨
    WeakForks.IsWeakFork (mutate (node 37) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 37) 3) 3 := by
  have he : mutate (node 37) 3 = relabel (node 46) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 37) 3) u v = (relabel (node 46) perm21) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 46) perm21)

theorem cyclic38 : ¬ Acyclic (node 38) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge38_0 : Core (mutate (node 38) 0) ∨
    WeakForks.IsWeakFork (mutate (node 38) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 38) 0) 0 := by
  right; right
  have he : relabel (reverse (mutate (node 38) 0)) perm5 = WeakRegions.root (3) (8) (10) (3) (4) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 38) 0)) perm5) u v = (WeakRegions.root (3) (8) (10) (3) (4) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 38) 0)) perm5) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (3) (8) (10) (3) (4) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm5 hb)

theorem edge38_1 : Core (mutate (node 38) 1) ∨
    WeakForks.IsWeakFork (mutate (node 38) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 38) 1) 1 := by
  have he : mutate (node 38) 1 = reverse (relabel (node 34) perm11) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 38) 1) u v = (reverse (relabel (node 34) perm11)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 34) perm11))

theorem edge38_2 : Core (mutate (node 38) 2) ∨
    WeakForks.IsWeakFork (mutate (node 38) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 38) 2) 2 := by
  have he : mutate (node 38) 2 = relabel (node 32) perm1 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 38) 2) u v = (relabel (node 32) perm1) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 32) perm1)

theorem edge38_3 : Core (mutate (node 38) 3) ∨
    WeakForks.IsWeakFork (mutate (node 38) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 38) 3) 3 := by
  have he : mutate (node 38) 3 = relabel (node 47) perm5 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 38) 3) u v = (relabel (node 47) perm5) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 47) perm5)

theorem cyclic39 : ¬ Acyclic (node 39) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (by decide)
  have h1 := hr 2 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge39_0 : Core (mutate (node 39) 0) ∨
    WeakForks.IsWeakFork (mutate (node 39) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 39) 0) 0 := by
  have he : mutate (node 39) 0 = reverse (relabel (node 35) perm19) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 39) 0) u v = (reverse (relabel (node 35) perm19)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 35) perm19))

theorem edge39_1 : Core (mutate (node 39) 1) ∨
    WeakForks.IsWeakFork (mutate (node 39) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 39) 1) 1 := by
  have he : mutate (node 39) 1 = relabel (node 24) perm5 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 39) 1) u v = (relabel (node 24) perm5) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 24) perm5)

theorem edge39_2 : Core (mutate (node 39) 2) ∨
    WeakForks.IsWeakFork (mutate (node 39) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 39) 2) 2 := by
  have he : mutate (node 39) 2 = relabel (node 44) perm0 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 39) 2) u v = (relabel (node 44) perm0) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 44) perm0)

theorem edge39_3 : Core (mutate (node 39) 3) ∨
    WeakForks.IsWeakFork (mutate (node 39) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 39) 3) 3 := by
  have he : mutate (node 39) 3 = relabel (node 47) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 39) 3) u v = (relabel (node 47) perm21) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 47) perm21)

theorem cyclic40 : ¬ Acyclic (node 40) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge40_0 : Core (mutate (node 40) 0) ∨
    WeakForks.IsWeakFork (mutate (node 40) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 40) 0) 0 := by
  right; right
  have he : relabel (reverse (mutate (node 40) 0)) perm5 = WeakRegions.root (2) (3) (3) (2) (3) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 40) 0)) perm5) u v = (WeakRegions.root (2) (3) (3) (2) (3) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 40) 0)) perm5) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (2) (3) (3) (2) (3) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm5 hb)

theorem edge40_1 : Core (mutate (node 40) 1) ∨
    WeakForks.IsWeakFork (mutate (node 40) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 40) 1) 1 := by
  have he : mutate (node 40) 1 = reverse (relabel (node 27) perm11) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 40) 1) u v = (reverse (relabel (node 27) perm11)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 27) perm11))

theorem edge40_2 : Core (mutate (node 40) 2) ∨
    WeakForks.IsWeakFork (mutate (node 40) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 40) 2) 2 := by
  have he : mutate (node 40) 2 = relabel (node 36) perm1 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 40) 2) u v = (relabel (node 36) perm1) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 36) perm1)

theorem edge40_3 : Core (mutate (node 40) 3) ∨
    WeakForks.IsWeakFork (mutate (node 40) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 40) 3) 3 := by
  have he : mutate (node 40) 3 = relabel (node 44) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 40) 3) u v = (relabel (node 44) perm21) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 44) perm21)

theorem cyclic41 : ¬ Acyclic (node 41) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge41_0 : Core (mutate (node 41) 0) ∨
    WeakForks.IsWeakFork (mutate (node 41) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 41) 0) 0 := by
  right; left
  have he : relabel (mutate (node 41) 0) perm4 = WeakForks.template (2) (3) (2) (3) (3) (2) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 41) 0) perm4) u v = (WeakForks.template (2) (3) (2) (3) (3) (2)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (mutate (node 41) 0) perm4) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (2) (3) (2) (3) (3) (2) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm4 hb

theorem edge41_1 : Core (mutate (node 41) 1) ∨
    WeakForks.IsWeakFork (mutate (node 41) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 41) 1) 1 := by
  right; left
  have he : relabel (reverse (mutate (node 41) 1)) perm10 = WeakForks.template (3) (3) (2) (7) (7) (2) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 41) 1)) perm10) u v = (WeakForks.template (3) (3) (2) (7) (7) (2)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (reverse (mutate (node 41) 1)) perm10) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (3) (3) (2) (7) (7) (2) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_reverse (WeakForks.fork_of_relabel perm10 hb)

theorem edge41_2 : Core (mutate (node 41) 2) ∨
    WeakForks.IsWeakFork (mutate (node 41) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 41) 2) 2 := by
  have he : mutate (node 41) 2 = relabel (node 31) perm1 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 41) 2) u v = (relabel (node 31) perm1) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 31) perm1)

theorem edge41_3 : Core (mutate (node 41) 3) ∨
    WeakForks.IsWeakFork (mutate (node 41) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 41) 3) 3 := by
  have he : mutate (node 41) 3 = reverse (relabel (node 43) perm19) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 41) 3) u v = (reverse (relabel (node 43) perm19)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 43) perm19))

theorem cyclic42 : ¬ Acyclic (node 42) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge42_0 : Core (mutate (node 42) 0) ∨
    WeakForks.IsWeakFork (mutate (node 42) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 42) 0) 0 := by
  right; right
  have he : relabel (reverse (mutate (node 42) 0)) perm4 = WeakRegions.root (3) (7) (5) (3) (2) (0) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 42) 0)) perm4) u v = (WeakRegions.root (3) (7) (5) (3) (2) (0)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 42) 0)) perm4) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (3) (7) (5) (3) (2) (0) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm4 hb)

theorem edge42_1 : Core (mutate (node 42) 1) ∨
    WeakForks.IsWeakFork (mutate (node 42) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 42) 1) 1 := by
  have he : mutate (node 42) 1 = relabel (node 43) perm5 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 42) 1) u v = (relabel (node 43) perm5) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 43) perm5)

theorem edge42_2 : Core (mutate (node 42) 2) ∨
    WeakForks.IsWeakFork (mutate (node 42) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 42) 2) 2 := by
  have he : mutate (node 42) 2 = reverse (relabel (node 46) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 42) 2) u v = (reverse (relabel (node 46) perm6)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 46) perm6))

theorem edge42_3 : Core (mutate (node 42) 3) ∨
    WeakForks.IsWeakFork (mutate (node 42) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 42) 3) 3 := by
  have he : mutate (node 42) 3 = reverse (relabel (node 45) perm0) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 42) 3) u v = (reverse (relabel (node 45) perm0)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 45) perm0))

theorem cyclic43 : ¬ Acyclic (node 43) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge43_0 : Core (mutate (node 43) 0) ∨
    WeakForks.IsWeakFork (mutate (node 43) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 43) 0) 0 := by
  right; right
  have he : relabel (reverse (mutate (node 43) 0)) perm5 = WeakRegions.root (3) (6) (7) (2) (3) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 43) 0)) perm5) u v = (WeakRegions.root (3) (6) (7) (2) (3) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 43) 0)) perm5) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (3) (6) (7) (2) (3) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm5 hb)

theorem edge43_1 : Core (mutate (node 43) 1) ∨
    WeakForks.IsWeakFork (mutate (node 43) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 43) 1) 1 := by
  have he : mutate (node 43) 1 = reverse (relabel (node 41) perm11) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 43) 1) u v = (reverse (relabel (node 41) perm11)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 41) perm11))

theorem edge43_2 : Core (mutate (node 43) 2) ∨
    WeakForks.IsWeakFork (mutate (node 43) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 43) 2) 2 := by
  have he : mutate (node 43) 2 = reverse (relabel (node 37) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 43) 2) u v = (reverse (relabel (node 37) perm6)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 37) perm6))

theorem edge43_3 : Core (mutate (node 43) 3) ∨
    WeakForks.IsWeakFork (mutate (node 43) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 43) 3) 3 := by
  have he : mutate (node 43) 3 = relabel (node 42) perm5 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 43) 3) u v = (relabel (node 42) perm5) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 42) perm5)

theorem cyclic44 : ¬ Acyclic (node 44) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge44_0 : Core (mutate (node 44) 0) ∨
    WeakForks.IsWeakFork (mutate (node 44) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 44) 0) 0 := by
  have he : mutate (node 44) 0 = relabel (node 40) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 44) 0) u v = (relabel (node 40) perm21) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 40) perm21)

theorem edge44_1 : Core (mutate (node 44) 1) ∨
    WeakForks.IsWeakFork (mutate (node 44) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 44) 1) 1 := by
  have he : mutate (node 44) 1 = reverse (relabel (node 28) perm11) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 44) 1) u v = (reverse (relabel (node 28) perm11)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 28) perm11))

theorem edge44_2 : Core (mutate (node 44) 2) ∨
    WeakForks.IsWeakFork (mutate (node 44) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 44) 2) 2 := by
  have he : mutate (node 44) 2 = relabel (node 39) perm0 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 44) 2) u v = (relabel (node 39) perm0) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 39) perm0)

theorem edge44_3 : Core (mutate (node 44) 3) ∨
    WeakForks.IsWeakFork (mutate (node 44) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 44) 3) 3 := by
  have he : mutate (node 44) 3 = reverse (relabel (node 45) perm19) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 44) 3) u v = (reverse (relabel (node 45) perm19)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 45) perm19))

theorem cyclic45 : ¬ Acyclic (node 45) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge45_0 : Core (mutate (node 45) 0) ∨
    WeakForks.IsWeakFork (mutate (node 45) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 45) 0) 0 := by
  have he : mutate (node 45) 0 = relabel (node 30) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 45) 0) u v = (relabel (node 30) perm21) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 30) perm21)

theorem edge45_1 : Core (mutate (node 45) 1) ∨
    WeakForks.IsWeakFork (mutate (node 45) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 45) 1) 1 := by
  have he : mutate (node 45) 1 = reverse (relabel (node 44) perm11) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 45) 1) u v = (reverse (relabel (node 44) perm11)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 44) perm11))

theorem edge45_2 : Core (mutate (node 45) 2) ∨
    WeakForks.IsWeakFork (mutate (node 45) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 45) 2) 2 := by
  have he : mutate (node 45) 2 = reverse (relabel (node 47) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 45) 2) u v = (reverse (relabel (node 47) perm6)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 47) perm6))

theorem edge45_3 : Core (mutate (node 45) 3) ∨
    WeakForks.IsWeakFork (mutate (node 45) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 45) 3) 3 := by
  have he : mutate (node 45) 3 = reverse (relabel (node 42) perm0) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 45) 3) u v = (reverse (relabel (node 42) perm0)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 42) perm0))

theorem cyclic46 : ¬ Acyclic (node 46) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge46_0 : Core (mutate (node 46) 0) ∨
    WeakForks.IsWeakFork (mutate (node 46) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 46) 0) 0 := by
  have he : mutate (node 46) 0 = relabel (node 37) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 46) 0) u v = (relabel (node 37) perm21) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 37) perm21)

theorem edge46_1 : Core (mutate (node 46) 1) ∨
    WeakForks.IsWeakFork (mutate (node 46) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 46) 1) 1 := by
  have he : mutate (node 46) 1 = relabel (node 33) perm4 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 46) 1) u v = (relabel (node 33) perm4) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 33) perm4)

theorem edge46_2 : Core (mutate (node 46) 2) ∨
    WeakForks.IsWeakFork (mutate (node 46) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 46) 2) 2 := by
  have he : mutate (node 46) 2 = reverse (relabel (node 42) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 46) 2) u v = (reverse (relabel (node 42) perm6)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 42) perm6))

theorem edge46_3 : Core (mutate (node 46) 3) ∨
    WeakForks.IsWeakFork (mutate (node 46) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 46) 3) 3 := by
  have he : mutate (node 46) 3 = relabel (node 48) perm3 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 46) 3) u v = (relabel (node 48) perm3) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 48) perm3)

theorem cyclic47 : ¬ Acyclic (node 47) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge47_0 : Core (mutate (node 47) 0) ∨
    WeakForks.IsWeakFork (mutate (node 47) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 47) 0) 0 := by
  have he : mutate (node 47) 0 = relabel (node 39) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 47) 0) u v = (relabel (node 39) perm21) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 39) perm21)

theorem edge47_1 : Core (mutate (node 47) 1) ∨
    WeakForks.IsWeakFork (mutate (node 47) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 47) 1) 1 := by
  have he : mutate (node 47) 1 = relabel (node 38) perm5 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 47) 1) u v = (relabel (node 38) perm5) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 38) perm5)

theorem edge47_2 : Core (mutate (node 47) 2) ∨
    WeakForks.IsWeakFork (mutate (node 47) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 47) 2) 2 := by
  have he : mutate (node 47) 2 = reverse (relabel (node 45) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 47) 2) u v = (reverse (relabel (node 45) perm6)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 45) perm6))

theorem edge47_3 : Core (mutate (node 47) 3) ∨
    WeakForks.IsWeakFork (mutate (node 47) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 47) 3) 3 := by
  have he : mutate (node 47) 3 = relabel (node 48) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 47) 3) u v = (relabel (node 48) perm21) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 48) perm21)

theorem cyclic48 : ¬ Acyclic (node 48) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge48_0 : Core (mutate (node 48) 0) ∨
    WeakForks.IsWeakFork (mutate (node 48) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 48) 0) 0 := by
  have he : mutate (node 48) 0 = relabel (node 47) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 48) 0) u v = (relabel (node 47) perm21) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 47) perm21)

theorem edge48_1 : Core (mutate (node 48) 1) ∨
    WeakForks.IsWeakFork (mutate (node 48) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 48) 1) 1 := by
  have he : mutate (node 48) 1 = relabel (node 46) perm4 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 48) 1) u v = (relabel (node 46) perm4) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 46) perm4)

theorem edge48_2 : Core (mutate (node 48) 2) ∨
    WeakForks.IsWeakFork (mutate (node 48) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 48) 2) 2 := by
  have he : mutate (node 48) 2 = reverse (relabel (node 46) perm15) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 48) 2) u v = (reverse (relabel (node 46) perm15)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 46) perm15))

theorem edge48_3 : Core (mutate (node 48) 3) ∨
    WeakForks.IsWeakFork (mutate (node 48) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 48) 3) 3 := by
  have he : mutate (node 48) 3 = reverse (relabel (node 47) perm2) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 48) 3) u v = (reverse (relabel (node 47) perm2)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 47) perm2))

theorem finite_skew (i : Fin 49) : SkewSymmetric (node i) := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 ∨ i = 32 ∨ i = 33 ∨ i = 34 ∨ i = 35 ∨ i = 36 ∨ i = 37 ∨ i = 38 ∨ i = 39 ∨ i = 40 ∨ i = 41 ∨ i = 42 ∨ i = 43 ∨ i = 44 ∨ i = 45 ∨ i = 46 ∨ i = 47 ∨ i = 48 := by omega
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ofSix_skew _ _ _ _ _ _

theorem finite_cyclic (i : Fin 49) : ¬ Acyclic (node i) := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 ∨ i = 32 ∨ i = 33 ∨ i = 34 ∨ i = 35 ∨ i = 36 ∨ i = 37 ∨ i = 38 ∨ i = 39 ∨ i = 40 ∨ i = 41 ∨ i = 42 ∨ i = 43 ∨ i = 44 ∨ i = 45 ∨ i = 46 ∨ i = 47 ∨ i = 48 := by omega
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · exact cyclic34
  · exact cyclic35
  · exact cyclic36
  · exact cyclic37
  · exact cyclic38
  · exact cyclic39
  · exact cyclic40
  · exact cyclic41
  · exact cyclic42
  · exact cyclic43
  · exact cyclic44
  · exact cyclic45
  · exact cyclic46
  · exact cyclic47
  · exact cyclic48

theorem finite_edges (i : Fin 49) (k : Fin 4) : Core (mutate (node i) k) ∨
    WeakForks.IsWeakFork (mutate (node i) k) k ∨ WeakRegions.IsRoot (mutate (node i) k) k := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 ∨ i = 32 ∨ i = 33 ∨ i = 34 ∨ i = 35 ∨ i = 36 ∨ i = 37 ∨ i = 38 ∨ i = 39 ∨ i = 40 ∨ i = 41 ∨ i = 42 ∨ i = 43 ∨ i = 44 ∨ i = 45 ∨ i = 46 ∨ i = 47 ∨ i = 48 := by omega
  have hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hk with rfl|rfl|rfl|rfl
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
  · exact edge34_0
  · exact edge34_1
  · exact edge34_2
  · exact edge34_3
  · exact edge35_0
  · exact edge35_1
  · exact edge35_2
  · exact edge35_3
  · exact edge36_0
  · exact edge36_1
  · exact edge36_2
  · exact edge36_3
  · exact edge37_0
  · exact edge37_1
  · exact edge37_2
  · exact edge37_3
  · exact edge38_0
  · exact edge38_1
  · exact edge38_2
  · exact edge38_3
  · exact edge39_0
  · exact edge39_1
  · exact edge39_2
  · exact edge39_3
  · exact edge40_0
  · exact edge40_1
  · exact edge40_2
  · exact edge40_3
  · exact edge41_0
  · exact edge41_1
  · exact edge41_2
  · exact edge41_3
  · exact edge42_0
  · exact edge42_1
  · exact edge42_2
  · exact edge42_3
  · exact edge43_0
  · exact edge43_1
  · exact edge43_2
  · exact edge43_3
  · exact edge44_0
  · exact edge44_1
  · exact edge44_2
  · exact edge44_3
  · exact edge45_0
  · exact edge45_1
  · exact edge45_2
  · exact edge45_3
  · exact edge46_0
  · exact edge46_1
  · exact edge46_2
  · exact edge46_3
  · exact edge47_0
  · exact edge47_1
  · exact edge47_2
  · exact edge47_3
  · exact edge48_0
  · exact edge48_1
  · exact edge48_2
  · exact edge48_3

theorem parent0_0 : Core (mutate (GenericStrip.root 2 seed0.A seed0.H seed0.Z) 1) := by
  have he : mutate (GenericStrip.root 2 seed0.A seed0.H seed0.Z) 1 = reverse (relabel (node 22) perm3) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (GenericStrip.root 2 seed0.A seed0.H seed0.Z) 1) u v = (reverse (relabel (node 22) perm3)) u v from by decide) u v
  rw [he]
  exact Core.reversed (Core.framed (Core.finite 22) perm3)

theorem parent0_1 : Core (mutate (GenericStrip.root 2 seed0.A seed0.H seed0.Z) 2) := by
  have he : mutate (GenericStrip.root 2 seed0.A seed0.H seed0.Z) 2 = relabel (node 32) perm17 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (GenericStrip.root 2 seed0.A seed0.H seed0.Z) 2) u v = (relabel (node 32) perm17) u v from by decide) u v
  rw [he]
  exact Core.framed (Core.finite 32) perm17

theorem parent0_2 : Core (mutate (GenericStrip.phaseQ 2 seed0.A seed0.H seed0.Z) 0) := by
  have he : mutate (GenericStrip.phaseQ 2 seed0.A seed0.H seed0.Z) 0 = reverse (relabel (node 14) perm16) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (GenericStrip.phaseQ 2 seed0.A seed0.H seed0.Z) 0) u v = (reverse (relabel (node 14) perm16)) u v from by decide) u v
  rw [he]
  exact Core.reversed (Core.framed (Core.finite 14) perm16)

theorem address0 {B : Matrix 4} (h : StripSemantics.Core 2 seed0 Core B) : Core B := by
  induction h with
  | base h => exact h
  | strip n i => exact Core.strip0 n i
  | framed h p ih => exact Core.framed ih p
  | reversed h ih => exact Core.reversed ih

theorem parent1_0 : Core (mutate (GenericStrip.root 2 seed1.A seed1.H seed1.Z) 1) := by
  have he : mutate (GenericStrip.root 2 seed1.A seed1.H seed1.Z) 1 = reverse (relabel (node 15) perm3) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (GenericStrip.root 2 seed1.A seed1.H seed1.Z) 1) u v = (reverse (relabel (node 15) perm3)) u v from by decide) u v
  rw [he]
  exact Core.reversed (Core.framed (Core.finite 15) perm3)

theorem parent1_1 : Core (mutate (GenericStrip.root 2 seed1.A seed1.H seed1.Z) 2) := by
  have he : mutate (GenericStrip.root 2 seed1.A seed1.H seed1.Z) 2 = relabel (node 19) perm17 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (GenericStrip.root 2 seed1.A seed1.H seed1.Z) 2) u v = (relabel (node 19) perm17) u v from by decide) u v
  rw [he]
  exact Core.framed (Core.finite 19) perm17

theorem parent1_2 : Core (mutate (GenericStrip.phaseQ 2 seed1.A seed1.H seed1.Z) 0) := by
  have he : mutate (GenericStrip.phaseQ 2 seed1.A seed1.H seed1.Z) 0 = reverse (relabel (node 10) perm16) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (GenericStrip.phaseQ 2 seed1.A seed1.H seed1.Z) 0) u v = (reverse (relabel (node 10) perm16)) u v from by decide) u v
  rw [he]
  exact Core.reversed (Core.framed (Core.finite 10) perm16)

theorem address1 {B : Matrix 4} (h : StripSemantics.Core 2 seed1 Core B) : Core B := by
  induction h with
  | base h => exact h
  | strip n i => exact Core.strip1 n i
  | framed h p ih => exact Core.framed ih p
  | reversed h ih => exact Core.reversed ih

theorem parent2_0 : Core (mutate (GenericStrip.root 3 seed2.A seed2.H seed2.Z) 1) := by
  have he : mutate (GenericStrip.root 3 seed2.A seed2.H seed2.Z) 1 = reverse (relabel (node 16) perm3) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (GenericStrip.root 3 seed2.A seed2.H seed2.Z) 1) u v = (reverse (relabel (node 16) perm3)) u v from by decide) u v
  rw [he]
  exact Core.reversed (Core.framed (Core.finite 16) perm3)

theorem parent2_1 : Core (mutate (GenericStrip.root 3 seed2.A seed2.H seed2.Z) 2) := by
  have he : mutate (GenericStrip.root 3 seed2.A seed2.H seed2.Z) 2 = relabel (node 25) perm17 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (GenericStrip.root 3 seed2.A seed2.H seed2.Z) 2) u v = (relabel (node 25) perm17) u v from by decide) u v
  rw [he]
  exact Core.framed (Core.finite 25) perm17

theorem parent2_2 : Core (mutate (GenericStrip.phaseQ 3 seed2.A seed2.H seed2.Z) 0) := by
  have he : mutate (GenericStrip.phaseQ 3 seed2.A seed2.H seed2.Z) 0 = reverse (relabel (node 5) perm16) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (GenericStrip.phaseQ 3 seed2.A seed2.H seed2.Z) 0) u v = (reverse (relabel (node 5) perm16)) u v from by decide) u v
  rw [he]
  exact Core.reversed (Core.framed (Core.finite 5) perm16)

theorem address2 {B : Matrix 4} (h : StripSemantics.Core 3 seed2 Core B) : Core B := by
  induction h with
  | base h => exact h
  | strip n i => exact Core.strip2 n i
  | framed h p ih => exact Core.framed ih p
  | reversed h ih => exact Core.reversed ih

theorem parent3_0 : Core (mutate (GenericStrip.root 3 seed3.A seed3.H seed3.Z) 1) := by
  have he : mutate (GenericStrip.root 3 seed3.A seed3.H seed3.Z) 1 = reverse (relabel (node 4) perm3) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (GenericStrip.root 3 seed3.A seed3.H seed3.Z) 1) u v = (reverse (relabel (node 4) perm3)) u v from by decide) u v
  rw [he]
  exact Core.reversed (Core.framed (Core.finite 4) perm3)

theorem parent3_1 : Core (mutate (GenericStrip.root 3 seed3.A seed3.H seed3.Z) 2) := by
  have he : mutate (GenericStrip.root 3 seed3.A seed3.H seed3.Z) 2 = relabel (node 12) perm17 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (GenericStrip.root 3 seed3.A seed3.H seed3.Z) 2) u v = (relabel (node 12) perm17) u v from by decide) u v
  rw [he]
  exact Core.framed (Core.finite 12) perm17

theorem parent3_2 : Core (mutate (GenericStrip.phaseQ 3 seed3.A seed3.H seed3.Z) 0) := by
  have he : mutate (GenericStrip.phaseQ 3 seed3.A seed3.H seed3.Z) 0 = reverse (relabel (node 1) perm16) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (GenericStrip.phaseQ 3 seed3.A seed3.H seed3.Z) 0) u v = (reverse (relabel (node 1) perm16)) u v from by decide) u v
  rw [he]
  exact Core.reversed (Core.framed (Core.finite 1) perm16)

theorem address3 {B : Matrix 4} (h : StripSemantics.Core 3 seed3 Core B) : Core B := by
  induction h with
  | base h => exact h
  | strip n i => exact Core.strip3 n i
  | framed h p ih => exact Core.framed ih p
  | reversed h ih => exact Core.reversed ih

theorem parent4_0 : Core (mutate (GenericStrip.root 6 seed4.A seed4.H seed4.Z) 1) := by
  have he : mutate (GenericStrip.root 6 seed4.A seed4.H seed4.Z) 1 = reverse (relabel (node 2) perm3) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (GenericStrip.root 6 seed4.A seed4.H seed4.Z) 1) u v = (reverse (relabel (node 2) perm3)) u v from by decide) u v
  rw [he]
  exact Core.reversed (Core.framed (Core.finite 2) perm3)

theorem parent4_1 : Core (mutate (GenericStrip.root 6 seed4.A seed4.H seed4.Z) 2) := by
  have he : mutate (GenericStrip.root 6 seed4.A seed4.H seed4.Z) 2 = relabel (node 7) perm17 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (GenericStrip.root 6 seed4.A seed4.H seed4.Z) 2) u v = (relabel (node 7) perm17) u v from by decide) u v
  rw [he]
  exact Core.framed (Core.finite 7) perm17

theorem parent4_2 : Core (mutate (GenericStrip.phaseQ 6 seed4.A seed4.H seed4.Z) 0) := by
  have he : mutate (GenericStrip.phaseQ 6 seed4.A seed4.H seed4.Z) 0 = reverse (relabel (node 0) perm16) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (GenericStrip.phaseQ 6 seed4.A seed4.H seed4.Z) 0) u v = (reverse (relabel (node 0) perm16)) u v from by decide) u v
  rw [he]
  exact Core.reversed (Core.framed (Core.finite 0) perm16)

theorem address4 {B : Matrix 4} (h : StripSemantics.Core 6 seed4 Core B) : Core B := by
  induction h with
  | base h => exact h
  | strip n i => exact Core.strip4 n i
  | framed h p ih => exact Core.framed ih p
  | reversed h ih => exact Core.reversed ih

theorem parent5_0 : Core (UnitZeroStrip.parent 2 seed5 0) := by
  have he : UnitZeroStrip.parent 2 seed5 0 = reverse (relabel (node 35) perm14) := by
    funext u v
    exact (show ∀ u v : Fin 4, (UnitZeroStrip.parent 2 seed5 0) u v = (reverse (relabel (node 35) perm14)) u v from by decide) u v
  rw [he]
  exact Core.reversed (Core.framed (Core.finite 35) perm14)

theorem parent5_1 : Core (UnitZeroStrip.parent 2 seed5 1) := by
  have he : UnitZeroStrip.parent 2 seed5 1 = relabel (node 36) perm12 := by
    funext u v
    exact (show ∀ u v : Fin 4, (UnitZeroStrip.parent 2 seed5 1) u v = (relabel (node 36) perm12) u v from by decide) u v
  rw [he]
  exact Core.framed (Core.finite 36) perm12

theorem parents5 (p : Fin 2) : Core (UnitZeroStrip.parent 2 seed5 p) := by
  have hp : p=0 ∨ p=1 := by omega
  rcases hp with rfl|rfl
  · exact parent5_0
  · exact parent5_1

theorem parent6_0 : Core (UnitZeroStrip.parent 2 seed6 0) := by
  have he : UnitZeroStrip.parent 2 seed6 0 = reverse (relabel (node 29) perm14) := by
    funext u v
    exact (show ∀ u v : Fin 4, (UnitZeroStrip.parent 2 seed6 0) u v = (reverse (relabel (node 29) perm14)) u v from by decide) u v
  rw [he]
  exact Core.reversed (Core.framed (Core.finite 29) perm14)

theorem parent6_1 : Core (UnitZeroStrip.parent 2 seed6 1) := by
  have he : UnitZeroStrip.parent 2 seed6 1 = relabel (node 31) perm12 := by
    funext u v
    exact (show ∀ u v : Fin 4, (UnitZeroStrip.parent 2 seed6 1) u v = (relabel (node 31) perm12) u v from by decide) u v
  rw [he]
  exact Core.framed (Core.finite 31) perm12

theorem parents6 (p : Fin 2) : Core (UnitZeroStrip.parent 2 seed6 p) := by
  have hp : p=0 ∨ p=1 := by omega
  rcases hp with rfl|rfl
  · exact parent6_0
  · exact parent6_1

theorem parent7_0 : Core (UnitZeroStrip.parent 3 seed7 0) := by
  have he : UnitZeroStrip.parent 3 seed7 0 = reverse (relabel (node 30) perm14) := by
    funext u v
    exact (show ∀ u v : Fin 4, (UnitZeroStrip.parent 3 seed7 0) u v = (reverse (relabel (node 30) perm14)) u v from by decide) u v
  rw [he]
  exact Core.reversed (Core.framed (Core.finite 30) perm14)

theorem parent7_1 : Core (UnitZeroStrip.parent 3 seed7 1) := by
  have he : UnitZeroStrip.parent 3 seed7 1 = relabel (node 32) perm12 := by
    funext u v
    exact (show ∀ u v : Fin 4, (UnitZeroStrip.parent 3 seed7 1) u v = (relabel (node 32) perm12) u v from by decide) u v
  rw [he]
  exact Core.framed (Core.finite 32) perm12

theorem parents7 (p : Fin 2) : Core (UnitZeroStrip.parent 3 seed7 p) := by
  have hp : p=0 ∨ p=1 := by omega
  rcases hp with rfl|rfl
  · exact parent7_0
  · exact parent7_1

theorem parent8_0 : Core (UnitZeroStrip.parent 3 seed8 0) := by
  have he : UnitZeroStrip.parent 3 seed8 0 = reverse (relabel (node 24) perm14) := by
    funext u v
    exact (show ∀ u v : Fin 4, (UnitZeroStrip.parent 3 seed8 0) u v = (reverse (relabel (node 24) perm14)) u v from by decide) u v
  rw [he]
  exact Core.reversed (Core.framed (Core.finite 24) perm14)

theorem parent8_1 : Core (UnitZeroStrip.parent 3 seed8 1) := by
  have he : UnitZeroStrip.parent 3 seed8 1 = relabel (node 25) perm12 := by
    funext u v
    exact (show ∀ u v : Fin 4, (UnitZeroStrip.parent 3 seed8 1) u v = (relabel (node 25) perm12) u v from by decide) u v
  rw [he]
  exact Core.framed (Core.finite 25) perm12

theorem parents8 (p : Fin 2) : Core (UnitZeroStrip.parent 3 seed8 p) := by
  have hp : p=0 ∨ p=1 := by omega
  rcases hp with rfl|rfl
  · exact parent8_0
  · exact parent8_1

theorem core_skew {B : Matrix 4} (h : Core B) : SkewSymmetric B := by
  induction h with
  | finite i => exact finite_skew i
  | strip0 n i => exact GenericStrip.phase_skew _ _ _ _ _
  | strip1 n i => exact GenericStrip.phase_skew _ _ _ _ _
  | strip2 n i => exact GenericStrip.phase_skew _ _ _ _ _
  | strip3 n i => exact GenericStrip.phase_skew _ _ _ _ _
  | strip4 n i => exact GenericStrip.phase_skew _ _ _ _ _
  | strip5 n i => exact UnitZeroStrip.strip_skew _ _ _ _
  | strip6 n i => exact UnitZeroStrip.strip_skew _ _ _ _
  | strip7 n i => exact UnitZeroStrip.strip_skew _ _ _ _
  | strip8 n i => exact UnitZeroStrip.strip_skew _ _ _ _
  | framed h p ih => exact relabel_skew _ p ih
  | reversed h ih => exact reverse_skew _ ih

theorem core_cyclic {B : Matrix 4} (h : Core B) : ¬ Acyclic B := by
  induction h with
  | finite i => exact finite_cyclic i
  | strip0 n i => exact GenericStrip.phase_cyclic _ _ _ _ (GenericStrip.orbit_domain 2 seed0 domain0 n) i
  | strip1 n i => exact GenericStrip.phase_cyclic _ _ _ _ (GenericStrip.orbit_domain 2 seed1 domain1 n) i
  | strip2 n i => exact GenericStrip.phase_cyclic _ _ _ _ (GenericStrip.orbit_domain 3 seed2 domain2 n) i
  | strip3 n i => exact GenericStrip.phase_cyclic _ _ _ _ (GenericStrip.orbit_domain 3 seed3 domain3 n) i
  | strip4 n i => exact GenericStrip.phase_cyclic _ _ _ _ (GenericStrip.orbit_domain 6 seed4 domain4 n) i
  | strip5 n i => exact UnitZeroStrip.strip_cyclic _ _ domain5 _ _
  | strip6 n i => exact UnitZeroStrip.strip_cyclic _ _ domain6 _ _
  | strip7 n i => exact UnitZeroStrip.strip_cyclic _ _ domain7 _ _
  | strip8 n i => exact UnitZeroStrip.strip_cyclic _ _ domain8 _ _
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
    rcases StripSemantics.strip_edges 2 seed1 Core domain1
      (.base parent1_0) (.base parent1_1) (.base parent1_2) n i k with hc|hf|hr
    · exact Or.inl (address1 hc)
    · exact Or.inr (Or.inl (strict_fork_weak hf))
    · exact Or.inr (Or.inr (strict_root_weak hr))
  | strip2 n i =>
    rcases StripSemantics.strip_edges 3 seed2 Core domain2
      (.base parent2_0) (.base parent2_1) (.base parent2_2) n i k with hc|hf|hr
    · exact Or.inl (address2 hc)
    · exact Or.inr (Or.inl (strict_fork_weak hf))
    · exact Or.inr (Or.inr (strict_root_weak hr))
  | strip3 n i =>
    rcases StripSemantics.strip_edges 3 seed3 Core domain3
      (.base parent3_0) (.base parent3_1) (.base parent3_2) n i k with hc|hf|hr
    · exact Or.inl (address3 hc)
    · exact Or.inr (Or.inl (strict_fork_weak hf))
    · exact Or.inr (Or.inr (strict_root_weak hr))
  | strip4 n i =>
    rcases StripSemantics.strip_edges 6 seed4 Core domain4
      (.base parent4_0) (.base parent4_1) (.base parent4_2) n i k with hc|hf|hr
    · exact Or.inl (address4 hc)
    · exact Or.inr (Or.inl (strict_fork_weak hf))
    · exact Or.inr (Or.inr (strict_root_weak hr))
  | strip5 n i =>
    rcases UnitZeroStrip.all_edges 2 seed5 domain5 n i k with
      ⟨n2,i2,p,he⟩ | ⟨p2,p,he⟩ | hf | hr
    · rw [show strip5 n i = UnitZeroStrip.strip 2 seed5 n i from rfl, he]
      exact Or.inl (.framed (.strip5 n2 i2) p)
    · rw [show strip5 n i = UnitZeroStrip.strip 2 seed5 n i from rfl, he]
      exact Or.inl (.framed (parents5 p2) p)
    · exact Or.inr (Or.inl (strict_fork_weak hf))
    · exact Or.inr (Or.inr (strict_root_weak hr))
  | strip6 n i =>
    rcases UnitZeroStrip.all_edges 2 seed6 domain6 n i k with
      ⟨n2,i2,p,he⟩ | ⟨p2,p,he⟩ | hf | hr
    · rw [show strip6 n i = UnitZeroStrip.strip 2 seed6 n i from rfl, he]
      exact Or.inl (.framed (.strip6 n2 i2) p)
    · rw [show strip6 n i = UnitZeroStrip.strip 2 seed6 n i from rfl, he]
      exact Or.inl (.framed (parents6 p2) p)
    · exact Or.inr (Or.inl (strict_fork_weak hf))
    · exact Or.inr (Or.inr (strict_root_weak hr))
  | strip7 n i =>
    rcases UnitZeroStrip.all_edges 3 seed7 domain7 n i k with
      ⟨n2,i2,p,he⟩ | ⟨p2,p,he⟩ | hf | hr
    · rw [show strip7 n i = UnitZeroStrip.strip 3 seed7 n i from rfl, he]
      exact Or.inl (.framed (.strip7 n2 i2) p)
    · rw [show strip7 n i = UnitZeroStrip.strip 3 seed7 n i from rfl, he]
      exact Or.inl (.framed (parents7 p2) p)
    · exact Or.inr (Or.inl (strict_fork_weak hf))
    · exact Or.inr (Or.inr (strict_root_weak hr))
  | strip8 n i =>
    rcases UnitZeroStrip.all_edges 3 seed8 domain8 n i k with
      ⟨n2,i2,p,he⟩ | ⟨p2,p,he⟩ | hf | hr
    · rw [show strip8 n i = UnitZeroStrip.strip 3 seed8 n i from rfl, he]
      exact Or.inl (.framed (.strip8 n2 i2) p)
    · rw [show strip8 n i = UnitZeroStrip.strip 3 seed8 n i from rfl, he]
      exact Or.inl (.framed (parents8 p2) p)
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

/-- Exact source q508: unconditional NMA for every finite mutation word. -/
theorem nma_q508 : ¬ MutationAcyclic (ofSix (-2) (-1) (2) (-1) (-1) (-2)) := by
  have he : (ofSix (-2) (-1) (2) (-1) (-1) (-2)) = relabel (node 48) perm0 := by
    funext u v
    exact (show ∀ u v : Fin 4, ((ofSix (-2) (-1) (2) (-1) (-1) (-2))) u v = (relabel (node 48) perm0) u v from by decide) u v
  rw [he]
  exact core_NMA (Core.framed (Core.finite 48) perm0)

end QuiverProofs.HereditaryTriangleRegions07
