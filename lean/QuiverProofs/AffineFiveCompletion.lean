import QuiverProofs.AffineFiveLocal
import QuiverProofs.HereditaryTrianglePendant
import QuiverProofs.StripSemantics

/-! Exact finite core joined to unbounded G/N strips. Every entrance parent is checked. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace QuiverProofs.AffineFiveCompletion
open ForkCertificates HereditaryTrianglePendant

def node (i : Fin 62) : Matrix 4 := match i.val with
  | 0 => (ofSix (-3709) (-5) (6) (-101) (-622) (-1))
  | 1 => (ofSix (-725) (-4) (5) (-26) (-147) (-1))
  | 2 => (ofSix (-622) (-1) (6) (-101) (-23) (-1))
  | 3 => (ofSix (-484) (-23) (101) (6) (-5) (1))
  | 4 => (ofSix (-472) (-5) (6) (-14) (-79) (-1))
  | 5 => (ofSix (-226) (-4) (5) (-7) (-46) (-1))
  | 6 => (ofSix (-147) (-1) (5) (-26) (-10) (-1))
  | 7 => (ofSix (-135) (-2) (3) (-10) (-49) (-1))
  | 8 => (ofSix (-124) (-5) (6) (-2) (-21) (-1))
  | 9 => (ofSix (-124) (-2) (23) (-5) (-1) (-1))
  | 10 => (ofSix (-101) (-23) (21) (1) (-5) (-1))
  | 11 => (ofSix (-97) (-10) (26) (5) (-4) (1))
  | 12 => (ofSix (-88) (-2) (3) (-11) (-31) (-1))
  | 13 => (ofSix (-79) (-1) (6) (-14) (-2) (-1))
  | 14 => (ofSix (-67) (-6) (5) (2) (-14) (-1))
  | 15 => (ofSix (-49) (-1) (3) (-10) (-12) (-1))
  | 16 => (ofSix (-46) (-1) (5) (-7) (-4) (-1))
  | 17 => (ofSix (-36) (-4) (5) (-3) (-7) (-1))
  | 18 => (ofSix (-36) (-3) (10) (-4) (-1) (-1))
  | 19 => (ofSix (-31) (-1) (3) (-11) (-5) (-1))
  | 20 => (ofSix (-26) (-10) (7) (1) (-4) (-1))
  | 21 => (ofSix (-26) (-5) (4) (4) (-7) (-1))
  | 22 => (ofSix (-25) (-2) (5) (-2) (-4) (-1))
  | 23 => (ofSix (-25) (-2) (6) (-2) (-3) (-1))
  | 24 => (ofSix (-22) (-5) (12) (-2) (-1) (-1))
  | 25 => (ofSix (-22) (-2) (3) (-5) (-7) (-1))
  | 26 => (ofSix (-21) (-2) (4) (-1) (-5) (-1))
  | 27 => (ofSix (-21) (-1) (6) (-2) (-2) (-1))
  | 28 => (ofSix (-16) (-5) (11) (3) (-2) (1))
  | 29 => (ofSix (-16) (1) (2) (-5) (-1) (-1))
  | 30 => (ofSix (-14) (-2) (3) (1) (-5) (-1))
  | 31 => (ofSix (-13) (-12) (10) (3) (-2) (1))
  | 32 => (ofSix (-12) (-10) (7) (-1) (-1) (-2))
  | 33 => (ofSix (-11) (-5) (6) (1) (-2) (-1))
  | 34 => (ofSix (-11) (-4) (5) (-2) (-2) (-1))
  | 35 => (ofSix (-11) (-2) (4) (-4) (-1) (-1))
  | 36 => (ofSix (-9) (-6) (5) (2) (-2) (-1))
  | 37 => (ofSix (-7) (-6) (4) (3) (-2) (-1))
  | 38 => (ofSix (-7) (-5) (4) (-1) (-2) (-1))
  | 39 => (ofSix (-7) (-4) (2) (1) (-4) (-1))
  | 40 => (ofSix (-7) (-3) (2) (-1) (-4) (-1))
  | 41 => (ofSix (-7) (-1) (2) (-5) (-4) (-1))
  | 42 => (ofSix (-7) (-1) (3) (-5) (1) (-1))
  | 43 => (ofSix (-6) (1) (1) (-5) (-4) (1))
  | 44 => (ofSix (-6) (1) (1) (-2) (-1) (1))
  | 45 => (ofSix (-5) (-5) (3) (-4) (-1) (-2))
  | 46 => (ofSix (-5) (-2) (4) (1) (-1) (-1))
  | 47 => (ofSix (-5) (-2) (5) (-1) (1) (-2))
  | 48 => (ofSix (-5) (-1) (1) (-4) (1) (-2))
  | 49 => (ofSix (-5) (-1) (1) (-2) (-1) (-2))
  | 50 => (ofSix (-5) (-1) (1) (-1) (-2) (-2))
  | 51 => (ofSix (-5) (-1) (1) (1) (-3) (1))
  | 52 => (ofSix (-4) (-2) (1) (-1) (-2) (-3))
  | 53 => (ofSix (-4) (-2) (1) (1) (-2) (1))
  | 54 => (ofSix (-4) (-1) (1) (-1) (-2) (1))
  | 55 => (ofSix (-4) (-1) (1) (1) (-2) (-2))
  | 56 => (ofSix (-4) (-1) (2) (-1) (-1) (1))
  | 57 => (ofSix (-3) (-2) (1) (1) (-1) (2))
  | 58 => (ofSix (-3) (-2) (2) (-1) (-1) (1))
  | 59 => (ofSix (-3) (-1) (1) (-2) (-2) (1))
  | 60 => (ofSix (-2) (-2) (-1) (-1) (1) (-2))
  | _ => (ofSix (-2) (-2) (-1) (-1) (2) (-1))

def seed0 : Cone.State := ⟨31,11,16⟩
theorem domain0 : GenericStrip.Domain 2 seed0.A seed0.H seed0.Z := by unfold GenericStrip.Domain seed0; decide
def strip0 (n : Nat) (i : Fin 6) : Matrix 4 :=
  GenericStrip.phase 2 (GenericStrip.orbit 2 seed0 n).A (GenericStrip.orbit 2 seed0 n).H (GenericStrip.orbit 2 seed0 n).Z i
def seed1 : Cone.State := ⟨49,10,22⟩
theorem domain1 : GenericStrip.Domain 2 seed1.A seed1.H seed1.Z := by unfold GenericStrip.Domain seed1; decide
def strip1 (n : Nat) (i : Fin 6) : Matrix 4 :=
  GenericStrip.phase 2 (GenericStrip.orbit 2 seed1 n).A (GenericStrip.orbit 2 seed1 n).H (GenericStrip.orbit 2 seed1 n).Z i
def seed2 : Cone.State := ⟨46,7,11⟩
theorem domain2 : GenericStrip.Domain 4 seed2.A seed2.H seed2.Z := by unfold GenericStrip.Domain seed2; decide
def strip2 (n : Nat) (i : Fin 6) : Matrix 4 :=
  GenericStrip.phase 4 (GenericStrip.orbit 4 seed2 n).A (GenericStrip.orbit 4 seed2 n).H (GenericStrip.orbit 4 seed2 n).Z i
def seed3 : Cone.State := ⟨147,26,36⟩
theorem domain3 : GenericStrip.Domain 4 seed3.A seed3.H seed3.Z := by unfold GenericStrip.Domain seed3; decide
def strip3 (n : Nat) (i : Fin 6) : Matrix 4 :=
  GenericStrip.phase 4 (GenericStrip.orbit 4 seed3 n).A (GenericStrip.orbit 4 seed3 n).H (GenericStrip.orbit 4 seed3 n).Z i
def seed4 : Cone.State := ⟨79,14,16⟩
theorem domain4 : GenericStrip.Domain 5 seed4.A seed4.H seed4.Z := by unfold GenericStrip.Domain seed4; decide
def strip4 (n : Nat) (i : Fin 6) : Matrix 4 :=
  GenericStrip.phase 5 (GenericStrip.orbit 5 seed4 n).A (GenericStrip.orbit 5 seed4 n).H (GenericStrip.orbit 5 seed4 n).Z i
def seed5 : Cone.State := ⟨622,101,124⟩
theorem domain5 : GenericStrip.Domain 5 seed5.A seed5.H seed5.Z := by unfold GenericStrip.Domain seed5; decide
def strip5 (n : Nat) (i : Fin 6) : Matrix 4 :=
  GenericStrip.phase 5 (GenericStrip.orbit 5 seed5 n).A (GenericStrip.orbit 5 seed5 n).H (GenericStrip.orbit 5 seed5 n).Z i

inductive Core : Matrix 4 → Prop
  | finite (i : Fin 62) : Core (node i)
  | affineSeven (n : Int) (hn : 0≤n) (i : Fin 4) : Core (AffineFiveLocal.Seven.tail n i)
  | affineNine (n : Int) (hn : 0≤n) (i : Fin 4) : Core (AffineFiveLocal.Nine.tail n i)
  | strip0 (n : Nat) (i : Fin 6) : Core (strip0 n i)
  | strip1 (n : Nat) (i : Fin 6) : Core (strip1 n i)
  | strip2 (n : Nat) (i : Fin 6) : Core (strip2 n i)
  | strip3 (n : Nat) (i : Fin 6) : Core (strip3 n i)
  | strip4 (n : Nat) (i : Fin 6) : Core (strip4 n i)
  | strip5 (n : Nat) (i : Fin 6) : Core (strip5 n i)
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
  have he : relabel (mutate (node 0) 0) perm5 = WeakForks.template (6) (5) (3709) (29) (21632) (101) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 0) 0) perm5) u v = (WeakForks.template (6) (5) (3709) (29) (21632) (101)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (mutate (node 0) 0) perm5) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (6) (5) (3709) (29) (21632) (101) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm5 hb

theorem edge0_1 : Core (mutate (node 0) 1) ∨
    WeakForks.IsWeakFork (mutate (node 0) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 0) 1) 1 := by
  right; right
  have he : relabel (reverse (mutate (node 0) 1)) perm6 = WeakRegions.root (3709) (374614) (2306992) (101) (622) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 0) 1)) perm6) u v = (WeakRegions.root (3709) (374614) (2306992) (101) (622) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 0) 1)) perm6) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (3709) (374614) (2306992) (101) (622) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm6 hb)

theorem edge0_2 : Core (mutate (node 0) 2) ∨
    WeakForks.IsWeakFork (mutate (node 0) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 0) 2) 2 := by
  have he : mutate (node 0) 2 = reverse (relabel (strip5 0 2) perm16) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 0) 2) u v = (reverse (relabel (strip5 0 2) perm16)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.strip5 0 2) perm16))

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
  have he : relabel (mutate (node 1) 0) perm5 = WeakForks.template (5) (4) (725) (19) (3478) (26) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 1) 0) perm5) u v = (WeakForks.template (5) (4) (725) (19) (3478) (26)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (mutate (node 1) 0) perm5) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (5) (4) (725) (19) (3478) (26) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm5 hb

theorem edge1_1 : Core (mutate (node 1) 1) ∨
    WeakForks.IsWeakFork (mutate (node 1) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 1) 1) 1 := by
  right; right
  have he : relabel (reverse (mutate (node 1) 1)) perm6 = WeakRegions.root (725) (18854) (106570) (26) (147) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 1) 1)) perm6) u v = (WeakRegions.root (725) (18854) (106570) (26) (147) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 1) 1)) perm6) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (725) (18854) (106570) (26) (147) (1) (by unfold WeakRegions.Domain; decide) (by decide)
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
  have he : mutate (node 1) 3 = relabel (node 6) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 1) 3) u v = (relabel (node 6) perm21) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 6) perm21)

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
  have he : relabel (reverse (mutate (node 2) 1)) perm6 = WeakRegions.root (622) (62823) (14300) (101) (23) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 2) 1)) perm6) u v = (WeakRegions.root (622) (62823) (14300) (101) (23) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 2) 1)) perm6) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (622) (62823) (14300) (101) (23) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm6 hb)

theorem edge2_2 : Core (mutate (node 2) 2) ∨
    WeakForks.IsWeakFork (mutate (node 2) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 2) 2) 2 := by
  have he : mutate (node 2) 2 = reverse (relabel (strip5 0 0) perm4) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 2) 2) u v = (reverse (relabel (strip5 0 0) perm4)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.strip5 0 0) perm4))

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
  have he : relabel (mutate (node 3) 0) perm4 = WeakForks.template (101) (484) (23) (48879) (2324) (6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 3) 0) perm4) u v = (WeakForks.template (101) (484) (23) (48879) (2324) (6)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (mutate (node 3) 0) perm4) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (101) (484) (23) (48879) (2324) (6) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm4 hb

theorem edge3_1 : Core (mutate (node 3) 1) ∨
    WeakForks.IsWeakFork (mutate (node 3) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 3) 1) 1 := by
  right; left
  have he : relabel (reverse (mutate (node 3) 1)) perm10 = WeakForks.template (5) (484) (6) (2319) (29) (23) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 3) 1)) perm10) u v = (WeakForks.template (5) (484) (6) (2319) (29) (23)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (reverse (mutate (node 3) 1)) perm10) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (5) (484) (6) (2319) (29) (23) (by unfold WeakForks.Domain; decide)
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
  have he : mutate (node 3) 3 = relabel (node 10) perm5 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 3) 3) u v = (relabel (node 10) perm5) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 10) perm5)

theorem cyclic4 : ¬ Acyclic (node 4) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge4_0 : Core (mutate (node 4) 0) ∨
    WeakForks.IsWeakFork (mutate (node 4) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 4) 0) 0 := by
  right; left
  have he : relabel (mutate (node 4) 0) perm5 = WeakForks.template (6) (5) (472) (29) (2753) (14) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 4) 0) perm5) u v = (WeakForks.template (6) (5) (472) (29) (2753) (14)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (mutate (node 4) 0) perm5) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (6) (5) (472) (29) (2753) (14) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm5 hb

theorem edge4_1 : Core (mutate (node 4) 1) ∨
    WeakForks.IsWeakFork (mutate (node 4) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 4) 1) 1 := by
  right; right
  have he : relabel (reverse (mutate (node 4) 1)) perm6 = WeakRegions.root (472) (6613) (37282) (14) (79) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 4) 1)) perm6) u v = (WeakRegions.root (472) (6613) (37282) (14) (79) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 4) 1)) perm6) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (472) (6613) (37282) (14) (79) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm6 hb)

theorem edge4_2 : Core (mutate (node 4) 2) ∨
    WeakForks.IsWeakFork (mutate (node 4) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 4) 2) 2 := by
  have he : mutate (node 4) 2 = reverse (relabel (strip4 0 2) perm16) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 4) 2) u v = (reverse (relabel (strip4 0 2) perm16)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.strip4 0 2) perm16))

theorem edge4_3 : Core (mutate (node 4) 3) ∨
    WeakForks.IsWeakFork (mutate (node 4) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 4) 3) 3 := by
  have he : mutate (node 4) 3 = relabel (node 13) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 4) 3) u v = (relabel (node 13) perm21) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 13) perm21)

theorem cyclic5 : ¬ Acyclic (node 5) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge5_0 : Core (mutate (node 5) 0) ∨
    WeakForks.IsWeakFork (mutate (node 5) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 5) 0) 0 := by
  right; left
  have he : relabel (mutate (node 5) 0) perm5 = WeakForks.template (5) (4) (226) (19) (1084) (7) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 5) 0) perm5) u v = (WeakForks.template (5) (4) (226) (19) (1084) (7)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (mutate (node 5) 0) perm5) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (5) (4) (226) (19) (1084) (7) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm5 hb

theorem edge5_1 : Core (mutate (node 5) 1) ∨
    WeakForks.IsWeakFork (mutate (node 5) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 5) 1) 1 := by
  right; right
  have he : relabel (reverse (mutate (node 5) 1)) perm6 = WeakRegions.root (226) (1586) (10391) (7) (46) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 5) 1)) perm6) u v = (WeakRegions.root (226) (1586) (10391) (7) (46) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 5) 1)) perm6) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (226) (1586) (10391) (7) (46) (1) (by unfold WeakRegions.Domain; decide) (by decide)
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
  have he : mutate (node 6) 0 = relabel (node 1) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 6) 0) u v = (relabel (node 1) perm21) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 1) perm21)

theorem edge6_1 : Core (mutate (node 6) 1) ∨
    WeakForks.IsWeakFork (mutate (node 6) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 6) 1) 1 := by
  right; right
  have he : relabel (reverse (mutate (node 6) 1)) perm6 = WeakRegions.root (147) (3823) (1465) (26) (10) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 6) 1)) perm6) u v = (WeakRegions.root (147) (3823) (1465) (26) (10) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 6) 1)) perm6) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (147) (3823) (1465) (26) (10) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm6 hb)

theorem edge6_2 : Core (mutate (node 6) 2) ∨
    WeakForks.IsWeakFork (mutate (node 6) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 6) 2) 2 := by
  have he : mutate (node 6) 2 = reverse (relabel (strip3 0 0) perm4) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 6) 2) u v = (reverse (relabel (strip3 0 0) perm4)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.strip3 0 0) perm4))

theorem edge6_3 : Core (mutate (node 6) 3) ∨
    WeakForks.IsWeakFork (mutate (node 6) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 6) 3) 3 := by
  have he : mutate (node 6) 3 = reverse (relabel (node 11) perm7) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 6) 3) u v = (reverse (relabel (node 11) perm7)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 11) perm7))

theorem cyclic7 : ¬ Acyclic (node 7) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge7_0 : Core (mutate (node 7) 0) ∨
    WeakForks.IsWeakFork (mutate (node 7) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 7) 0) 0 := by
  right; left
  have he : relabel (mutate (node 7) 0) perm5 = WeakForks.template (3) (2) (135) (5) (356) (10) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 7) 0) perm5) u v = (WeakForks.template (3) (2) (135) (5) (356) (10)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (mutate (node 7) 0) perm5) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (3) (2) (135) (5) (356) (10) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm5 hb

theorem edge7_1 : Core (mutate (node 7) 1) ∨
    WeakForks.IsWeakFork (mutate (node 7) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 7) 1) 1 := by
  right; right
  have he : relabel (reverse (mutate (node 7) 1)) perm6 = WeakRegions.root (135) (1352) (6612) (10) (49) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 7) 1)) perm6) u v = (WeakRegions.root (135) (1352) (6612) (10) (49) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 7) 1)) perm6) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (135) (1352) (6612) (10) (49) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm6 hb)

theorem edge7_2 : Core (mutate (node 7) 2) ∨
    WeakForks.IsWeakFork (mutate (node 7) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 7) 2) 2 := by
  have he : mutate (node 7) 2 = reverse (relabel (strip1 0 2) perm16) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 7) 2) u v = (reverse (relabel (strip1 0 2) perm16)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.strip1 0 2) perm16))

theorem edge7_3 : Core (mutate (node 7) 3) ∨
    WeakForks.IsWeakFork (mutate (node 7) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 7) 3) 3 := by
  have he : mutate (node 7) 3 = relabel (node 15) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 7) 3) u v = (relabel (node 15) perm21) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 15) perm21)

theorem cyclic8 : ¬ Acyclic (node 8) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge8_0 : Core (mutate (node 8) 0) ∨
    WeakForks.IsWeakFork (mutate (node 8) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 8) 0) 0 := by
  right; left
  have he : relabel (mutate (node 8) 0) perm5 = WeakForks.template (6) (5) (124) (29) (723) (2) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 8) 0) perm5) u v = (WeakForks.template (6) (5) (124) (29) (723) (2)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (mutate (node 8) 0) perm5) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (6) (5) (124) (29) (723) (2) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm5 hb

theorem edge8_1 : Core (mutate (node 8) 1) ∨
    WeakForks.IsWeakFork (mutate (node 8) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 8) 1) 1 := by
  right; right
  have he : relabel (reverse (mutate (node 8) 1)) perm6 = WeakRegions.root (124) (253) (2598) (2) (21) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 8) 1)) perm6) u v = (WeakRegions.root (124) (253) (2598) (2) (21) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 8) 1)) perm6) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (124) (253) (2598) (2) (21) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm6 hb)

theorem edge8_2 : Core (mutate (node 8) 2) ∨
    WeakForks.IsWeakFork (mutate (node 8) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 8) 2) 2 := by
  have he : mutate (node 8) 2 = reverse (relabel (node 9) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 8) 2) u v = (reverse (relabel (node 9) perm6)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 9) perm6))

theorem edge8_3 : Core (mutate (node 8) 3) ∨
    WeakForks.IsWeakFork (mutate (node 8) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 8) 3) 3 := by
  have he : mutate (node 8) 3 = relabel (node 27) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 8) 3) u v = (relabel (node 27) perm21) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 27) perm21)

theorem cyclic9 : ¬ Acyclic (node 9) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge9_0 : Core (mutate (node 9) 0) ∨
    WeakForks.IsWeakFork (mutate (node 9) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 9) 0) 0 := by
  right; left
  have he : relabel (mutate (node 9) 0) perm5 = WeakForks.template (23) (2) (124) (45) (2851) (5) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 9) 0) perm5) u v = (WeakForks.template (23) (2) (124) (45) (2851) (5)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (mutate (node 9) 0) perm5) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (23) (2) (124) (45) (2851) (5) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm5 hb

theorem edge9_1 : Core (mutate (node 9) 1) ∨
    WeakForks.IsWeakFork (mutate (node 9) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 9) 1) 1 := by
  have he : mutate (node 9) 1 = relabel (strip5 0 0) perm22 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 9) 1) u v = (relabel (strip5 0 0) perm22) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.strip5 0 0) perm22)

theorem edge9_2 : Core (mutate (node 9) 2) ∨
    WeakForks.IsWeakFork (mutate (node 9) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 9) 2) 2 := by
  have he : mutate (node 9) 2 = reverse (relabel (node 8) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 9) 2) u v = (reverse (relabel (node 8) perm6)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 8) perm6))

theorem edge9_3 : Core (mutate (node 9) 3) ∨
    WeakForks.IsWeakFork (mutate (node 9) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 9) 3) 3 := by
  have he : mutate (node 9) 3 = relabel (node 10) perm1 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 9) 3) u v = (relabel (node 10) perm1) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 10) perm1)

theorem cyclic10 : ¬ Acyclic (node 10) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge10_0 : Core (mutate (node 10) 0) ∨
    WeakForks.IsWeakFork (mutate (node 10) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 10) 0) 0 := by
  right; right
  have he : relabel (reverse (mutate (node 10) 0)) perm5 = WeakRegions.root (21) (482) (2116) (23) (101) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 10) 0)) perm5) u v = (WeakRegions.root (21) (482) (2116) (23) (101) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 10) 0)) perm5) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (21) (482) (2116) (23) (101) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm5 hb)

theorem edge10_1 : Core (mutate (node 10) 1) ∨
    WeakForks.IsWeakFork (mutate (node 10) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 10) 1) 1 := by
  have he : mutate (node 10) 1 = relabel (node 3) perm5 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 10) 1) u v = (relabel (node 3) perm5) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 3) perm5)

theorem edge10_2 : Core (mutate (node 10) 2) ∨
    WeakForks.IsWeakFork (mutate (node 10) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 10) 2) 2 := by
  have he : mutate (node 10) 2 = relabel (node 9) perm1 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 10) 2) u v = (relabel (node 9) perm1) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 9) perm1)

theorem edge10_3 : Core (mutate (node 10) 3) ∨
    WeakForks.IsWeakFork (mutate (node 10) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 10) 3) 3 := by
  have he : mutate (node 10) 3 = relabel (node 26) perm5 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 10) 3) u v = (relabel (node 26) perm5) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 26) perm5)

theorem cyclic11 : ¬ Acyclic (node 11) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge11_0 : Core (mutate (node 11) 0) ∨
    WeakForks.IsWeakFork (mutate (node 11) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 11) 0) 0 := by
  right; left
  have he : relabel (mutate (node 11) 0) perm4 = WeakForks.template (26) (97) (10) (2518) (261) (5) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 11) 0) perm4) u v = (WeakForks.template (26) (97) (10) (2518) (261) (5)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (mutate (node 11) 0) perm4) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (26) (97) (10) (2518) (261) (5) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm4 hb

theorem edge11_1 : Core (mutate (node 11) 1) ∨
    WeakForks.IsWeakFork (mutate (node 11) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 11) 1) 1 := by
  right; left
  have he : relabel (reverse (mutate (node 11) 1)) perm10 = WeakForks.template (4) (97) (5) (362) (19) (10) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 11) 1)) perm10) u v = (WeakForks.template (4) (97) (5) (362) (19) (10)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (reverse (mutate (node 11) 1)) perm10) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (4) (97) (5) (362) (19) (10) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_reverse (WeakForks.fork_of_relabel perm10 hb)

theorem edge11_2 : Core (mutate (node 11) 2) ∨
    WeakForks.IsWeakFork (mutate (node 11) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 11) 2) 2 := by
  have he : mutate (node 11) 2 = reverse (relabel (node 6) perm7) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 11) 2) u v = (reverse (relabel (node 6) perm7)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 6) perm7))

theorem edge11_3 : Core (mutate (node 11) 3) ∨
    WeakForks.IsWeakFork (mutate (node 11) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 11) 3) 3 := by
  have he : mutate (node 11) 3 = relabel (node 20) perm5 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 11) 3) u v = (relabel (node 20) perm5) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 20) perm5)

theorem cyclic12 : ¬ Acyclic (node 12) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge12_0 : Core (mutate (node 12) 0) ∨
    WeakForks.IsWeakFork (mutate (node 12) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 12) 0) 0 := by
  right; left
  have he : relabel (mutate (node 12) 0) perm5 = WeakForks.template (3) (2) (88) (5) (233) (11) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 12) 0) perm5) u v = (WeakForks.template (3) (2) (88) (5) (233) (11)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (mutate (node 12) 0) perm5) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (3) (2) (88) (5) (233) (11) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm5 hb

theorem edge12_1 : Core (mutate (node 12) 1) ∨
    WeakForks.IsWeakFork (mutate (node 12) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 12) 1) 1 := by
  right; right
  have he : relabel (reverse (mutate (node 12) 1)) perm6 = WeakRegions.root (88) (970) (2725) (11) (31) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 12) 1)) perm6) u v = (WeakRegions.root (88) (970) (2725) (11) (31) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 12) 1)) perm6) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (88) (970) (2725) (11) (31) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm6 hb)

theorem edge12_2 : Core (mutate (node 12) 2) ∨
    WeakForks.IsWeakFork (mutate (node 12) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 12) 2) 2 := by
  have he : mutate (node 12) 2 = reverse (relabel (strip0 0 2) perm16) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 12) 2) u v = (reverse (relabel (strip0 0 2) perm16)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.strip0 0 2) perm16))

theorem edge12_3 : Core (mutate (node 12) 3) ∨
    WeakForks.IsWeakFork (mutate (node 12) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 12) 3) 3 := by
  have he : mutate (node 12) 3 = relabel (node 19) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 12) 3) u v = (relabel (node 19) perm21) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 19) perm21)

theorem cyclic13 : ¬ Acyclic (node 13) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge13_0 : Core (mutate (node 13) 0) ∨
    WeakForks.IsWeakFork (mutate (node 13) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 13) 0) 0 := by
  have he : mutate (node 13) 0 = relabel (node 4) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 13) 0) u v = (relabel (node 4) perm21) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 4) perm21)

theorem edge13_1 : Core (mutate (node 13) 1) ∨
    WeakForks.IsWeakFork (mutate (node 13) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 13) 1) 1 := by
  right; right
  have he : relabel (reverse (mutate (node 13) 1)) perm6 = WeakRegions.root (79) (1107) (152) (14) (2) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 13) 1)) perm6) u v = (WeakRegions.root (79) (1107) (152) (14) (2) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 13) 1)) perm6) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (79) (1107) (152) (14) (2) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm6 hb)

theorem edge13_2 : Core (mutate (node 13) 2) ∨
    WeakForks.IsWeakFork (mutate (node 13) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 13) 2) 2 := by
  have he : mutate (node 13) 2 = reverse (relabel (strip4 0 0) perm4) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 13) 2) u v = (reverse (relabel (strip4 0 0) perm4)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.strip4 0 0) perm4))

theorem edge13_3 : Core (mutate (node 13) 3) ∨
    WeakForks.IsWeakFork (mutate (node 13) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 13) 3) 3 := by
  have he : mutate (node 13) 3 = relabel (node 14) perm1 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 13) 3) u v = (relabel (node 14) perm1) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 14) perm1)

theorem cyclic14 : ¬ Acyclic (node 14) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge14_0 : Core (mutate (node 14) 0) ∨
    WeakForks.IsWeakFork (mutate (node 14) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 14) 0) 0 := by
  right; left
  have he : relabel (mutate (node 14) 0) perm4 = WeakForks.template (5) (67) (6) (321) (29) (2) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 14) 0) perm4) u v = (WeakForks.template (5) (67) (6) (321) (29) (2)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (mutate (node 14) 0) perm4) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (5) (67) (6) (321) (29) (2) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm4 hb

theorem edge14_1 : Core (mutate (node 14) 1) ∨
    WeakForks.IsWeakFork (mutate (node 14) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 14) 1) 1 := by
  right; left
  have he : relabel (reverse (mutate (node 14) 1)) perm10 = WeakForks.template (14) (67) (2) (933) (29) (6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 14) 1)) perm10) u v = (WeakForks.template (14) (67) (2) (933) (29) (6)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (reverse (mutate (node 14) 1)) perm10) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (14) (67) (2) (933) (29) (6) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_reverse (WeakForks.fork_of_relabel perm10 hb)

theorem edge14_2 : Core (mutate (node 14) 2) ∨
    WeakForks.IsWeakFork (mutate (node 14) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 14) 2) 2 := by
  have he : mutate (node 14) 2 = relabel (node 13) perm1 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 14) 2) u v = (relabel (node 13) perm1) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 13) perm1)

theorem edge14_3 : Core (mutate (node 14) 3) ∨
    WeakForks.IsWeakFork (mutate (node 14) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 14) 3) 3 := by
  have he : mutate (node 14) 3 = reverse (relabel (node 30) perm19) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 14) 3) u v = (reverse (relabel (node 30) perm19)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 30) perm19))

theorem cyclic15 : ¬ Acyclic (node 15) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge15_0 : Core (mutate (node 15) 0) ∨
    WeakForks.IsWeakFork (mutate (node 15) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 15) 0) 0 := by
  have he : mutate (node 15) 0 = relabel (node 7) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 15) 0) u v = (relabel (node 7) perm21) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 7) perm21)

theorem edge15_1 : Core (mutate (node 15) 1) ∨
    WeakForks.IsWeakFork (mutate (node 15) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 15) 1) 1 := by
  right; right
  have he : relabel (reverse (mutate (node 15) 1)) perm6 = WeakRegions.root (49) (491) (585) (10) (12) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 15) 1)) perm6) u v = (WeakRegions.root (49) (491) (585) (10) (12) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 15) 1)) perm6) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (49) (491) (585) (10) (12) (1) (by unfold WeakRegions.Domain; decide) (by decide)
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
  have he : mutate (node 15) 3 = reverse (relabel (node 31) perm7) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 15) 3) u v = (reverse (relabel (node 31) perm7)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 31) perm7))

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
  have he : relabel (reverse (mutate (node 16) 1)) perm6 = WeakRegions.root (46) (323) (179) (7) (4) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 16) 1)) perm6) u v = (WeakRegions.root (46) (323) (179) (7) (4) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 16) 1)) perm6) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (46) (323) (179) (7) (4) (1) (by unfold WeakRegions.Domain; decide) (by decide)
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
  have he : mutate (node 16) 3 = relabel (node 21) perm1 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 16) 3) u v = (relabel (node 21) perm1) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 21) perm1)

theorem cyclic17 : ¬ Acyclic (node 17) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge17_0 : Core (mutate (node 17) 0) ∨
    WeakForks.IsWeakFork (mutate (node 17) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 17) 0) 0 := by
  right; left
  have he : relabel (mutate (node 17) 0) perm5 = WeakForks.template (5) (4) (36) (19) (173) (3) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 17) 0) perm5) u v = (WeakForks.template (5) (4) (36) (19) (173) (3)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (mutate (node 17) 0) perm5) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (5) (4) (36) (19) (173) (3) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm5 hb

theorem edge17_1 : Core (mutate (node 17) 1) ∨
    WeakForks.IsWeakFork (mutate (node 17) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 17) 1) 1 := by
  right; right
  have he : relabel (reverse (mutate (node 17) 1)) perm6 = WeakRegions.root (36) (112) (247) (3) (7) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 17) 1)) perm6) u v = (WeakRegions.root (36) (112) (247) (3) (7) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 17) 1)) perm6) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (36) (112) (247) (3) (7) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm6 hb)

theorem edge17_2 : Core (mutate (node 17) 2) ∨
    WeakForks.IsWeakFork (mutate (node 17) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 17) 2) 2 := by
  have he : mutate (node 17) 2 = reverse (relabel (node 18) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 17) 2) u v = (reverse (relabel (node 18) perm6)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 18) perm6))

theorem edge17_3 : Core (mutate (node 17) 3) ∨
    WeakForks.IsWeakFork (mutate (node 17) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 17) 3) 3 := by
  have he : mutate (node 17) 3 = reverse (relabel (node 42) perm13) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 17) 3) u v = (reverse (relabel (node 42) perm13)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 42) perm13))

theorem cyclic18 : ¬ Acyclic (node 18) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge18_0 : Core (mutate (node 18) 0) ∨
    WeakForks.IsWeakFork (mutate (node 18) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 18) 0) 0 := by
  right; left
  have he : relabel (mutate (node 18) 0) perm5 = WeakForks.template (10) (3) (36) (29) (359) (4) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 18) 0) perm5) u v = (WeakForks.template (10) (3) (36) (29) (359) (4)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (mutate (node 18) 0) perm5) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (10) (3) (36) (29) (359) (4) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm5 hb

theorem edge18_1 : Core (mutate (node 18) 1) ∨
    WeakForks.IsWeakFork (mutate (node 18) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 18) 1) 1 := by
  have he : mutate (node 18) 1 = relabel (strip3 0 0) perm22 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 18) 1) u v = (relabel (strip3 0 0) perm22) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.strip3 0 0) perm22)

theorem edge18_2 : Core (mutate (node 18) 2) ∨
    WeakForks.IsWeakFork (mutate (node 18) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 18) 2) 2 := by
  have he : mutate (node 18) 2 = reverse (relabel (node 17) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 18) 2) u v = (reverse (relabel (node 17) perm6)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 17) perm6))

theorem edge18_3 : Core (mutate (node 18) 3) ∨
    WeakForks.IsWeakFork (mutate (node 18) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 18) 3) 3 := by
  have he : mutate (node 18) 3 = relabel (node 20) perm1 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 18) 3) u v = (relabel (node 20) perm1) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 20) perm1)

theorem cyclic19 : ¬ Acyclic (node 19) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge19_0 : Core (mutate (node 19) 0) ∨
    WeakForks.IsWeakFork (mutate (node 19) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 19) 0) 0 := by
  have he : mutate (node 19) 0 = relabel (node 12) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 19) 0) u v = (relabel (node 12) perm21) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 12) perm21)

theorem edge19_1 : Core (mutate (node 19) 1) ∨
    WeakForks.IsWeakFork (mutate (node 19) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 19) 1) 1 := by
  right; right
  have he : relabel (reverse (mutate (node 19) 1)) perm6 = WeakRegions.root (31) (342) (152) (11) (5) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 19) 1)) perm6) u v = (WeakRegions.root (31) (342) (152) (11) (5) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 19) 1)) perm6) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (31) (342) (152) (11) (5) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm6 hb)

theorem edge19_2 : Core (mutate (node 19) 2) ∨
    WeakForks.IsWeakFork (mutate (node 19) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 19) 2) 2 := by
  have he : mutate (node 19) 2 = reverse (relabel (strip0 0 0) perm4) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 19) 2) u v = (reverse (relabel (strip0 0 0) perm4)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.strip0 0 0) perm4))

theorem edge19_3 : Core (mutate (node 19) 3) ∨
    WeakForks.IsWeakFork (mutate (node 19) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 19) 3) 3 := by
  have he : mutate (node 19) 3 = reverse (relabel (node 28) perm7) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 19) 3) u v = (reverse (relabel (node 28) perm7)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 28) perm7))

theorem cyclic20 : ¬ Acyclic (node 20) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge20_0 : Core (mutate (node 20) 0) ∨
    WeakForks.IsWeakFork (mutate (node 20) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 20) 0) 0 := by
  right; right
  have he : relabel (reverse (mutate (node 20) 0)) perm5 = WeakRegions.root (7) (69) (178) (10) (26) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 20) 0)) perm5) u v = (WeakRegions.root (7) (69) (178) (10) (26) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 20) 0)) perm5) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (7) (69) (178) (10) (26) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm5 hb)

theorem edge20_1 : Core (mutate (node 20) 1) ∨
    WeakForks.IsWeakFork (mutate (node 20) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 20) 1) 1 := by
  have he : mutate (node 20) 1 = relabel (node 11) perm5 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 20) 1) u v = (relabel (node 11) perm5) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 11) perm5)

theorem edge20_2 : Core (mutate (node 20) 2) ∨
    WeakForks.IsWeakFork (mutate (node 20) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 20) 2) 2 := by
  have he : mutate (node 20) 2 = relabel (node 18) perm1 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 20) 2) u v = (relabel (node 18) perm1) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 18) perm1)

theorem edge20_3 : Core (mutate (node 20) 3) ∨
    WeakForks.IsWeakFork (mutate (node 20) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 20) 3) 3 := by
  have he : mutate (node 20) 3 = relabel (node 40) perm5 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 20) 3) u v = (relabel (node 40) perm5) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 40) perm5)

theorem cyclic21 : ¬ Acyclic (node 21) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge21_0 : Core (mutate (node 21) 0) ∨
    WeakForks.IsWeakFork (mutate (node 21) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 21) 0) 0 := by
  right; left
  have he : relabel (mutate (node 21) 0) perm4 = WeakForks.template (4) (26) (5) (97) (19) (4) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 21) 0) perm4) u v = (WeakForks.template (4) (26) (5) (97) (19) (4)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (mutate (node 21) 0) perm4) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (4) (26) (5) (97) (19) (4) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm4 hb

theorem edge21_1 : Core (mutate (node 21) 1) ∨
    WeakForks.IsWeakFork (mutate (node 21) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 21) 1) 1 := by
  right; left
  have he : relabel (reverse (mutate (node 21) 1)) perm10 = WeakForks.template (7) (26) (4) (178) (29) (5) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 21) 1)) perm10) u v = (WeakForks.template (7) (26) (4) (178) (29) (5)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (reverse (mutate (node 21) 1)) perm10) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (7) (26) (4) (178) (29) (5) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_reverse (WeakForks.fork_of_relabel perm10 hb)

theorem edge21_2 : Core (mutate (node 21) 2) ∨
    WeakForks.IsWeakFork (mutate (node 21) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 21) 2) 2 := by
  have he : mutate (node 21) 2 = relabel (node 16) perm1 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 21) 2) u v = (relabel (node 16) perm1) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 16) perm1)

theorem edge21_3 : Core (mutate (node 21) 3) ∨
    WeakForks.IsWeakFork (mutate (node 21) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 21) 3) 3 := by
  have he : mutate (node 21) 3 = reverse (relabel (node 39) perm19) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 21) 3) u v = (reverse (relabel (node 39) perm19)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 39) perm19))

theorem cyclic22 : ¬ Acyclic (node 22) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge22_0 : Core (mutate (node 22) 0) ∨
    WeakForks.IsWeakFork (mutate (node 22) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 22) 0) 0 := by
  right; left
  have he : relabel (mutate (node 22) 0) perm5 = WeakForks.template (5) (2) (25) (9) (121) (2) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 22) 0) perm5) u v = (WeakForks.template (5) (2) (25) (9) (121) (2)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (mutate (node 22) 0) perm5) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (5) (2) (25) (9) (121) (2) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm5 hb

theorem edge22_1 : Core (mutate (node 22) 1) ∨
    WeakForks.IsWeakFork (mutate (node 22) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 22) 1) 1 := by
  right; right
  have he : relabel (reverse (mutate (node 22) 1)) perm6 = WeakRegions.root (25) (52) (95) (2) (4) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 22) 1)) perm6) u v = (WeakRegions.root (25) (52) (95) (2) (4) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 22) 1)) perm6) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (25) (52) (95) (2) (4) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm6 hb)

theorem edge22_2 : Core (mutate (node 22) 2) ∨
    WeakForks.IsWeakFork (mutate (node 22) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 22) 2) 2 := by
  have he : mutate (node 22) 2 = reverse (relabel (node 23) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 22) 2) u v = (reverse (relabel (node 23) perm6)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 23) perm6))

theorem edge22_3 : Core (mutate (node 22) 3) ∨
    WeakForks.IsWeakFork (mutate (node 22) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 22) 3) 3 := by
  have he : mutate (node 22) 3 = relabel (node 45) perm3 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 22) 3) u v = (relabel (node 45) perm3) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 45) perm3)

theorem cyclic23 : ¬ Acyclic (node 23) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge23_0 : Core (mutate (node 23) 0) ∨
    WeakForks.IsWeakFork (mutate (node 23) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 23) 0) 0 := by
  right; left
  have he : relabel (mutate (node 23) 0) perm5 = WeakForks.template (6) (2) (25) (11) (147) (2) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 23) 0) perm5) u v = (WeakForks.template (6) (2) (25) (11) (147) (2)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (mutate (node 23) 0) perm5) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (6) (2) (25) (11) (147) (2) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm5 hb

theorem edge23_1 : Core (mutate (node 23) 1) ∨
    WeakForks.IsWeakFork (mutate (node 23) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 23) 1) 1 := by
  right; right
  have he : relabel (reverse (mutate (node 23) 1)) perm6 = WeakRegions.root (25) (52) (69) (2) (3) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 23) 1)) perm6) u v = (WeakRegions.root (25) (52) (69) (2) (3) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 23) 1)) perm6) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (25) (52) (69) (2) (3) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm6 hb)

theorem edge23_2 : Core (mutate (node 23) 2) ∨
    WeakForks.IsWeakFork (mutate (node 23) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 23) 2) 2 := by
  have he : mutate (node 23) 2 = reverse (relabel (node 22) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 23) 2) u v = (reverse (relabel (node 22) perm6)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 22) perm6))

theorem edge23_3 : Core (mutate (node 23) 3) ∨
    WeakForks.IsWeakFork (mutate (node 23) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 23) 3) 3 := by
  have he : mutate (node 23) 3 = relabel (node 37) perm1 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 23) 3) u v = (relabel (node 37) perm1) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 37) perm1)

theorem cyclic24 : ¬ Acyclic (node 24) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge24_0 : Core (mutate (node 24) 0) ∨
    WeakForks.IsWeakFork (mutate (node 24) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 24) 0) 0 := by
  right; left
  have he : relabel (mutate (node 24) 0) perm5 = WeakForks.template (12) (5) (22) (59) (263) (2) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 24) 0) perm5) u v = (WeakForks.template (12) (5) (22) (59) (263) (2)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (mutate (node 24) 0) perm5) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (12) (5) (22) (59) (263) (2) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm5 hb

theorem edge24_1 : Core (mutate (node 24) 1) ∨
    WeakForks.IsWeakFork (mutate (node 24) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 24) 1) 1 := by
  have he : mutate (node 24) 1 = relabel (strip1 0 0) perm22 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 24) 1) u v = (relabel (strip1 0 0) perm22) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.strip1 0 0) perm22)

theorem edge24_2 : Core (mutate (node 24) 2) ∨
    WeakForks.IsWeakFork (mutate (node 24) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 24) 2) 2 := by
  have he : mutate (node 24) 2 = reverse (relabel (node 25) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 24) 2) u v = (reverse (relabel (node 25) perm6)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 25) perm6))

theorem edge24_3 : Core (mutate (node 24) 3) ∨
    WeakForks.IsWeakFork (mutate (node 24) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 24) 3) 3 := by
  have he : mutate (node 24) 3 = relabel (node 32) perm3 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 24) 3) u v = (relabel (node 32) perm3) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 32) perm3)

theorem cyclic25 : ¬ Acyclic (node 25) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge25_0 : Core (mutate (node 25) 0) ∨
    WeakForks.IsWeakFork (mutate (node 25) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 25) 0) 0 := by
  right; left
  have he : relabel (mutate (node 25) 0) perm5 = WeakForks.template (3) (2) (22) (5) (59) (5) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 25) 0) perm5) u v = (WeakForks.template (3) (2) (22) (5) (59) (5)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (mutate (node 25) 0) perm5) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (3) (2) (22) (5) (59) (5) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm5 hb

theorem edge25_1 : Core (mutate (node 25) 1) ∨
    WeakForks.IsWeakFork (mutate (node 25) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 25) 1) 1 := by
  right; right
  have he : relabel (reverse (mutate (node 25) 1)) perm6 = WeakRegions.root (22) (112) (151) (5) (7) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 25) 1)) perm6) u v = (WeakRegions.root (22) (112) (151) (5) (7) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 25) 1)) perm6) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (22) (112) (151) (5) (7) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm6 hb)

theorem edge25_2 : Core (mutate (node 25) 2) ∨
    WeakForks.IsWeakFork (mutate (node 25) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 25) 2) 2 := by
  have he : mutate (node 25) 2 = reverse (relabel (node 24) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 25) 2) u v = (reverse (relabel (node 24) perm6)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 24) perm6))

theorem edge25_3 : Core (mutate (node 25) 3) ∨
    WeakForks.IsWeakFork (mutate (node 25) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 25) 3) 3 := by
  have he : mutate (node 25) 3 = relabel (node 42) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 25) 3) u v = (relabel (node 42) perm21) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 42) perm21)

theorem cyclic26 : ¬ Acyclic (node 26) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge26_0 : Core (mutate (node 26) 0) ∨
    WeakForks.IsWeakFork (mutate (node 26) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 26) 0) 0 := by
  right; right
  have he : relabel (reverse (mutate (node 26) 0)) perm4 = WeakRegions.root (4) (79) (7) (21) (2) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 26) 0)) perm4) u v = (WeakRegions.root (4) (79) (7) (21) (2) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 26) 0)) perm4) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (4) (79) (7) (21) (2) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm4 hb)

theorem edge26_1 : Core (mutate (node 26) 1) ∨
    WeakForks.IsWeakFork (mutate (node 26) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 26) 1) 1 := by
  have he : mutate (node 26) 1 = relabel (node 10) perm5 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 26) 1) u v = (relabel (node 10) perm5) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 10) perm5)

theorem edge26_2 : Core (mutate (node 26) 2) ∨
    WeakForks.IsWeakFork (mutate (node 26) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 26) 2) 2 := by
  have he : mutate (node 26) 2 = reverse (relabel (node 27) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 26) 2) u v = (reverse (relabel (node 27) perm6)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 27) perm6))

theorem edge26_3 : Core (mutate (node 26) 3) ∨
    WeakForks.IsWeakFork (mutate (node 26) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 26) 3) 3 := by
  have he : mutate (node 26) 3 = reverse (relabel (node 48) perm13) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 26) 3) u v = (reverse (relabel (node 48) perm13)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 48) perm13))

theorem cyclic27 : ¬ Acyclic (node 27) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge27_0 : Core (mutate (node 27) 0) ∨
    WeakForks.IsWeakFork (mutate (node 27) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 27) 0) 0 := by
  have he : mutate (node 27) 0 = relabel (node 8) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 27) 0) u v = (relabel (node 8) perm21) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 8) perm21)

theorem edge27_1 : Core (mutate (node 27) 1) ∨
    WeakForks.IsWeakFork (mutate (node 27) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 27) 1) 1 := by
  right; right
  have he : relabel (reverse (mutate (node 27) 1)) perm6 = WeakRegions.root (21) (43) (36) (2) (2) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 27) 1)) perm6) u v = (WeakRegions.root (21) (43) (36) (2) (2) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 27) 1)) perm6) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (21) (43) (36) (2) (2) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm6 hb)

theorem edge27_2 : Core (mutate (node 27) 2) ∨
    WeakForks.IsWeakFork (mutate (node 27) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 27) 2) 2 := by
  have he : mutate (node 27) 2 = reverse (relabel (node 26) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 27) 2) u v = (reverse (relabel (node 26) perm6)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 26) perm6))

theorem edge27_3 : Core (mutate (node 27) 3) ∨
    WeakForks.IsWeakFork (mutate (node 27) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 27) 3) 3 := by
  have he : mutate (node 27) 3 = relabel (node 36) perm1 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 27) 3) u v = (relabel (node 36) perm1) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 36) perm1)

theorem cyclic28 : ¬ Acyclic (node 28) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge28_0 : Core (mutate (node 28) 0) ∨
    WeakForks.IsWeakFork (mutate (node 28) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 28) 0) 0 := by
  right; left
  have he : relabel (mutate (node 28) 0) perm4 = WeakForks.template (11) (16) (5) (174) (56) (3) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 28) 0) perm4) u v = (WeakForks.template (11) (16) (5) (174) (56) (3)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (mutate (node 28) 0) perm4) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (11) (16) (5) (174) (56) (3) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm4 hb

theorem edge28_1 : Core (mutate (node 28) 1) ∨
    WeakForks.IsWeakFork (mutate (node 28) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 28) 1) 1 := by
  right; left
  have he : relabel (reverse (mutate (node 28) 1)) perm10 = WeakForks.template (2) (16) (3) (21) (5) (5) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 28) 1)) perm10) u v = (WeakForks.template (2) (16) (3) (21) (5) (5)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (reverse (mutate (node 28) 1)) perm10) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (2) (16) (3) (21) (5) (5) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_reverse (WeakForks.fork_of_relabel perm10 hb)

theorem edge28_2 : Core (mutate (node 28) 2) ∨
    WeakForks.IsWeakFork (mutate (node 28) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 28) 2) 2 := by
  have he : mutate (node 28) 2 = reverse (relabel (node 19) perm7) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 28) 2) u v = (reverse (relabel (node 19) perm7)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 19) perm7))

theorem edge28_3 : Core (mutate (node 28) 3) ∨
    WeakForks.IsWeakFork (mutate (node 28) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 28) 3) 3 := by
  have he : mutate (node 28) 3 = relabel (node 33) perm5 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 28) 3) u v = (relabel (node 33) perm5) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 33) perm5)

theorem cyclic29 : ¬ Acyclic (node 29) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (by decide)
  have h1 := hr 2 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge29_0 : Core (mutate (node 29) 0) ∨
    WeakForks.IsWeakFork (mutate (node 29) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 29) 0) 0 := by
  have he : mutate (node 29) 0 = reverse (relabel (strip0 0 0) perm17) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 29) 0) u v = (reverse (relabel (strip0 0 0) perm17)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.strip0 0 0) perm17))

theorem edge29_1 : Core (mutate (node 29) 1) ∨
    WeakForks.IsWeakFork (mutate (node 29) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 29) 1) 1 := by
  have he : mutate (node 29) 1 = relabel (strip4 0 0) perm22 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 29) 1) u v = (relabel (strip4 0 0) perm22) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.strip4 0 0) perm22)

theorem edge29_2 : Core (mutate (node 29) 2) ∨
    WeakForks.IsWeakFork (mutate (node 29) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 29) 2) 2 := by
  have he : mutate (node 29) 2 = reverse (relabel (node 33) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 29) 2) u v = (reverse (relabel (node 33) perm6)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 33) perm6))

theorem edge29_3 : Core (mutate (node 29) 3) ∨
    WeakForks.IsWeakFork (mutate (node 29) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 29) 3) 3 := by
  have he : mutate (node 29) 3 = relabel (node 30) perm1 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 29) 3) u v = (relabel (node 30) perm1) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 30) perm1)

theorem cyclic30 : ¬ Acyclic (node 30) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge30_0 : Core (mutate (node 30) 0) ∨
    WeakForks.IsWeakFork (mutate (node 30) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 30) 0) 0 := by
  right; right
  have he : relabel (reverse (mutate (node 30) 0)) perm5 = WeakRegions.root (3) (5) (37) (2) (14) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 30) 0)) perm5) u v = (WeakRegions.root (3) (5) (37) (2) (14) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 30) 0)) perm5) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (3) (5) (37) (2) (14) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm5 hb)

theorem edge30_1 : Core (mutate (node 30) 1) ∨
    WeakForks.IsWeakFork (mutate (node 30) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 30) 1) 1 := by
  have he : mutate (node 30) 1 = reverse (relabel (node 14) perm11) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 30) 1) u v = (reverse (relabel (node 14) perm11)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 14) perm11))

theorem edge30_2 : Core (mutate (node 30) 2) ∨
    WeakForks.IsWeakFork (mutate (node 30) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 30) 2) 2 := by
  have he : mutate (node 30) 2 = relabel (node 29) perm1 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 30) 2) u v = (relabel (node 29) perm1) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 29) perm1)

theorem edge30_3 : Core (mutate (node 30) 3) ∨
    WeakForks.IsWeakFork (mutate (node 30) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 30) 3) 3 := by
  have he : mutate (node 30) 3 = reverse (relabel (node 51) perm19) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 30) 3) u v = (reverse (relabel (node 51) perm19)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 51) perm19))

theorem cyclic31 : ¬ Acyclic (node 31) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge31_0 : Core (mutate (node 31) 0) ∨
    WeakForks.IsWeakFork (mutate (node 31) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 31) 0) 0 := by
  right; left
  have he : relabel (mutate (node 31) 0) perm4 = WeakForks.template (10) (13) (12) (128) (121) (3) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 31) 0) perm4) u v = (WeakForks.template (10) (13) (12) (128) (121) (3)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (mutate (node 31) 0) perm4) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (10) (13) (12) (128) (121) (3) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm4 hb

theorem edge31_1 : Core (mutate (node 31) 1) ∨
    WeakForks.IsWeakFork (mutate (node 31) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 31) 1) 1 := by
  right; left
  have he : relabel (reverse (mutate (node 31) 1)) perm10 = WeakForks.template (2) (13) (3) (16) (5) (12) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 31) 1)) perm10) u v = (WeakForks.template (2) (13) (3) (16) (5) (12)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (reverse (mutate (node 31) 1)) perm10) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (2) (13) (3) (16) (5) (12) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_reverse (WeakForks.fork_of_relabel perm10 hb)

theorem edge31_2 : Core (mutate (node 31) 2) ∨
    WeakForks.IsWeakFork (mutate (node 31) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 31) 2) 2 := by
  have he : mutate (node 31) 2 = reverse (relabel (node 15) perm7) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 31) 2) u v = (reverse (relabel (node 15) perm7)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 15) perm7))

theorem edge31_3 : Core (mutate (node 31) 3) ∨
    WeakForks.IsWeakFork (mutate (node 31) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 31) 3) 3 := by
  have he : mutate (node 31) 3 = relabel (node 32) perm4 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 31) 3) u v = (relabel (node 32) perm4) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 32) perm4)

theorem cyclic32 : ¬ Acyclic (node 32) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge32_0 : Core (mutate (node 32) 0) ∨
    WeakForks.IsWeakFork (mutate (node 32) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 32) 0) 0 := by
  right; right
  have he : relabel (reverse (mutate (node 32) 0)) perm4 = WeakRegions.root (7) (83) (68) (12) (10) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 32) 0)) perm4) u v = (WeakRegions.root (7) (83) (68) (12) (10) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 32) 0)) perm4) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (7) (83) (68) (12) (10) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm4 hb)

theorem edge32_1 : Core (mutate (node 32) 1) ∨
    WeakForks.IsWeakFork (mutate (node 32) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 32) 1) 1 := by
  have he : mutate (node 32) 1 = relabel (node 24) perm4 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 32) 1) u v = (relabel (node 24) perm4) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 24) perm4)

theorem edge32_2 : Core (mutate (node 32) 2) ∨
    WeakForks.IsWeakFork (mutate (node 32) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 32) 2) 2 := by
  have he : mutate (node 32) 2 = relabel (node 31) perm3 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 32) 2) u v = (relabel (node 31) perm3) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 31) perm3)

theorem edge32_3 : Core (mutate (node 32) 3) ∨
    WeakForks.IsWeakFork (mutate (node 32) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 32) 3) 3 := by
  have he : mutate (node 32) 3 = relabel (node 38) perm3 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 32) 3) u v = (relabel (node 38) perm3) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 38) perm3)

theorem cyclic33 : ¬ Acyclic (node 33) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge33_0 : Core (mutate (node 33) 0) ∨
    WeakForks.IsWeakFork (mutate (node 33) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 33) 0) 0 := by
  right; right
  have he : relabel (reverse (mutate (node 33) 0)) perm5 = WeakRegions.root (6) (29) (64) (5) (11) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 33) 0)) perm5) u v = (WeakRegions.root (6) (29) (64) (5) (11) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 33) 0)) perm5) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (6) (29) (64) (5) (11) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm5 hb)

theorem edge33_1 : Core (mutate (node 33) 1) ∨
    WeakForks.IsWeakFork (mutate (node 33) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 33) 1) 1 := by
  have he : mutate (node 33) 1 = relabel (node 28) perm5 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 33) 1) u v = (relabel (node 28) perm5) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 28) perm5)

theorem edge33_2 : Core (mutate (node 33) 2) ∨
    WeakForks.IsWeakFork (mutate (node 33) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 33) 2) 2 := by
  have he : mutate (node 33) 2 = reverse (relabel (node 29) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 33) 2) u v = (reverse (relabel (node 29) perm6)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 29) perm6))

theorem edge33_3 : Core (mutate (node 33) 3) ∨
    WeakForks.IsWeakFork (mutate (node 33) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 33) 3) 3 := by
  have he : mutate (node 33) 3 = relabel (node 44) perm3 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 33) 3) u v = (relabel (node 44) perm3) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 44) perm3)

theorem cyclic34 : ¬ Acyclic (node 34) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge34_0 : Core (mutate (node 34) 0) ∨
    WeakForks.IsWeakFork (mutate (node 34) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 34) 0) 0 := by
  right; left
  have he : relabel (mutate (node 34) 0) perm5 = WeakForks.template (5) (4) (11) (19) (53) (2) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 34) 0) perm5) u v = (WeakForks.template (5) (4) (11) (19) (53) (2)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (mutate (node 34) 0) perm5) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (5) (4) (11) (19) (53) (2) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm5 hb

theorem edge34_1 : Core (mutate (node 34) 1) ∨
    WeakForks.IsWeakFork (mutate (node 34) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 34) 1) 1 := by
  right; right
  have he : relabel (reverse (mutate (node 34) 1)) perm6 = WeakRegions.root (11) (26) (17) (2) (2) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 34) 1)) perm6) u v = (WeakRegions.root (11) (26) (17) (2) (2) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 34) 1)) perm6) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (11) (26) (17) (2) (2) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm6 hb)

theorem edge34_2 : Core (mutate (node 34) 2) ∨
    WeakForks.IsWeakFork (mutate (node 34) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 34) 2) 2 := by
  have he : mutate (node 34) 2 = reverse (relabel (node 35) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 34) 2) u v = (reverse (relabel (node 35) perm6)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 35) perm6))

theorem edge34_3 : Core (mutate (node 34) 3) ∨
    WeakForks.IsWeakFork (mutate (node 34) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 34) 3) 3 := by
  have he : mutate (node 34) 3 = relabel (node 49) perm3 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 34) 3) u v = (relabel (node 49) perm3) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 49) perm3)

theorem cyclic35 : ¬ Acyclic (node 35) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge35_0 : Core (mutate (node 35) 0) ∨
    WeakForks.IsWeakFork (mutate (node 35) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 35) 0) 0 := by
  right; left
  have he : relabel (mutate (node 35) 0) perm5 = WeakForks.template (4) (2) (11) (7) (43) (4) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 35) 0) perm5) u v = (WeakForks.template (4) (2) (11) (7) (43) (4)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (mutate (node 35) 0) perm5) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (4) (2) (11) (7) (43) (4) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm5 hb

theorem edge35_1 : Core (mutate (node 35) 1) ∨
    WeakForks.IsWeakFork (mutate (node 35) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 35) 1) 1 := by
  have he : mutate (node 35) 1 = relabel (strip2 0 0) perm22 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 35) 1) u v = (relabel (strip2 0 0) perm22) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.strip2 0 0) perm22)

theorem edge35_2 : Core (mutate (node 35) 2) ∨
    WeakForks.IsWeakFork (mutate (node 35) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 35) 2) 2 := by
  have he : mutate (node 35) 2 = reverse (relabel (node 34) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 35) 2) u v = (reverse (relabel (node 34) perm6)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 34) perm6))

theorem edge35_3 : Core (mutate (node 35) 3) ∨
    WeakForks.IsWeakFork (mutate (node 35) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 35) 3) 3 := by
  have he : mutate (node 35) 3 = relabel (node 39) perm1 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 35) 3) u v = (relabel (node 39) perm1) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 39) perm1)

theorem cyclic36 : ¬ Acyclic (node 36) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge36_0 : Core (mutate (node 36) 0) ∨
    WeakForks.IsWeakFork (mutate (node 36) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 36) 0) 0 := by
  right; left
  have he : relabel (mutate (node 36) 0) perm4 = WeakForks.template (5) (9) (6) (43) (29) (2) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 36) 0) perm4) u v = (WeakForks.template (5) (9) (6) (43) (29) (2)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (mutate (node 36) 0) perm4) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (5) (9) (6) (43) (29) (2) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm4 hb

theorem edge36_1 : Core (mutate (node 36) 1) ∨
    WeakForks.IsWeakFork (mutate (node 36) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 36) 1) 1 := by
  right; left
  have he : relabel (reverse (mutate (node 36) 1)) perm10 = WeakForks.template (2) (9) (2) (13) (5) (6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 36) 1)) perm10) u v = (WeakForks.template (2) (9) (2) (13) (5) (6)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (reverse (mutate (node 36) 1)) perm10) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (2) (9) (2) (13) (5) (6) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_reverse (WeakForks.fork_of_relabel perm10 hb)

theorem edge36_2 : Core (mutate (node 36) 2) ∨
    WeakForks.IsWeakFork (mutate (node 36) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 36) 2) 2 := by
  have he : mutate (node 36) 2 = relabel (node 27) perm1 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 36) 2) u v = (relabel (node 27) perm1) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 27) perm1)

theorem edge36_3 : Core (mutate (node 36) 3) ∨
    WeakForks.IsWeakFork (mutate (node 36) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 36) 3) 3 := by
  have he : mutate (node 36) 3 = relabel (node 50) perm5 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 36) 3) u v = (relabel (node 50) perm5) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 50) perm5)

theorem cyclic37 : ¬ Acyclic (node 37) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge37_0 : Core (mutate (node 37) 0) ∨
    WeakForks.IsWeakFork (mutate (node 37) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 37) 0) 0 := by
  right; left
  have he : relabel (mutate (node 37) 0) perm4 = WeakForks.template (4) (7) (6) (26) (23) (3) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 37) 0) perm4) u v = (WeakForks.template (4) (7) (6) (26) (23) (3)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (mutate (node 37) 0) perm4) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (4) (7) (6) (26) (23) (3) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm4 hb

theorem edge37_1 : Core (mutate (node 37) 1) ∨
    WeakForks.IsWeakFork (mutate (node 37) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 37) 1) 1 := by
  right; left
  have he : relabel (reverse (mutate (node 37) 1)) perm10 = WeakForks.template (2) (7) (3) (10) (7) (6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 37) 1)) perm10) u v = (WeakForks.template (2) (7) (3) (10) (7) (6)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (reverse (mutate (node 37) 1)) perm10) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (2) (7) (3) (10) (7) (6) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_reverse (WeakForks.fork_of_relabel perm10 hb)

theorem edge37_2 : Core (mutate (node 37) 2) ∨
    WeakForks.IsWeakFork (mutate (node 37) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 37) 2) 2 := by
  have he : mutate (node 37) 2 = relabel (node 23) perm1 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 37) 2) u v = (relabel (node 23) perm1) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 23) perm1)

theorem edge37_3 : Core (mutate (node 37) 3) ∨
    WeakForks.IsWeakFork (mutate (node 37) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 37) 3) 3 := by
  have he : mutate (node 37) 3 = relabel (node 52) perm5 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 37) 3) u v = (relabel (node 52) perm5) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 52) perm5)

theorem cyclic38 : ¬ Acyclic (node 38) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge38_0 : Core (mutate (node 38) 0) ∨
    WeakForks.IsWeakFork (mutate (node 38) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 38) 0) 0 := by
  right; right
  have he : relabel (reverse (mutate (node 38) 0)) perm4 = WeakRegions.root (4) (26) (19) (7) (5) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 38) 0)) perm4) u v = (WeakRegions.root (4) (26) (19) (7) (5) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 38) 0)) perm4) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (4) (26) (19) (7) (5) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm4 hb)

theorem edge38_1 : Core (mutate (node 38) 1) ∨
    WeakForks.IsWeakFork (mutate (node 38) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 38) 1) 1 := by
  have he : mutate (node 38) 1 = relabel (node 32) perm4 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 38) 1) u v = (relabel (node 32) perm4) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 32) perm4)

theorem edge38_2 : Core (mutate (node 38) 2) ∨
    WeakForks.IsWeakFork (mutate (node 38) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 38) 2) 2 := by
  have he : mutate (node 38) 2 = reverse (relabel (node 42) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 38) 2) u v = (reverse (relabel (node 42) perm6)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 42) perm6))

theorem edge38_3 : Core (mutate (node 38) 3) ∨
    WeakForks.IsWeakFork (mutate (node 38) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 38) 3) 3 := by
  have he : mutate (node 38) 3 = relabel (node 54) perm5 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 38) 3) u v = (relabel (node 54) perm5) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 54) perm5)

theorem cyclic39 : ¬ Acyclic (node 39) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge39_0 : Core (mutate (node 39) 0) ∨
    WeakForks.IsWeakFork (mutate (node 39) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 39) 0) 0 := by
  right; right
  have he : relabel (reverse (mutate (node 39) 0)) perm5 = WeakRegions.root (2) (7) (10) (4) (7) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 39) 0)) perm5) u v = (WeakRegions.root (2) (7) (10) (4) (7) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 39) 0)) perm5) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (2) (7) (10) (4) (7) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm5 hb)

theorem edge39_1 : Core (mutate (node 39) 1) ∨
    WeakForks.IsWeakFork (mutate (node 39) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 39) 1) 1 := by
  have he : mutate (node 39) 1 = reverse (relabel (node 21) perm11) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 39) 1) u v = (reverse (relabel (node 21) perm11)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 21) perm11))

theorem edge39_2 : Core (mutate (node 39) 2) ∨
    WeakForks.IsWeakFork (mutate (node 39) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 39) 2) 2 := by
  have he : mutate (node 39) 2 = relabel (node 35) perm1 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 39) 2) u v = (relabel (node 35) perm1) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 35) perm1)

theorem edge39_3 : Core (mutate (node 39) 3) ∨
    WeakForks.IsWeakFork (mutate (node 39) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 39) 3) 3 := by
  have he : mutate (node 39) 3 = reverse (relabel (node 55) perm19) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 39) 3) u v = (reverse (relabel (node 55) perm19)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 55) perm19))

theorem cyclic40 : ¬ Acyclic (node 40) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge40_0 : Core (mutate (node 40) 0) ∨
    WeakForks.IsWeakFork (mutate (node 40) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 40) 0) 0 := by
  right; right
  have he : relabel (reverse (mutate (node 40) 0)) perm4 = WeakRegions.root (2) (10) (5) (7) (3) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 40) 0)) perm4) u v = (WeakRegions.root (2) (10) (5) (7) (3) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 40) 0)) perm4) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (2) (10) (5) (7) (3) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm4 hb)

theorem edge40_1 : Core (mutate (node 40) 1) ∨
    WeakForks.IsWeakFork (mutate (node 40) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 40) 1) 1 := by
  have he : mutate (node 40) 1 = relabel (node 20) perm5 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 40) 1) u v = (relabel (node 20) perm5) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 20) perm5)

theorem edge40_2 : Core (mutate (node 40) 2) ∨
    WeakForks.IsWeakFork (mutate (node 40) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 40) 2) 2 := by
  have he : mutate (node 40) 2 = relabel (node 42) perm1 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 40) 2) u v = (relabel (node 42) perm1) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 42) perm1)

theorem edge40_3 : Core (mutate (node 40) 3) ∨
    WeakForks.IsWeakFork (mutate (node 40) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 40) 3) 3 := by
  have he : mutate (node 40) 3 = relabel (node 56) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 40) 3) u v = (relabel (node 56) perm21) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 56) perm21)

theorem cyclic41 : ¬ Acyclic (node 41) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge41_0 : Core (mutate (node 41) 0) ∨
    WeakForks.IsWeakFork (mutate (node 41) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 41) 0) 0 := by
  have he : mutate (node 41) 0 = relabel (AffineFiveLocal.Nine.tail 0 3) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 41) 0) u v = (relabel (AffineFiveLocal.Nine.tail 0 3) perm21) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.affineNine 0 (by omega) 3) perm21)

theorem edge41_1 : Core (mutate (node 41) 1) ∨
    WeakForks.IsWeakFork (mutate (node 41) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 41) 1) 1 := by
  right; right
  have he : relabel (reverse (mutate (node 41) 1)) perm6 = WeakRegions.root (7) (36) (26) (5) (4) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 41) 1)) perm6) u v = (WeakRegions.root (7) (36) (26) (5) (4) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 41) 1)) perm6) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (7) (36) (26) (5) (4) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm6 hb)

theorem edge41_2 : Core (mutate (node 41) 2) ∨
    WeakForks.IsWeakFork (mutate (node 41) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 41) 2) 2 := by
  have he : mutate (node 41) 2 = reverse (relabel (AffineFiveLocal.Nine.tail 0 0) perm15) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 41) 2) u v = (reverse (relabel (AffineFiveLocal.Nine.tail 0 0) perm15)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.affineNine 0 (by omega) 0) perm15))

theorem edge41_3 : Core (mutate (node 41) 3) ∨
    WeakForks.IsWeakFork (mutate (node 41) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 41) 3) 3 := by
  have he : mutate (node 41) 3 = reverse (relabel (node 48) perm20) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 41) 3) u v = (reverse (relabel (node 48) perm20)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 48) perm20))

theorem cyclic42 : ¬ Acyclic (node 42) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 2 (by decide)
  have h2 := hr 2 0 (by decide)
  omega

theorem edge42_0 : Core (mutate (node 42) 0) ∨
    WeakForks.IsWeakFork (mutate (node 42) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 42) 0) 0 := by
  have he : mutate (node 42) 0 = relabel (node 25) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 42) 0) u v = (relabel (node 25) perm21) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 25) perm21)

theorem edge42_1 : Core (mutate (node 42) 1) ∨
    WeakForks.IsWeakFork (mutate (node 42) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 42) 1) 1 := by
  have he : mutate (node 42) 1 = reverse (relabel (node 17) perm10) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 42) 1) u v = (reverse (relabel (node 17) perm10)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 17) perm10))

theorem edge42_2 : Core (mutate (node 42) 2) ∨
    WeakForks.IsWeakFork (mutate (node 42) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 42) 2) 2 := by
  have he : mutate (node 42) 2 = reverse (relabel (node 38) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 42) 2) u v = (reverse (relabel (node 38) perm6)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 38) perm6))

theorem edge42_3 : Core (mutate (node 42) 3) ∨
    WeakForks.IsWeakFork (mutate (node 42) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 42) 3) 3 := by
  have he : mutate (node 42) 3 = relabel (node 40) perm1 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 42) 3) u v = (relabel (node 40) perm1) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 40) perm1)

theorem cyclic43 : ¬ Acyclic (node 43) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (by decide)
  have h1 := hr 2 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge43_0 : Core (mutate (node 43) 0) ∨
    WeakForks.IsWeakFork (mutate (node 43) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 43) 0) 0 := by
  have he : mutate (node 43) 0 = reverse (relabel (node 44) perm1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 43) 0) u v = (reverse (relabel (node 44) perm1)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 44) perm1))

theorem edge43_1 : Core (mutate (node 43) 1) ∨
    WeakForks.IsWeakFork (mutate (node 43) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 43) 1) 1 := by
  right; right
  have he : relabel (reverse (mutate (node 43) 1)) perm7 = WeakRegions.root (6) (23) (29) (4) (5) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 43) 1)) perm7) u v = (WeakRegions.root (6) (23) (29) (4) (5) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 43) 1)) perm7) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (6) (23) (29) (4) (5) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm7 hb)

theorem edge43_2 : Core (mutate (node 43) 2) ∨
    WeakForks.IsWeakFork (mutate (node 43) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 43) 2) 2 := by
  have he : mutate (node 43) 2 = relabel (node 48) perm20 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 43) 2) u v = (relabel (node 48) perm20) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 48) perm20)

theorem edge43_3 : Core (mutate (node 43) 3) ∨
    WeakForks.IsWeakFork (mutate (node 43) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 43) 3) 3 := by
  have he : mutate (node 43) 3 = reverse (relabel (AffineFiveLocal.Nine.tail 0 1) perm20) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 43) 3) u v = (reverse (relabel (AffineFiveLocal.Nine.tail 0 1) perm20)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.affineNine 0 (by omega) 1) perm20))

theorem cyclic44 : ¬ Acyclic (node 44) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (by decide)
  have h1 := hr 2 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge44_0 : Core (mutate (node 44) 0) ∨
    WeakForks.IsWeakFork (mutate (node 44) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 44) 0) 0 := by
  have he : mutate (node 44) 0 = reverse (relabel (node 43) perm1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 44) 0) u v = (reverse (relabel (node 43) perm1)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 43) perm1))

theorem edge44_1 : Core (mutate (node 44) 1) ∨
    WeakForks.IsWeakFork (mutate (node 44) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 44) 1) 1 := by
  have he : mutate (node 44) 1 = relabel (node 33) perm4 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 44) 1) u v = (relabel (node 33) perm4) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 33) perm4)

theorem edge44_2 : Core (mutate (node 44) 2) ∨
    WeakForks.IsWeakFork (mutate (node 44) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 44) 2) 2 := by
  have he : mutate (node 44) 2 = reverse (relabel (node 53) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 44) 2) u v = (reverse (relabel (node 53) perm6)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 53) perm6))

theorem edge44_3 : Core (mutate (node 44) 3) ∨
    WeakForks.IsWeakFork (mutate (node 44) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 44) 3) 3 := by
  have he : mutate (node 44) 3 = relabel (node 51) perm1 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 44) 3) u v = (relabel (node 51) perm1) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 51) perm1)

theorem cyclic45 : ¬ Acyclic (node 45) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge45_0 : Core (mutate (node 45) 0) ∨
    WeakForks.IsWeakFork (mutate (node 45) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 45) 0) 0 := by
  right; left
  have he : relabel (mutate (node 45) 0) perm5 = WeakForks.template (3) (5) (5) (13) (14) (4) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 45) 0) perm5) u v = (WeakForks.template (3) (5) (5) (13) (14) (4)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (mutate (node 45) 0) perm5) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (3) (5) (5) (13) (14) (4) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_relabel perm5 hb

theorem edge45_1 : Core (mutate (node 45) 1) ∨
    WeakForks.IsWeakFork (mutate (node 45) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 45) 1) 1 := by
  have he : mutate (node 45) 1 = relabel (node 22) perm4 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 45) 1) u v = (relabel (node 22) perm4) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 22) perm4)

theorem edge45_2 : Core (mutate (node 45) 2) ∨
    WeakForks.IsWeakFork (mutate (node 45) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 45) 2) 2 := by
  right; left
  have he : relabel (reverse (mutate (node 45) 2)) perm16 = WeakForks.template (2) (5) (4) (7) (9) (5) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 45) 2)) perm16) u v = (WeakForks.template (2) (5) (4) (7) (9) (5)) u v from by decide) u v
  have hb : WeakForks.IsWeakFork (relabel (reverse (mutate (node 45) 2)) perm16) 0 := by
    rw [he]
    exact WeakForks.IsWeakFork.basic (2) (5) (4) (7) (9) (5) (by unfold WeakForks.Domain; decide)
  exact WeakForks.fork_of_reverse (WeakForks.fork_of_relabel perm16 hb)

theorem edge45_3 : Core (mutate (node 45) 3) ∨
    WeakForks.IsWeakFork (mutate (node 45) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 45) 3) 3 := by
  have he : mutate (node 45) 3 = reverse (relabel (node 52) perm20) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 45) 3) u v = (reverse (relabel (node 52) perm20)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 52) perm20))

theorem cyclic46 : ¬ Acyclic (node 46) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge46_0 : Core (mutate (node 46) 0) ∨
    WeakForks.IsWeakFork (mutate (node 46) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 46) 0) 0 := by
  right; right
  have he : relabel (reverse (mutate (node 46) 0)) perm5 = WeakRegions.root (4) (7) (19) (2) (5) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 46) 0)) perm5) u v = (WeakRegions.root (4) (7) (19) (2) (5) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 46) 0)) perm5) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (4) (7) (19) (2) (5) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm5 hb)

theorem edge46_1 : Core (mutate (node 46) 1) ∨
    WeakForks.IsWeakFork (mutate (node 46) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 46) 1) 1 := by
  have he : mutate (node 46) 1 = relabel (node 49) perm6 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 46) 1) u v = (relabel (node 49) perm6) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 49) perm6)

theorem edge46_2 : Core (mutate (node 46) 2) ∨
    WeakForks.IsWeakFork (mutate (node 46) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 46) 2) 2 := by
  have he : mutate (node 46) 2 = reverse (relabel (AffineFiveLocal.Seven.tail 0 1) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 46) 2) u v = (reverse (relabel (AffineFiveLocal.Seven.tail 0 1) perm6)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.affineSeven 0 (by omega) 1) perm6))

theorem edge46_3 : Core (mutate (node 46) 3) ∨
    WeakForks.IsWeakFork (mutate (node 46) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 46) 3) 3 := by
  have he : mutate (node 46) 3 = relabel (node 56) perm3 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 46) 3) u v = (relabel (node 56) perm3) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 56) perm3)

theorem cyclic47 : ¬ Acyclic (node 47) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 2 (by decide)
  have h2 := hr 2 0 (by decide)
  omega

theorem edge47_0 : Core (mutate (node 47) 0) ∨
    WeakForks.IsWeakFork (mutate (node 47) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 47) 0) 0 := by
  right; right
  have he : relabel (reverse (mutate (node 47) 0)) perm4 = WeakRegions.root (5) (26) (8) (5) (2) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 47) 0)) perm4) u v = (WeakRegions.root (5) (26) (8) (5) (2) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 47) 0)) perm4) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (5) (26) (8) (5) (2) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm4 hb)

theorem edge47_1 : Core (mutate (node 47) 1) ∨
    WeakForks.IsWeakFork (mutate (node 47) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 47) 1) 1 := by
  have he : mutate (node 47) 1 = reverse (relabel (AffineFiveLocal.Seven.tail 0 0) perm10) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 47) 1) u v = (reverse (relabel (AffineFiveLocal.Seven.tail 0 0) perm10)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.affineSeven 0 (by omega) 0) perm10))

theorem edge47_2 : Core (mutate (node 47) 2) ∨
    WeakForks.IsWeakFork (mutate (node 47) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 47) 2) 2 := by
  have he : mutate (node 47) 2 = reverse (relabel (node 49) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 47) 2) u v = (reverse (relabel (node 49) perm6)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 49) perm6))

theorem edge47_3 : Core (mutate (node 47) 3) ∨
    WeakForks.IsWeakFork (mutate (node 47) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 47) 3) 3 := by
  have he : mutate (node 47) 3 = relabel (AffineFiveLocal.Seven.tail 0 3) perm8 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 47) 3) u v = (relabel (AffineFiveLocal.Seven.tail 0 3) perm8) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.affineSeven 0 (by omega) 3) perm8)

theorem cyclic48 : ¬ Acyclic (node 48) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 2 (by decide)
  have h2 := hr 2 0 (by decide)
  omega

theorem edge48_0 : Core (mutate (node 48) 0) ∨
    WeakForks.IsWeakFork (mutate (node 48) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 48) 0) 0 := by
  have he : mutate (node 48) 0 = relabel (node 43) perm15 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 48) 0) u v = (relabel (node 43) perm15) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 43) perm15)

theorem edge48_1 : Core (mutate (node 48) 1) ∨
    WeakForks.IsWeakFork (mutate (node 48) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 48) 1) 1 := by
  have he : mutate (node 48) 1 = reverse (relabel (node 26) perm10) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 48) 1) u v = (reverse (relabel (node 26) perm10)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 26) perm10))

theorem edge48_2 : Core (mutate (node 48) 2) ∨
    WeakForks.IsWeakFork (mutate (node 48) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 48) 2) 2 := by
  have he : mutate (node 48) 2 = reverse (relabel (node 41) perm15) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 48) 2) u v = (reverse (relabel (node 41) perm15)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 41) perm15))

theorem edge48_3 : Core (mutate (node 48) 3) ∨
    WeakForks.IsWeakFork (mutate (node 48) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 48) 3) 3 := by
  have he : mutate (node 48) 3 = relabel (node 50) perm1 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 48) 3) u v = (relabel (node 50) perm1) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 50) perm1)

theorem cyclic49 : ¬ Acyclic (node 49) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge49_0 : Core (mutate (node 49) 0) ∨
    WeakForks.IsWeakFork (mutate (node 49) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 49) 0) 0 := by
  have he : mutate (node 49) 0 = relabel (node 46) perm6 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 49) 0) u v = (relabel (node 46) perm6) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 46) perm6)

theorem edge49_1 : Core (mutate (node 49) 1) ∨
    WeakForks.IsWeakFork (mutate (node 49) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 49) 1) 1 := by
  have he : mutate (node 49) 1 = relabel (node 34) perm4 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 49) 1) u v = (relabel (node 34) perm4) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 34) perm4)

theorem edge49_2 : Core (mutate (node 49) 2) ∨
    WeakForks.IsWeakFork (mutate (node 49) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 49) 2) 2 := by
  have he : mutate (node 49) 2 = reverse (relabel (node 47) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 49) 2) u v = (reverse (relabel (node 47) perm6)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 47) perm6))

theorem edge49_3 : Core (mutate (node 49) 3) ∨
    WeakForks.IsWeakFork (mutate (node 49) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 49) 3) 3 := by
  have he : mutate (node 49) 3 = relabel (node 55) perm1 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 49) 3) u v = (relabel (node 55) perm1) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 55) perm1)

theorem cyclic50 : ¬ Acyclic (node 50) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge50_0 : Core (mutate (node 50) 0) ∨
    WeakForks.IsWeakFork (mutate (node 50) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 50) 0) 0 := by
  have he : mutate (node 50) 0 = reverse (relabel (node 51) perm0) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 50) 0) u v = (reverse (relabel (node 51) perm0)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 51) perm0))

theorem edge50_1 : Core (mutate (node 50) 1) ∨
    WeakForks.IsWeakFork (mutate (node 50) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 50) 1) 1 := by
  have he : mutate (node 50) 1 = relabel (node 36) perm5 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 50) 1) u v = (relabel (node 36) perm5) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 36) perm5)

theorem edge50_2 : Core (mutate (node 50) 2) ∨
    WeakForks.IsWeakFork (mutate (node 50) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 50) 2) 2 := by
  have he : mutate (node 50) 2 = relabel (node 48) perm1 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 50) 2) u v = (relabel (node 48) perm1) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 48) perm1)

theorem edge50_3 : Core (mutate (node 50) 3) ∨
    WeakForks.IsWeakFork (mutate (node 50) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 50) 3) 3 := by
  have he : mutate (node 50) 3 = reverse (relabel (node 57) perm7) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 50) 3) u v = (reverse (relabel (node 57) perm7)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 57) perm7))

theorem cyclic51 : ¬ Acyclic (node 51) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge51_0 : Core (mutate (node 51) 0) ∨
    WeakForks.IsWeakFork (mutate (node 51) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 51) 0) 0 := by
  have he : mutate (node 51) 0 = reverse (relabel (node 50) perm0) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 51) 0) u v = (reverse (relabel (node 50) perm0)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 50) perm0))

theorem edge51_1 : Core (mutate (node 51) 1) ∨
    WeakForks.IsWeakFork (mutate (node 51) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 51) 1) 1 := by
  have he : mutate (node 51) 1 = reverse (relabel (node 30) perm11) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 51) 1) u v = (reverse (relabel (node 30) perm11)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 30) perm11))

theorem edge51_2 : Core (mutate (node 51) 2) ∨
    WeakForks.IsWeakFork (mutate (node 51) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 51) 2) 2 := by
  have he : mutate (node 51) 2 = relabel (node 44) perm1 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 51) 2) u v = (relabel (node 44) perm1) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 44) perm1)

theorem edge51_3 : Core (mutate (node 51) 3) ∨
    WeakForks.IsWeakFork (mutate (node 51) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 51) 3) 3 := by
  have he : mutate (node 51) 3 = reverse (relabel (node 58) perm13) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 51) 3) u v = (reverse (relabel (node 58) perm13)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 58) perm13))

theorem cyclic52 : ¬ Acyclic (node 52) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge52_0 : Core (mutate (node 52) 0) ∨
    WeakForks.IsWeakFork (mutate (node 52) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 52) 0) 0 := by
  have he : mutate (node 52) 0 = reverse (relabel (node 53) perm0) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 52) 0) u v = (reverse (relabel (node 53) perm0)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 53) perm0))

theorem edge52_1 : Core (mutate (node 52) 1) ∨
    WeakForks.IsWeakFork (mutate (node 52) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 52) 1) 1 := by
  have he : mutate (node 52) 1 = relabel (node 37) perm5 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 52) 1) u v = (relabel (node 37) perm5) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 37) perm5)

theorem edge52_2 : Core (mutate (node 52) 2) ∨
    WeakForks.IsWeakFork (mutate (node 52) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 52) 2) 2 := by
  have he : mutate (node 52) 2 = reverse (relabel (node 45) perm15) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 52) 2) u v = (reverse (relabel (node 45) perm15)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 45) perm15))

theorem edge52_3 : Core (mutate (node 52) 3) ∨
    WeakForks.IsWeakFork (mutate (node 52) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 52) 3) 3 := by
  have he : mutate (node 52) 3 = relabel (node 57) perm23 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 52) 3) u v = (relabel (node 57) perm23) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 57) perm23)

theorem cyclic53 : ¬ Acyclic (node 53) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge53_0 : Core (mutate (node 53) 0) ∨
    WeakForks.IsWeakFork (mutate (node 53) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 53) 0) 0 := by
  have he : mutate (node 53) 0 = reverse (relabel (node 52) perm0) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 53) 0) u v = (reverse (relabel (node 52) perm0)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 52) perm0))

theorem edge53_1 : Core (mutate (node 53) 1) ∨
    WeakForks.IsWeakFork (mutate (node 53) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 53) 1) 1 := by
  have he : mutate (node 53) 1 = relabel (AffineFiveLocal.Nine.tail 0 2) perm5 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 53) 1) u v = (relabel (AffineFiveLocal.Nine.tail 0 2) perm5) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.affineNine 0 (by omega) 2) perm5)

theorem edge53_2 : Core (mutate (node 53) 2) ∨
    WeakForks.IsWeakFork (mutate (node 53) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 53) 2) 2 := by
  have he : mutate (node 53) 2 = reverse (relabel (node 44) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 53) 2) u v = (reverse (relabel (node 44) perm6)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 44) perm6))

theorem edge53_3 : Core (mutate (node 53) 3) ∨
    WeakForks.IsWeakFork (mutate (node 53) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 53) 3) 3 := by
  have he : mutate (node 53) 3 = relabel (node 61) perm0 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 53) 3) u v = (relabel (node 61) perm0) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 61) perm0)

theorem cyclic54 : ¬ Acyclic (node 54) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge54_0 : Core (mutate (node 54) 0) ∨
    WeakForks.IsWeakFork (mutate (node 54) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 54) 0) 0 := by
  have he : mutate (node 54) 0 = reverse (relabel (node 55) perm0) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 54) 0) u v = (reverse (relabel (node 55) perm0)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 55) perm0))

theorem edge54_1 : Core (mutate (node 54) 1) ∨
    WeakForks.IsWeakFork (mutate (node 54) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 54) 1) 1 := by
  have he : mutate (node 54) 1 = relabel (node 38) perm5 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 54) 1) u v = (relabel (node 38) perm5) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 38) perm5)

theorem edge54_2 : Core (mutate (node 54) 2) ∨
    WeakForks.IsWeakFork (mutate (node 54) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 54) 2) 2 := by
  have he : mutate (node 54) 2 = reverse (relabel (node 56) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 54) 2) u v = (reverse (relabel (node 56) perm6)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 56) perm6))

theorem edge54_3 : Core (mutate (node 54) 3) ∨
    WeakForks.IsWeakFork (mutate (node 54) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 54) 3) 3 := by
  have he : mutate (node 54) 3 = reverse (relabel (node 59) perm14) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 54) 3) u v = (reverse (relabel (node 59) perm14)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 59) perm14))

theorem cyclic55 : ¬ Acyclic (node 55) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge55_0 : Core (mutate (node 55) 0) ∨
    WeakForks.IsWeakFork (mutate (node 55) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 55) 0) 0 := by
  have he : mutate (node 55) 0 = reverse (relabel (node 54) perm0) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 55) 0) u v = (reverse (relabel (node 54) perm0)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 54) perm0))

theorem edge55_1 : Core (mutate (node 55) 1) ∨
    WeakForks.IsWeakFork (mutate (node 55) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 55) 1) 1 := by
  have he : mutate (node 55) 1 = reverse (relabel (node 39) perm11) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 55) 1) u v = (reverse (relabel (node 39) perm11)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 39) perm11))

theorem edge55_2 : Core (mutate (node 55) 2) ∨
    WeakForks.IsWeakFork (mutate (node 55) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 55) 2) 2 := by
  have he : mutate (node 55) 2 = relabel (node 49) perm1 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 55) 2) u v = (relabel (node 49) perm1) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 49) perm1)

theorem edge55_3 : Core (mutate (node 55) 3) ∨
    WeakForks.IsWeakFork (mutate (node 55) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 55) 3) 3 := by
  have he : mutate (node 55) 3 = reverse (relabel (node 61) perm13) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 55) 3) u v = (reverse (relabel (node 61) perm13)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 61) perm13))

theorem cyclic56 : ¬ Acyclic (node 56) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge56_0 : Core (mutate (node 56) 0) ∨
    WeakForks.IsWeakFork (mutate (node 56) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 56) 0) 0 := by
  have he : mutate (node 56) 0 = relabel (node 40) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 56) 0) u v = (relabel (node 40) perm21) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 40) perm21)

theorem edge56_1 : Core (mutate (node 56) 1) ∨
    WeakForks.IsWeakFork (mutate (node 56) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 56) 1) 1 := by
  have he : mutate (node 56) 1 = relabel (node 46) perm4 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 56) 1) u v = (relabel (node 46) perm4) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 46) perm4)

theorem edge56_2 : Core (mutate (node 56) 2) ∨
    WeakForks.IsWeakFork (mutate (node 56) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 56) 2) 2 := by
  have he : mutate (node 56) 2 = reverse (relabel (node 54) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 56) 2) u v = (reverse (relabel (node 54) perm6)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 54) perm6))

theorem edge56_3 : Core (mutate (node 56) 3) ∨
    WeakForks.IsWeakFork (mutate (node 56) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 56) 3) 3 := by
  have he : mutate (node 56) 3 = relabel (node 60) perm3 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 56) 3) u v = (relabel (node 60) perm3) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 60) perm3)

theorem cyclic57 : ¬ Acyclic (node 57) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge57_0 : Core (mutate (node 57) 0) ∨
    WeakForks.IsWeakFork (mutate (node 57) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 57) 0) 0 := by
  have he : mutate (node 57) 0 = relabel (node 52) perm23 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 57) 0) u v = (relabel (node 52) perm23) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 52) perm23)

theorem edge57_1 : Core (mutate (node 57) 1) ∨
    WeakForks.IsWeakFork (mutate (node 57) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 57) 1) 1 := by
  have he : mutate (node 57) 1 = relabel (node 59) perm6 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 57) 1) u v = (relabel (node 59) perm6) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 59) perm6)

theorem edge57_2 : Core (mutate (node 57) 2) ∨
    WeakForks.IsWeakFork (mutate (node 57) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 57) 2) 2 := by
  have he : mutate (node 57) 2 = reverse (relabel (node 50) perm7) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 57) 2) u v = (reverse (relabel (node 50) perm7)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 50) perm7))

theorem edge57_3 : Core (mutate (node 57) 3) ∨
    WeakForks.IsWeakFork (mutate (node 57) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 57) 3) 3 := by
  have he : mutate (node 57) 3 = relabel (node 60) perm0 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 57) 3) u v = (relabel (node 60) perm0) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 60) perm0)

theorem cyclic58 : ¬ Acyclic (node 58) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge58_0 : Core (mutate (node 58) 0) ∨
    WeakForks.IsWeakFork (mutate (node 58) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 58) 0) 0 := by
  right; right
  have he : relabel (reverse (mutate (node 58) 0)) perm4 = WeakRegions.root (2) (5) (5) (3) (2) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 58) 0)) perm4) u v = (WeakRegions.root (2) (5) (5) (3) (2) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 58) 0)) perm4) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (2) (5) (5) (3) (2) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm4 hb)

theorem edge58_1 : Core (mutate (node 58) 1) ∨
    WeakForks.IsWeakFork (mutate (node 58) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 58) 1) 1 := by
  have he : mutate (node 58) 1 = reverse (relabel (node 51) perm10) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 58) 1) u v = (reverse (relabel (node 51) perm10)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 51) perm10))

theorem edge58_2 : Core (mutate (node 58) 2) ∨
    WeakForks.IsWeakFork (mutate (node 58) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 58) 2) 2 := by
  have he : mutate (node 58) 2 = reverse (relabel (node 59) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 58) 2) u v = (reverse (relabel (node 59) perm6)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 59) perm6))

theorem edge58_3 : Core (mutate (node 58) 3) ∨
    WeakForks.IsWeakFork (mutate (node 58) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 58) 3) 3 := by
  have he : mutate (node 58) 3 = relabel (node 61) perm4 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 58) 3) u v = (relabel (node 61) perm4) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 61) perm4)

theorem cyclic59 : ¬ Acyclic (node 59) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge59_0 : Core (mutate (node 59) 0) ∨
    WeakForks.IsWeakFork (mutate (node 59) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 59) 0) 0 := by
  have he : mutate (node 59) 0 = relabel (node 57) perm6 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 59) 0) u v = (relabel (node 57) perm6) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 57) perm6)

theorem edge59_1 : Core (mutate (node 59) 1) ∨
    WeakForks.IsWeakFork (mutate (node 59) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 59) 1) 1 := by
  right; right
  have he : relabel (reverse (mutate (node 59) 1)) perm7 = WeakRegions.root (3) (5) (7) (2) (2) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 59) 1)) perm7) u v = (WeakRegions.root (3) (5) (7) (2) (2) (1)) u v from by decide) u v
  have hb : WeakRegions.IsRoot (relabel (reverse (mutate (node 59) 1)) perm7) 0 := by
    rw [he]
    exact WeakRegions.IsRoot.basic (3) (5) (7) (2) (2) (1) (by unfold WeakRegions.Domain; decide) (by decide)
  exact WeakRegions.root_of_reverse (WeakRegions.root_of_relabel perm7 hb)

theorem edge59_2 : Core (mutate (node 59) 2) ∨
    WeakForks.IsWeakFork (mutate (node 59) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 59) 2) 2 := by
  have he : mutate (node 59) 2 = reverse (relabel (node 58) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 59) 2) u v = (reverse (relabel (node 58) perm6)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 58) perm6))

theorem edge59_3 : Core (mutate (node 59) 3) ∨
    WeakForks.IsWeakFork (mutate (node 59) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 59) 3) 3 := by
  have he : mutate (node 59) 3 = reverse (relabel (node 54) perm14) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 59) 3) u v = (reverse (relabel (node 54) perm14)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 54) perm14))

theorem cyclic60 : ¬ Acyclic (node 60) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 1 3 (by decide)
  have h1 := hr 3 2 (by decide)
  have h2 := hr 2 1 (by decide)
  omega

theorem edge60_0 : Core (mutate (node 60) 0) ∨
    WeakForks.IsWeakFork (mutate (node 60) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 60) 0) 0 := by
  have he : mutate (node 60) 0 = reverse (relabel (node 61) perm2) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 60) 0) u v = (reverse (relabel (node 61) perm2)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 61) perm2))

theorem edge60_1 : Core (mutate (node 60) 1) ∨
    WeakForks.IsWeakFork (mutate (node 60) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 60) 1) 1 := by
  have he : mutate (node 60) 1 = relabel (node 56) perm4 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 60) 1) u v = (relabel (node 56) perm4) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 56) perm4)

theorem edge60_2 : Core (mutate (node 60) 2) ∨
    WeakForks.IsWeakFork (mutate (node 60) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 60) 2) 2 := by
  have he : mutate (node 60) 2 = relabel (AffineFiveLocal.Seven.tail 0 2) perm3 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 60) 2) u v = (relabel (AffineFiveLocal.Seven.tail 0 2) perm3) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.affineSeven 0 (by omega) 2) perm3)

theorem edge60_3 : Core (mutate (node 60) 3) ∨
    WeakForks.IsWeakFork (mutate (node 60) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 60) 3) 3 := by
  have he : mutate (node 60) 3 = relabel (node 57) perm0 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 60) 3) u v = (relabel (node 57) perm0) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 57) perm0)

theorem cyclic61 : ¬ Acyclic (node 61) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 1 3 (by decide)
  have h1 := hr 3 2 (by decide)
  have h2 := hr 2 1 (by decide)
  omega

theorem edge61_0 : Core (mutate (node 61) 0) ∨
    WeakForks.IsWeakFork (mutate (node 61) 0) 0 ∨ WeakRegions.IsRoot (mutate (node 61) 0) 0 := by
  have he : mutate (node 61) 0 = reverse (relabel (node 60) perm2) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 61) 0) u v = (reverse (relabel (node 60) perm2)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 60) perm2))

theorem edge61_1 : Core (mutate (node 61) 1) ∨
    WeakForks.IsWeakFork (mutate (node 61) 1) 1 ∨ WeakRegions.IsRoot (mutate (node 61) 1) 1 := by
  have he : mutate (node 61) 1 = reverse (relabel (node 55) perm10) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 61) 1) u v = (reverse (relabel (node 55) perm10)) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.reversed (Core.framed (Core.finite 55) perm10))

theorem edge61_2 : Core (mutate (node 61) 2) ∨
    WeakForks.IsWeakFork (mutate (node 61) 2) 2 ∨ WeakRegions.IsRoot (mutate (node 61) 2) 2 := by
  have he : mutate (node 61) 2 = relabel (node 58) perm3 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 61) 2) u v = (relabel (node 58) perm3) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 58) perm3)

theorem edge61_3 : Core (mutate (node 61) 3) ∨
    WeakForks.IsWeakFork (mutate (node 61) 3) 3 ∨ WeakRegions.IsRoot (mutate (node 61) 3) 3 := by
  have he : mutate (node 61) 3 = relabel (node 53) perm0 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 61) 3) u v = (relabel (node 53) perm0) u v from by decide) u v
  rw [he]
  exact Or.inl (Core.framed (Core.finite 53) perm0)

theorem finite_skew (i : Fin 62) : SkewSymmetric (node i) := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 ∨ i = 32 ∨ i = 33 ∨ i = 34 ∨ i = 35 ∨ i = 36 ∨ i = 37 ∨ i = 38 ∨ i = 39 ∨ i = 40 ∨ i = 41 ∨ i = 42 ∨ i = 43 ∨ i = 44 ∨ i = 45 ∨ i = 46 ∨ i = 47 ∨ i = 48 ∨ i = 49 ∨ i = 50 ∨ i = 51 ∨ i = 52 ∨ i = 53 ∨ i = 54 ∨ i = 55 ∨ i = 56 ∨ i = 57 ∨ i = 58 ∨ i = 59 ∨ i = 60 ∨ i = 61 := by omega
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ofSix_skew _ _ _ _ _ _

theorem finite_cyclic (i : Fin 62) : ¬ Acyclic (node i) := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 ∨ i = 32 ∨ i = 33 ∨ i = 34 ∨ i = 35 ∨ i = 36 ∨ i = 37 ∨ i = 38 ∨ i = 39 ∨ i = 40 ∨ i = 41 ∨ i = 42 ∨ i = 43 ∨ i = 44 ∨ i = 45 ∨ i = 46 ∨ i = 47 ∨ i = 48 ∨ i = 49 ∨ i = 50 ∨ i = 51 ∨ i = 52 ∨ i = 53 ∨ i = 54 ∨ i = 55 ∨ i = 56 ∨ i = 57 ∨ i = 58 ∨ i = 59 ∨ i = 60 ∨ i = 61 := by omega
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · exact cyclic49
  · exact cyclic50
  · exact cyclic51
  · exact cyclic52
  · exact cyclic53
  · exact cyclic54
  · exact cyclic55
  · exact cyclic56
  · exact cyclic57
  · exact cyclic58
  · exact cyclic59
  · exact cyclic60
  · exact cyclic61

theorem finite_edges (i : Fin 62) (k : Fin 4) : Core (mutate (node i) k) ∨
    WeakForks.IsWeakFork (mutate (node i) k) k ∨ WeakRegions.IsRoot (mutate (node i) k) k := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 ∨ i = 32 ∨ i = 33 ∨ i = 34 ∨ i = 35 ∨ i = 36 ∨ i = 37 ∨ i = 38 ∨ i = 39 ∨ i = 40 ∨ i = 41 ∨ i = 42 ∨ i = 43 ∨ i = 44 ∨ i = 45 ∨ i = 46 ∨ i = 47 ∨ i = 48 ∨ i = 49 ∨ i = 50 ∨ i = 51 ∨ i = 52 ∨ i = 53 ∨ i = 54 ∨ i = 55 ∨ i = 56 ∨ i = 57 ∨ i = 58 ∨ i = 59 ∨ i = 60 ∨ i = 61 := by omega
  have hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hk with rfl|rfl|rfl|rfl
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
  · exact edge49_0
  · exact edge49_1
  · exact edge49_2
  · exact edge49_3
  · exact edge50_0
  · exact edge50_1
  · exact edge50_2
  · exact edge50_3
  · exact edge51_0
  · exact edge51_1
  · exact edge51_2
  · exact edge51_3
  · exact edge52_0
  · exact edge52_1
  · exact edge52_2
  · exact edge52_3
  · exact edge53_0
  · exact edge53_1
  · exact edge53_2
  · exact edge53_3
  · exact edge54_0
  · exact edge54_1
  · exact edge54_2
  · exact edge54_3
  · exact edge55_0
  · exact edge55_1
  · exact edge55_2
  · exact edge55_3
  · exact edge56_0
  · exact edge56_1
  · exact edge56_2
  · exact edge56_3
  · exact edge57_0
  · exact edge57_1
  · exact edge57_2
  · exact edge57_3
  · exact edge58_0
  · exact edge58_1
  · exact edge58_2
  · exact edge58_3
  · exact edge59_0
  · exact edge59_1
  · exact edge59_2
  · exact edge59_3
  · exact edge60_0
  · exact edge60_1
  · exact edge60_2
  · exact edge60_3
  · exact edge61_0
  · exact edge61_1
  · exact edge61_2
  · exact edge61_3

theorem affineSeven_parent0 : Core (AffineFiveLocal.Seven.base 0) := by
  have he : AffineFiveLocal.Seven.base 0 = reverse (relabel (node 47) perm13) := by
    funext u v
    exact (show ∀ u v : Fin 4, (AffineFiveLocal.Seven.base 0) u v = (reverse (relabel (node 47) perm13)) u v from by decide) u v
  rw [he]
  exact Core.reversed (Core.framed (Core.finite 47) perm13)

theorem affineSeven_parent1 : Core (AffineFiveLocal.Seven.base 1) := by
  have he : AffineFiveLocal.Seven.base 1 = reverse (relabel (node 46) perm6) := by
    funext u v
    exact (show ∀ u v : Fin 4, (AffineFiveLocal.Seven.base 1) u v = (reverse (relabel (node 46) perm6)) u v from by decide) u v
  rw [he]
  exact Core.reversed (Core.framed (Core.finite 46) perm6)

theorem affineSeven_parent2 : Core (AffineFiveLocal.Seven.base 2) := by
  have he : AffineFiveLocal.Seven.base 2 = relabel (node 60) perm4 := by
    funext u v
    exact (show ∀ u v : Fin 4, (AffineFiveLocal.Seven.base 2) u v = (relabel (node 60) perm4) u v from by decide) u v
  rw [he]
  exact Core.framed (Core.finite 60) perm4

theorem affineSeven_parent3 : Core (AffineFiveLocal.Seven.base 3) := by
  have he : AffineFiveLocal.Seven.base 3 = relabel (node 47) perm12 := by
    funext u v
    exact (show ∀ u v : Fin 4, (AffineFiveLocal.Seven.base 3) u v = (relabel (node 47) perm12) u v from by decide) u v
  rw [he]
  exact Core.framed (Core.finite 47) perm12

theorem affineSeven_address {B : Matrix 4} (h : AffineFiveLocal.Seven.Core B) : Core B := by
  induction h with
  | base i =>
    have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
    rcases hi with rfl|rfl|rfl|rfl
    · exact affineSeven_parent0
    · exact affineSeven_parent1
    · exact affineSeven_parent2
    · exact affineSeven_parent3
  | tail n hn i => exact Core.affineSeven n hn i
  | framed h p ih => exact Core.framed ih p
  | reversed h ih => exact Core.reversed ih

theorem affineNine_parent0 : Core (AffineFiveLocal.Nine.base 0) := by
  have he : AffineFiveLocal.Nine.base 0 = reverse (relabel (node 41) perm20) := by
    funext u v
    exact (show ∀ u v : Fin 4, (AffineFiveLocal.Nine.base 0) u v = (reverse (relabel (node 41) perm20)) u v from by decide) u v
  rw [he]
  exact Core.reversed (Core.framed (Core.finite 41) perm20)

theorem affineNine_parent1 : Core (AffineFiveLocal.Nine.base 1) := by
  have he : AffineFiveLocal.Nine.base 1 = reverse (relabel (node 43) perm15) := by
    funext u v
    exact (show ∀ u v : Fin 4, (AffineFiveLocal.Nine.base 1) u v = (reverse (relabel (node 43) perm15)) u v from by decide) u v
  rw [he]
  exact Core.reversed (Core.framed (Core.finite 43) perm15)

theorem affineNine_parent2 : Core (AffineFiveLocal.Nine.base 2) := by
  have he : AffineFiveLocal.Nine.base 2 = relabel (node 53) perm5 := by
    funext u v
    exact (show ∀ u v : Fin 4, (AffineFiveLocal.Nine.base 2) u v = (relabel (node 53) perm5) u v from by decide) u v
  rw [he]
  exact Core.framed (Core.finite 53) perm5

theorem affineNine_parent3 : Core (AffineFiveLocal.Nine.base 3) := by
  have he : AffineFiveLocal.Nine.base 3 = relabel (node 41) perm21 := by
    funext u v
    exact (show ∀ u v : Fin 4, (AffineFiveLocal.Nine.base 3) u v = (relabel (node 41) perm21) u v from by decide) u v
  rw [he]
  exact Core.framed (Core.finite 41) perm21

theorem affineNine_address {B : Matrix 4} (h : AffineFiveLocal.Nine.Core B) : Core B := by
  induction h with
  | base i =>
    have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
    rcases hi with rfl|rfl|rfl|rfl
    · exact affineNine_parent0
    · exact affineNine_parent1
    · exact affineNine_parent2
    · exact affineNine_parent3
  | tail n hn i => exact Core.affineNine n hn i
  | framed h p ih => exact Core.framed ih p
  | reversed h ih => exact Core.reversed ih

theorem parent0_0 : Core (mutate (GenericStrip.root 2 seed0.A seed0.H seed0.Z) 1) := by
  have he : mutate (GenericStrip.root 2 seed0.A seed0.H seed0.Z) 1 = reverse (relabel (node 19) perm3) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (GenericStrip.root 2 seed0.A seed0.H seed0.Z) 1) u v = (reverse (relabel (node 19) perm3)) u v from by decide) u v
  rw [he]
  exact Core.reversed (Core.framed (Core.finite 19) perm3)

theorem parent0_1 : Core (mutate (GenericStrip.root 2 seed0.A seed0.H seed0.Z) 2) := by
  have he : mutate (GenericStrip.root 2 seed0.A seed0.H seed0.Z) 2 = reverse (relabel (node 29) perm22) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (GenericStrip.root 2 seed0.A seed0.H seed0.Z) 2) u v = (reverse (relabel (node 29) perm22)) u v from by decide) u v
  rw [he]
  exact Core.reversed (Core.framed (Core.finite 29) perm22)

theorem parent0_2 : Core (mutate (GenericStrip.phaseQ 2 seed0.A seed0.H seed0.Z) 0) := by
  have he : mutate (GenericStrip.phaseQ 2 seed0.A seed0.H seed0.Z) 0 = reverse (relabel (node 12) perm16) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (GenericStrip.phaseQ 2 seed0.A seed0.H seed0.Z) 0) u v = (reverse (relabel (node 12) perm16)) u v from by decide) u v
  rw [he]
  exact Core.reversed (Core.framed (Core.finite 12) perm16)

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
  have he : mutate (GenericStrip.root 2 seed1.A seed1.H seed1.Z) 2 = relabel (node 24) perm17 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (GenericStrip.root 2 seed1.A seed1.H seed1.Z) 2) u v = (relabel (node 24) perm17) u v from by decide) u v
  rw [he]
  exact Core.framed (Core.finite 24) perm17

theorem parent1_2 : Core (mutate (GenericStrip.phaseQ 2 seed1.A seed1.H seed1.Z) 0) := by
  have he : mutate (GenericStrip.phaseQ 2 seed1.A seed1.H seed1.Z) 0 = reverse (relabel (node 7) perm16) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (GenericStrip.phaseQ 2 seed1.A seed1.H seed1.Z) 0) u v = (reverse (relabel (node 7) perm16)) u v from by decide) u v
  rw [he]
  exact Core.reversed (Core.framed (Core.finite 7) perm16)

theorem address1 {B : Matrix 4} (h : StripSemantics.Core 2 seed1 Core B) : Core B := by
  induction h with
  | base h => exact h
  | strip n i => exact Core.strip1 n i
  | framed h p ih => exact Core.framed ih p
  | reversed h ih => exact Core.reversed ih

theorem parent2_0 : Core (mutate (GenericStrip.root 4 seed2.A seed2.H seed2.Z) 1) := by
  have he : mutate (GenericStrip.root 4 seed2.A seed2.H seed2.Z) 1 = reverse (relabel (node 16) perm3) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (GenericStrip.root 4 seed2.A seed2.H seed2.Z) 1) u v = (reverse (relabel (node 16) perm3)) u v from by decide) u v
  rw [he]
  exact Core.reversed (Core.framed (Core.finite 16) perm3)

theorem parent2_1 : Core (mutate (GenericStrip.root 4 seed2.A seed2.H seed2.Z) 2) := by
  have he : mutate (GenericStrip.root 4 seed2.A seed2.H seed2.Z) 2 = relabel (node 35) perm17 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (GenericStrip.root 4 seed2.A seed2.H seed2.Z) 2) u v = (relabel (node 35) perm17) u v from by decide) u v
  rw [he]
  exact Core.framed (Core.finite 35) perm17

theorem parent2_2 : Core (mutate (GenericStrip.phaseQ 4 seed2.A seed2.H seed2.Z) 0) := by
  have he : mutate (GenericStrip.phaseQ 4 seed2.A seed2.H seed2.Z) 0 = reverse (relabel (node 5) perm16) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (GenericStrip.phaseQ 4 seed2.A seed2.H seed2.Z) 0) u v = (reverse (relabel (node 5) perm16)) u v from by decide) u v
  rw [he]
  exact Core.reversed (Core.framed (Core.finite 5) perm16)

theorem address2 {B : Matrix 4} (h : StripSemantics.Core 4 seed2 Core B) : Core B := by
  induction h with
  | base h => exact h
  | strip n i => exact Core.strip2 n i
  | framed h p ih => exact Core.framed ih p
  | reversed h ih => exact Core.reversed ih

theorem parent3_0 : Core (mutate (GenericStrip.root 4 seed3.A seed3.H seed3.Z) 1) := by
  have he : mutate (GenericStrip.root 4 seed3.A seed3.H seed3.Z) 1 = reverse (relabel (node 6) perm3) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (GenericStrip.root 4 seed3.A seed3.H seed3.Z) 1) u v = (reverse (relabel (node 6) perm3)) u v from by decide) u v
  rw [he]
  exact Core.reversed (Core.framed (Core.finite 6) perm3)

theorem parent3_1 : Core (mutate (GenericStrip.root 4 seed3.A seed3.H seed3.Z) 2) := by
  have he : mutate (GenericStrip.root 4 seed3.A seed3.H seed3.Z) 2 = relabel (node 18) perm17 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (GenericStrip.root 4 seed3.A seed3.H seed3.Z) 2) u v = (relabel (node 18) perm17) u v from by decide) u v
  rw [he]
  exact Core.framed (Core.finite 18) perm17

theorem parent3_2 : Core (mutate (GenericStrip.phaseQ 4 seed3.A seed3.H seed3.Z) 0) := by
  have he : mutate (GenericStrip.phaseQ 4 seed3.A seed3.H seed3.Z) 0 = reverse (relabel (node 1) perm16) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (GenericStrip.phaseQ 4 seed3.A seed3.H seed3.Z) 0) u v = (reverse (relabel (node 1) perm16)) u v from by decide) u v
  rw [he]
  exact Core.reversed (Core.framed (Core.finite 1) perm16)

theorem address3 {B : Matrix 4} (h : StripSemantics.Core 4 seed3 Core B) : Core B := by
  induction h with
  | base h => exact h
  | strip n i => exact Core.strip3 n i
  | framed h p ih => exact Core.framed ih p
  | reversed h ih => exact Core.reversed ih

theorem parent4_0 : Core (mutate (GenericStrip.root 5 seed4.A seed4.H seed4.Z) 1) := by
  have he : mutate (GenericStrip.root 5 seed4.A seed4.H seed4.Z) 1 = reverse (relabel (node 13) perm3) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (GenericStrip.root 5 seed4.A seed4.H seed4.Z) 1) u v = (reverse (relabel (node 13) perm3)) u v from by decide) u v
  rw [he]
  exact Core.reversed (Core.framed (Core.finite 13) perm3)

theorem parent4_1 : Core (mutate (GenericStrip.root 5 seed4.A seed4.H seed4.Z) 2) := by
  have he : mutate (GenericStrip.root 5 seed4.A seed4.H seed4.Z) 2 = relabel (node 29) perm17 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (GenericStrip.root 5 seed4.A seed4.H seed4.Z) 2) u v = (relabel (node 29) perm17) u v from by decide) u v
  rw [he]
  exact Core.framed (Core.finite 29) perm17

theorem parent4_2 : Core (mutate (GenericStrip.phaseQ 5 seed4.A seed4.H seed4.Z) 0) := by
  have he : mutate (GenericStrip.phaseQ 5 seed4.A seed4.H seed4.Z) 0 = reverse (relabel (node 4) perm16) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (GenericStrip.phaseQ 5 seed4.A seed4.H seed4.Z) 0) u v = (reverse (relabel (node 4) perm16)) u v from by decide) u v
  rw [he]
  exact Core.reversed (Core.framed (Core.finite 4) perm16)

theorem address4 {B : Matrix 4} (h : StripSemantics.Core 5 seed4 Core B) : Core B := by
  induction h with
  | base h => exact h
  | strip n i => exact Core.strip4 n i
  | framed h p ih => exact Core.framed ih p
  | reversed h ih => exact Core.reversed ih

theorem parent5_0 : Core (mutate (GenericStrip.root 5 seed5.A seed5.H seed5.Z) 1) := by
  have he : mutate (GenericStrip.root 5 seed5.A seed5.H seed5.Z) 1 = reverse (relabel (node 2) perm3) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (GenericStrip.root 5 seed5.A seed5.H seed5.Z) 1) u v = (reverse (relabel (node 2) perm3)) u v from by decide) u v
  rw [he]
  exact Core.reversed (Core.framed (Core.finite 2) perm3)

theorem parent5_1 : Core (mutate (GenericStrip.root 5 seed5.A seed5.H seed5.Z) 2) := by
  have he : mutate (GenericStrip.root 5 seed5.A seed5.H seed5.Z) 2 = relabel (node 9) perm17 := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (GenericStrip.root 5 seed5.A seed5.H seed5.Z) 2) u v = (relabel (node 9) perm17) u v from by decide) u v
  rw [he]
  exact Core.framed (Core.finite 9) perm17

theorem parent5_2 : Core (mutate (GenericStrip.phaseQ 5 seed5.A seed5.H seed5.Z) 0) := by
  have he : mutate (GenericStrip.phaseQ 5 seed5.A seed5.H seed5.Z) 0 = reverse (relabel (node 0) perm16) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (GenericStrip.phaseQ 5 seed5.A seed5.H seed5.Z) 0) u v = (reverse (relabel (node 0) perm16)) u v from by decide) u v
  rw [he]
  exact Core.reversed (Core.framed (Core.finite 0) perm16)

theorem address5 {B : Matrix 4} (h : StripSemantics.Core 5 seed5 Core B) : Core B := by
  induction h with
  | base h => exact h
  | strip n i => exact Core.strip5 n i
  | framed h p ih => exact Core.framed ih p
  | reversed h ih => exact Core.reversed ih

theorem core_skew {B : Matrix 4} (h : Core B) : SkewSymmetric B := by
  induction h with
  | finite i => exact finite_skew i
  | affineSeven n hn i => exact AffineFiveLocal.Seven.tail_skew n i
  | affineNine n hn i => exact AffineFiveLocal.Nine.tail_skew n i
  | strip0 n i => exact GenericStrip.phase_skew _ _ _ _ _
  | strip1 n i => exact GenericStrip.phase_skew _ _ _ _ _
  | strip2 n i => exact GenericStrip.phase_skew _ _ _ _ _
  | strip3 n i => exact GenericStrip.phase_skew _ _ _ _ _
  | strip4 n i => exact GenericStrip.phase_skew _ _ _ _ _
  | strip5 n i => exact GenericStrip.phase_skew _ _ _ _ _
  | framed h p ih => exact relabel_skew _ p ih
  | reversed h ih => exact reverse_skew _ ih

theorem core_cyclic {B : Matrix 4} (h : Core B) : ¬ Acyclic B := by
  induction h with
  | finite i => exact finite_cyclic i
  | affineSeven n hn i => exact AffineFiveLocal.Seven.tail_cyclic n hn i
  | affineNine n hn i => exact AffineFiveLocal.Nine.tail_cyclic n hn i
  | strip0 n i => exact GenericStrip.phase_cyclic _ _ _ _ (GenericStrip.orbit_domain 2 seed0 domain0 n) i
  | strip1 n i => exact GenericStrip.phase_cyclic _ _ _ _ (GenericStrip.orbit_domain 2 seed1 domain1 n) i
  | strip2 n i => exact GenericStrip.phase_cyclic _ _ _ _ (GenericStrip.orbit_domain 4 seed2 domain2 n) i
  | strip3 n i => exact GenericStrip.phase_cyclic _ _ _ _ (GenericStrip.orbit_domain 4 seed3 domain3 n) i
  | strip4 n i => exact GenericStrip.phase_cyclic _ _ _ _ (GenericStrip.orbit_domain 5 seed4 domain4 n) i
  | strip5 n i => exact GenericStrip.phase_cyclic _ _ _ _ (GenericStrip.orbit_domain 5 seed5 domain5 n) i
  | framed h p ih => exact fun ha => ih ((acyclic_relabel_iff _ p).mp ha)
  | reversed h ih => exact fun ha => ih ((acyclic_reverse_iff _ (core_skew h)).mp ha)

theorem core_edges {B : Matrix 4} (h : Core B) (k : Fin 4) :
    Core (mutate B k) ∨ WeakForks.IsWeakFork (mutate B k) k ∨ WeakRegions.IsRoot (mutate B k) k := by
  induction h generalizing k with
  | finite i => exact finite_edges i k
  | affineSeven n hn i =>
    rcases AffineFiveLocal.Seven.tail_edges n hn i k with hc|hf|hr
    · exact Or.inl (affineSeven_address hc)
    · exact Or.inr (Or.inl hf)
    · exact Or.inr (Or.inr hr)
  | affineNine n hn i =>
    rcases AffineFiveLocal.Nine.tail_edges n hn i k with hc|hf|hr
    · exact Or.inl (affineNine_address hc)
    · exact Or.inr (Or.inl hf)
    · exact Or.inr (Or.inr hr)
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
    rcases StripSemantics.strip_edges 4 seed2 Core domain2
      (.base parent2_0) (.base parent2_1) (.base parent2_2) n i k with hc|hf|hr
    · exact Or.inl (address2 hc)
    · exact Or.inr (Or.inl (strict_fork_weak hf))
    · exact Or.inr (Or.inr (strict_root_weak hr))
  | strip3 n i =>
    rcases StripSemantics.strip_edges 4 seed3 Core domain3
      (.base parent3_0) (.base parent3_1) (.base parent3_2) n i k with hc|hf|hr
    · exact Or.inl (address3 hc)
    · exact Or.inr (Or.inl (strict_fork_weak hf))
    · exact Or.inr (Or.inr (strict_root_weak hr))
  | strip4 n i =>
    rcases StripSemantics.strip_edges 5 seed4 Core domain4
      (.base parent4_0) (.base parent4_1) (.base parent4_2) n i k with hc|hf|hr
    · exact Or.inl (address4 hc)
    · exact Or.inr (Or.inl (strict_fork_weak hf))
    · exact Or.inr (Or.inr (strict_root_weak hr))
  | strip5 n i =>
    rcases StripSemantics.strip_edges 5 seed5 Core domain5
      (.base parent5_0) (.base parent5_1) (.base parent5_2) n i k with hc|hf|hr
    · exact Or.inl (address5 hc)
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

/-- Exact source q065: unconditional NMA for every finite mutation word. -/
theorem nma_q065 : ¬ MutationAcyclic (ofSix (-2) (-2) (-1) (-1) (1) (-2)) := by
  have he : (ofSix (-2) (-2) (-1) (-1) (1) (-2)) = relabel (node 60) perm0 := by
    funext u v
    exact (show ∀ u v : Fin 4, ((ofSix (-2) (-2) (-1) (-1) (1) (-2))) u v = (relabel (node 60) perm0) u v from by decide) u v
  rw [he]
  exact core_NMA (Core.framed (Core.finite 60) perm0)

/-- Exact source q071: unconditional NMA for every finite mutation word. -/
theorem nma_q071 : ¬ MutationAcyclic (ofSix (-2) (-2) (-1) (-1) (2) (-1)) := by
  have he : (ofSix (-2) (-2) (-1) (-1) (2) (-1)) = relabel (node 61) perm0 := by
    funext u v
    exact (show ∀ u v : Fin 4, ((ofSix (-2) (-2) (-1) (-1) (2) (-1))) u v = (relabel (node 61) perm0) u v from by decide) u v
  rw [he]
  exact core_NMA (Core.framed (Core.finite 61) perm0)

/-- Exact source q185: unconditional NMA for every finite mutation word. -/
theorem nma_q185 : ¬ MutationAcyclic (ofSix (-2) (-2) (1) (-1) (-1) (2)) := by
  have he : (ofSix (-2) (-2) (1) (-1) (-1) (2)) = reverse (relabel (node 61) perm10) := by
    funext u v
    exact (show ∀ u v : Fin 4, ((ofSix (-2) (-2) (1) (-1) (-1) (2))) u v = (reverse (relabel (node 61) perm10)) u v from by decide) u v
  rw [he]
  exact core_NMA (Core.reversed (Core.framed (Core.finite 61) perm10))

/-- Exact source q421: unconditional NMA for every finite mutation word. -/
theorem nma_q421 : ¬ MutationAcyclic (ofSix (-2) (-1) (1) (-2) (-1) (2)) := by
  have he : (ofSix (-2) (-1) (1) (-2) (-1) (2)) = reverse (relabel (node 60) perm22) := by
    funext u v
    exact (show ∀ u v : Fin 4, ((ofSix (-2) (-1) (1) (-2) (-1) (2))) u v = (reverse (relabel (node 60) perm22)) u v from by decide) u v
  rw [he]
  exact core_NMA (Core.reversed (Core.framed (Core.finite 60) perm22))

end QuiverProofs.AffineFiveCompletion
