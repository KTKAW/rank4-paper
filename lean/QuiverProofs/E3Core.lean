import QuiverProofs.GenericStrip
import QuiverProofs.ForkCertificates
import QuiverProofs.TriangleRegions

/-! The exact 67-state printed E3 core and all 268 labeled mutations.
All equalities, cyclicity, reachability and induced-triangle witnesses
are checked by the Lean kernel. Target names only the finite interfaces;
it does not assert unproved soundness of the N/D continuation regions. -/
namespace QuiverProofs.E3Core
open Forks Regions ForkCertificates
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000

private theorem fin2 (i : Fin 2) : i=0 ∨ i=1 := by omega

private theorem fin4 (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega

private theorem fin6 (i : Fin 6) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 := by omega

private theorem fin67 (i : Fin 67) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 ∨ i=15 ∨ i=16 ∨ i=17 ∨ i=18 ∨ i=19 ∨ i=20 ∨ i=21 ∨ i=22 ∨ i=23 ∨ i=24 ∨ i=25 ∨ i=26 ∨ i=27 ∨ i=28 ∨ i=29 ∨ i=30 ∨ i=31 ∨ i=32 ∨ i=33 ∨ i=34 ∨ i=35 ∨ i=36 ∨ i=37 ∨ i=38 ∨ i=39 ∨ i=40 ∨ i=41 ∨ i=42 ∨ i=43 ∨ i=44 ∨ i=45 ∨ i=46 ∨ i=47 ∨ i=48 ∨ i=49 ∨ i=50 ∨ i=51 ∨ i=52 ∨ i=53 ∨ i=54 ∨ i=55 ∨ i=56 ∨ i=57 ∨ i=58 ∨ i=59 ∨ i=60 ∨ i=61 ∨ i=62 ∨ i=63 ∨ i=64 ∨ i=65 ∨ i=66 := by omega

def node (i : Fin 67) : Matrix 4 := match i.val with
  | 0 => ofSix (-2) (-1) (1) (1) (-2) (2)
  | 1 => ofSix (2) (1) (-1) (1) (0) (3)
  | 2 => ofSix (2) (-1) (-3) (-1) (2) (0)
  | 3 => ofSix (-2) (3) (-1) (-1) (0) (3)
  | 4 => ofSix (2) (-1) (2) (-1) (3) (-3)
  | 5 => ofSix (2) (-2) (1) (1) (0) (-3)
  | 6 => ofSix (-2) (1) (3) (-3) (-4) (0)
  | 7 => ofSix (2) (1) (-3) (1) (2) (0)
  | 8 => ofSix (-4) (-1) (3) (-1) (-2) (0)
  | 9 => ofSix (2) (-3) (1) (5) (0) (0)
  | 10 => ofSix (1) (-3) (8) (1) (0) (-3)
  | 11 => ofSix (-2) (0) (1) (-1) (0) (-3)
  | 12 => ofSix (-2) (-1) (8) (1) (-3) (0)
  | 13 => ofSix (0) (2) (-5) (-1) (0) (3)
  | 14 => ofSix (1) (-1) (3) (3) (-4) (0)
  | 15 => ofSix (-2) (-1) (3) (1) (-4) (-3)
  | 16 => ofSix (-4) (1) (3) (1) (-2) (0)
  | 17 => ofSix (4) (1) (-3) (-1) (10) (3)
  | 18 => ofSix (4) (-5) (-5) (1) (2) (0)
  | 19 => ofSix (-1) (3) (-8) (-2) (0) (21)
  | 20 => ofSix (1) (21) (-8) (1) (0) (3)
  | 21 => ofSix (2) (1) (-8) (1) (13) (8)
  | 22 => ofSix (22) (-1) (-8) (1) (3) (0)
  | 23 => ofSix (-1) (2) (3) (-3) (4) (-12)
  | 24 => ofSix (2) (-1) (-5) (-1) (4) (-7)
  | 25 => ofSix (4) (-1) (-3) (5) (10) (0)
  | 26 => ofSix (4) (1) (-5) (-1) (2) (-2)
  | 27 => ofSix (-4) (1) (37) (1) (-10) (13)
  | 28 => ofSix (5) (-1) (0) (1) (10) (-3)
  | 29 => ofSix (-1) (5) (-5) (-1) (2) (0)
  | 30 => ofSix (1) (1) (-8) (2) (0) (21)
  | 31 => ofSix (-1) (-21) (8) (1) (-8) (-165)
  | 32 => ofSix (1) (-21) (55) (-1) (3) (-3)
  | 33 => ofSix (-2) (3) (18) (-1) (-13) (8)
  | 34 => ofSix (-22) (1) (8) (-21) (-173) (0)
  | 35 => ofSix (-22) (21) (58) (-1) (-3) (0)
  | 36 => ofSix (1) (-2) (-3) (-1) (7) (-12)
  | 37 => ofSix (-2) (1) (5) (-3) (-6) (-7)
  | 38 => ofSix (-4) (-1) (5) (-1) (-18) (-7)
  | 39 => ofSix (4) (-1) (-37) (5) (138) (13)
  | 40 => ofSix (-4) (-1) (50) (-1) (3) (-13)
  | 41 => ofSix (-5) (4) (50) (-1) (-10) (-3)
  | 42 => ofSix (1) (-5) (5) (4) (2) (-25)
  | 43 => ofSix (1) (-1) (13) (-2) (42) (-21)
  | 44 => ofSix (1) (-21) (0) (-1) (8) (-173)
  | 45 => ofSix (-22) (21) (-3457) (-1) (-8) (165)
  | 46 => ofSix (-1) (21) (-55) (-22) (3) (1152)
  | 47 => ofSix (-1) (-21) (58) (1) (-3) (0)
  | 48 => ofSix (1) (-3) (42) (1) (-13) (-8)
  | 49 => ofSix (1) (2) (-27) (1) (-5) (12)
  | 50 => ofSix (1) (-1) (5) (3) (-27) (7)
  | 51 => ofSix (4) (-5) (-67) (1) (18) (-7)
  | 52 => ofSix (-4) (1) (-2) (1) (-25) (7)
  | 53 => ofSix (-1) (1) (-37) (-5) (203) (-13)
  | 54 => ofSix (4) (1) (-50) (-1) (203) (37)
  | 55 => ofSix (-1) (3) (-42) (-2) (-13) (118)
  | 56 => ofSix (1) (21) (-3633) (1) (-165) (173)
  | 57 => ofSix (22) (-1) (-3633) (1) (8) (165)
  | 58 => ofSix (1) (-1) (-55) (22) (-3) (1218)
  | 59 => ofSix (1) (21) (-58) (1) (55) (1218)
  | 60 => ofSix (-1) (2) (5) (-3) (27) (-74)
  | 61 => ofSix (-1) (5) (-102) (-1) (18) (7)
  | 62 => ofSix (4) (1) (-102) (-1) (25) (-18)
  | 63 => ofSix (1) (-4) (-37) (5) (-203) (1002)
  | 64 => ofSix (-1) (21) (165) (-22) (3633) (-79918)
  | 65 => ofSix (-21) (1) (-55) (-22) (26793) (-1218)
  | _ => ofSix (1) (-5) (102) (4) (18) (-503)

def nodeWord (i : Fin 67) : List (Fin 4) := match i.val with
  | 0 => []
  | 1 => [0]
  | 2 => [1]
  | 3 => [0, 1]
  | 4 => [0, 2]
  | 5 => [0, 3]
  | 6 => [1, 0]
  | 7 => [1, 2]
  | 8 => [1, 3]
  | 9 => [0, 1, 0]
  | 10 => [0, 1, 2]
  | 11 => [0, 1, 3]
  | 12 => [0, 2, 1]
  | 13 => [0, 3, 2]
  | 14 => [1, 0, 2]
  | 15 => [1, 2, 0]
  | 16 => [1, 2, 3]
  | 17 => [1, 3, 0]
  | 18 => [1, 3, 1]
  | 19 => [0, 1, 2, 0]
  | 20 => [0, 1, 2, 3]
  | 21 => [0, 2, 1, 0]
  | 22 => [0, 2, 1, 3]
  | 23 => [1, 0, 2, 1]
  | 24 => [1, 2, 0, 1]
  | 25 => [1, 2, 3, 0]
  | 26 => [1, 2, 3, 1]
  | 27 => [1, 3, 0, 1]
  | 28 => [1, 3, 0, 2]
  | 29 => [1, 3, 1, 2]
  | 30 => [0, 1, 2, 0, 1]
  | 31 => [0, 1, 2, 3, 0]
  | 32 => [0, 1, 2, 3, 2]
  | 33 => [0, 2, 1, 0, 1]
  | 34 => [0, 2, 1, 3, 0]
  | 35 => [0, 2, 1, 3, 1]
  | 36 => [1, 0, 2, 1, 0]
  | 37 => [1, 2, 0, 1, 0]
  | 38 => [1, 2, 3, 1, 0]
  | 39 => [1, 3, 0, 1, 0]
  | 40 => [1, 3, 0, 1, 2]
  | 41 => [1, 3, 0, 2, 1]
  | 42 => [1, 3, 1, 2, 0]
  | 43 => [0, 1, 2, 0, 1, 2]
  | 44 => [0, 1, 2, 3, 0, 1]
  | 45 => [0, 1, 2, 3, 0, 2]
  | 46 => [0, 1, 2, 3, 2, 0]
  | 47 => [0, 1, 2, 3, 2, 1]
  | 48 => [0, 2, 1, 0, 1, 2]
  | 49 => [1, 0, 2, 1, 0, 2]
  | 50 => [1, 2, 0, 1, 0, 2]
  | 51 => [1, 2, 3, 1, 0, 1]
  | 52 => [1, 2, 3, 1, 0, 2]
  | 53 => [1, 3, 0, 1, 0, 2]
  | 54 => [1, 3, 0, 1, 2, 0]
  | 55 => [0, 1, 2, 0, 1, 2, 1, 0, 1]
  | 56 => [0, 1, 2, 3, 0, 1, 2]
  | 57 => [0, 1, 2, 3, 0, 2, 1]
  | 58 => [0, 1, 2, 3, 2, 0, 1]
  | 59 => [0, 1, 2, 3, 2, 1, 0]
  | 60 => [1, 0, 2, 1, 0, 2, 0, 1, 0]
  | 61 => [1, 2, 3, 1, 0, 1, 2]
  | 62 => [1, 2, 3, 1, 0, 2, 1]
  | 63 => [1, 3, 0, 1, 0, 2, 1]
  | 64 => [0, 1, 2, 3, 0, 1, 2, 0, 1, 0]
  | 65 => [0, 1, 2, 3, 2, 0, 1, 2]
  | _ => [1, 2, 3, 1, 0, 1, 2, 0]

def stripM (j : Fin 6) : Int := match j.val with
  | 0 => 2
  | 1 => 2
  | 2 => 4
  | 3 => 21
  | 4 => 21
  | _ => 4

def stripSeed (j : Fin 6) : Cone.State := match j.val with
  | 0 => ⟨42,13,21⟩
  | 1 => ⟨27,5,12⟩
  | 2 => ⟨203,37,50⟩
  | 3 => ⟨3633,165,173⟩
  | 4 => ⟨1218,55,58⟩
  | _ => ⟨102,18,25⟩

def stripPhase (j i : Fin 6) : Matrix 4 :=
  GenericStrip.phase (stripM j) (stripSeed j).A (stripSeed j).H (stripSeed j).Z i

structure ZeroSeed where
  x : Int
  u : Int
  v : Int
  w : Int

structure PendantSeed where
  d : Int
  x : Int
  y : Int

def zeroSeed (j : Fin 6) : ZeroSeed := match j.val with
  | 0 => ⟨3,3,4,10⟩
  | 1 => ⟨2,5,5,6⟩
  | 2 => ⟨8,2,21,165⟩
  | 3 => ⟨3,5,10,26⟩
  | 4 => ⟨8,21,173,1362⟩
  | _ => ⟨3,21,58,152⟩

def pendantSeed (j : Fin 2) : PendantSeed := match j.val with
  | 0 => ⟨5,2,7⟩
  | _ => ⟨5,3,13⟩

def zeroRoot (x u v w : Int) (s : Fin 2) : Matrix 4 :=
  if s.val=0 then ofSix 0 (-u) 1 v (-x) w
  else mutate (ofSix 0 (-u) 1 v (-x) w) 0

def pendantRoot (d x y : Int) (s : Fin 2) : Matrix 4 :=
  if s.val=0 then ofSix 0 0 1 d (-x) y
  else mutate (ofSix 0 0 1 d (-x) y) 0

def zeroPhase (j : Fin 6) (s : Fin 2) : Matrix 4 :=
  zeroRoot (zeroSeed j).x (zeroSeed j).u (zeroSeed j).v (zeroSeed j).w s

def pendantPhase (j s : Fin 2) : Matrix 4 :=
  pendantRoot (pendantSeed j).d (pendantSeed j).x (pendantSeed j).y s

inductive Target : Matrix 4 → Prop
  | base (i : Fin 67) : Target (node i)
  | strip (j i : Fin 6) : Target (stripPhase j i)
  | zero (j : Fin 6) (s : Fin 2) : Target (zeroPhase j s)
  | pendant (j s : Fin 2) : Target (pendantPhase j s)
  | framed {B : Matrix 4} : Target B → (p : Relabeling 4) → Target (relabel B p)
  | reversed {B : Matrix 4} : Target B → Target (reverse B)

theorem strip_domain (j : Fin 6) :
    GenericStrip.Domain (stripM j) (stripSeed j).A (stripSeed j).H (stripSeed j).Z := by
  exact (show ∀ j : Fin 6, GenericStrip.Domain (stripM j)
    (stripSeed j).A (stripSeed j).H (stripSeed j).Z from by unfold GenericStrip.Domain; decide) j

theorem zero_domain (j : Fin 6) :
    2 ≤ (zeroSeed j).x ∧ 2 ≤ (zeroSeed j).u ∧
    (zeroSeed j).x < (zeroSeed j).v ∧ (zeroSeed j).v < (zeroSeed j).w := by
  exact (show ∀ j : Fin 6, 2 ≤ (zeroSeed j).x ∧ 2 ≤ (zeroSeed j).u ∧
    (zeroSeed j).x < (zeroSeed j).v ∧ (zeroSeed j).v < (zeroSeed j).w from by decide) j

theorem pendant_domain (j : Fin 2) :
    2 ≤ (pendantSeed j).d ∧ 2 ≤ (pendantSeed j).x ∧
    max (pendantSeed j).d (pendantSeed j).x < (pendantSeed j).y := by
  exact (show ∀ j : Fin 2, 2 ≤ (pendantSeed j).d ∧ 2 ≤ (pendantSeed j).x ∧
    max (pendantSeed j).d (pendantSeed j).x < (pendantSeed j).y from by decide) j

theorem cyclic0 : ¬ Acyclic (node 0) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge0_0 : Target (mutate (node 0) 0) ∨ IsFork (mutate (node 0) 0) 0 ∨ IsRoot (mutate (node 0) 0) 0 := by
  left
  have he : (mutate (node 0) 0) = relabel (node 1) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 0) 0) u v = (relabel (node 1) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 1) perm0.symm

theorem edge0_1 : Target (mutate (node 0) 1) ∨ IsFork (mutate (node 0) 1) 1 ∨ IsRoot (mutate (node 0) 1) 1 := by
  left
  have he : (mutate (node 0) 1) = relabel (node 2) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 0) 1) u v = (relabel (node 2) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 2) perm0.symm

theorem edge0_2 : Target (mutate (node 0) 2) ∨ IsFork (mutate (node 0) 2) 2 ∨ IsRoot (mutate (node 0) 2) 2 := by
  left
  have he : (mutate (node 0) 2) = reverse (relabel (node 1) perm16.symm) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 0) 2) u v = (reverse (relabel (node 1) perm16.symm)) u v from by decide) u v
  rw [he]; exact Target.reversed (Target.framed (Target.base 1) perm16.symm)

theorem edge0_3 : Target (mutate (node 0) 3) ∨ IsFork (mutate (node 0) 3) 3 ∨ IsRoot (mutate (node 0) 3) 3 := by
  left
  have he : (mutate (node 0) 3) = reverse (relabel (node 2) perm16.symm) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 0) 3) u v = (reverse (relabel (node 2) perm16.symm)) u v from by decide) u v
  rw [he]; exact Target.reversed (Target.framed (Target.base 2) perm16.symm)

theorem cyclic1 : ¬ Acyclic (node 1) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (by decide)
  have h1 := hr 2 3 (by decide)
  have h2 := hr 3 0 (by decide)
  omega

theorem edge1_0 : Target (mutate (node 1) 0) ∨ IsFork (mutate (node 1) 0) 0 ∨ IsRoot (mutate (node 1) 0) 0 := by
  left
  have he : (mutate (node 1) 0) = relabel (node 0) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 1) 0) u v = (relabel (node 0) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 0) perm0.symm

theorem edge1_1 : Target (mutate (node 1) 1) ∨ IsFork (mutate (node 1) 1) 1 ∨ IsRoot (mutate (node 1) 1) 1 := by
  left
  have he : (mutate (node 1) 1) = relabel (node 3) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 1) 1) u v = (relabel (node 3) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 3) perm0.symm

theorem edge1_2 : Target (mutate (node 1) 2) ∨ IsFork (mutate (node 1) 2) 2 ∨ IsRoot (mutate (node 1) 2) 2 := by
  left
  have he : (mutate (node 1) 2) = relabel (node 4) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 1) 2) u v = (relabel (node 4) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 4) perm0.symm

theorem edge1_3 : Target (mutate (node 1) 3) ∨ IsFork (mutate (node 1) 3) 3 ∨ IsRoot (mutate (node 1) 3) 3 := by
  left
  have he : (mutate (node 1) 3) = relabel (node 5) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 1) 3) u v = (relabel (node 5) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 5) perm0.symm

theorem cyclic2 : ¬ Acyclic (node 2) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (by decide)
  have h1 := hr 1 3 (by decide)
  have h2 := hr 3 0 (by decide)
  omega

theorem edge2_0 : Target (mutate (node 2) 0) ∨ IsFork (mutate (node 2) 0) 0 ∨ IsRoot (mutate (node 2) 0) 0 := by
  left
  have he : (mutate (node 2) 0) = relabel (node 6) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 2) 0) u v = (relabel (node 6) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 6) perm0.symm

theorem edge2_1 : Target (mutate (node 2) 1) ∨ IsFork (mutate (node 2) 1) 1 ∨ IsRoot (mutate (node 2) 1) 1 := by
  left
  have he : (mutate (node 2) 1) = relabel (node 0) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 2) 1) u v = (relabel (node 0) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 0) perm0.symm

theorem edge2_2 : Target (mutate (node 2) 2) ∨ IsFork (mutate (node 2) 2) 2 ∨ IsRoot (mutate (node 2) 2) 2 := by
  left
  have he : (mutate (node 2) 2) = relabel (node 7) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 2) 2) u v = (relabel (node 7) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 7) perm0.symm

theorem edge2_3 : Target (mutate (node 2) 3) ∨ IsFork (mutate (node 2) 3) 3 ∨ IsRoot (mutate (node 2) 3) 3 := by
  left
  have he : (mutate (node 2) 3) = relabel (node 8) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 2) 3) u v = (relabel (node 8) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 8) perm0.symm

theorem cyclic3 : ¬ Acyclic (node 3) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (by decide)
  have h1 := hr 2 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge3_0 : Target (mutate (node 3) 0) ∨ IsFork (mutate (node 3) 0) 0 ∨ IsRoot (mutate (node 3) 0) 0 := by
  left
  have he : (mutate (node 3) 0) = relabel (node 9) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 3) 0) u v = (relabel (node 9) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 9) perm0.symm

theorem edge3_1 : Target (mutate (node 3) 1) ∨ IsFork (mutate (node 3) 1) 1 ∨ IsRoot (mutate (node 3) 1) 1 := by
  left
  have he : (mutate (node 3) 1) = relabel (node 1) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 3) 1) u v = (relabel (node 1) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 1) perm0.symm

theorem edge3_2 : Target (mutate (node 3) 2) ∨ IsFork (mutate (node 3) 2) 2 ∨ IsRoot (mutate (node 3) 2) 2 := by
  left
  have he : (mutate (node 3) 2) = relabel (node 10) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 3) 2) u v = (relabel (node 10) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 10) perm0.symm

theorem edge3_3 : Target (mutate (node 3) 3) ∨ IsFork (mutate (node 3) 3) 3 ∨ IsRoot (mutate (node 3) 3) 3 := by
  left
  have he : (mutate (node 3) 3) = relabel (node 11) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 3) 3) u v = (relabel (node 11) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 11) perm0.symm

theorem cyclic4 : ¬ Acyclic (node 4) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 2 (by decide)
  have h2 := hr 2 0 (by decide)
  omega

theorem edge4_0 : Target (mutate (node 4) 0) ∨ IsFork (mutate (node 4) 0) 0 ∨ IsRoot (mutate (node 4) 0) 0 := by
  left
  have he : (mutate (node 4) 0) = reverse (relabel (node 4) perm5.symm) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 4) 0) u v = (reverse (relabel (node 4) perm5.symm)) u v from by decide) u v
  rw [he]; exact Target.reversed (Target.framed (Target.base 4) perm5.symm)

theorem edge4_1 : Target (mutate (node 4) 1) ∨ IsFork (mutate (node 4) 1) 1 ∨ IsRoot (mutate (node 4) 1) 1 := by
  left
  have he : (mutate (node 4) 1) = relabel (node 12) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 4) 1) u v = (relabel (node 12) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 12) perm0.symm

theorem edge4_2 : Target (mutate (node 4) 2) ∨ IsFork (mutate (node 4) 2) 2 ∨ IsRoot (mutate (node 4) 2) 2 := by
  left
  have he : (mutate (node 4) 2) = relabel (node 1) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 4) 2) u v = (relabel (node 1) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 1) perm0.symm

theorem edge4_3 : Target (mutate (node 4) 3) ∨ IsFork (mutate (node 4) 3) 3 ∨ IsRoot (mutate (node 4) 3) 3 := by
  right; left
  have he : relabel (mutate (node 4) 3) perm22 = Forks.template (3) (2) (3) (5) (8) (2) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 4) 3) perm22) u v = (Forks.template (3) (2) (3) (5) (8) (2)) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 4) 3) perm22) 0 := by
    rw [he]
    exact IsFork.basic (3) (2) (3) (5) (8) (2) (by unfold Forks.Domain; decide)
  exact fork_of_relabel perm22 hf

theorem cyclic5 : ¬ Acyclic (node 5) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (by decide)
  have h1 := hr 1 2 (by decide)
  have h2 := hr 2 0 (by decide)
  omega

theorem edge5_0 : Target (mutate (node 5) 0) ∨ IsFork (mutate (node 5) 0) 0 ∨ IsRoot (mutate (node 5) 0) 0 := by
  left
  have he : (mutate (node 5) 0) = reverse (relabel (node 7) perm13.symm) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 5) 0) u v = (reverse (relabel (node 7) perm13.symm)) u v from by decide) u v
  rw [he]; exact Target.reversed (Target.framed (Target.base 7) perm13.symm)

theorem edge5_1 : Target (mutate (node 5) 1) ∨ IsFork (mutate (node 5) 1) 1 ∨ IsRoot (mutate (node 5) 1) 1 := by
  left
  have he : (mutate (node 5) 1) = relabel (node 11) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 5) 1) u v = (relabel (node 11) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 11) perm0.symm

theorem edge5_2 : Target (mutate (node 5) 2) ∨ IsFork (mutate (node 5) 2) 2 ∨ IsRoot (mutate (node 5) 2) 2 := by
  left
  have he : (mutate (node 5) 2) = relabel (node 13) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 5) 2) u v = (relabel (node 13) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 13) perm0.symm

theorem edge5_3 : Target (mutate (node 5) 3) ∨ IsFork (mutate (node 5) 3) 3 ∨ IsRoot (mutate (node 5) 3) 3 := by
  left
  have he : (mutate (node 5) 3) = relabel (node 1) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 5) 3) u v = (relabel (node 1) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 1) perm0.symm

theorem cyclic6 : ¬ Acyclic (node 6) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (by decide)
  have h1 := hr 2 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge6_0 : Target (mutate (node 6) 0) ∨ IsFork (mutate (node 6) 0) 0 ∨ IsRoot (mutate (node 6) 0) 0 := by
  left
  have he : (mutate (node 6) 0) = relabel (node 2) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 6) 0) u v = (relabel (node 2) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 2) perm0.symm

theorem edge6_1 : Target (mutate (node 6) 1) ∨ IsFork (mutate (node 6) 1) 1 ∨ IsRoot (mutate (node 6) 1) 1 := by
  right; right
  have he : relabel (reverse (mutate (node 6) 1)) perm6 = Regions.root (2) (5) (5) (3) (4) (0) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 6) 1)) perm6) u v = (Regions.root (2) (5) (5) (3) (4) (0)) u v from by decide) u v
  have hf : IsRoot (relabel (reverse (mutate (node 6) 1)) perm6) 0 := by
    rw [he]
    exact IsRoot.basic (2) (5) (5) (3) (4) (0) (by unfold Regions.Domain; decide) (by decide)
  exact root_of_reverse (root_of_relabel perm6 hf)

theorem edge6_2 : Target (mutate (node 6) 2) ∨ IsFork (mutate (node 6) 2) 2 ∨ IsRoot (mutate (node 6) 2) 2 := by
  left
  have he : (mutate (node 6) 2) = relabel (node 14) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 6) 2) u v = (relabel (node 14) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 14) perm0.symm

theorem edge6_3 : Target (mutate (node 6) 3) ∨ IsFork (mutate (node 6) 3) 3 ∨ IsRoot (mutate (node 6) 3) 3 := by
  left
  have he : (mutate (node 6) 3) = reverse (relabel (zeroPhase 0 0) perm17.symm) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 6) 3) u v = (reverse (relabel (zeroPhase 0 0) perm17.symm)) u v from by decide) u v
  rw [he]; exact Target.reversed (Target.framed (Target.zero 0 0) perm17.symm)

theorem cyclic7 : ¬ Acyclic (node 7) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (by decide)
  have h1 := hr 1 3 (by decide)
  have h2 := hr 3 0 (by decide)
  omega

theorem edge7_0 : Target (mutate (node 7) 0) ∨ IsFork (mutate (node 7) 0) 0 ∨ IsRoot (mutate (node 7) 0) 0 := by
  left
  have he : (mutate (node 7) 0) = relabel (node 15) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 7) 0) u v = (relabel (node 15) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 15) perm0.symm

theorem edge7_1 : Target (mutate (node 7) 1) ∨ IsFork (mutate (node 7) 1) 1 ∨ IsRoot (mutate (node 7) 1) 1 := by
  left
  have he : (mutate (node 7) 1) = reverse (relabel (node 5) perm10.symm) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 7) 1) u v = (reverse (relabel (node 5) perm10.symm)) u v from by decide) u v
  rw [he]; exact Target.reversed (Target.framed (Target.base 5) perm10.symm)

theorem edge7_2 : Target (mutate (node 7) 2) ∨ IsFork (mutate (node 7) 2) 2 ∨ IsRoot (mutate (node 7) 2) 2 := by
  left
  have he : (mutate (node 7) 2) = relabel (node 2) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 7) 2) u v = (relabel (node 2) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 2) perm0.symm

theorem edge7_3 : Target (mutate (node 7) 3) ∨ IsFork (mutate (node 7) 3) 3 ∨ IsRoot (mutate (node 7) 3) 3 := by
  left
  have he : (mutate (node 7) 3) = relabel (node 16) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 7) 3) u v = (relabel (node 16) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 16) perm0.symm

theorem cyclic8 : ¬ Acyclic (node 8) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge8_0 : Target (mutate (node 8) 0) ∨ IsFork (mutate (node 8) 0) 0 ∨ IsRoot (mutate (node 8) 0) 0 := by
  left
  have he : (mutate (node 8) 0) = relabel (node 17) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 8) 0) u v = (relabel (node 17) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 17) perm0.symm

theorem edge8_1 : Target (mutate (node 8) 1) ∨ IsFork (mutate (node 8) 1) 1 ∨ IsRoot (mutate (node 8) 1) 1 := by
  left
  have he : (mutate (node 8) 1) = relabel (node 18) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 8) 1) u v = (relabel (node 18) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 18) perm0.symm

theorem edge8_2 : Target (mutate (node 8) 2) ∨ IsFork (mutate (node 8) 2) 2 ∨ IsRoot (mutate (node 8) 2) 2 := by
  left
  have he : (mutate (node 8) 2) = relabel (node 16) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 8) 2) u v = (relabel (node 16) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 16) perm0.symm

theorem edge8_3 : Target (mutate (node 8) 3) ∨ IsFork (mutate (node 8) 3) 3 ∨ IsRoot (mutate (node 8) 3) 3 := by
  left
  have he : (mutate (node 8) 3) = relabel (node 2) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 8) 3) u v = (relabel (node 2) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 2) perm0.symm

theorem cyclic9 : ¬ Acyclic (node 9) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (by decide)
  have h1 := hr 1 2 (by decide)
  have h2 := hr 2 0 (by decide)
  omega

theorem edge9_0 : Target (mutate (node 9) 0) ∨ IsFork (mutate (node 9) 0) 0 ∨ IsRoot (mutate (node 9) 0) 0 := by
  left
  have he : (mutate (node 9) 0) = relabel (node 3) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 9) 0) u v = (relabel (node 3) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 3) perm0.symm

theorem edge9_1 : Target (mutate (node 9) 1) ∨ IsFork (mutate (node 9) 1) 1 ∨ IsRoot (mutate (node 9) 1) 1 := by
  left
  have he : (mutate (node 9) 1) = reverse (relabel (pendantPhase 0 0) perm21.symm) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 9) 1) u v = (reverse (relabel (pendantPhase 0 0) perm21.symm)) u v from by decide) u v
  rw [he]; exact Target.reversed (Target.framed (Target.pendant 0 0) perm21.symm)

theorem edge9_2 : Target (mutate (node 9) 2) ∨ IsFork (mutate (node 9) 2) 2 ∨ IsRoot (mutate (node 9) 2) 2 := by
  left
  have he : (mutate (node 9) 2) = relabel (pendantPhase 1 1) perm23.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 9) 2) u v = (relabel (pendantPhase 1 1) perm23.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.pendant 1 1) perm23.symm

theorem edge9_3 : Target (mutate (node 9) 3) ∨ IsFork (mutate (node 9) 3) 3 ∨ IsRoot (mutate (node 9) 3) 3 := by
  left
  have he : (mutate (node 9) 3) = reverse (relabel (node 13) perm10.symm) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 9) 3) u v = (reverse (relabel (node 13) perm10.symm)) u v from by decide) u v
  rw [he]; exact Target.reversed (Target.framed (Target.base 13) perm10.symm)

theorem cyclic10 : ¬ Acyclic (node 10) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (by decide)
  have h1 := hr 1 2 (by decide)
  have h2 := hr 2 0 (by decide)
  omega

theorem edge10_0 : Target (mutate (node 10) 0) ∨ IsFork (mutate (node 10) 0) 0 ∨ IsRoot (mutate (node 10) 0) 0 := by
  left
  have he : (mutate (node 10) 0) = relabel (node 19) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 10) 0) u v = (relabel (node 19) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 19) perm0.symm

theorem edge10_1 : Target (mutate (node 10) 1) ∨ IsFork (mutate (node 10) 1) 1 ∨ IsRoot (mutate (node 10) 1) 1 := by
  left
  have he : (mutate (node 10) 1) = relabel (node 12) perm2.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 10) 1) u v = (relabel (node 12) perm2.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 12) perm2.symm

theorem edge10_2 : Target (mutate (node 10) 2) ∨ IsFork (mutate (node 10) 2) 2 ∨ IsRoot (mutate (node 10) 2) 2 := by
  left
  have he : (mutate (node 10) 2) = relabel (node 3) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 10) 2) u v = (relabel (node 3) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 3) perm0.symm

theorem edge10_3 : Target (mutate (node 10) 3) ∨ IsFork (mutate (node 10) 3) 3 ∨ IsRoot (mutate (node 10) 3) 3 := by
  left
  have he : (mutate (node 10) 3) = relabel (node 20) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 10) 3) u v = (relabel (node 20) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 20) perm0.symm

theorem cyclic11 : ¬ Acyclic (node 11) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 2 (by decide)
  have h2 := hr 2 1 (by decide)
  have h3 := hr 1 0 (by decide)
  omega

theorem edge11_0 : Target (mutate (node 11) 0) ∨ IsFork (mutate (node 11) 0) 0 ∨ IsRoot (mutate (node 11) 0) 0 := by
  left
  have he : (mutate (node 11) 0) = reverse (relabel (node 5) perm7.symm) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 11) 0) u v = (reverse (relabel (node 5) perm7.symm)) u v from by decide) u v
  rw [he]; exact Target.reversed (Target.framed (Target.base 5) perm7.symm)

theorem edge11_1 : Target (mutate (node 11) 1) ∨ IsFork (mutate (node 11) 1) 1 ∨ IsRoot (mutate (node 11) 1) 1 := by
  left
  have he : (mutate (node 11) 1) = relabel (node 5) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 11) 1) u v = (relabel (node 5) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 5) perm0.symm

theorem edge11_2 : Target (mutate (node 11) 2) ∨ IsFork (mutate (node 11) 2) 2 ∨ IsRoot (mutate (node 11) 2) 2 := by
  left
  have he : (mutate (node 11) 2) = reverse (relabel (node 3) perm7.symm) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 11) 2) u v = (reverse (relabel (node 3) perm7.symm)) u v from by decide) u v
  rw [he]; exact Target.reversed (Target.framed (Target.base 3) perm7.symm)

theorem edge11_3 : Target (mutate (node 11) 3) ∨ IsFork (mutate (node 11) 3) 3 ∨ IsRoot (mutate (node 11) 3) 3 := by
  left
  have he : (mutate (node 11) 3) = relabel (node 3) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 11) 3) u v = (relabel (node 3) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 3) perm0.symm

theorem cyclic12 : ¬ Acyclic (node 12) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge12_0 : Target (mutate (node 12) 0) ∨ IsFork (mutate (node 12) 0) 0 ∨ IsRoot (mutate (node 12) 0) 0 := by
  left
  have he : (mutate (node 12) 0) = relabel (node 21) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 12) 0) u v = (relabel (node 21) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 21) perm0.symm

theorem edge12_1 : Target (mutate (node 12) 1) ∨ IsFork (mutate (node 12) 1) 1 ∨ IsRoot (mutate (node 12) 1) 1 := by
  left
  have he : (mutate (node 12) 1) = relabel (node 4) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 12) 1) u v = (relabel (node 4) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 4) perm0.symm

theorem edge12_2 : Target (mutate (node 12) 2) ∨ IsFork (mutate (node 12) 2) 2 ∨ IsRoot (mutate (node 12) 2) 2 := by
  left
  have he : (mutate (node 12) 2) = relabel (node 10) perm2.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 12) 2) u v = (relabel (node 10) perm2.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 10) perm2.symm

theorem edge12_3 : Target (mutate (node 12) 3) ∨ IsFork (mutate (node 12) 3) 3 ∨ IsRoot (mutate (node 12) 3) 3 := by
  left
  have he : (mutate (node 12) 3) = relabel (node 22) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 12) 3) u v = (relabel (node 22) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 22) perm0.symm

theorem cyclic13 : ¬ Acyclic (node 13) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (by decide)
  have h1 := hr 2 3 (by decide)
  have h2 := hr 3 0 (by decide)
  omega

theorem edge13_0 : Target (mutate (node 13) 0) ∨ IsFork (mutate (node 13) 0) 0 ∨ IsRoot (mutate (node 13) 0) 0 := by
  left
  have he : (mutate (node 13) 0) = relabel (pendantPhase 0 1) perm7.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 13) 0) u v = (relabel (pendantPhase 0 1) perm7.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.pendant 0 1) perm7.symm

theorem edge13_1 : Target (mutate (node 13) 1) ∨ IsFork (mutate (node 13) 1) 1 ∨ IsRoot (mutate (node 13) 1) 1 := by
  left
  have he : (mutate (node 13) 1) = reverse (relabel (node 9) perm13.symm) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 13) 1) u v = (reverse (relabel (node 9) perm13.symm)) u v from by decide) u v
  rw [he]; exact Target.reversed (Target.framed (Target.base 9) perm13.symm)

theorem edge13_2 : Target (mutate (node 13) 2) ∨ IsFork (mutate (node 13) 2) 2 ∨ IsRoot (mutate (node 13) 2) 2 := by
  left
  have he : (mutate (node 13) 2) = relabel (node 5) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 13) 2) u v = (relabel (node 5) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 5) perm0.symm

theorem edge13_3 : Target (mutate (node 13) 3) ∨ IsFork (mutate (node 13) 3) 3 ∨ IsRoot (mutate (node 13) 3) 3 := by
  left
  have he : (mutate (node 13) 3) = reverse (relabel (pendantPhase 1 0) perm10.symm) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 13) 3) u v = (reverse (relabel (pendantPhase 1 0) perm10.symm)) u v from by decide) u v
  rw [he]; exact Target.reversed (Target.framed (Target.pendant 1 0) perm10.symm)

theorem cyclic14 : ¬ Acyclic (node 14) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (by decide)
  have h1 := hr 1 2 (by decide)
  have h2 := hr 2 0 (by decide)
  omega

theorem edge14_0 : Target (mutate (node 14) 0) ∨ IsFork (mutate (node 14) 0) 0 ∨ IsRoot (mutate (node 14) 0) 0 := by
  left
  have he : (mutate (node 14) 0) = relabel (node 15) perm14.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 14) 0) u v = (relabel (node 15) perm14.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 15) perm14.symm

theorem edge14_1 : Target (mutate (node 14) 1) ∨ IsFork (mutate (node 14) 1) 1 ∨ IsRoot (mutate (node 14) 1) 1 := by
  left
  have he : (mutate (node 14) 1) = relabel (node 23) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 14) 1) u v = (relabel (node 23) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 23) perm0.symm

theorem edge14_2 : Target (mutate (node 14) 2) ∨ IsFork (mutate (node 14) 2) 2 ∨ IsRoot (mutate (node 14) 2) 2 := by
  left
  have he : (mutate (node 14) 2) = relabel (node 6) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 14) 2) u v = (relabel (node 6) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 6) perm0.symm

theorem edge14_3 : Target (mutate (node 14) 3) ∨ IsFork (mutate (node 14) 3) 3 ∨ IsRoot (mutate (node 14) 3) 3 := by
  left
  have he : (mutate (node 14) 3) = reverse (relabel (zeroPhase 0 1) perm17.symm) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 14) 3) u v = (reverse (relabel (zeroPhase 0 1) perm17.symm)) u v from by decide) u v
  rw [he]; exact Target.reversed (Target.framed (Target.zero 0 1) perm17.symm)

theorem cyclic15 : ¬ Acyclic (node 15) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge15_0 : Target (mutate (node 15) 0) ∨ IsFork (mutate (node 15) 0) 0 ∨ IsRoot (mutate (node 15) 0) 0 := by
  left
  have he : (mutate (node 15) 0) = relabel (node 7) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 15) 0) u v = (relabel (node 7) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 7) perm0.symm

theorem edge15_1 : Target (mutate (node 15) 1) ∨ IsFork (mutate (node 15) 1) 1 ∨ IsRoot (mutate (node 15) 1) 1 := by
  left
  have he : (mutate (node 15) 1) = relabel (node 24) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 15) 1) u v = (relabel (node 24) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 24) perm0.symm

theorem edge15_2 : Target (mutate (node 15) 2) ∨ IsFork (mutate (node 15) 2) 2 ∨ IsRoot (mutate (node 15) 2) 2 := by
  left
  have he : (mutate (node 15) 2) = relabel (node 14) perm14.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 15) 2) u v = (relabel (node 14) perm14.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 14) perm14.symm

theorem edge15_3 : Target (mutate (node 15) 3) ∨ IsFork (mutate (node 15) 3) 3 ∨ IsRoot (mutate (node 15) 3) 3 := by
  right; right
  have he : relabel (mutate (node 15) 3) perm18 = Regions.root (3) (10) (8) (4) (3) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 15) 3) perm18) u v = (Regions.root (3) (10) (8) (4) (3) (1)) u v from by decide) u v
  have hf : IsRoot (relabel (mutate (node 15) 3) perm18) 0 := by
    rw [he]
    exact IsRoot.basic (3) (10) (8) (4) (3) (1) (by unfold Regions.Domain; decide) (by decide)
  exact root_of_relabel perm18 hf

theorem cyclic16 : ¬ Acyclic (node 16) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge16_0 : Target (mutate (node 16) 0) ∨ IsFork (mutate (node 16) 0) 0 ∨ IsRoot (mutate (node 16) 0) 0 := by
  left
  have he : (mutate (node 16) 0) = relabel (node 25) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 16) 0) u v = (relabel (node 25) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 25) perm0.symm

theorem edge16_1 : Target (mutate (node 16) 1) ∨ IsFork (mutate (node 16) 1) 1 ∨ IsRoot (mutate (node 16) 1) 1 := by
  left
  have he : (mutate (node 16) 1) = relabel (node 26) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 16) 1) u v = (relabel (node 26) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 26) perm0.symm

theorem edge16_2 : Target (mutate (node 16) 2) ∨ IsFork (mutate (node 16) 2) 2 ∨ IsRoot (mutate (node 16) 2) 2 := by
  left
  have he : (mutate (node 16) 2) = relabel (node 8) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 16) 2) u v = (relabel (node 8) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 8) perm0.symm

theorem edge16_3 : Target (mutate (node 16) 3) ∨ IsFork (mutate (node 16) 3) 3 ∨ IsRoot (mutate (node 16) 3) 3 := by
  left
  have he : (mutate (node 16) 3) = relabel (node 7) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 16) 3) u v = (relabel (node 7) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 7) perm0.symm

theorem cyclic17 : ¬ Acyclic (node 17) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (by decide)
  have h1 := hr 1 3 (by decide)
  have h2 := hr 3 0 (by decide)
  omega

theorem edge17_0 : Target (mutate (node 17) 0) ∨ IsFork (mutate (node 17) 0) 0 ∨ IsRoot (mutate (node 17) 0) 0 := by
  left
  have he : (mutate (node 17) 0) = relabel (node 8) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 17) 0) u v = (relabel (node 8) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 8) perm0.symm

theorem edge17_1 : Target (mutate (node 17) 1) ∨ IsFork (mutate (node 17) 1) 1 ∨ IsRoot (mutate (node 17) 1) 1 := by
  left
  have he : (mutate (node 17) 1) = relabel (node 27) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 17) 1) u v = (relabel (node 27) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 27) perm0.symm

theorem edge17_2 : Target (mutate (node 17) 2) ∨ IsFork (mutate (node 17) 2) 2 ∨ IsRoot (mutate (node 17) 2) 2 := by
  left
  have he : (mutate (node 17) 2) = relabel (node 28) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 17) 2) u v = (relabel (node 28) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 28) perm0.symm

theorem edge17_3 : Target (mutate (node 17) 3) ∨ IsFork (mutate (node 17) 3) 3 ∨ IsRoot (mutate (node 17) 3) 3 := by
  right; right
  have he : relabel (reverse (mutate (node 17) 3)) perm18 = Regions.root (3) (26) (8) (10) (3) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 17) 3)) perm18) u v = (Regions.root (3) (26) (8) (10) (3) (1)) u v from by decide) u v
  have hf : IsRoot (relabel (reverse (mutate (node 17) 3)) perm18) 0 := by
    rw [he]
    exact IsRoot.basic (3) (26) (8) (10) (3) (1) (by unfold Regions.Domain; decide) (by decide)
  exact root_of_reverse (root_of_relabel perm18 hf)

theorem cyclic18 : ¬ Acyclic (node 18) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (by decide)
  have h1 := hr 1 2 (by decide)
  have h2 := hr 2 0 (by decide)
  omega

theorem edge18_0 : Target (mutate (node 18) 0) ∨ IsFork (mutate (node 18) 0) 0 ∨ IsRoot (mutate (node 18) 0) 0 := by
  right; right
  have he : relabel (reverse (mutate (node 18) 0)) perm0 = Regions.root (4) (19) (18) (5) (5) (0) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 18) 0)) perm0) u v = (Regions.root (4) (19) (18) (5) (5) (0)) u v from by decide) u v
  have hf : IsRoot (relabel (reverse (mutate (node 18) 0)) perm0) 0 := by
    rw [he]
    exact IsRoot.basic (4) (19) (18) (5) (5) (0) (by unfold Regions.Domain; decide) (by decide)
  exact root_of_reverse (root_of_relabel perm0 hf)

theorem edge18_1 : Target (mutate (node 18) 1) ∨ IsFork (mutate (node 18) 1) 1 ∨ IsRoot (mutate (node 18) 1) 1 := by
  left
  have he : (mutate (node 18) 1) = relabel (node 8) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 18) 1) u v = (relabel (node 8) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 8) perm0.symm

theorem edge18_2 : Target (mutate (node 18) 2) ∨ IsFork (mutate (node 18) 2) 2 ∨ IsRoot (mutate (node 18) 2) 2 := by
  left
  have he : (mutate (node 18) 2) = relabel (node 29) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 18) 2) u v = (relabel (node 29) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 29) perm0.symm

theorem edge18_3 : Target (mutate (node 18) 3) ∨ IsFork (mutate (node 18) 3) 3 ∨ IsRoot (mutate (node 18) 3) 3 := by
  left
  have he : (mutate (node 18) 3) = reverse (relabel (zeroPhase 1 0) perm16.symm) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 18) 3) u v = (reverse (relabel (zeroPhase 1 0) perm16.symm)) u v from by decide) u v
  rw [he]; exact Target.reversed (Target.framed (Target.zero 1 0) perm16.symm)

theorem cyclic19 : ¬ Acyclic (node 19) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (by decide)
  have h1 := hr 2 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge19_0 : Target (mutate (node 19) 0) ∨ IsFork (mutate (node 19) 0) 0 ∨ IsRoot (mutate (node 19) 0) 0 := by
  left
  have he : (mutate (node 19) 0) = relabel (node 10) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 19) 0) u v = (relabel (node 10) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 10) perm0.symm

theorem edge19_1 : Target (mutate (node 19) 1) ∨ IsFork (mutate (node 19) 1) 1 ∨ IsRoot (mutate (node 19) 1) 1 := by
  left
  have he : (mutate (node 19) 1) = relabel (node 30) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 19) 1) u v = (relabel (node 30) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 30) perm0.symm

theorem edge19_2 : Target (mutate (node 19) 2) ∨ IsFork (mutate (node 19) 2) 2 ∨ IsRoot (mutate (node 19) 2) 2 := by
  right; right
  have he : relabel (mutate (node 19) 2) perm12 = Regions.root (3) (5) (55) (2) (21) (0) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 19) 2) perm12) u v = (Regions.root (3) (5) (55) (2) (21) (0)) u v from by decide) u v
  have hf : IsRoot (relabel (mutate (node 19) 2) perm12) 0 := by
    rw [he]
    exact IsRoot.basic (3) (5) (55) (2) (21) (0) (by unfold Regions.Domain; decide) (by decide)
  exact root_of_relabel perm12 hf

theorem edge19_3 : Target (mutate (node 19) 3) ∨ IsFork (mutate (node 19) 3) 3 ∨ IsRoot (mutate (node 19) 3) 3 := by
  left
  have he : (mutate (node 19) 3) = relabel (zeroPhase 2 0) perm11.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 19) 3) u v = (relabel (zeroPhase 2 0) perm11.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.zero 2 0) perm11.symm

theorem cyclic20 : ¬ Acyclic (node 20) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (by decide)
  have h1 := hr 2 3 (by decide)
  have h2 := hr 3 0 (by decide)
  omega

theorem edge20_0 : Target (mutate (node 20) 0) ∨ IsFork (mutate (node 20) 0) 0 ∨ IsRoot (mutate (node 20) 0) 0 := by
  left
  have he : (mutate (node 20) 0) = relabel (node 31) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 20) 0) u v = (relabel (node 31) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 31) perm0.symm

theorem edge20_1 : Target (mutate (node 20) 1) ∨ IsFork (mutate (node 20) 1) 1 ∨ IsRoot (mutate (node 20) 1) 1 := by
  left
  have he : (mutate (node 20) 1) = relabel (node 22) perm2.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 20) 1) u v = (relabel (node 22) perm2.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 22) perm2.symm

theorem edge20_2 : Target (mutate (node 20) 2) ∨ IsFork (mutate (node 20) 2) 2 ∨ IsRoot (mutate (node 20) 2) 2 := by
  left
  have he : (mutate (node 20) 2) = relabel (node 32) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 20) 2) u v = (relabel (node 32) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 32) perm0.symm

theorem edge20_3 : Target (mutate (node 20) 3) ∨ IsFork (mutate (node 20) 3) 3 ∨ IsRoot (mutate (node 20) 3) 3 := by
  left
  have he : (mutate (node 20) 3) = relabel (node 10) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 20) 3) u v = (relabel (node 10) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 10) perm0.symm

theorem cyclic21 : ¬ Acyclic (node 21) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (by decide)
  have h1 := hr 1 3 (by decide)
  have h2 := hr 3 0 (by decide)
  omega

theorem edge21_0 : Target (mutate (node 21) 0) ∨ IsFork (mutate (node 21) 0) 0 ∨ IsRoot (mutate (node 21) 0) 0 := by
  left
  have he : (mutate (node 21) 0) = relabel (node 12) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 21) 0) u v = (relabel (node 12) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 12) perm0.symm

theorem edge21_1 : Target (mutate (node 21) 1) ∨ IsFork (mutate (node 21) 1) 1 ∨ IsRoot (mutate (node 21) 1) 1 := by
  left
  have he : (mutate (node 21) 1) = relabel (node 33) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 21) 1) u v = (relabel (node 33) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 33) perm0.symm

theorem edge21_2 : Target (mutate (node 21) 2) ∨ IsFork (mutate (node 21) 2) 2 ∨ IsRoot (mutate (node 21) 2) 2 := by
  left
  have he : (mutate (node 21) 2) = relabel (node 30) perm12.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 21) 2) u v = (relabel (node 30) perm12.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 30) perm12.symm

theorem edge21_3 : Target (mutate (node 21) 3) ∨ IsFork (mutate (node 21) 3) 3 ∨ IsRoot (mutate (node 21) 3) 3 := by
  right; right
  have he : relabel (reverse (mutate (node 21) 3)) perm19 = Regions.root (8) (63) (102) (8) (13) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 21) 3)) perm19) u v = (Regions.root (8) (63) (102) (8) (13) (1)) u v from by decide) u v
  have hf : IsRoot (relabel (reverse (mutate (node 21) 3)) perm19) 0 := by
    rw [he]
    exact IsRoot.basic (8) (63) (102) (8) (13) (1) (by unfold Regions.Domain; decide) (by decide)
  exact root_of_reverse (root_of_relabel perm19 hf)

theorem cyclic22 : ¬ Acyclic (node 22) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (by decide)
  have h1 := hr 1 2 (by decide)
  have h2 := hr 2 0 (by decide)
  omega

theorem edge22_0 : Target (mutate (node 22) 0) ∨ IsFork (mutate (node 22) 0) 0 ∨ IsRoot (mutate (node 22) 0) 0 := by
  left
  have he : (mutate (node 22) 0) = relabel (node 34) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 22) 0) u v = (relabel (node 34) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 34) perm0.symm

theorem edge22_1 : Target (mutate (node 22) 1) ∨ IsFork (mutate (node 22) 1) 1 ∨ IsRoot (mutate (node 22) 1) 1 := by
  left
  have he : (mutate (node 22) 1) = relabel (node 35) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 22) 1) u v = (relabel (node 35) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 35) perm0.symm

theorem edge22_2 : Target (mutate (node 22) 2) ∨ IsFork (mutate (node 22) 2) 2 ∨ IsRoot (mutate (node 22) 2) 2 := by
  left
  have he : (mutate (node 22) 2) = relabel (node 20) perm2.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 22) 2) u v = (relabel (node 20) perm2.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 20) perm2.symm

theorem edge22_3 : Target (mutate (node 22) 3) ∨ IsFork (mutate (node 22) 3) 3 ∨ IsRoot (mutate (node 22) 3) 3 := by
  left
  have he : (mutate (node 22) 3) = relabel (node 12) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 22) 3) u v = (relabel (node 12) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 12) perm0.symm

theorem cyclic23 : ¬ Acyclic (node 23) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (by decide)
  have h1 := hr 2 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge23_0 : Target (mutate (node 23) 0) ∨ IsFork (mutate (node 23) 0) 0 ∨ IsRoot (mutate (node 23) 0) 0 := by
  left
  have he : (mutate (node 23) 0) = relabel (node 36) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 23) 0) u v = (relabel (node 36) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 36) perm0.symm

theorem edge23_1 : Target (mutate (node 23) 1) ∨ IsFork (mutate (node 23) 1) 1 ∨ IsRoot (mutate (node 23) 1) 1 := by
  left
  have he : (mutate (node 23) 1) = relabel (node 14) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 23) 1) u v = (relabel (node 14) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 14) perm0.symm

theorem edge23_2 : Target (mutate (node 23) 2) ∨ IsFork (mutate (node 23) 2) 2 ∨ IsRoot (mutate (node 23) 2) 2 := by
  right; left
  have he : relabel (mutate (node 23) 2) perm14 = Forks.template (3) (2) (12) (5) (32) (3) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 23) 2) perm14) u v = (Forks.template (3) (2) (12) (5) (32) (3)) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 23) 2) perm14) 0 := by
    rw [he]
    exact IsFork.basic (3) (2) (12) (5) (32) (3) (by unfold Forks.Domain; decide)
  exact fork_of_relabel perm14 hf

theorem edge23_3 : Target (mutate (node 23) 3) ∨ IsFork (mutate (node 23) 3) 3 ∨ IsRoot (mutate (node 23) 3) 3 := by
  right; right
  have he : relabel (reverse (mutate (node 23) 3)) perm22 = Regions.root (12) (38) (45) (3) (4) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 23) 3)) perm22) u v = (Regions.root (12) (38) (45) (3) (4) (1)) u v from by decide) u v
  have hf : IsRoot (relabel (reverse (mutate (node 23) 3)) perm22) 0 := by
    rw [he]
    exact IsRoot.basic (12) (38) (45) (3) (4) (1) (by unfold Regions.Domain; decide) (by decide)
  exact root_of_reverse (root_of_relabel perm22 hf)

theorem cyclic24 : ¬ Acyclic (node 24) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (by decide)
  have h1 := hr 1 3 (by decide)
  have h2 := hr 3 0 (by decide)
  omega

theorem edge24_0 : Target (mutate (node 24) 0) ∨ IsFork (mutate (node 24) 0) 0 ∨ IsRoot (mutate (node 24) 0) 0 := by
  left
  have he : (mutate (node 24) 0) = relabel (node 37) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 24) 0) u v = (relabel (node 37) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 37) perm0.symm

theorem edge24_1 : Target (mutate (node 24) 1) ∨ IsFork (mutate (node 24) 1) 1 ∨ IsRoot (mutate (node 24) 1) 1 := by
  left
  have he : (mutate (node 24) 1) = relabel (node 15) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 24) 1) u v = (relabel (node 15) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 15) perm0.symm

theorem edge24_2 : Target (mutate (node 24) 2) ∨ IsFork (mutate (node 24) 2) 2 ∨ IsRoot (mutate (node 24) 2) 2 := by
  left
  have he : (mutate (node 24) 2) = relabel (node 36) perm8.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 24) 2) u v = (relabel (node 36) perm8.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 36) perm8.symm

theorem edge24_3 : Target (mutate (node 24) 3) ∨ IsFork (mutate (node 24) 3) 3 ∨ IsRoot (mutate (node 24) 3) 3 := by
  right; right
  have he : relabel (mutate (node 24) 3) perm21 = Regions.root (4) (27) (18) (7) (5) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 24) 3) perm21) u v = (Regions.root (4) (27) (18) (7) (5) (1)) u v from by decide) u v
  have hf : IsRoot (relabel (mutate (node 24) 3) perm21) 0 := by
    rw [he]
    exact IsRoot.basic (4) (27) (18) (7) (5) (1) (by unfold Regions.Domain; decide) (by decide)
  exact root_of_relabel perm21 hf

theorem cyclic25 : ¬ Acyclic (node 25) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (by decide)
  have h1 := hr 1 2 (by decide)
  have h2 := hr 2 0 (by decide)
  omega

theorem edge25_0 : Target (mutate (node 25) 0) ∨ IsFork (mutate (node 25) 0) 0 ∨ IsRoot (mutate (node 25) 0) 0 := by
  left
  have he : (mutate (node 25) 0) = relabel (node 16) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 25) 0) u v = (relabel (node 16) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 16) perm0.symm

theorem edge25_1 : Target (mutate (node 25) 1) ∨ IsFork (mutate (node 25) 1) 1 ∨ IsRoot (mutate (node 25) 1) 1 := by
  right; right
  have he : relabel (mutate (node 25) 1) perm6 = Regions.root (4) (19) (37) (5) (10) (0) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 25) 1) perm6) u v = (Regions.root (4) (19) (37) (5) (10) (0)) u v from by decide) u v
  have hf : IsRoot (relabel (mutate (node 25) 1) perm6) 0 := by
    rw [he]
    exact IsRoot.basic (4) (19) (37) (5) (10) (0) (by unfold Regions.Domain; decide) (by decide)
  exact root_of_relabel perm6 hf

theorem edge25_2 : Target (mutate (node 25) 2) ∨ IsFork (mutate (node 25) 2) 2 ∨ IsRoot (mutate (node 25) 2) 2 := by
  left
  have he : (mutate (node 25) 2) = relabel (node 28) perm14.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 25) 2) u v = (relabel (node 28) perm14.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 28) perm14.symm

theorem edge25_3 : Target (mutate (node 25) 3) ∨ IsFork (mutate (node 25) 3) 3 ∨ IsRoot (mutate (node 25) 3) 3 := by
  left
  have he : (mutate (node 25) 3) = relabel (zeroPhase 3 0) perm17.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 25) 3) u v = (relabel (zeroPhase 3 0) perm17.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.zero 3 0) perm17.symm

theorem cyclic26 : ¬ Acyclic (node 26) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (by decide)
  have h1 := hr 1 3 (by decide)
  have h2 := hr 3 0 (by decide)
  omega

theorem edge26_0 : Target (mutate (node 26) 0) ∨ IsFork (mutate (node 26) 0) 0 ∨ IsRoot (mutate (node 26) 0) 0 := by
  left
  have he : (mutate (node 26) 0) = relabel (node 38) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 26) 0) u v = (relabel (node 38) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 38) perm0.symm

theorem edge26_1 : Target (mutate (node 26) 1) ∨ IsFork (mutate (node 26) 1) 1 ∨ IsRoot (mutate (node 26) 1) 1 := by
  left
  have he : (mutate (node 26) 1) = relabel (node 16) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 26) 1) u v = (relabel (node 16) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 16) perm0.symm

theorem edge26_2 : Target (mutate (node 26) 2) ∨ IsFork (mutate (node 26) 2) 2 ∨ IsRoot (mutate (node 26) 2) 2 := by
  left
  have he : (mutate (node 26) 2) = relabel (node 29) perm2.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 26) 2) u v = (relabel (node 29) perm2.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 29) perm2.symm

theorem edge26_3 : Target (mutate (node 26) 3) ∨ IsFork (mutate (node 26) 3) 3 ∨ IsRoot (mutate (node 26) 3) 3 := by
  right; right
  have he : relabel (mutate (node 26) 3) perm20 = Regions.root (2) (6) (3) (5) (2) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 26) 3) perm20) u v = (Regions.root (2) (6) (3) (5) (2) (1)) u v from by decide) u v
  have hf : IsRoot (relabel (mutate (node 26) 3) perm20) 0 := by
    rw [he]
    exact IsRoot.basic (2) (6) (3) (5) (2) (1) (by unfold Regions.Domain; decide) (by decide)
  exact root_of_relabel perm20 hf

theorem cyclic27 : ¬ Acyclic (node 27) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge27_0 : Target (mutate (node 27) 0) ∨ IsFork (mutate (node 27) 0) 0 ∨ IsRoot (mutate (node 27) 0) 0 := by
  left
  have he : (mutate (node 27) 0) = relabel (node 39) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 27) 0) u v = (relabel (node 39) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 39) perm0.symm

theorem edge27_1 : Target (mutate (node 27) 1) ∨ IsFork (mutate (node 27) 1) 1 ∨ IsRoot (mutate (node 27) 1) 1 := by
  left
  have he : (mutate (node 27) 1) = relabel (node 17) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 27) 1) u v = (relabel (node 17) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 17) perm0.symm

theorem edge27_2 : Target (mutate (node 27) 2) ∨ IsFork (mutate (node 27) 2) 2 ∨ IsRoot (mutate (node 27) 2) 2 := by
  left
  have he : (mutate (node 27) 2) = relabel (node 40) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 27) 2) u v = (relabel (node 40) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 40) perm0.symm

theorem edge27_3 : Target (mutate (node 27) 3) ∨ IsFork (mutate (node 27) 3) 3 ∨ IsRoot (mutate (node 27) 3) 3 := by
  right; right
  have he : relabel (reverse (mutate (node 27) 3)) perm21 = Regions.root (10) (129) (366) (13) (37) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 27) 3)) perm21) u v = (Regions.root (10) (129) (366) (13) (37) (1)) u v from by decide) u v
  have hf : IsRoot (relabel (reverse (mutate (node 27) 3)) perm21) 0 := by
    rw [he]
    exact IsRoot.basic (10) (129) (366) (13) (37) (1) (by unfold Regions.Domain; decide) (by decide)
  exact root_of_reverse (root_of_relabel perm21 hf)

theorem cyclic28 : ¬ Acyclic (node 28) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (by decide)
  have h1 := hr 1 2 (by decide)
  have h2 := hr 2 0 (by decide)
  omega

theorem edge28_0 : Target (mutate (node 28) 0) ∨ IsFork (mutate (node 28) 0) 0 ∨ IsRoot (mutate (node 28) 0) 0 := by
  left
  have he : (mutate (node 28) 0) = relabel (node 25) perm14.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 28) 0) u v = (relabel (node 25) perm14.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 25) perm14.symm

theorem edge28_1 : Target (mutate (node 28) 1) ∨ IsFork (mutate (node 28) 1) 1 ∨ IsRoot (mutate (node 28) 1) 1 := by
  left
  have he : (mutate (node 28) 1) = relabel (node 41) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 28) 1) u v = (relabel (node 41) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 41) perm0.symm

theorem edge28_2 : Target (mutate (node 28) 2) ∨ IsFork (mutate (node 28) 2) 2 ∨ IsRoot (mutate (node 28) 2) 2 := by
  left
  have he : (mutate (node 28) 2) = relabel (node 17) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 28) 2) u v = (relabel (node 17) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 17) perm0.symm

theorem edge28_3 : Target (mutate (node 28) 3) ∨ IsFork (mutate (node 28) 3) 3 ∨ IsRoot (mutate (node 28) 3) 3 := by
  left
  have he : (mutate (node 28) 3) = relabel (zeroPhase 3 1) perm4.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 28) 3) u v = (relabel (zeroPhase 3 1) perm4.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.zero 3 1) perm4.symm

theorem cyclic29 : ¬ Acyclic (node 29) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (by decide)
  have h1 := hr 2 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge29_0 : Target (mutate (node 29) 0) ∨ IsFork (mutate (node 29) 0) 0 ∨ IsRoot (mutate (node 29) 0) 0 := by
  left
  have he : (mutate (node 29) 0) = relabel (node 42) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 29) 0) u v = (relabel (node 42) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 42) perm0.symm

theorem edge29_1 : Target (mutate (node 29) 1) ∨ IsFork (mutate (node 29) 1) 1 ∨ IsRoot (mutate (node 29) 1) 1 := by
  left
  have he : (mutate (node 29) 1) = relabel (node 26) perm2.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 29) 1) u v = (relabel (node 26) perm2.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 26) perm2.symm

theorem edge29_2 : Target (mutate (node 29) 2) ∨ IsFork (mutate (node 29) 2) 2 ∨ IsRoot (mutate (node 29) 2) 2 := by
  left
  have he : (mutate (node 29) 2) = relabel (node 18) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 29) 2) u v = (relabel (node 18) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 18) perm0.symm

theorem edge29_3 : Target (mutate (node 29) 3) ∨ IsFork (mutate (node 29) 3) 3 ∨ IsRoot (mutate (node 29) 3) 3 := by
  left
  have he : (mutate (node 29) 3) = reverse (relabel (zeroPhase 1 1) perm16.symm) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 29) 3) u v = (reverse (relabel (zeroPhase 1 1) perm16.symm)) u v from by decide) u v
  rw [he]; exact Target.reversed (Target.framed (Target.zero 1 1) perm16.symm)

theorem cyclic30 : ¬ Acyclic (node 30) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (by decide)
  have h1 := hr 2 3 (by decide)
  have h2 := hr 3 0 (by decide)
  omega

theorem edge30_0 : Target (mutate (node 30) 0) ∨ IsFork (mutate (node 30) 0) 0 ∨ IsRoot (mutate (node 30) 0) 0 := by
  left
  have he : (mutate (node 30) 0) = relabel (node 21) perm8.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 30) 0) u v = (relabel (node 21) perm8.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 21) perm8.symm

theorem edge30_1 : Target (mutate (node 30) 1) ∨ IsFork (mutate (node 30) 1) 1 ∨ IsRoot (mutate (node 30) 1) 1 := by
  left
  have he : (mutate (node 30) 1) = relabel (node 19) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 30) 1) u v = (relabel (node 19) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 19) perm0.symm

theorem edge30_2 : Target (mutate (node 30) 2) ∨ IsFork (mutate (node 30) 2) 2 ∨ IsRoot (mutate (node 30) 2) 2 := by
  left
  have he : (mutate (node 30) 2) = relabel (node 43) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 30) 2) u v = (relabel (node 43) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 43) perm0.symm

theorem edge30_3 : Target (mutate (node 30) 3) ∨ IsFork (mutate (node 30) 3) 3 ∨ IsRoot (mutate (node 30) 3) 3 := by
  left
  have he : (mutate (node 30) 3) = relabel (zeroPhase 2 1) perm11.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 30) 3) u v = (relabel (zeroPhase 2 1) perm11.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.zero 2 1) perm11.symm

theorem cyclic31 : ¬ Acyclic (node 31) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge31_0 : Target (mutate (node 31) 0) ∨ IsFork (mutate (node 31) 0) 0 ∨ IsRoot (mutate (node 31) 0) 0 := by
  left
  have he : (mutate (node 31) 0) = relabel (node 20) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 31) 0) u v = (relabel (node 20) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 20) perm0.symm

theorem edge31_1 : Target (mutate (node 31) 1) ∨ IsFork (mutate (node 31) 1) 1 ∨ IsRoot (mutate (node 31) 1) 1 := by
  left
  have he : (mutate (node 31) 1) = relabel (node 44) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 31) 1) u v = (relabel (node 44) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 44) perm0.symm

theorem edge31_2 : Target (mutate (node 31) 2) ∨ IsFork (mutate (node 31) 2) 2 ∨ IsRoot (mutate (node 31) 2) 2 := by
  left
  have he : (mutate (node 31) 2) = relabel (node 45) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 31) 2) u v = (relabel (node 45) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 45) perm0.symm

theorem edge31_3 : Target (mutate (node 31) 3) ∨ IsFork (mutate (node 31) 3) 3 ∨ IsRoot (mutate (node 31) 3) 3 := by
  right; right
  have he : relabel (mutate (node 31) 3) perm18 = Regions.root (8) (63) (1299) (8) (165) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 31) 3) perm18) u v = (Regions.root (8) (63) (1299) (8) (165) (1)) u v from by decide) u v
  have hf : IsRoot (relabel (mutate (node 31) 3) perm18) 0 := by
    rw [he]
    exact IsRoot.basic (8) (63) (1299) (8) (165) (1) (by unfold Regions.Domain; decide) (by decide)
  exact root_of_relabel perm18 hf

theorem cyclic32 : ¬ Acyclic (node 32) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 2 (by decide)
  have h2 := hr 2 0 (by decide)
  omega

theorem edge32_0 : Target (mutate (node 32) 0) ∨ IsFork (mutate (node 32) 0) 0 ∨ IsRoot (mutate (node 32) 0) 0 := by
  left
  have he : (mutate (node 32) 0) = relabel (node 46) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 32) 0) u v = (relabel (node 46) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 46) perm0.symm

theorem edge32_1 : Target (mutate (node 32) 1) ∨ IsFork (mutate (node 32) 1) 1 ∨ IsRoot (mutate (node 32) 1) 1 := by
  left
  have he : (mutate (node 32) 1) = relabel (node 47) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 32) 1) u v = (relabel (node 47) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 47) perm0.symm

theorem edge32_2 : Target (mutate (node 32) 2) ∨ IsFork (mutate (node 32) 2) 2 ∨ IsRoot (mutate (node 32) 2) 2 := by
  left
  have he : (mutate (node 32) 2) = relabel (node 20) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 32) 2) u v = (relabel (node 20) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 20) perm0.symm

theorem edge32_3 : Target (mutate (node 32) 3) ∨ IsFork (mutate (node 32) 3) 3 ∨ IsRoot (mutate (node 32) 3) 3 := by
  right; right
  have he : relabel (reverse (mutate (node 32) 3)) perm23 = Regions.root (3) (8) (144) (3) (55) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 32) 3)) perm23) u v = (Regions.root (3) (8) (144) (3) (55) (1)) u v from by decide) u v
  have hf : IsRoot (relabel (reverse (mutate (node 32) 3)) perm23) 0 := by
    rw [he]
    exact IsRoot.basic (3) (8) (144) (3) (55) (1) (by unfold Regions.Domain; decide) (by decide)
  exact root_of_reverse (root_of_relabel perm23 hf)

theorem cyclic33 : ¬ Acyclic (node 33) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (by decide)
  have h1 := hr 2 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge33_0 : Target (mutate (node 33) 0) ∨ IsFork (mutate (node 33) 0) 0 ∨ IsRoot (mutate (node 33) 0) 0 := by
  right; left
  have he : relabel (reverse (mutate (node 33) 0)) perm1 = Forks.template (2) (18) (3) (23) (5) (8) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 33) 0)) perm1) u v = (Forks.template (2) (18) (3) (23) (5) (8)) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 33) 0)) perm1) 0 := by
    rw [he]
    exact IsFork.basic (2) (18) (3) (23) (5) (8) (by unfold Forks.Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm1 hf)

theorem edge33_1 : Target (mutate (node 33) 1) ∨ IsFork (mutate (node 33) 1) 1 ∨ IsRoot (mutate (node 33) 1) 1 := by
  left
  have he : (mutate (node 33) 1) = relabel (node 21) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 33) 1) u v = (relabel (node 21) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 21) perm0.symm

theorem edge33_2 : Target (mutate (node 33) 2) ∨ IsFork (mutate (node 33) 2) 2 ∨ IsRoot (mutate (node 33) 2) 2 := by
  left
  have he : (mutate (node 33) 2) = relabel (node 48) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 33) 2) u v = (relabel (node 48) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 48) perm0.symm

theorem edge33_3 : Target (mutate (node 33) 3) ∨ IsFork (mutate (node 33) 3) 3 ∨ IsRoot (mutate (node 33) 3) 3 := by
  right; left
  have he : relabel (mutate (node 33) 3) perm20 = Forks.template (13) (18) (8) (232) (105) (3) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 33) 3) perm20) u v = (Forks.template (13) (18) (8) (232) (105) (3)) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 33) 3) perm20) 0 := by
    rw [he]
    exact IsFork.basic (13) (18) (8) (232) (105) (3) (by unfold Forks.Domain; decide)
  exact fork_of_relabel perm20 hf

theorem cyclic34 : ¬ Acyclic (node 34) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (by decide)
  have h1 := hr 2 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge34_0 : Target (mutate (node 34) 0) ∨ IsFork (mutate (node 34) 0) 0 ∨ IsRoot (mutate (node 34) 0) 0 := by
  left
  have he : (mutate (node 34) 0) = relabel (node 22) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 34) 0) u v = (relabel (node 22) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 22) perm0.symm

theorem edge34_1 : Target (mutate (node 34) 1) ∨ IsFork (mutate (node 34) 1) 1 ∨ IsRoot (mutate (node 34) 1) 1 := by
  right; right
  have he : relabel (reverse (mutate (node 34) 1)) perm6 = Regions.root (22) (461) (3798) (21) (173) (0) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 34) 1)) perm6) u v = (Regions.root (22) (461) (3798) (21) (173) (0)) u v from by decide) u v
  have hf : IsRoot (relabel (reverse (mutate (node 34) 1)) perm6) 0 := by
    rw [he]
    exact IsRoot.basic (22) (461) (3798) (21) (173) (0) (by unfold Regions.Domain; decide) (by decide)
  exact root_of_reverse (root_of_relabel perm6 hf)

theorem edge34_2 : Target (mutate (node 34) 2) ∨ IsFork (mutate (node 34) 2) 2 ∨ IsRoot (mutate (node 34) 2) 2 := by
  left
  have he : (mutate (node 34) 2) = relabel (node 44) perm12.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 34) 2) u v = (relabel (node 44) perm12.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 44) perm12.symm

theorem edge34_3 : Target (mutate (node 34) 3) ∨ IsFork (mutate (node 34) 3) 3 ∨ IsRoot (mutate (node 34) 3) 3 := by
  left
  have he : (mutate (node 34) 3) = reverse (relabel (zeroPhase 4 0) perm17.symm) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 34) 3) u v = (reverse (relabel (zeroPhase 4 0) perm17.symm)) u v from by decide) u v
  rw [he]; exact Target.reversed (Target.framed (Target.zero 4 0) perm17.symm)

theorem cyclic35 : ¬ Acyclic (node 35) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (by decide)
  have h1 := hr 2 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge35_0 : Target (mutate (node 35) 0) ∨ IsFork (mutate (node 35) 0) 0 ∨ IsRoot (mutate (node 35) 0) 0 := by
  right; right
  have he : relabel (mutate (node 35) 0) perm0 = Regions.root (22) (461) (1273) (21) (58) (0) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 35) 0) perm0) u v = (Regions.root (22) (461) (1273) (21) (58) (0)) u v from by decide) u v
  have hf : IsRoot (relabel (mutate (node 35) 0) perm0) 0 := by
    rw [he]
    exact IsRoot.basic (22) (461) (1273) (21) (58) (0) (by unfold Regions.Domain; decide) (by decide)
  exact root_of_relabel perm0 hf

theorem edge35_1 : Target (mutate (node 35) 1) ∨ IsFork (mutate (node 35) 1) 1 ∨ IsRoot (mutate (node 35) 1) 1 := by
  left
  have he : (mutate (node 35) 1) = relabel (node 22) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 35) 1) u v = (relabel (node 22) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 22) perm0.symm

theorem edge35_2 : Target (mutate (node 35) 2) ∨ IsFork (mutate (node 35) 2) 2 ∨ IsRoot (mutate (node 35) 2) 2 := by
  left
  have he : (mutate (node 35) 2) = relabel (node 47) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 35) 2) u v = (relabel (node 47) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 47) perm0.symm

theorem edge35_3 : Target (mutate (node 35) 3) ∨ IsFork (mutate (node 35) 3) 3 ∨ IsRoot (mutate (node 35) 3) 3 := by
  left
  have he : (mutate (node 35) 3) = relabel (zeroPhase 5 0) perm16.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 35) 3) u v = (relabel (zeroPhase 5 0) perm16.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.zero 5 0) perm16.symm

theorem cyclic36 : ¬ Acyclic (node 36) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (by decide)
  have h1 := hr 1 3 (by decide)
  have h2 := hr 3 0 (by decide)
  omega

theorem edge36_0 : Target (mutate (node 36) 0) ∨ IsFork (mutate (node 36) 0) 0 ∨ IsRoot (mutate (node 36) 0) 0 := by
  left
  have he : (mutate (node 36) 0) = relabel (node 23) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 36) 0) u v = (relabel (node 23) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 23) perm0.symm

theorem edge36_1 : Target (mutate (node 36) 1) ∨ IsFork (mutate (node 36) 1) 1 ∨ IsRoot (mutate (node 36) 1) 1 := by
  left
  have he : (mutate (node 36) 1) = relabel (node 24) perm12.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 36) 1) u v = (relabel (node 24) perm12.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 24) perm12.symm

theorem edge36_2 : Target (mutate (node 36) 2) ∨ IsFork (mutate (node 36) 2) 2 ∨ IsRoot (mutate (node 36) 2) 2 := by
  left
  have he : (mutate (node 36) 2) = relabel (node 49) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 36) 2) u v = (relabel (node 49) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 49) perm0.symm

theorem edge36_3 : Target (mutate (node 36) 3) ∨ IsFork (mutate (node 36) 3) 3 ∨ IsRoot (mutate (node 36) 3) 3 := by
  right; left
  have he : relabel (reverse (mutate (node 36) 3)) perm20 = Forks.template (7) (3) (12) (20) (83) (2) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 36) 3)) perm20) u v = (Forks.template (7) (3) (12) (20) (83) (2)) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 36) 3)) perm20) 0 := by
    rw [he]
    exact IsFork.basic (7) (3) (12) (20) (83) (2) (by unfold Forks.Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm20 hf)

theorem cyclic37 : ¬ Acyclic (node 37) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (by decide)
  have h1 := hr 2 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge37_0 : Target (mutate (node 37) 0) ∨ IsFork (mutate (node 37) 0) 0 ∨ IsRoot (mutate (node 37) 0) 0 := by
  left
  have he : (mutate (node 37) 0) = relabel (node 24) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 37) 0) u v = (relabel (node 24) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 24) perm0.symm

theorem edge37_1 : Target (mutate (node 37) 1) ∨ IsFork (mutate (node 37) 1) 1 ∨ IsRoot (mutate (node 37) 1) 1 := by
  right; left
  have he : relabel (mutate (node 37) 1) perm7 = Forks.template (2) (6) (3) (7) (5) (7) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 37) 1) perm7) u v = (Forks.template (2) (6) (3) (7) (5) (7)) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 37) 1) perm7) 0 := by
    rw [he]
    exact IsFork.basic (2) (6) (3) (7) (5) (7) (by unfold Forks.Domain; decide)
  exact fork_of_relabel perm7 hf

theorem edge37_2 : Target (mutate (node 37) 2) ∨ IsFork (mutate (node 37) 2) 2 ∨ IsRoot (mutate (node 37) 2) 2 := by
  left
  have he : (mutate (node 37) 2) = relabel (node 50) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 37) 2) u v = (relabel (node 50) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 50) perm0.symm

theorem edge37_3 : Target (mutate (node 37) 3) ∨ IsFork (mutate (node 37) 3) 3 ∨ IsRoot (mutate (node 37) 3) 3 := by
  right; left
  have he : relabel (reverse (mutate (node 37) 3)) perm18 = Forks.template (5) (6) (7) (28) (36) (3) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 37) 3)) perm18) u v = (Forks.template (5) (6) (7) (28) (36) (3)) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 37) 3)) perm18) 0 := by
    rw [he]
    exact IsFork.basic (5) (6) (7) (28) (36) (3) (by unfold Forks.Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm18 hf)

theorem cyclic38 : ¬ Acyclic (node 38) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge38_0 : Target (mutate (node 38) 0) ∨ IsFork (mutate (node 38) 0) 0 ∨ IsRoot (mutate (node 38) 0) 0 := by
  left
  have he : (mutate (node 38) 0) = relabel (node 26) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 38) 0) u v = (relabel (node 26) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 26) perm0.symm

theorem edge38_1 : Target (mutate (node 38) 1) ∨ IsFork (mutate (node 38) 1) 1 ∨ IsRoot (mutate (node 38) 1) 1 := by
  left
  have he : (mutate (node 38) 1) = relabel (node 51) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 38) 1) u v = (relabel (node 51) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 51) perm0.symm

theorem edge38_2 : Target (mutate (node 38) 2) ∨ IsFork (mutate (node 38) 2) 2 ∨ IsRoot (mutate (node 38) 2) 2 := by
  left
  have he : (mutate (node 38) 2) = relabel (node 52) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 38) 2) u v = (relabel (node 52) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 52) perm0.symm

theorem edge38_3 : Target (mutate (node 38) 3) ∨ IsFork (mutate (node 38) 3) 3 ∨ IsRoot (mutate (node 38) 3) 3 := by
  right; right
  have he : relabel (mutate (node 38) 3) perm19 = Regions.root (5) (34) (86) (7) (18) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 38) 3) perm19) u v = (Regions.root (5) (34) (86) (7) (18) (1)) u v from by decide) u v
  have hf : IsRoot (relabel (mutate (node 38) 3) perm19) 0 := by
    rw [he]
    exact IsRoot.basic (5) (34) (86) (7) (18) (1) (by unfold Regions.Domain; decide) (by decide)
  exact root_of_relabel perm19 hf

theorem cyclic39 : ¬ Acyclic (node 39) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (by decide)
  have h1 := hr 1 2 (by decide)
  have h2 := hr 2 0 (by decide)
  omega

theorem edge39_0 : Target (mutate (node 39) 0) ∨ IsFork (mutate (node 39) 0) 0 ∨ IsRoot (mutate (node 39) 0) 0 := by
  left
  have he : (mutate (node 39) 0) = relabel (node 27) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 39) 0) u v = (relabel (node 27) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 27) perm0.symm

theorem edge39_1 : Target (mutate (node 39) 1) ∨ IsFork (mutate (node 39) 1) 1 ∨ IsRoot (mutate (node 39) 1) 1 := by
  right; left
  have he : relabel (reverse (mutate (node 39) 1)) perm7 = Forks.template (4) (138) (5) (515) (19) (13) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 39) 1)) perm7) u v = (Forks.template (4) (138) (5) (515) (19) (13)) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 39) 1)) perm7) 0 := by
    rw [he]
    exact IsFork.basic (4) (138) (5) (515) (19) (13) (by unfold Forks.Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm7 hf)

theorem edge39_2 : Target (mutate (node 39) 2) ∨ IsFork (mutate (node 39) 2) 2 ∨ IsRoot (mutate (node 39) 2) 2 := by
  left
  have he : (mutate (node 39) 2) = relabel (node 53) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 39) 2) u v = (relabel (node 53) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 53) perm0.symm

theorem edge39_3 : Target (mutate (node 39) 3) ∨ IsFork (mutate (node 39) 3) 3 ∨ IsRoot (mutate (node 39) 3) 3 := by
  right; left
  have he : relabel (mutate (node 39) 3) perm18 = Forks.template (37) (138) (13) (5102) (482) (5) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 39) 3) perm18) u v = (Forks.template (37) (138) (13) (5102) (482) (5)) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 39) 3) perm18) 0 := by
    rw [he]
    exact IsFork.basic (37) (138) (13) (5102) (482) (5) (by unfold Forks.Domain; decide)
  exact fork_of_relabel perm18 hf

theorem cyclic40 : ¬ Acyclic (node 40) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 2 (by decide)
  have h2 := hr 2 0 (by decide)
  omega

theorem edge40_0 : Target (mutate (node 40) 0) ∨ IsFork (mutate (node 40) 0) 0 ∨ IsRoot (mutate (node 40) 0) 0 := by
  left
  have he : (mutate (node 40) 0) = relabel (node 54) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 40) 0) u v = (relabel (node 54) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 54) perm0.symm

theorem edge40_1 : Target (mutate (node 40) 1) ∨ IsFork (mutate (node 40) 1) 1 ∨ IsRoot (mutate (node 40) 1) 1 := by
  left
  have he : (mutate (node 40) 1) = relabel (node 41) perm2.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 40) 1) u v = (relabel (node 41) perm2.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 41) perm2.symm

theorem edge40_2 : Target (mutate (node 40) 2) ∨ IsFork (mutate (node 40) 2) 2 ∨ IsRoot (mutate (node 40) 2) 2 := by
  left
  have he : (mutate (node 40) 2) = relabel (node 27) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 40) 2) u v = (relabel (node 27) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 27) perm0.symm

theorem edge40_3 : Target (mutate (node 40) 3) ∨ IsFork (mutate (node 40) 3) 3 ∨ IsRoot (mutate (node 40) 3) 3 := by
  right; left
  have he : relabel (mutate (node 40) 3) perm23 = Forks.template (13) (3) (50) (38) (649) (4) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 40) 3) perm23) u v = (Forks.template (13) (3) (50) (38) (649) (4)) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 40) 3) perm23) 0 := by
    rw [he]
    exact IsFork.basic (13) (3) (50) (38) (649) (4) (by unfold Forks.Domain; decide)
  exact fork_of_relabel perm23 hf

theorem cyclic41 : ¬ Acyclic (node 41) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (by decide)
  have h1 := hr 2 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge41_0 : Target (mutate (node 41) 0) ∨ IsFork (mutate (node 41) 0) 0 ∨ IsRoot (mutate (node 41) 0) 0 := by
  right; left
  have he : relabel (reverse (mutate (node 41) 0)) perm0 = Forks.template (5) (4) (50) (19) (240) (3) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 41) 0)) perm0) u v = (Forks.template (5) (4) (50) (19) (240) (3)) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 41) 0)) perm0) 0 := by
    rw [he]
    exact IsFork.basic (5) (4) (50) (19) (240) (3) (by unfold Forks.Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm0 hf)

theorem edge41_1 : Target (mutate (node 41) 1) ∨ IsFork (mutate (node 41) 1) 1 ∨ IsRoot (mutate (node 41) 1) 1 := by
  left
  have he : (mutate (node 41) 1) = relabel (node 28) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 41) 1) u v = (relabel (node 28) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 28) perm0.symm

theorem edge41_2 : Target (mutate (node 41) 2) ∨ IsFork (mutate (node 41) 2) 2 ∨ IsRoot (mutate (node 41) 2) 2 := by
  left
  have he : (mutate (node 41) 2) = relabel (node 40) perm2.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 41) 2) u v = (relabel (node 40) perm2.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 40) perm2.symm

theorem edge41_3 : Target (mutate (node 41) 3) ∨ IsFork (mutate (node 41) 3) 3 ∨ IsRoot (mutate (node 41) 3) 3 := by
  right; right
  have he : relabel (mutate (node 41) 3) perm19 = Regions.root (50) (154) (495) (3) (10) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 41) 3) perm19) u v = (Regions.root (50) (154) (495) (3) (10) (1)) u v from by decide) u v
  have hf : IsRoot (relabel (mutate (node 41) 3) perm19) 0 := by
    rw [he]
    exact IsRoot.basic (50) (154) (495) (3) (10) (1) (by unfold Regions.Domain; decide) (by decide)
  exact root_of_relabel perm19 hf

theorem cyclic42 : ¬ Acyclic (node 42) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (by decide)
  have h1 := hr 1 2 (by decide)
  have h2 := hr 2 0 (by decide)
  omega

theorem edge42_0 : Target (mutate (node 42) 0) ∨ IsFork (mutate (node 42) 0) 0 ∨ IsRoot (mutate (node 42) 0) 0 := by
  left
  have he : (mutate (node 42) 0) = relabel (node 29) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 42) 0) u v = (relabel (node 29) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 29) perm0.symm

theorem edge42_1 : Target (mutate (node 42) 1) ∨ IsFork (mutate (node 42) 1) 1 ∨ IsRoot (mutate (node 42) 1) 1 := by
  left
  have he : (mutate (node 42) 1) = relabel (node 52) perm8.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 42) 1) u v = (relabel (node 52) perm8.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 52) perm8.symm

theorem edge42_2 : Target (mutate (node 42) 2) ∨ IsFork (mutate (node 42) 2) 2 ∨ IsRoot (mutate (node 42) 2) 2 := by
  right; left
  have he : relabel (mutate (node 42) 2) perm12 = Forks.template (5) (4) (25) (19) (120) (2) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 42) 2) perm12) u v = (Forks.template (5) (4) (25) (19) (120) (2)) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 42) 2) perm12) 0 := by
    rw [he]
    exact IsFork.basic (5) (4) (25) (19) (120) (2) (by unfold Forks.Domain; decide)
  exact fork_of_relabel perm12 hf

theorem edge42_3 : Target (mutate (node 42) 3) ∨ IsFork (mutate (node 42) 3) 3 ∨ IsRoot (mutate (node 42) 3) 3 := by
  right; right
  have he : relabel (reverse (mutate (node 42) 3)) perm23 = Regions.root (25) (54) (120) (2) (5) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 42) 3)) perm23) u v = (Regions.root (25) (54) (120) (2) (5) (1)) u v from by decide) u v
  have hf : IsRoot (relabel (reverse (mutate (node 42) 3)) perm23) 0 := by
    rw [he]
    exact IsRoot.basic (25) (54) (120) (2) (5) (1) (by unfold Regions.Domain; decide) (by decide)
  exact root_of_reverse (root_of_relabel perm23 hf)

theorem cyclic43 : ¬ Acyclic (node 43) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 2 (by decide)
  have h2 := hr 2 0 (by decide)
  omega

theorem edge43_0 : Target (mutate (node 43) 0) ∨ IsFork (mutate (node 43) 0) 0 ∨ IsRoot (mutate (node 43) 0) 0 := by
  left
  have he : (mutate (node 43) 0) = relabel (node 48) perm6.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 43) 0) u v = (relabel (node 48) perm6.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 48) perm6.symm

theorem edge43_1 : Target (mutate (node 43) 1) ∨ IsFork (mutate (node 43) 1) 1 ∨ IsRoot (mutate (node 43) 1) 1 := by
  left
  have he : (mutate (node 43) 1) = relabel (stripPhase 0 1) perm6.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 43) 1) u v = (relabel (stripPhase 0 1) perm6.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.strip 0 1) perm6.symm

theorem edge43_2 : Target (mutate (node 43) 2) ∨ IsFork (mutate (node 43) 2) 2 ∨ IsRoot (mutate (node 43) 2) 2 := by
  left
  have he : (mutate (node 43) 2) = relabel (node 30) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 43) 2) u v = (relabel (node 30) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 30) perm0.symm

theorem edge43_3 : Target (mutate (node 43) 3) ∨ IsFork (mutate (node 43) 3) 3 ∨ IsRoot (mutate (node 43) 3) 3 := by
  right; right
  have he : relabel (reverse (mutate (node 43) 3)) perm23 = Regions.root (21) (880) (272) (42) (13) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 43) 3)) perm23) u v = (Regions.root (21) (880) (272) (42) (13) (1)) u v from by decide) u v
  have hf : IsRoot (relabel (reverse (mutate (node 43) 3)) perm23) 0 := by
    rw [he]
    exact IsRoot.basic (21) (880) (272) (42) (13) (1) (by unfold Regions.Domain; decide) (by decide)
  exact root_of_reverse (root_of_relabel perm23 hf)

theorem cyclic44 : ¬ Acyclic (node 44) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 1 3 (by decide)
  have h1 := hr 3 2 (by decide)
  have h2 := hr 2 1 (by decide)
  omega

theorem edge44_0 : Target (mutate (node 44) 0) ∨ IsFork (mutate (node 44) 0) 0 ∨ IsRoot (mutate (node 44) 0) 0 := by
  left
  have he : (mutate (node 44) 0) = relabel (node 34) perm8.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 44) 0) u v = (relabel (node 34) perm8.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 34) perm8.symm

theorem edge44_1 : Target (mutate (node 44) 1) ∨ IsFork (mutate (node 44) 1) 1 ∨ IsRoot (mutate (node 44) 1) 1 := by
  left
  have he : (mutate (node 44) 1) = relabel (node 31) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 44) 1) u v = (relabel (node 31) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 31) perm0.symm

theorem edge44_2 : Target (mutate (node 44) 2) ∨ IsFork (mutate (node 44) 2) 2 ∨ IsRoot (mutate (node 44) 2) 2 := by
  left
  have he : (mutate (node 44) 2) = relabel (node 56) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 44) 2) u v = (relabel (node 56) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 56) perm0.symm

theorem edge44_3 : Target (mutate (node 44) 3) ∨ IsFork (mutate (node 44) 3) 3 ∨ IsRoot (mutate (node 44) 3) 3 := by
  left
  have he : (mutate (node 44) 3) = reverse (relabel (zeroPhase 4 1) perm5.symm) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 44) 3) u v = (reverse (relabel (zeroPhase 4 1) perm5.symm)) u v from by decide) u v
  rw [he]; exact Target.reversed (Target.framed (Target.zero 4 1) perm5.symm)

theorem cyclic45 : ¬ Acyclic (node 45) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (by decide)
  have h1 := hr 2 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge45_0 : Target (mutate (node 45) 0) ∨ IsFork (mutate (node 45) 0) 0 ∨ IsRoot (mutate (node 45) 0) 0 := by
  right; left
  have he : relabel (mutate (node 45) 0) perm3 = Forks.template (21) (3457) (22) (72432) (461) (8) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 45) 0) perm3) u v = (Forks.template (21) (3457) (22) (72432) (461) (8)) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 45) 0) perm3) 0 := by
    rw [he]
    exact IsFork.basic (21) (3457) (22) (72432) (461) (8) (by unfold Forks.Domain; decide)
  exact fork_of_relabel perm3 hf

theorem edge45_1 : Target (mutate (node 45) 1) ∨ IsFork (mutate (node 45) 1) 1 ∨ IsRoot (mutate (node 45) 1) 1 := by
  left
  have he : (mutate (node 45) 1) = relabel (node 57) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 45) 1) u v = (relabel (node 57) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 57) perm0.symm

theorem edge45_2 : Target (mutate (node 45) 2) ∨ IsFork (mutate (node 45) 2) 2 ∨ IsRoot (mutate (node 45) 2) 2 := by
  left
  have he : (mutate (node 45) 2) = relabel (node 31) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 45) 2) u v = (relabel (node 31) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 31) perm0.symm

theorem edge45_3 : Target (mutate (node 45) 3) ∨ IsFork (mutate (node 45) 3) 3 ∨ IsRoot (mutate (node 45) 3) 3 := by
  right; left
  have he : relabel (reverse (mutate (node 45) 3)) perm22 = Forks.template (165) (3457) (8) (570384) (1321) (22) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 45) 3)) perm22) u v = (Forks.template (165) (3457) (8) (570384) (1321) (22)) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 45) 3)) perm22) 0 := by
    rw [he]
    exact IsFork.basic (165) (3457) (8) (570384) (1321) (22) (by unfold Forks.Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm22 hf)

theorem cyclic46 : ¬ Acyclic (node 46) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (by decide)
  have h1 := hr 2 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge46_0 : Target (mutate (node 46) 0) ∨ IsFork (mutate (node 46) 0) 0 ∨ IsRoot (mutate (node 46) 0) 0 := by
  left
  have he : (mutate (node 46) 0) = relabel (node 32) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 46) 0) u v = (relabel (node 32) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 32) perm0.symm

theorem edge46_1 : Target (mutate (node 46) 1) ∨ IsFork (mutate (node 46) 1) 1 ∨ IsRoot (mutate (node 46) 1) 1 := by
  left
  have he : (mutate (node 46) 1) = relabel (node 58) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 46) 1) u v = (relabel (node 58) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 58) perm0.symm

theorem edge46_2 : Target (mutate (node 46) 2) ∨ IsFork (mutate (node 46) 2) 2 ∨ IsRoot (mutate (node 46) 2) 2 := by
  right; left
  have he : relabel (reverse (mutate (node 46) 2)) perm13 = Forks.template (21) (1152) (22) (24137) (461) (3) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 46) 2)) perm13) u v = (Forks.template (21) (1152) (22) (24137) (461) (3)) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 46) 2)) perm13) 0 := by
    rw [he]
    exact IsFork.basic (21) (1152) (22) (24137) (461) (3) (by unfold Forks.Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm13 hf)

theorem edge46_3 : Target (mutate (node 46) 3) ∨ IsFork (mutate (node 46) 3) 3 ∨ IsRoot (mutate (node 46) 3) 3 := by
  right; left
  have he : relabel (mutate (node 46) 3) perm19 = Forks.template (55) (1152) (3) (63339) (166) (22) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 46) 3) perm19) u v = (Forks.template (55) (1152) (3) (63339) (166) (22)) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 46) 3) perm19) 0 := by
    rw [he]
    exact IsFork.basic (55) (1152) (3) (63339) (166) (22) (by unfold Forks.Domain; decide)
  exact fork_of_relabel perm19 hf

theorem cyclic47 : ¬ Acyclic (node 47) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge47_0 : Target (mutate (node 47) 0) ∨ IsFork (mutate (node 47) 0) 0 ∨ IsRoot (mutate (node 47) 0) 0 := by
  left
  have he : (mutate (node 47) 0) = relabel (node 59) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 47) 0) u v = (relabel (node 59) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 59) perm0.symm

theorem edge47_1 : Target (mutate (node 47) 1) ∨ IsFork (mutate (node 47) 1) 1 ∨ IsRoot (mutate (node 47) 1) 1 := by
  left
  have he : (mutate (node 47) 1) = relabel (node 32) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 47) 1) u v = (relabel (node 32) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 32) perm0.symm

theorem edge47_2 : Target (mutate (node 47) 2) ∨ IsFork (mutate (node 47) 2) 2 ∨ IsRoot (mutate (node 47) 2) 2 := by
  left
  have he : (mutate (node 47) 2) = relabel (node 35) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 47) 2) u v = (relabel (node 35) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 35) perm0.symm

theorem edge47_3 : Target (mutate (node 47) 3) ∨ IsFork (mutate (node 47) 3) 3 ∨ IsRoot (mutate (node 47) 3) 3 := by
  left
  have he : (mutate (node 47) 3) = relabel (zeroPhase 5 1) perm16.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 47) 3) u v = (relabel (zeroPhase 5 1) perm16.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.zero 5 1) perm16.symm

theorem cyclic48 : ¬ Acyclic (node 48) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (by decide)
  have h1 := hr 1 2 (by decide)
  have h2 := hr 2 0 (by decide)
  omega

theorem edge48_0 : Target (mutate (node 48) 0) ∨ IsFork (mutate (node 48) 0) 0 ∨ IsRoot (mutate (node 48) 0) 0 := by
  left
  have he : (mutate (node 48) 0) = relabel (node 55) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 48) 0) u v = (relabel (node 55) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 55) perm0.symm

theorem edge48_1 : Target (mutate (node 48) 1) ∨ IsFork (mutate (node 48) 1) 1 ∨ IsRoot (mutate (node 48) 1) 1 := by
  left
  have he : (mutate (node 48) 1) = relabel (node 43) perm6.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 48) 1) u v = (relabel (node 43) perm6.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 43) perm6.symm

theorem edge48_2 : Target (mutate (node 48) 2) ∨ IsFork (mutate (node 48) 2) 2 ∨ IsRoot (mutate (node 48) 2) 2 := by
  left
  have he : (mutate (node 48) 2) = relabel (node 33) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 48) 2) u v = (relabel (node 33) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 33) perm0.symm

theorem edge48_3 : Target (mutate (node 48) 3) ∨ IsFork (mutate (node 48) 3) 3 ∨ IsRoot (mutate (node 48) 3) 3 := by
  right; right
  have he : relabel (mutate (node 48) 3) perm18 = Regions.root (42) (547) (333) (13) (8) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 48) 3) perm18) u v = (Regions.root (42) (547) (333) (13) (8) (1)) u v from by decide) u v
  have hf : IsRoot (relabel (mutate (node 48) 3) perm18) 0 := by
    rw [he]
    exact IsRoot.basic (42) (547) (333) (13) (8) (1) (by unfold Regions.Domain; decide) (by decide)
  exact root_of_relabel perm18 hf

theorem cyclic49 : ¬ Acyclic (node 49) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (by decide)
  have h1 := hr 2 3 (by decide)
  have h2 := hr 3 0 (by decide)
  omega

theorem edge49_0 : Target (mutate (node 49) 0) ∨ IsFork (mutate (node 49) 0) 0 ∨ IsRoot (mutate (node 49) 0) 0 := by
  left
  have he : (mutate (node 49) 0) = reverse (relabel (stripPhase 1 1) perm0.symm) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 49) 0) u v = (reverse (relabel (stripPhase 1 1) perm0.symm)) u v from by decide) u v
  rw [he]; exact Target.reversed (Target.framed (Target.strip 1 1) perm0.symm)

theorem edge49_1 : Target (mutate (node 49) 1) ∨ IsFork (mutate (node 49) 1) 1 ∨ IsRoot (mutate (node 49) 1) 1 := by
  left
  have he : (mutate (node 49) 1) = relabel (node 50) perm6.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 49) 1) u v = (relabel (node 50) perm6.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 50) perm6.symm

theorem edge49_2 : Target (mutate (node 49) 2) ∨ IsFork (mutate (node 49) 2) 2 ∨ IsRoot (mutate (node 49) 2) 2 := by
  left
  have he : (mutate (node 49) 2) = relabel (node 36) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 49) 2) u v = (relabel (node 36) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 36) perm0.symm

theorem edge49_3 : Target (mutate (node 49) 3) ∨ IsFork (mutate (node 49) 3) 3 ∨ IsRoot (mutate (node 49) 3) 3 := by
  right; right
  have he : relabel (mutate (node 49) 3) perm22 = Regions.root (12) (322) (59) (27) (5) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 49) 3) perm22) u v = (Regions.root (12) (322) (59) (27) (5) (1)) u v from by decide) u v
  have hf : IsRoot (relabel (mutate (node 49) 3) perm22) 0 := by
    rw [he]
    exact IsRoot.basic (12) (322) (59) (27) (5) (1) (by unfold Regions.Domain; decide) (by decide)
  exact root_of_relabel perm22 hf

theorem cyclic50 : ¬ Acyclic (node 50) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (by decide)
  have h1 := hr 1 2 (by decide)
  have h2 := hr 2 0 (by decide)
  omega

theorem edge50_0 : Target (mutate (node 50) 0) ∨ IsFork (mutate (node 50) 0) 0 ∨ IsRoot (mutate (node 50) 0) 0 := by
  left
  have he : (mutate (node 50) 0) = relabel (node 49) perm6.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 50) 0) u v = (relabel (node 49) perm6.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 49) perm6.symm

theorem edge50_1 : Target (mutate (node 50) 1) ∨ IsFork (mutate (node 50) 1) 1 ∨ IsRoot (mutate (node 50) 1) 1 := by
  left
  have he : (mutate (node 50) 1) = relabel (node 60) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 50) 1) u v = (relabel (node 60) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 60) perm0.symm

theorem edge50_2 : Target (mutate (node 50) 2) ∨ IsFork (mutate (node 50) 2) 2 ∨ IsRoot (mutate (node 50) 2) 2 := by
  left
  have he : (mutate (node 50) 2) = relabel (node 37) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 50) 2) u v = (relabel (node 37) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 37) perm0.symm

theorem edge50_3 : Target (mutate (node 50) 3) ∨ IsFork (mutate (node 50) 3) 3 ∨ IsRoot (mutate (node 50) 3) 3 := by
  right; right
  have he : relabel (reverse (mutate (node 50) 3)) perm20 = Regions.root (27) (136) (186) (5) (7) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 50) 3)) perm20) u v = (Regions.root (27) (136) (186) (5) (7) (1)) u v from by decide) u v
  have hf : IsRoot (relabel (reverse (mutate (node 50) 3)) perm20) 0 := by
    rw [he]
    exact IsRoot.basic (27) (136) (186) (5) (7) (1) (by unfold Regions.Domain; decide) (by decide)
  exact root_of_reverse (root_of_relabel perm20 hf)

theorem cyclic51 : ¬ Acyclic (node 51) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (by decide)
  have h1 := hr 1 2 (by decide)
  have h2 := hr 2 0 (by decide)
  omega

theorem edge51_0 : Target (mutate (node 51) 0) ∨ IsFork (mutate (node 51) 0) 0 ∨ IsRoot (mutate (node 51) 0) 0 := by
  right; left
  have he : relabel (mutate (node 51) 0) perm1 = Forks.template (4) (67) (5) (250) (19) (7) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 51) 0) perm1) u v = (Forks.template (4) (67) (5) (250) (19) (7)) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 51) 0) perm1) 0 := by
    rw [he]
    exact IsFork.basic (4) (67) (5) (250) (19) (7) (by unfold Forks.Domain; decide)
  exact fork_of_relabel perm1 hf

theorem edge51_1 : Target (mutate (node 51) 1) ∨ IsFork (mutate (node 51) 1) 1 ∨ IsRoot (mutate (node 51) 1) 1 := by
  left
  have he : (mutate (node 51) 1) = relabel (node 38) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 51) 1) u v = (relabel (node 38) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 38) perm0.symm

theorem edge51_2 : Target (mutate (node 51) 2) ∨ IsFork (mutate (node 51) 2) 2 ∨ IsRoot (mutate (node 51) 2) 2 := by
  left
  have he : (mutate (node 51) 2) = relabel (node 61) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 51) 2) u v = (relabel (node 61) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 61) perm0.symm

theorem edge51_3 : Target (mutate (node 51) 3) ∨ IsFork (mutate (node 51) 3) 3 ∨ IsRoot (mutate (node 51) 3) 3 := by
  right; left
  have he : relabel (reverse (mutate (node 51) 3)) perm20 = Forks.template (18) (67) (7) (1202) (127) (5) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 51) 3)) perm20) u v = (Forks.template (18) (67) (7) (1202) (127) (5)) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 51) 3)) perm20) 0 := by
    rw [he]
    exact IsFork.basic (18) (67) (7) (1202) (127) (5) (by unfold Forks.Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm20 hf)

theorem cyclic52 : ¬ Acyclic (node 52) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (by decide)
  have h1 := hr 2 3 (by decide)
  have h2 := hr 3 0 (by decide)
  omega

theorem edge52_0 : Target (mutate (node 52) 0) ∨ IsFork (mutate (node 52) 0) 0 ∨ IsRoot (mutate (node 52) 0) 0 := by
  left
  have he : (mutate (node 52) 0) = relabel (node 42) perm12.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 52) 0) u v = (relabel (node 42) perm12.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 42) perm12.symm

theorem edge52_1 : Target (mutate (node 52) 1) ∨ IsFork (mutate (node 52) 1) 1 ∨ IsRoot (mutate (node 52) 1) 1 := by
  left
  have he : (mutate (node 52) 1) = relabel (node 62) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 52) 1) u v = (relabel (node 62) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 62) perm0.symm

theorem edge52_2 : Target (mutate (node 52) 2) ∨ IsFork (mutate (node 52) 2) 2 ∨ IsRoot (mutate (node 52) 2) 2 := by
  left
  have he : (mutate (node 52) 2) = relabel (node 38) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 52) 2) u v = (relabel (node 38) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 38) perm0.symm

theorem edge52_3 : Target (mutate (node 52) 3) ∨ IsFork (mutate (node 52) 3) 3 ∨ IsRoot (mutate (node 52) 3) 3 := by
  right; left
  have he : relabel (reverse (mutate (node 52) 3)) perm22 = Forks.template (7) (2) (25) (13) (174) (4) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 52) 3)) perm22) u v = (Forks.template (7) (2) (25) (13) (174) (4)) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 52) 3)) perm22) 0 := by
    rw [he]
    exact IsFork.basic (7) (2) (25) (13) (174) (4) (by unfold Forks.Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm22 hf)

theorem cyclic53 : ¬ Acyclic (node 53) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (by decide)
  have h1 := hr 2 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge53_0 : Target (mutate (node 53) 0) ∨ IsFork (mutate (node 53) 0) 0 ∨ IsRoot (mutate (node 53) 0) 0 := by
  left
  have he : (mutate (node 53) 0) = relabel (node 54) perm14.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 53) 0) u v = (relabel (node 54) perm14.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 54) perm14.symm

theorem edge53_1 : Target (mutate (node 53) 1) ∨ IsFork (mutate (node 53) 1) 1 ∨ IsRoot (mutate (node 53) 1) 1 := by
  left
  have he : (mutate (node 53) 1) = relabel (node 63) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 53) 1) u v = (relabel (node 63) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 63) perm0.symm

theorem edge53_2 : Target (mutate (node 53) 2) ∨ IsFork (mutate (node 53) 2) 2 ∨ IsRoot (mutate (node 53) 2) 2 := by
  left
  have he : (mutate (node 53) 2) = relabel (node 39) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 53) 2) u v = (relabel (node 39) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 39) perm0.symm

theorem edge53_3 : Target (mutate (node 53) 3) ∨ IsFork (mutate (node 53) 3) 3 ∨ IsRoot (mutate (node 53) 3) 3 := by
  right; right
  have he : relabel (mutate (node 53) 3) perm20 = Regions.root (203) (7512) (2634) (37) (13) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 53) 3) perm20) u v = (Regions.root (203) (7512) (2634) (37) (13) (1)) u v from by decide) u v
  have hf : IsRoot (relabel (mutate (node 53) 3) perm20) 0 := by
    rw [he]
    exact IsRoot.basic (203) (7512) (2634) (37) (13) (1) (by unfold Regions.Domain; decide) (by decide)
  exact root_of_relabel perm20 hf

theorem cyclic54 : ¬ Acyclic (node 54) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (by decide)
  have h1 := hr 1 3 (by decide)
  have h2 := hr 3 0 (by decide)
  omega

theorem edge54_0 : Target (mutate (node 54) 0) ∨ IsFork (mutate (node 54) 0) 0 ∨ IsRoot (mutate (node 54) 0) 0 := by
  left
  have he : (mutate (node 54) 0) = relabel (node 40) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 54) 0) u v = (relabel (node 40) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 40) perm0.symm

theorem edge54_1 : Target (mutate (node 54) 1) ∨ IsFork (mutate (node 54) 1) 1 ∨ IsRoot (mutate (node 54) 1) 1 := by
  left
  have he : (mutate (node 54) 1) = relabel (stripPhase 2 1) perm8.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 54) 1) u v = (relabel (stripPhase 2 1) perm8.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.strip 2 1) perm8.symm

theorem edge54_2 : Target (mutate (node 54) 2) ∨ IsFork (mutate (node 54) 2) 2 ∨ IsRoot (mutate (node 54) 2) 2 := by
  left
  have he : (mutate (node 54) 2) = relabel (node 53) perm14.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 54) 2) u v = (relabel (node 53) perm14.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 53) perm14.symm

theorem edge54_3 : Target (mutate (node 54) 3) ∨ IsFork (mutate (node 54) 3) 3 ∨ IsRoot (mutate (node 54) 3) 3 := by
  right; right
  have he : relabel (reverse (mutate (node 54) 3)) perm18 = Regions.root (50) (10146) (1849) (203) (37) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 54) 3)) perm18) u v = (Regions.root (50) (10146) (1849) (203) (37) (1)) u v from by decide) u v
  have hf : IsRoot (relabel (reverse (mutate (node 54) 3)) perm18) 0 := by
    rw [he]
    exact IsRoot.basic (50) (10146) (1849) (203) (37) (1) (by unfold Regions.Domain; decide) (by decide)
  exact root_of_reverse (root_of_relabel perm18 hf)

theorem cyclic55 : ¬ Acyclic (node 55) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (by decide)
  have h1 := hr 2 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge55_0 : Target (mutate (node 55) 0) ∨ IsFork (mutate (node 55) 0) 0 ∨ IsRoot (mutate (node 55) 0) 0 := by
  left
  have he : (mutate (node 55) 0) = relabel (node 48) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 55) 0) u v = (relabel (node 48) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 48) perm0.symm

theorem edge55_1 : Target (mutate (node 55) 1) ∨ IsFork (mutate (node 55) 1) 1 ∨ IsRoot (mutate (node 55) 1) 1 := by
  left
  have he : (mutate (node 55) 1) = relabel (stripPhase 0 2) perm6.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 55) 1) u v = (relabel (stripPhase 0 2) perm6.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.strip 0 2) perm6.symm

theorem edge55_2 : Target (mutate (node 55) 2) ∨ IsFork (mutate (node 55) 2) 2 ∨ IsRoot (mutate (node 55) 2) 2 := by
  right; left
  have he : relabel (reverse (mutate (node 55) 2)) perm12 = Forks.template (3) (2) (118) (5) (312) (13) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 55) 2)) perm12) u v = (Forks.template (3) (2) (118) (5) (312) (13)) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 55) 2)) perm12) 0 := by
    rw [he]
    exact IsFork.basic (3) (2) (118) (5) (312) (13) (by unfold Forks.Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm12 hf)

theorem edge55_3 : Target (mutate (node 55) 3) ∨ IsFork (mutate (node 55) 3) 3 ∨ IsRoot (mutate (node 55) 3) 3 := by
  right; right
  have he : relabel (mutate (node 55) 3) perm23 = Regions.root (118) (1536) (4953) (13) (42) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 55) 3) perm23) u v = (Regions.root (118) (1536) (4953) (13) (42) (1)) u v from by decide) u v
  have hf : IsRoot (relabel (mutate (node 55) 3) perm23) 0 := by
    rw [he]
    exact IsRoot.basic (118) (1536) (4953) (13) (42) (1) (by unfold Regions.Domain; decide) (by decide)
  exact root_of_relabel perm23 hf

theorem cyclic56 : ¬ Acyclic (node 56) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (by decide)
  have h1 := hr 2 3 (by decide)
  have h2 := hr 3 0 (by decide)
  omega

theorem edge56_0 : Target (mutate (node 56) 0) ∨ IsFork (mutate (node 56) 0) 0 ∨ IsRoot (mutate (node 56) 0) 0 := by
  left
  have he : (mutate (node 56) 0) = reverse (relabel (stripPhase 3 1) perm0.symm) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 56) 0) u v = (reverse (relabel (stripPhase 3 1) perm0.symm)) u v from by decide) u v
  rw [he]; exact Target.reversed (Target.framed (Target.strip 3 1) perm0.symm)

theorem edge56_1 : Target (mutate (node 56) 1) ∨ IsFork (mutate (node 56) 1) 1 ∨ IsRoot (mutate (node 56) 1) 1 := by
  left
  have he : (mutate (node 56) 1) = relabel (node 57) perm2.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 56) 1) u v = (relabel (node 57) perm2.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 57) perm2.symm

theorem edge56_2 : Target (mutate (node 56) 2) ∨ IsFork (mutate (node 56) 2) 2 ∨ IsRoot (mutate (node 56) 2) 2 := by
  left
  have he : (mutate (node 56) 2) = relabel (node 44) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 56) 2) u v = (relabel (node 44) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 44) perm0.symm

theorem edge56_3 : Target (mutate (node 56) 3) ∨ IsFork (mutate (node 56) 3) 3 ∨ IsRoot (mutate (node 56) 3) 3 := by
  right; right
  have he : relabel (mutate (node 56) 3) perm22 = Regions.root (173) (628488) (28544) (3633) (165) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 56) 3) perm22) u v = (Regions.root (173) (628488) (28544) (3633) (165) (1)) u v from by decide) u v
  have hf : IsRoot (relabel (mutate (node 56) 3) perm22) 0 := by
    rw [he]
    exact IsRoot.basic (173) (628488) (28544) (3633) (165) (1) (by unfold Regions.Domain; decide) (by decide)
  exact root_of_relabel perm22 hf

theorem cyclic57 : ¬ Acyclic (node 57) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (by decide)
  have h1 := hr 1 2 (by decide)
  have h2 := hr 2 0 (by decide)
  omega

theorem edge57_0 : Target (mutate (node 57) 0) ∨ IsFork (mutate (node 57) 0) 0 ∨ IsRoot (mutate (node 57) 0) 0 := by
  left
  have he : (mutate (node 57) 0) = relabel (node 64) perm12.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 57) 0) u v = (relabel (node 64) perm12.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 64) perm12.symm

theorem edge57_1 : Target (mutate (node 57) 1) ∨ IsFork (mutate (node 57) 1) 1 ∨ IsRoot (mutate (node 57) 1) 1 := by
  left
  have he : (mutate (node 57) 1) = relabel (node 45) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 57) 1) u v = (relabel (node 45) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 45) perm0.symm

theorem edge57_2 : Target (mutate (node 57) 2) ∨ IsFork (mutate (node 57) 2) 2 ∨ IsRoot (mutate (node 57) 2) 2 := by
  left
  have he : (mutate (node 57) 2) = relabel (node 56) perm2.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 57) 2) u v = (relabel (node 56) perm2.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 56) perm2.symm

theorem edge57_3 : Target (mutate (node 57) 3) ∨ IsFork (mutate (node 57) 3) 3 ∨ IsRoot (mutate (node 57) 3) 3 := by
  right; right
  have he : relabel (reverse (mutate (node 57) 3)) perm19 = Regions.root (3633) (599446) (29042) (165) (8) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 57) 3)) perm19) u v = (Regions.root (3633) (599446) (29042) (165) (8) (1)) u v from by decide) u v
  have hf : IsRoot (relabel (reverse (mutate (node 57) 3)) perm19) 0 := by
    rw [he]
    exact IsRoot.basic (3633) (599446) (29042) (165) (8) (1) (by unfold Regions.Domain; decide) (by decide)
  exact root_of_reverse (root_of_relabel perm19 hf)

theorem cyclic58 : ¬ Acyclic (node 58) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (by decide)
  have h1 := hr 1 2 (by decide)
  have h2 := hr 2 0 (by decide)
  omega

theorem edge58_0 : Target (mutate (node 58) 0) ∨ IsFork (mutate (node 58) 0) 0 ∨ IsRoot (mutate (node 58) 0) 0 := by
  left
  have he : (mutate (node 58) 0) = relabel (node 59) perm6.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 58) 0) u v = (relabel (node 59) perm6.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 59) perm6.symm

theorem edge58_1 : Target (mutate (node 58) 1) ∨ IsFork (mutate (node 58) 1) 1 ∨ IsRoot (mutate (node 58) 1) 1 := by
  left
  have he : (mutate (node 58) 1) = relabel (node 46) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 58) 1) u v = (relabel (node 46) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 46) perm0.symm

theorem edge58_2 : Target (mutate (node 58) 2) ∨ IsFork (mutate (node 58) 2) 2 ∨ IsRoot (mutate (node 58) 2) 2 := by
  left
  have he : (mutate (node 58) 2) = relabel (node 65) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 58) 2) u v = (relabel (node 65) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 65) perm0.symm

theorem edge58_3 : Target (mutate (node 58) 3) ∨ IsFork (mutate (node 58) 3) 3 ∨ IsRoot (mutate (node 58) 3) 3 := by
  right; right
  have he : relabel (mutate (node 58) 3) perm22 = Regions.root (1218) (66991) (3632) (55) (3) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 58) 3) perm22) u v = (Regions.root (1218) (66991) (3632) (55) (3) (1)) u v from by decide) u v
  have hf : IsRoot (relabel (mutate (node 58) 3) perm22) 0 := by
    rw [he]
    exact IsRoot.basic (1218) (66991) (3632) (55) (3) (1) (by unfold Regions.Domain; decide) (by decide)
  exact root_of_relabel perm22 hf

theorem cyclic59 : ¬ Acyclic (node 59) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (by decide)
  have h1 := hr 1 3 (by decide)
  have h2 := hr 3 0 (by decide)
  omega

theorem edge59_0 : Target (mutate (node 59) 0) ∨ IsFork (mutate (node 59) 0) 0 ∨ IsRoot (mutate (node 59) 0) 0 := by
  left
  have he : (mutate (node 59) 0) = relabel (node 47) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 59) 0) u v = (relabel (node 47) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 47) perm0.symm

theorem edge59_1 : Target (mutate (node 59) 1) ∨ IsFork (mutate (node 59) 1) 1 ∨ IsRoot (mutate (node 59) 1) 1 := by
  left
  have he : (mutate (node 59) 1) = relabel (node 58) perm6.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 59) 1) u v = (relabel (node 58) perm6.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 58) perm6.symm

theorem edge59_2 : Target (mutate (node 59) 2) ∨ IsFork (mutate (node 59) 2) 2 ∨ IsRoot (mutate (node 59) 2) 2 := by
  left
  have he : (mutate (node 59) 2) = relabel (stripPhase 4 1) perm14.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 59) 2) u v = (relabel (stripPhase 4 1) perm14.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.strip 4 1) perm14.symm

theorem edge59_3 : Target (mutate (node 59) 3) ∨ IsFork (mutate (node 59) 3) 3 ∨ IsRoot (mutate (node 59) 3) 3 := by
  right; right
  have he : relabel (reverse (mutate (node 59) 3)) perm19 = Regions.root (58) (70623) (3189) (1218) (55) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 59) 3)) perm19) u v = (Regions.root (58) (70623) (3189) (1218) (55) (1)) u v from by decide) u v
  have hf : IsRoot (relabel (reverse (mutate (node 59) 3)) perm19) 0 := by
    rw [he]
    exact IsRoot.basic (58) (70623) (3189) (1218) (55) (1) (by unfold Regions.Domain; decide) (by decide)
  exact root_of_reverse (root_of_relabel perm19 hf)

theorem cyclic60 : ¬ Acyclic (node 60) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (by decide)
  have h1 := hr 2 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge60_0 : Target (mutate (node 60) 0) ∨ IsFork (mutate (node 60) 0) 0 ∨ IsRoot (mutate (node 60) 0) 0 := by
  left
  have he : (mutate (node 60) 0) = reverse (relabel (stripPhase 1 2) perm0.symm) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 60) 0) u v = (reverse (relabel (stripPhase 1 2) perm0.symm)) u v from by decide) u v
  rw [he]; exact Target.reversed (Target.framed (Target.strip 1 2) perm0.symm)

theorem edge60_1 : Target (mutate (node 60) 1) ∨ IsFork (mutate (node 60) 1) 1 ∨ IsRoot (mutate (node 60) 1) 1 := by
  left
  have he : (mutate (node 60) 1) = relabel (node 50) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 60) 1) u v = (relabel (node 50) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 50) perm0.symm

theorem edge60_2 : Target (mutate (node 60) 2) ∨ IsFork (mutate (node 60) 2) 2 ∨ IsRoot (mutate (node 60) 2) 2 := by
  right; left
  have he : relabel (mutate (node 60) 2) perm14 = Forks.template (3) (2) (74) (5) (195) (5) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 60) 2) perm14) u v = (Forks.template (3) (2) (74) (5) (195) (5)) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 60) 2) perm14) 0 := by
    rw [he]
    exact IsFork.basic (3) (2) (74) (5) (195) (5) (by unfold Forks.Domain; decide)
  exact fork_of_relabel perm14 hf

theorem edge60_3 : Target (mutate (node 60) 3) ∨ IsFork (mutate (node 60) 3) 3 ∨ IsRoot (mutate (node 60) 3) 3 := by
  right; right
  have he : relabel (reverse (mutate (node 60) 3)) perm22 = Regions.root (74) (372) (1995) (5) (27) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 60) 3)) perm22) u v = (Regions.root (74) (372) (1995) (5) (27) (1)) u v from by decide) u v
  have hf : IsRoot (relabel (reverse (mutate (node 60) 3)) perm22) 0 := by
    rw [he]
    exact IsRoot.basic (74) (372) (1995) (5) (27) (1) (by unfold Regions.Domain; decide) (by decide)
  exact root_of_reverse (root_of_relabel perm22 hf)

theorem cyclic61 : ¬ Acyclic (node 61) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (by decide)
  have h1 := hr 2 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge61_0 : Target (mutate (node 61) 0) ∨ IsFork (mutate (node 61) 0) 0 ∨ IsRoot (mutate (node 61) 0) 0 := by
  left
  have he : (mutate (node 61) 0) = relabel (node 66) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 61) 0) u v = (relabel (node 66) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 66) perm0.symm

theorem edge61_1 : Target (mutate (node 61) 1) ∨ IsFork (mutate (node 61) 1) 1 ∨ IsRoot (mutate (node 61) 1) 1 := by
  left
  have he : (mutate (node 61) 1) = relabel (node 62) perm2.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 61) 1) u v = (relabel (node 62) perm2.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 62) perm2.symm

theorem edge61_2 : Target (mutate (node 61) 2) ∨ IsFork (mutate (node 61) 2) 2 ∨ IsRoot (mutate (node 61) 2) 2 := by
  left
  have he : (mutate (node 61) 2) = relabel (node 51) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 61) 2) u v = (relabel (node 51) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 51) perm0.symm

theorem edge61_3 : Target (mutate (node 61) 3) ∨ IsFork (mutate (node 61) 3) 3 ∨ IsRoot (mutate (node 61) 3) 3 := by
  right; right
  have he : relabel (reverse (mutate (node 61) 3)) perm18 = Regions.root (102) (1837) (709) (18) (7) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 61) 3)) perm18) u v = (Regions.root (102) (1837) (709) (18) (7) (1)) u v from by decide) u v
  have hf : IsRoot (relabel (reverse (mutate (node 61) 3)) perm18) 0 := by
    rw [he]
    exact IsRoot.basic (102) (1837) (709) (18) (7) (1) (by unfold Regions.Domain; decide) (by decide)
  exact root_of_reverse (root_of_relabel perm18 hf)

theorem cyclic62 : ¬ Acyclic (node 62) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (by decide)
  have h1 := hr 1 3 (by decide)
  have h2 := hr 3 0 (by decide)
  omega

theorem edge62_0 : Target (mutate (node 62) 0) ∨ IsFork (mutate (node 62) 0) 0 ∨ IsRoot (mutate (node 62) 0) 0 := by
  left
  have he : (mutate (node 62) 0) = reverse (relabel (stripPhase 5 1) perm2.symm) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 62) 0) u v = (reverse (relabel (stripPhase 5 1) perm2.symm)) u v from by decide) u v
  rw [he]; exact Target.reversed (Target.framed (Target.strip 5 1) perm2.symm)

theorem edge62_1 : Target (mutate (node 62) 1) ∨ IsFork (mutate (node 62) 1) 1 ∨ IsRoot (mutate (node 62) 1) 1 := by
  left
  have he : (mutate (node 62) 1) = relabel (node 52) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 62) 1) u v = (relabel (node 52) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 52) perm0.symm

theorem edge62_2 : Target (mutate (node 62) 2) ∨ IsFork (mutate (node 62) 2) 2 ∨ IsRoot (mutate (node 62) 2) 2 := by
  left
  have he : (mutate (node 62) 2) = relabel (node 61) perm2.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 62) 2) u v = (relabel (node 61) perm2.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 61) perm2.symm

theorem edge62_3 : Target (mutate (node 62) 3) ∨ IsFork (mutate (node 62) 3) 3 ∨ IsRoot (mutate (node 62) 3) 3 := by
  right; right
  have he : relabel (mutate (node 62) 3) perm20 = Regions.root (25) (2546) (449) (102) (18) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 62) 3) perm20) u v = (Regions.root (25) (2546) (449) (102) (18) (1)) u v from by decide) u v
  have hf : IsRoot (relabel (mutate (node 62) 3) perm20) 0 := by
    rw [he]
    exact IsRoot.basic (25) (2546) (449) (102) (18) (1) (by unfold Regions.Domain; decide) (by decide)
  exact root_of_relabel perm20 hf

theorem cyclic63 : ¬ Acyclic (node 63) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (by decide)
  have h1 := hr 1 2 (by decide)
  have h2 := hr 2 0 (by decide)
  omega

theorem edge63_0 : Target (mutate (node 63) 0) ∨ IsFork (mutate (node 63) 0) 0 ∨ IsRoot (mutate (node 63) 0) 0 := by
  left
  have he : (mutate (node 63) 0) = relabel (stripPhase 2 2) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 63) 0) u v = (relabel (stripPhase 2 2) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.strip 2 2) perm0.symm

theorem edge63_1 : Target (mutate (node 63) 1) ∨ IsFork (mutate (node 63) 1) 1 ∨ IsRoot (mutate (node 63) 1) 1 := by
  left
  have he : (mutate (node 63) 1) = relabel (node 53) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 63) 1) u v = (relabel (node 53) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 53) perm0.symm

theorem edge63_2 : Target (mutate (node 63) 2) ∨ IsFork (mutate (node 63) 2) 2 ∨ IsRoot (mutate (node 63) 2) 2 := by
  right; left
  have he : relabel (reverse (mutate (node 63) 2)) perm14 = Forks.template (5) (4) (1002) (19) (4807) (37) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 63) 2)) perm14) u v = (Forks.template (5) (4) (1002) (19) (4807) (37)) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 63) 2)) perm14) 0 := by
    rw [he]
    exact IsFork.basic (5) (4) (1002) (19) (4807) (37) (by unfold Forks.Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm14 hf)

theorem edge63_3 : Target (mutate (node 63) 3) ∨ IsFork (mutate (node 63) 3) 3 ∨ IsRoot (mutate (node 63) 3) 3 := by
  right; right
  have he : relabel (mutate (node 63) 3) perm22 = Regions.root (1002) (37078) (203401) (37) (203) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 63) 3) perm22) u v = (Regions.root (1002) (37078) (203401) (37) (203) (1)) u v from by decide) u v
  have hf : IsRoot (relabel (mutate (node 63) 3) perm22) 0 := by
    rw [he]
    exact IsRoot.basic (1002) (37078) (203401) (37) (203) (1) (by unfold Regions.Domain; decide) (by decide)
  exact root_of_relabel perm22 hf

theorem cyclic64 : ¬ Acyclic (node 64) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (by decide)
  have h1 := hr 2 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge64_0 : Target (mutate (node 64) 0) ∨ IsFork (mutate (node 64) 0) 0 ∨ IsRoot (mutate (node 64) 0) 0 := by
  left
  have he : (mutate (node 64) 0) = reverse (relabel (stripPhase 3 2) perm0.symm) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 64) 0) u v = (reverse (relabel (stripPhase 3 2) perm0.symm)) u v from by decide) u v
  rw [he]; exact Target.reversed (Target.framed (Target.strip 3 2) perm0.symm)

theorem edge64_1 : Target (mutate (node 64) 1) ∨ IsFork (mutate (node 64) 1) 1 ∨ IsRoot (mutate (node 64) 1) 1 := by
  left
  have he : (mutate (node 64) 1) = relabel (node 57) perm8.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 64) 1) u v = (relabel (node 57) perm8.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 57) perm8.symm

theorem edge64_2 : Target (mutate (node 64) 2) ∨ IsFork (mutate (node 64) 2) 2 ∨ IsRoot (mutate (node 64) 2) 2 := by
  right; left
  have he : relabel (mutate (node 64) 2) perm14 = Forks.template (22) (21) (79918) (461) (1754563) (165) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 64) 2) perm14) u v = (Forks.template (22) (21) (79918) (461) (1754563) (165)) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 64) 2) perm14) 0 := by
    rw [he]
    exact IsFork.basic (22) (21) (79918) (461) (1754563) (165) (by unfold Forks.Domain; decide)
  exact fork_of_relabel perm14 hf

theorem edge64_3 : Target (mutate (node 64) 3) ∨ IsFork (mutate (node 64) 3) 3 ∨ IsRoot (mutate (node 64) 3) 3 := by
  right; right
  have he : relabel (reverse (mutate (node 64) 3)) perm22 = Regions.root (79918) (13186491) (290342072) (165) (3633) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 64) 3)) perm22) u v = (Regions.root (79918) (13186491) (290342072) (165) (3633) (1)) u v from by decide) u v
  have hf : IsRoot (relabel (reverse (mutate (node 64) 3)) perm22) 0 := by
    rw [he]
    exact IsRoot.basic (79918) (13186491) (290342072) (165) (3633) (1) (by unfold Regions.Domain; decide) (by decide)
  exact root_of_reverse (root_of_relabel perm22 hf)

theorem cyclic65 : ¬ Acyclic (node 65) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (by decide)
  have h1 := hr 2 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge65_0 : Target (mutate (node 65) 0) ∨ IsFork (mutate (node 65) 0) 0 ∨ IsRoot (mutate (node 65) 0) 0 := by
  left
  have he : (mutate (node 65) 0) = relabel (stripPhase 4 2) perm2.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 65) 0) u v = (relabel (stripPhase 4 2) perm2.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.strip 4 2) perm2.symm

theorem edge65_1 : Target (mutate (node 65) 1) ∨ IsFork (mutate (node 65) 1) 1 ∨ IsRoot (mutate (node 65) 1) 1 := by
  right; left
  have he : relabel (reverse (mutate (node 65) 1)) perm8 = Forks.template (22) (21) (26793) (461) (588228) (55) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 65) 1)) perm8) u v = (Forks.template (22) (21) (26793) (461) (588228) (55)) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 65) 1)) perm8) 0 := by
    rw [he]
    exact IsFork.basic (22) (21) (26793) (461) (588228) (55) (by unfold Forks.Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm8 hf)

theorem edge65_2 : Target (mutate (node 65) 2) ∨ IsFork (mutate (node 65) 2) 2 ∨ IsRoot (mutate (node 65) 2) 2 := by
  left
  have he : (mutate (node 65) 2) = relabel (node 58) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 65) 2) u v = (relabel (node 58) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 58) perm0.symm

theorem edge65_3 : Target (mutate (node 65) 3) ∨ IsFork (mutate (node 65) 3) 3 ∨ IsRoot (mutate (node 65) 3) 3 := by
  right; right
  have he : relabel (mutate (node 65) 3) perm20 = Regions.root (26793) (1473636) (32633852) (55) (1218) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 65) 3) perm20) u v = (Regions.root (26793) (1473636) (32633852) (55) (1218) (1)) u v from by decide) u v
  have hf : IsRoot (relabel (mutate (node 65) 3) perm20) 0 := by
    rw [he]
    exact IsRoot.basic (26793) (1473636) (32633852) (55) (1218) (1) (by unfold Regions.Domain; decide) (by decide)
  exact root_of_relabel perm20 hf

theorem cyclic66 : ¬ Acyclic (node 66) := by
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (by decide)
  have h1 := hr 1 2 (by decide)
  have h2 := hr 2 0 (by decide)
  omega

theorem edge66_0 : Target (mutate (node 66) 0) ∨ IsFork (mutate (node 66) 0) 0 ∨ IsRoot (mutate (node 66) 0) 0 := by
  left
  have he : (mutate (node 66) 0) = relabel (node 61) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 66) 0) u v = (relabel (node 61) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 61) perm0.symm

theorem edge66_1 : Target (mutate (node 66) 1) ∨ IsFork (mutate (node 66) 1) 1 ∨ IsRoot (mutate (node 66) 1) 1 := by
  left
  have he : (mutate (node 66) 1) = reverse (relabel (stripPhase 5 2) perm6.symm) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (node 66) 1) u v = (reverse (relabel (stripPhase 5 2) perm6.symm)) u v from by decide) u v
  rw [he]; exact Target.reversed (Target.framed (Target.strip 5 2) perm6.symm)

theorem edge66_2 : Target (mutate (node 66) 2) ∨ IsFork (mutate (node 66) 2) 2 ∨ IsRoot (mutate (node 66) 2) 2 := by
  right; left
  have he : relabel (mutate (node 66) 2) perm12 = Forks.template (5) (4) (503) (19) (2413) (18) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (mutate (node 66) 2) perm12) u v = (Forks.template (5) (4) (503) (19) (2413) (18)) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 66) 2) perm12) 0 := by
    rw [he]
    exact IsFork.basic (5) (4) (503) (19) (2413) (18) (by unfold Forks.Domain; decide)
  exact fork_of_relabel perm12 hf

theorem edge66_3 : Target (mutate (node 66) 3) ∨ IsFork (mutate (node 66) 3) 3 ∨ IsRoot (mutate (node 66) 3) 3 := by
  right; right
  have he : relabel (reverse (mutate (node 66) 3)) perm23 = Regions.root (503) (9058) (51301) (18) (102) (1) := by
    funext u v
    exact (show ∀ u v : Fin 4, (relabel (reverse (mutate (node 66) 3)) perm23) u v = (Regions.root (503) (9058) (51301) (18) (102) (1)) u v from by decide) u v
  have hf : IsRoot (relabel (reverse (mutate (node 66) 3)) perm23) 0 := by
    rw [he]
    exact IsRoot.basic (503) (9058) (51301) (18) (102) (1) (by unfold Regions.Domain; decide) (by decide)
  exact root_of_reverse (root_of_relabel perm23 hf)

theorem all_skew (i : Fin 67) : SkewSymmetric (node i) := by
  rcases fin67 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact ofSix_skew _ _ _ _ _ _

theorem all_cyclic (i : Fin 67) : ¬ Acyclic (node i) := by
  rcases fin67 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
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
  · exact cyclic62
  · exact cyclic63
  · exact cyclic64
  · exact cyclic65
  · exact cyclic66

theorem all_edges (i : Fin 67) (k : Fin 4) :
    Target (mutate (node i) k) ∨ IsFork (mutate (node i) k) k ∨ IsRoot (mutate (node i) k) k := by
  rcases fin67 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rcases fin4 k with rfl|rfl|rfl|rfl
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
  · exact edge62_0
  · exact edge62_1
  · exact edge62_2
  · exact edge62_3
  · exact edge63_0
  · exact edge63_1
  · exact edge63_2
  · exact edge63_3
  · exact edge64_0
  · exact edge64_1
  · exact edge64_2
  · exact edge64_3
  · exact edge65_0
  · exact edge65_1
  · exact edge65_2
  · exact edge65_3
  · exact edge66_0
  · exact edge66_1
  · exact edge66_2
  · exact edge66_3

theorem reachable0 : applyWord (node 0) (nodeWord 0) = node 0 := by
  rfl

theorem reachable1 : applyWord (node 0) (nodeWord 1) = node 1 := by
  have hw : nodeWord 1 = nodeWord 0 ++ [0] := by decide
  rw [hw,applyWord_append,reachable0]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 0) [0]) u v = (node 1) u v from by decide) u v

theorem reachable2 : applyWord (node 0) (nodeWord 2) = node 2 := by
  have hw : nodeWord 2 = nodeWord 0 ++ [1] := by decide
  rw [hw,applyWord_append,reachable0]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 0) [1]) u v = (node 2) u v from by decide) u v

theorem reachable3 : applyWord (node 0) (nodeWord 3) = node 3 := by
  have hw : nodeWord 3 = nodeWord 1 ++ [1] := by decide
  rw [hw,applyWord_append,reachable1]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 1) [1]) u v = (node 3) u v from by decide) u v

theorem reachable4 : applyWord (node 0) (nodeWord 4) = node 4 := by
  have hw : nodeWord 4 = nodeWord 1 ++ [2] := by decide
  rw [hw,applyWord_append,reachable1]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 1) [2]) u v = (node 4) u v from by decide) u v

theorem reachable5 : applyWord (node 0) (nodeWord 5) = node 5 := by
  have hw : nodeWord 5 = nodeWord 1 ++ [3] := by decide
  rw [hw,applyWord_append,reachable1]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 1) [3]) u v = (node 5) u v from by decide) u v

theorem reachable6 : applyWord (node 0) (nodeWord 6) = node 6 := by
  have hw : nodeWord 6 = nodeWord 2 ++ [0] := by decide
  rw [hw,applyWord_append,reachable2]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 2) [0]) u v = (node 6) u v from by decide) u v

theorem reachable7 : applyWord (node 0) (nodeWord 7) = node 7 := by
  have hw : nodeWord 7 = nodeWord 2 ++ [2] := by decide
  rw [hw,applyWord_append,reachable2]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 2) [2]) u v = (node 7) u v from by decide) u v

theorem reachable8 : applyWord (node 0) (nodeWord 8) = node 8 := by
  have hw : nodeWord 8 = nodeWord 2 ++ [3] := by decide
  rw [hw,applyWord_append,reachable2]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 2) [3]) u v = (node 8) u v from by decide) u v

theorem reachable9 : applyWord (node 0) (nodeWord 9) = node 9 := by
  have hw : nodeWord 9 = nodeWord 3 ++ [0] := by decide
  rw [hw,applyWord_append,reachable3]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 3) [0]) u v = (node 9) u v from by decide) u v

theorem reachable10 : applyWord (node 0) (nodeWord 10) = node 10 := by
  have hw : nodeWord 10 = nodeWord 3 ++ [2] := by decide
  rw [hw,applyWord_append,reachable3]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 3) [2]) u v = (node 10) u v from by decide) u v

theorem reachable11 : applyWord (node 0) (nodeWord 11) = node 11 := by
  have hw : nodeWord 11 = nodeWord 3 ++ [3] := by decide
  rw [hw,applyWord_append,reachable3]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 3) [3]) u v = (node 11) u v from by decide) u v

theorem reachable12 : applyWord (node 0) (nodeWord 12) = node 12 := by
  have hw : nodeWord 12 = nodeWord 4 ++ [1] := by decide
  rw [hw,applyWord_append,reachable4]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 4) [1]) u v = (node 12) u v from by decide) u v

theorem reachable13 : applyWord (node 0) (nodeWord 13) = node 13 := by
  have hw : nodeWord 13 = nodeWord 5 ++ [2] := by decide
  rw [hw,applyWord_append,reachable5]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 5) [2]) u v = (node 13) u v from by decide) u v

theorem reachable14 : applyWord (node 0) (nodeWord 14) = node 14 := by
  have hw : nodeWord 14 = nodeWord 6 ++ [2] := by decide
  rw [hw,applyWord_append,reachable6]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 6) [2]) u v = (node 14) u v from by decide) u v

theorem reachable15 : applyWord (node 0) (nodeWord 15) = node 15 := by
  have hw : nodeWord 15 = nodeWord 7 ++ [0] := by decide
  rw [hw,applyWord_append,reachable7]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 7) [0]) u v = (node 15) u v from by decide) u v

theorem reachable16 : applyWord (node 0) (nodeWord 16) = node 16 := by
  have hw : nodeWord 16 = nodeWord 7 ++ [3] := by decide
  rw [hw,applyWord_append,reachable7]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 7) [3]) u v = (node 16) u v from by decide) u v

theorem reachable17 : applyWord (node 0) (nodeWord 17) = node 17 := by
  have hw : nodeWord 17 = nodeWord 8 ++ [0] := by decide
  rw [hw,applyWord_append,reachable8]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 8) [0]) u v = (node 17) u v from by decide) u v

theorem reachable18 : applyWord (node 0) (nodeWord 18) = node 18 := by
  have hw : nodeWord 18 = nodeWord 8 ++ [1] := by decide
  rw [hw,applyWord_append,reachable8]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 8) [1]) u v = (node 18) u v from by decide) u v

theorem reachable19 : applyWord (node 0) (nodeWord 19) = node 19 := by
  have hw : nodeWord 19 = nodeWord 10 ++ [0] := by decide
  rw [hw,applyWord_append,reachable10]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 10) [0]) u v = (node 19) u v from by decide) u v

theorem reachable20 : applyWord (node 0) (nodeWord 20) = node 20 := by
  have hw : nodeWord 20 = nodeWord 10 ++ [3] := by decide
  rw [hw,applyWord_append,reachable10]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 10) [3]) u v = (node 20) u v from by decide) u v

theorem reachable21 : applyWord (node 0) (nodeWord 21) = node 21 := by
  have hw : nodeWord 21 = nodeWord 12 ++ [0] := by decide
  rw [hw,applyWord_append,reachable12]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 12) [0]) u v = (node 21) u v from by decide) u v

theorem reachable22 : applyWord (node 0) (nodeWord 22) = node 22 := by
  have hw : nodeWord 22 = nodeWord 12 ++ [3] := by decide
  rw [hw,applyWord_append,reachable12]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 12) [3]) u v = (node 22) u v from by decide) u v

theorem reachable23 : applyWord (node 0) (nodeWord 23) = node 23 := by
  have hw : nodeWord 23 = nodeWord 14 ++ [1] := by decide
  rw [hw,applyWord_append,reachable14]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 14) [1]) u v = (node 23) u v from by decide) u v

theorem reachable24 : applyWord (node 0) (nodeWord 24) = node 24 := by
  have hw : nodeWord 24 = nodeWord 15 ++ [1] := by decide
  rw [hw,applyWord_append,reachable15]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 15) [1]) u v = (node 24) u v from by decide) u v

theorem reachable25 : applyWord (node 0) (nodeWord 25) = node 25 := by
  have hw : nodeWord 25 = nodeWord 16 ++ [0] := by decide
  rw [hw,applyWord_append,reachable16]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 16) [0]) u v = (node 25) u v from by decide) u v

theorem reachable26 : applyWord (node 0) (nodeWord 26) = node 26 := by
  have hw : nodeWord 26 = nodeWord 16 ++ [1] := by decide
  rw [hw,applyWord_append,reachable16]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 16) [1]) u v = (node 26) u v from by decide) u v

theorem reachable27 : applyWord (node 0) (nodeWord 27) = node 27 := by
  have hw : nodeWord 27 = nodeWord 17 ++ [1] := by decide
  rw [hw,applyWord_append,reachable17]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 17) [1]) u v = (node 27) u v from by decide) u v

theorem reachable28 : applyWord (node 0) (nodeWord 28) = node 28 := by
  have hw : nodeWord 28 = nodeWord 17 ++ [2] := by decide
  rw [hw,applyWord_append,reachable17]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 17) [2]) u v = (node 28) u v from by decide) u v

theorem reachable29 : applyWord (node 0) (nodeWord 29) = node 29 := by
  have hw : nodeWord 29 = nodeWord 18 ++ [2] := by decide
  rw [hw,applyWord_append,reachable18]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 18) [2]) u v = (node 29) u v from by decide) u v

theorem reachable30 : applyWord (node 0) (nodeWord 30) = node 30 := by
  have hw : nodeWord 30 = nodeWord 19 ++ [1] := by decide
  rw [hw,applyWord_append,reachable19]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 19) [1]) u v = (node 30) u v from by decide) u v

theorem reachable31 : applyWord (node 0) (nodeWord 31) = node 31 := by
  have hw : nodeWord 31 = nodeWord 20 ++ [0] := by decide
  rw [hw,applyWord_append,reachable20]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 20) [0]) u v = (node 31) u v from by decide) u v

theorem reachable32 : applyWord (node 0) (nodeWord 32) = node 32 := by
  have hw : nodeWord 32 = nodeWord 20 ++ [2] := by decide
  rw [hw,applyWord_append,reachable20]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 20) [2]) u v = (node 32) u v from by decide) u v

theorem reachable33 : applyWord (node 0) (nodeWord 33) = node 33 := by
  have hw : nodeWord 33 = nodeWord 21 ++ [1] := by decide
  rw [hw,applyWord_append,reachable21]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 21) [1]) u v = (node 33) u v from by decide) u v

theorem reachable34 : applyWord (node 0) (nodeWord 34) = node 34 := by
  have hw : nodeWord 34 = nodeWord 22 ++ [0] := by decide
  rw [hw,applyWord_append,reachable22]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 22) [0]) u v = (node 34) u v from by decide) u v

theorem reachable35 : applyWord (node 0) (nodeWord 35) = node 35 := by
  have hw : nodeWord 35 = nodeWord 22 ++ [1] := by decide
  rw [hw,applyWord_append,reachable22]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 22) [1]) u v = (node 35) u v from by decide) u v

theorem reachable36 : applyWord (node 0) (nodeWord 36) = node 36 := by
  have hw : nodeWord 36 = nodeWord 23 ++ [0] := by decide
  rw [hw,applyWord_append,reachable23]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 23) [0]) u v = (node 36) u v from by decide) u v

theorem reachable37 : applyWord (node 0) (nodeWord 37) = node 37 := by
  have hw : nodeWord 37 = nodeWord 24 ++ [0] := by decide
  rw [hw,applyWord_append,reachable24]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 24) [0]) u v = (node 37) u v from by decide) u v

theorem reachable38 : applyWord (node 0) (nodeWord 38) = node 38 := by
  have hw : nodeWord 38 = nodeWord 26 ++ [0] := by decide
  rw [hw,applyWord_append,reachable26]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 26) [0]) u v = (node 38) u v from by decide) u v

theorem reachable39 : applyWord (node 0) (nodeWord 39) = node 39 := by
  have hw : nodeWord 39 = nodeWord 27 ++ [0] := by decide
  rw [hw,applyWord_append,reachable27]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 27) [0]) u v = (node 39) u v from by decide) u v

theorem reachable40 : applyWord (node 0) (nodeWord 40) = node 40 := by
  have hw : nodeWord 40 = nodeWord 27 ++ [2] := by decide
  rw [hw,applyWord_append,reachable27]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 27) [2]) u v = (node 40) u v from by decide) u v

theorem reachable41 : applyWord (node 0) (nodeWord 41) = node 41 := by
  have hw : nodeWord 41 = nodeWord 28 ++ [1] := by decide
  rw [hw,applyWord_append,reachable28]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 28) [1]) u v = (node 41) u v from by decide) u v

theorem reachable42 : applyWord (node 0) (nodeWord 42) = node 42 := by
  have hw : nodeWord 42 = nodeWord 29 ++ [0] := by decide
  rw [hw,applyWord_append,reachable29]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 29) [0]) u v = (node 42) u v from by decide) u v

theorem reachable43 : applyWord (node 0) (nodeWord 43) = node 43 := by
  have hw : nodeWord 43 = nodeWord 30 ++ [2] := by decide
  rw [hw,applyWord_append,reachable30]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 30) [2]) u v = (node 43) u v from by decide) u v

theorem reachable44 : applyWord (node 0) (nodeWord 44) = node 44 := by
  have hw : nodeWord 44 = nodeWord 31 ++ [1] := by decide
  rw [hw,applyWord_append,reachable31]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 31) [1]) u v = (node 44) u v from by decide) u v

theorem reachable45 : applyWord (node 0) (nodeWord 45) = node 45 := by
  have hw : nodeWord 45 = nodeWord 31 ++ [2] := by decide
  rw [hw,applyWord_append,reachable31]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 31) [2]) u v = (node 45) u v from by decide) u v

theorem reachable46 : applyWord (node 0) (nodeWord 46) = node 46 := by
  have hw : nodeWord 46 = nodeWord 32 ++ [0] := by decide
  rw [hw,applyWord_append,reachable32]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 32) [0]) u v = (node 46) u v from by decide) u v

theorem reachable47 : applyWord (node 0) (nodeWord 47) = node 47 := by
  have hw : nodeWord 47 = nodeWord 32 ++ [1] := by decide
  rw [hw,applyWord_append,reachable32]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 32) [1]) u v = (node 47) u v from by decide) u v

theorem reachable48 : applyWord (node 0) (nodeWord 48) = node 48 := by
  have hw : nodeWord 48 = nodeWord 33 ++ [2] := by decide
  rw [hw,applyWord_append,reachable33]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 33) [2]) u v = (node 48) u v from by decide) u v

theorem reachable49 : applyWord (node 0) (nodeWord 49) = node 49 := by
  have hw : nodeWord 49 = nodeWord 36 ++ [2] := by decide
  rw [hw,applyWord_append,reachable36]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 36) [2]) u v = (node 49) u v from by decide) u v

theorem reachable50 : applyWord (node 0) (nodeWord 50) = node 50 := by
  have hw : nodeWord 50 = nodeWord 37 ++ [2] := by decide
  rw [hw,applyWord_append,reachable37]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 37) [2]) u v = (node 50) u v from by decide) u v

theorem reachable51 : applyWord (node 0) (nodeWord 51) = node 51 := by
  have hw : nodeWord 51 = nodeWord 38 ++ [1] := by decide
  rw [hw,applyWord_append,reachable38]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 38) [1]) u v = (node 51) u v from by decide) u v

theorem reachable52 : applyWord (node 0) (nodeWord 52) = node 52 := by
  have hw : nodeWord 52 = nodeWord 38 ++ [2] := by decide
  rw [hw,applyWord_append,reachable38]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 38) [2]) u v = (node 52) u v from by decide) u v

theorem reachable53 : applyWord (node 0) (nodeWord 53) = node 53 := by
  have hw : nodeWord 53 = nodeWord 39 ++ [2] := by decide
  rw [hw,applyWord_append,reachable39]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 39) [2]) u v = (node 53) u v from by decide) u v

theorem reachable54 : applyWord (node 0) (nodeWord 54) = node 54 := by
  have hw : nodeWord 54 = nodeWord 40 ++ [0] := by decide
  rw [hw,applyWord_append,reachable40]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 40) [0]) u v = (node 54) u v from by decide) u v

theorem reachable55 : applyWord (node 0) (nodeWord 55) = node 55 := by
  have hw : nodeWord 55 = nodeWord 43 ++ [1, 0, 1] := by decide
  rw [hw,applyWord_append,reachable43]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 43) [1, 0, 1]) u v = (node 55) u v from by decide) u v

theorem reachable56 : applyWord (node 0) (nodeWord 56) = node 56 := by
  have hw : nodeWord 56 = nodeWord 44 ++ [2] := by decide
  rw [hw,applyWord_append,reachable44]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 44) [2]) u v = (node 56) u v from by decide) u v

theorem reachable57 : applyWord (node 0) (nodeWord 57) = node 57 := by
  have hw : nodeWord 57 = nodeWord 45 ++ [1] := by decide
  rw [hw,applyWord_append,reachable45]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 45) [1]) u v = (node 57) u v from by decide) u v

theorem reachable58 : applyWord (node 0) (nodeWord 58) = node 58 := by
  have hw : nodeWord 58 = nodeWord 46 ++ [1] := by decide
  rw [hw,applyWord_append,reachable46]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 46) [1]) u v = (node 58) u v from by decide) u v

theorem reachable59 : applyWord (node 0) (nodeWord 59) = node 59 := by
  have hw : nodeWord 59 = nodeWord 47 ++ [0] := by decide
  rw [hw,applyWord_append,reachable47]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 47) [0]) u v = (node 59) u v from by decide) u v

theorem reachable60 : applyWord (node 0) (nodeWord 60) = node 60 := by
  have hw : nodeWord 60 = nodeWord 49 ++ [0, 1, 0] := by decide
  rw [hw,applyWord_append,reachable49]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 49) [0, 1, 0]) u v = (node 60) u v from by decide) u v

theorem reachable61 : applyWord (node 0) (nodeWord 61) = node 61 := by
  have hw : nodeWord 61 = nodeWord 51 ++ [2] := by decide
  rw [hw,applyWord_append,reachable51]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 51) [2]) u v = (node 61) u v from by decide) u v

theorem reachable62 : applyWord (node 0) (nodeWord 62) = node 62 := by
  have hw : nodeWord 62 = nodeWord 52 ++ [1] := by decide
  rw [hw,applyWord_append,reachable52]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 52) [1]) u v = (node 62) u v from by decide) u v

theorem reachable63 : applyWord (node 0) (nodeWord 63) = node 63 := by
  have hw : nodeWord 63 = nodeWord 53 ++ [1] := by decide
  rw [hw,applyWord_append,reachable53]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 53) [1]) u v = (node 63) u v from by decide) u v

theorem reachable64 : applyWord (node 0) (nodeWord 64) = node 64 := by
  have hw : nodeWord 64 = nodeWord 56 ++ [0, 1, 0] := by decide
  rw [hw,applyWord_append,reachable56]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 56) [0, 1, 0]) u v = (node 64) u v from by decide) u v

theorem reachable65 : applyWord (node 0) (nodeWord 65) = node 65 := by
  have hw : nodeWord 65 = nodeWord 58 ++ [2] := by decide
  rw [hw,applyWord_append,reachable58]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 58) [2]) u v = (node 65) u v from by decide) u v

theorem reachable66 : applyWord (node 0) (nodeWord 66) = node 66 := by
  have hw : nodeWord 66 = nodeWord 61 ++ [0] := by decide
  rw [hw,applyWord_append,reachable61]
  funext u v
  exact (show ∀ u v : Fin 4, (applyWord (node 61) [0]) u v = (node 66) u v from by decide) u v

theorem reachable (i : Fin 67) : applyWord (node 0) (nodeWord i) = node i := by
  rcases fin67 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact reachable0
  · exact reachable1
  · exact reachable2
  · exact reachable3
  · exact reachable4
  · exact reachable5
  · exact reachable6
  · exact reachable7
  · exact reachable8
  · exact reachable9
  · exact reachable10
  · exact reachable11
  · exact reachable12
  · exact reachable13
  · exact reachable14
  · exact reachable15
  · exact reachable16
  · exact reachable17
  · exact reachable18
  · exact reachable19
  · exact reachable20
  · exact reachable21
  · exact reachable22
  · exact reachable23
  · exact reachable24
  · exact reachable25
  · exact reachable26
  · exact reachable27
  · exact reachable28
  · exact reachable29
  · exact reachable30
  · exact reachable31
  · exact reachable32
  · exact reachable33
  · exact reachable34
  · exact reachable35
  · exact reachable36
  · exact reachable37
  · exact reachable38
  · exact reachable39
  · exact reachable40
  · exact reachable41
  · exact reachable42
  · exact reachable43
  · exact reachable44
  · exact reachable45
  · exact reachable46
  · exact reachable47
  · exact reachable48
  · exact reachable49
  · exact reachable50
  · exact reachable51
  · exact reachable52
  · exact reachable53
  · exact reachable54
  · exact reachable55
  · exact reachable56
  · exact reachable57
  · exact reachable58
  · exact reachable59
  · exact reachable60
  · exact reachable61
  · exact reachable62
  · exact reachable63
  · exact reachable64
  · exact reachable65
  · exact reachable66

theorem strip0_identification : relabel (node 43) perm6 = stripPhase 0 0 := by
  funext u v
  exact (show ∀ u v : Fin 4, (relabel (node 43) perm6) u v = (stripPhase 0 0) u v from by decide) u v

theorem strip0_root_one_return : Target (mutate (stripPhase 0 0) 1) := by
  have he : (mutate (stripPhase 0 0) 1) = relabel (node 48) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (stripPhase 0 0) 1) u v = (relabel (node 48) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 48) perm0.symm

theorem strip0_root_two_return : Target (mutate (stripPhase 0 0) 2) := by
  have he : (mutate (stripPhase 0 0) 2) = relabel (node 30) perm6.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (stripPhase 0 0) 2) u v = (relabel (node 30) perm6.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 30) perm6.symm

theorem strip0_Q_zero_return : Target (mutate (stripPhase 0 2) 0) := by
  have he : (mutate (stripPhase 0 2) 0) = relabel (node 55) perm6.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (stripPhase 0 2) 0) u v = (relabel (node 55) perm6.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 55) perm6.symm

theorem strip1_identification : reverse (relabel (node 49) perm0) = stripPhase 1 0 := by
  funext u v
  exact (show ∀ u v : Fin 4, (reverse (relabel (node 49) perm0)) u v = (stripPhase 1 0) u v from by decide) u v

theorem strip1_root_one_return : Target (mutate (stripPhase 1 0) 1) := by
  have he : (mutate (stripPhase 1 0) 1) = reverse (relabel (node 50) perm6.symm) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (stripPhase 1 0) 1) u v = (reverse (relabel (node 50) perm6.symm)) u v from by decide) u v
  rw [he]; exact Target.reversed (Target.framed (Target.base 50) perm6.symm)

theorem strip1_root_two_return : Target (mutate (stripPhase 1 0) 2) := by
  have he : (mutate (stripPhase 1 0) 2) = reverse (relabel (node 36) perm0.symm) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (stripPhase 1 0) 2) u v = (reverse (relabel (node 36) perm0.symm)) u v from by decide) u v
  rw [he]; exact Target.reversed (Target.framed (Target.base 36) perm0.symm)

theorem strip1_Q_zero_return : Target (mutate (stripPhase 1 2) 0) := by
  have he : (mutate (stripPhase 1 2) 0) = reverse (relabel (node 60) perm0.symm) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (stripPhase 1 2) 0) u v = (reverse (relabel (node 60) perm0.symm)) u v from by decide) u v
  rw [he]; exact Target.reversed (Target.framed (Target.base 60) perm0.symm)

theorem strip2_identification : relabel (node 54) perm8 = stripPhase 2 0 := by
  funext u v
  exact (show ∀ u v : Fin 4, (relabel (node 54) perm8) u v = (stripPhase 2 0) u v from by decide) u v

theorem strip2_root_one_return : Target (mutate (stripPhase 2 0) 1) := by
  have he : (mutate (stripPhase 2 0) 1) = relabel (node 53) perm6.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (stripPhase 2 0) 1) u v = (relabel (node 53) perm6.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 53) perm6.symm

theorem strip2_root_two_return : Target (mutate (stripPhase 2 0) 2) := by
  have he : (mutate (stripPhase 2 0) 2) = relabel (node 40) perm12.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (stripPhase 2 0) 2) u v = (relabel (node 40) perm12.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 40) perm12.symm

theorem strip2_Q_zero_return : Target (mutate (stripPhase 2 2) 0) := by
  have he : (mutate (stripPhase 2 2) 0) = relabel (node 63) perm0.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (stripPhase 2 2) 0) u v = (relabel (node 63) perm0.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 63) perm0.symm

theorem strip3_identification : reverse (relabel (node 56) perm0) = stripPhase 3 0 := by
  funext u v
  exact (show ∀ u v : Fin 4, (reverse (relabel (node 56) perm0)) u v = (stripPhase 3 0) u v from by decide) u v

theorem strip3_root_one_return : Target (mutate (stripPhase 3 0) 1) := by
  have he : (mutate (stripPhase 3 0) 1) = reverse (relabel (node 57) perm2.symm) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (stripPhase 3 0) 1) u v = (reverse (relabel (node 57) perm2.symm)) u v from by decide) u v
  rw [he]; exact Target.reversed (Target.framed (Target.base 57) perm2.symm)

theorem strip3_root_two_return : Target (mutate (stripPhase 3 0) 2) := by
  have he : (mutate (stripPhase 3 0) 2) = reverse (relabel (node 44) perm0.symm) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (stripPhase 3 0) 2) u v = (reverse (relabel (node 44) perm0.symm)) u v from by decide) u v
  rw [he]; exact Target.reversed (Target.framed (Target.base 44) perm0.symm)

theorem strip3_Q_zero_return : Target (mutate (stripPhase 3 2) 0) := by
  have he : (mutate (stripPhase 3 2) 0) = reverse (relabel (node 64) perm0.symm) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (stripPhase 3 2) 0) u v = (reverse (relabel (node 64) perm0.symm)) u v from by decide) u v
  rw [he]; exact Target.reversed (Target.framed (Target.base 64) perm0.symm)

theorem strip4_identification : relabel (node 59) perm14 = stripPhase 4 0 := by
  funext u v
  exact (show ∀ u v : Fin 4, (relabel (node 59) perm14) u v = (stripPhase 4 0) u v from by decide) u v

theorem strip4_root_one_return : Target (mutate (stripPhase 4 0) 1) := by
  have he : (mutate (stripPhase 4 0) 1) = relabel (node 58) perm8.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (stripPhase 4 0) 1) u v = (relabel (node 58) perm8.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 58) perm8.symm

theorem strip4_root_two_return : Target (mutate (stripPhase 4 0) 2) := by
  have he : (mutate (stripPhase 4 0) 2) = relabel (node 47) perm14.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (stripPhase 4 0) 2) u v = (relabel (node 47) perm14.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 47) perm14.symm

theorem strip4_Q_zero_return : Target (mutate (stripPhase 4 2) 0) := by
  have he : (mutate (stripPhase 4 2) 0) = relabel (node 65) perm2.symm := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (stripPhase 4 2) 0) u v = (relabel (node 65) perm2.symm) u v from by decide) u v
  rw [he]; exact Target.framed (Target.base 65) perm2.symm

theorem strip5_identification : reverse (relabel (node 62) perm2) = stripPhase 5 0 := by
  funext u v
  exact (show ∀ u v : Fin 4, (reverse (relabel (node 62) perm2)) u v = (stripPhase 5 0) u v from by decide) u v

theorem strip5_root_one_return : Target (mutate (stripPhase 5 0) 1) := by
  have he : (mutate (stripPhase 5 0) 1) = reverse (relabel (node 61) perm0.symm) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (stripPhase 5 0) 1) u v = (reverse (relabel (node 61) perm0.symm)) u v from by decide) u v
  rw [he]; exact Target.reversed (Target.framed (Target.base 61) perm0.symm)

theorem strip5_root_two_return : Target (mutate (stripPhase 5 0) 2) := by
  have he : (mutate (stripPhase 5 0) 2) = reverse (relabel (node 52) perm2.symm) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (stripPhase 5 0) 2) u v = (reverse (relabel (node 52) perm2.symm)) u v from by decide) u v
  rw [he]; exact Target.reversed (Target.framed (Target.base 52) perm2.symm)

theorem strip5_Q_zero_return : Target (mutate (stripPhase 5 2) 0) := by
  have he : (mutate (stripPhase 5 2) 0) = reverse (relabel (node 66) perm6.symm) := by
    funext u v
    exact (show ∀ u v : Fin 4, (mutate (stripPhase 5 2) 0) u v = (reverse (relabel (node 66) perm6.symm)) u v from by decide) u v
  rw [he]; exact Target.reversed (Target.framed (Target.base 66) perm6.symm)

theorem strip_root_one_return (j : Fin 6) : Target (mutate (stripPhase j 0) 1) := by
  rcases fin6 j with rfl|rfl|rfl|rfl|rfl|rfl
  · exact strip0_root_one_return
  · exact strip1_root_one_return
  · exact strip2_root_one_return
  · exact strip3_root_one_return
  · exact strip4_root_one_return
  · exact strip5_root_one_return

theorem strip_root_two_return (j : Fin 6) : Target (mutate (stripPhase j 0) 2) := by
  rcases fin6 j with rfl|rfl|rfl|rfl|rfl|rfl
  · exact strip0_root_two_return
  · exact strip1_root_two_return
  · exact strip2_root_two_return
  · exact strip3_root_two_return
  · exact strip4_root_two_return
  · exact strip5_root_two_return

theorem strip_Q_zero_return (j : Fin 6) : Target (mutate (stripPhase j 2) 0) := by
  rcases fin6 j with rfl|rfl|rfl|rfl|rfl|rfl
  · exact strip0_Q_zero_return
  · exact strip1_Q_zero_return
  · exact strip2_Q_zero_return
  · exact strip3_Q_zero_return
  · exact strip4_Q_zero_return
  · exact strip5_Q_zero_return

theorem local0_parent_identity : reverse (relabel (node 6) perm17) = mutate (zeroPhase 0 0) 1 := by
  funext u v
  exact (show ∀ u v : Fin 4, (reverse (relabel (node 6) perm17)) u v = (mutate (zeroPhase 0 0) 1) u v from by decide) u v

theorem zero0_parent0 : Target (mutate (zeroPhase 0 0) 1) := by
  rw [←local0_parent_identity]
  exact Target.reversed (Target.framed (Target.base 6) perm17)

theorem local0_entering_label : perm17.toFun 1 = (3 : Fin 4) := by decide

theorem local0_alternate_root : reverse (relabel (mutate (node 6) 2) perm17) = mutate (zeroPhase 0 1) 1 := by
  funext u v
  exact (show ∀ u v : Fin 4, (reverse (relabel (mutate (node 6) 2) perm17)) u v = (mutate (zeroPhase 0 1) 1) u v from by decide) u v

theorem local0_alternate_core : relabel (mutate (node 6) 2) perm0 = node 14 := by
  funext u v
  exact (show ∀ u v : Fin 4, (relabel (mutate (node 6) 2) perm0) u v = (node 14) u v from by decide) u v

theorem local1_parent_identity : reverse (relabel (node 9) perm21) = mutate (pendantPhase 0 0) 1 := by
  funext u v
  exact (show ∀ u v : Fin 4, (reverse (relabel (node 9) perm21)) u v = (mutate (pendantPhase 0 0) 1) u v from by decide) u v

theorem pendant0_parent0 : Target (mutate (pendantPhase 0 0) 1) := by
  rw [←local1_parent_identity]
  exact Target.reversed (Target.framed (Target.base 9) perm21)

theorem local1_entering_label : perm21.toFun 1 = (1 : Fin 4) := by decide

theorem local1_alternate_root : reverse (relabel (mutate (node 9) 3) perm21) = mutate (pendantPhase 0 1) 1 := by
  funext u v
  exact (show ∀ u v : Fin 4, (reverse (relabel (mutate (node 9) 3) perm21)) u v = (mutate (pendantPhase 0 1) 1) u v from by decide) u v

theorem local1_alternate_core : reverse (relabel (mutate (node 9) 3) perm10) = node 13 := by
  funext u v
  exact (show ∀ u v : Fin 4, (reverse (relabel (mutate (node 9) 3) perm10)) u v = (node 13) u v from by decide) u v

theorem local2_parent_identity : relabel (node 9) perm23 = mutate (pendantPhase 1 1) 1 := by
  funext u v
  exact (show ∀ u v : Fin 4, (relabel (node 9) perm23) u v = (mutate (pendantPhase 1 1) 1) u v from by decide) u v

theorem pendant1_parent1 : Target (mutate (pendantPhase 1 1) 1) := by
  rw [←local2_parent_identity]
  exact Target.framed (Target.base 9) perm23

theorem local2_entering_label : perm23.toFun 1 = (2 : Fin 4) := by decide

theorem local2_alternate_root : relabel (mutate (node 9) 3) perm23 = mutate (pendantPhase 1 0) 1 := by
  funext u v
  exact (show ∀ u v : Fin 4, (relabel (mutate (node 9) 3) perm23) u v = (mutate (pendantPhase 1 0) 1) u v from by decide) u v

theorem local2_alternate_core : reverse (relabel (mutate (node 9) 3) perm10) = node 13 := by
  funext u v
  exact (show ∀ u v : Fin 4, (reverse (relabel (mutate (node 9) 3) perm10)) u v = (node 13) u v from by decide) u v

theorem local3_parent_identity : relabel (node 13) perm7 = mutate (pendantPhase 0 1) 1 := by
  funext u v
  exact (show ∀ u v : Fin 4, (relabel (node 13) perm7) u v = (mutate (pendantPhase 0 1) 1) u v from by decide) u v

theorem pendant0_parent1 : Target (mutate (pendantPhase 0 1) 1) := by
  rw [←local3_parent_identity]
  exact Target.framed (Target.base 13) perm7

theorem local3_entering_label : perm7.toFun 1 = (0 : Fin 4) := by decide

theorem local3_alternate_root : relabel (mutate (node 13) 1) perm7 = mutate (pendantPhase 0 0) 1 := by
  funext u v
  exact (show ∀ u v : Fin 4, (relabel (mutate (node 13) 1) perm7) u v = (mutate (pendantPhase 0 0) 1) u v from by decide) u v

theorem local3_alternate_core : reverse (relabel (mutate (node 13) 1) perm13) = node 9 := by
  funext u v
  exact (show ∀ u v : Fin 4, (reverse (relabel (mutate (node 13) 1) perm13)) u v = (node 9) u v from by decide) u v

theorem local4_parent_identity : reverse (relabel (node 13) perm10) = mutate (pendantPhase 1 0) 1 := by
  funext u v
  exact (show ∀ u v : Fin 4, (reverse (relabel (node 13) perm10)) u v = (mutate (pendantPhase 1 0) 1) u v from by decide) u v

theorem pendant1_parent0 : Target (mutate (pendantPhase 1 0) 1) := by
  rw [←local4_parent_identity]
  exact Target.reversed (Target.framed (Target.base 13) perm10)

theorem local4_entering_label : perm10.toFun 1 = (3 : Fin 4) := by decide

theorem local4_alternate_root : reverse (relabel (mutate (node 13) 1) perm10) = mutate (pendantPhase 1 1) 1 := by
  funext u v
  exact (show ∀ u v : Fin 4, (reverse (relabel (mutate (node 13) 1) perm10)) u v = (mutate (pendantPhase 1 1) 1) u v from by decide) u v

theorem local4_alternate_core : reverse (relabel (mutate (node 13) 1) perm13) = node 9 := by
  funext u v
  exact (show ∀ u v : Fin 4, (reverse (relabel (mutate (node 13) 1) perm13)) u v = (node 9) u v from by decide) u v

theorem local5_parent_identity : reverse (relabel (node 14) perm17) = mutate (zeroPhase 0 1) 1 := by
  funext u v
  exact (show ∀ u v : Fin 4, (reverse (relabel (node 14) perm17)) u v = (mutate (zeroPhase 0 1) 1) u v from by decide) u v

theorem zero0_parent1 : Target (mutate (zeroPhase 0 1) 1) := by
  rw [←local5_parent_identity]
  exact Target.reversed (Target.framed (Target.base 14) perm17)

theorem local5_entering_label : perm17.toFun 1 = (3 : Fin 4) := by decide

theorem local5_alternate_root : reverse (relabel (mutate (node 14) 2) perm17) = mutate (zeroPhase 0 0) 1 := by
  funext u v
  exact (show ∀ u v : Fin 4, (reverse (relabel (mutate (node 14) 2) perm17)) u v = (mutate (zeroPhase 0 0) 1) u v from by decide) u v

theorem local5_alternate_core : relabel (mutate (node 14) 2) perm0 = node 6 := by
  funext u v
  exact (show ∀ u v : Fin 4, (relabel (mutate (node 14) 2) perm0) u v = (node 6) u v from by decide) u v

theorem local6_parent_identity : reverse (relabel (node 18) perm16) = mutate (zeroPhase 1 0) 1 := by
  funext u v
  exact (show ∀ u v : Fin 4, (reverse (relabel (node 18) perm16)) u v = (mutate (zeroPhase 1 0) 1) u v from by decide) u v

theorem zero1_parent0 : Target (mutate (zeroPhase 1 0) 1) := by
  rw [←local6_parent_identity]
  exact Target.reversed (Target.framed (Target.base 18) perm16)

theorem local6_entering_label : perm16.toFun 1 = (3 : Fin 4) := by decide

theorem local6_alternate_root : reverse (relabel (mutate (node 18) 2) perm16) = mutate (zeroPhase 1 1) 1 := by
  funext u v
  exact (show ∀ u v : Fin 4, (reverse (relabel (mutate (node 18) 2) perm16)) u v = (mutate (zeroPhase 1 1) 1) u v from by decide) u v

theorem local6_alternate_core : relabel (mutate (node 18) 2) perm0 = node 29 := by
  funext u v
  exact (show ∀ u v : Fin 4, (relabel (mutate (node 18) 2) perm0) u v = (node 29) u v from by decide) u v

theorem local7_parent_identity : relabel (node 19) perm11 = mutate (zeroPhase 2 0) 1 := by
  funext u v
  exact (show ∀ u v : Fin 4, (relabel (node 19) perm11) u v = (mutate (zeroPhase 2 0) 1) u v from by decide) u v

theorem zero2_parent0 : Target (mutate (zeroPhase 2 0) 1) := by
  rw [←local7_parent_identity]
  exact Target.framed (Target.base 19) perm11

theorem local7_entering_label : perm11.toFun 1 = (3 : Fin 4) := by decide

theorem local7_alternate_root : relabel (mutate (node 19) 1) perm11 = mutate (zeroPhase 2 1) 1 := by
  funext u v
  exact (show ∀ u v : Fin 4, (relabel (mutate (node 19) 1) perm11) u v = (mutate (zeroPhase 2 1) 1) u v from by decide) u v

theorem local7_alternate_core : relabel (mutate (node 19) 1) perm0 = node 30 := by
  funext u v
  exact (show ∀ u v : Fin 4, (relabel (mutate (node 19) 1) perm0) u v = (node 30) u v from by decide) u v

theorem local8_parent_identity : relabel (node 25) perm17 = mutate (zeroPhase 3 0) 1 := by
  funext u v
  exact (show ∀ u v : Fin 4, (relabel (node 25) perm17) u v = (mutate (zeroPhase 3 0) 1) u v from by decide) u v

theorem zero3_parent0 : Target (mutate (zeroPhase 3 0) 1) := by
  rw [←local8_parent_identity]
  exact Target.framed (Target.base 25) perm17

theorem local8_entering_label : perm17.toFun 1 = (3 : Fin 4) := by decide

theorem local8_alternate_root : relabel (mutate (node 25) 2) perm17 = mutate (zeroPhase 3 1) 1 := by
  funext u v
  exact (show ∀ u v : Fin 4, (relabel (mutate (node 25) 2) perm17) u v = (mutate (zeroPhase 3 1) 1) u v from by decide) u v

theorem local8_alternate_core : relabel (mutate (node 25) 2) perm14 = node 28 := by
  funext u v
  exact (show ∀ u v : Fin 4, (relabel (mutate (node 25) 2) perm14) u v = (node 28) u v from by decide) u v

theorem local9_parent_identity : relabel (node 28) perm4 = mutate (zeroPhase 3 1) 1 := by
  funext u v
  exact (show ∀ u v : Fin 4, (relabel (node 28) perm4) u v = (mutate (zeroPhase 3 1) 1) u v from by decide) u v

theorem zero3_parent1 : Target (mutate (zeroPhase 3 1) 1) := by
  rw [←local9_parent_identity]
  exact Target.framed (Target.base 28) perm4

theorem local9_entering_label : perm4.toFun 1 = (3 : Fin 4) := by decide

theorem local9_alternate_root : relabel (mutate (node 28) 0) perm4 = mutate (zeroPhase 3 0) 1 := by
  funext u v
  exact (show ∀ u v : Fin 4, (relabel (mutate (node 28) 0) perm4) u v = (mutate (zeroPhase 3 0) 1) u v from by decide) u v

theorem local9_alternate_core : relabel (mutate (node 28) 0) perm14 = node 25 := by
  funext u v
  exact (show ∀ u v : Fin 4, (relabel (mutate (node 28) 0) perm14) u v = (node 25) u v from by decide) u v

theorem local10_parent_identity : reverse (relabel (node 29) perm16) = mutate (zeroPhase 1 1) 1 := by
  funext u v
  exact (show ∀ u v : Fin 4, (reverse (relabel (node 29) perm16)) u v = (mutate (zeroPhase 1 1) 1) u v from by decide) u v

theorem zero1_parent1 : Target (mutate (zeroPhase 1 1) 1) := by
  rw [←local10_parent_identity]
  exact Target.reversed (Target.framed (Target.base 29) perm16)

theorem local10_entering_label : perm16.toFun 1 = (3 : Fin 4) := by decide

theorem local10_alternate_root : reverse (relabel (mutate (node 29) 2) perm16) = mutate (zeroPhase 1 0) 1 := by
  funext u v
  exact (show ∀ u v : Fin 4, (reverse (relabel (mutate (node 29) 2) perm16)) u v = (mutate (zeroPhase 1 0) 1) u v from by decide) u v

theorem local10_alternate_core : relabel (mutate (node 29) 2) perm0 = node 18 := by
  funext u v
  exact (show ∀ u v : Fin 4, (relabel (mutate (node 29) 2) perm0) u v = (node 18) u v from by decide) u v

theorem local11_parent_identity : relabel (node 30) perm11 = mutate (zeroPhase 2 1) 1 := by
  funext u v
  exact (show ∀ u v : Fin 4, (relabel (node 30) perm11) u v = (mutate (zeroPhase 2 1) 1) u v from by decide) u v

theorem zero2_parent1 : Target (mutate (zeroPhase 2 1) 1) := by
  rw [←local11_parent_identity]
  exact Target.framed (Target.base 30) perm11

theorem local11_entering_label : perm11.toFun 1 = (3 : Fin 4) := by decide

theorem local11_alternate_root : relabel (mutate (node 30) 1) perm11 = mutate (zeroPhase 2 0) 1 := by
  funext u v
  exact (show ∀ u v : Fin 4, (relabel (mutate (node 30) 1) perm11) u v = (mutate (zeroPhase 2 0) 1) u v from by decide) u v

theorem local11_alternate_core : relabel (mutate (node 30) 1) perm0 = node 19 := by
  funext u v
  exact (show ∀ u v : Fin 4, (relabel (mutate (node 30) 1) perm0) u v = (node 19) u v from by decide) u v

theorem local12_parent_identity : reverse (relabel (node 34) perm17) = mutate (zeroPhase 4 0) 1 := by
  funext u v
  exact (show ∀ u v : Fin 4, (reverse (relabel (node 34) perm17)) u v = (mutate (zeroPhase 4 0) 1) u v from by decide) u v

theorem zero4_parent0 : Target (mutate (zeroPhase 4 0) 1) := by
  rw [←local12_parent_identity]
  exact Target.reversed (Target.framed (Target.base 34) perm17)

theorem local12_entering_label : perm17.toFun 1 = (3 : Fin 4) := by decide

theorem local12_alternate_root : reverse (relabel (mutate (node 34) 2) perm17) = mutate (zeroPhase 4 1) 1 := by
  funext u v
  exact (show ∀ u v : Fin 4, (reverse (relabel (mutate (node 34) 2) perm17)) u v = (mutate (zeroPhase 4 1) 1) u v from by decide) u v

theorem local12_alternate_core : relabel (mutate (node 34) 2) perm12 = node 44 := by
  funext u v
  exact (show ∀ u v : Fin 4, (relabel (mutate (node 34) 2) perm12) u v = (node 44) u v from by decide) u v

theorem local13_parent_identity : relabel (node 35) perm16 = mutate (zeroPhase 5 0) 1 := by
  funext u v
  exact (show ∀ u v : Fin 4, (relabel (node 35) perm16) u v = (mutate (zeroPhase 5 0) 1) u v from by decide) u v

theorem zero5_parent0 : Target (mutate (zeroPhase 5 0) 1) := by
  rw [←local13_parent_identity]
  exact Target.framed (Target.base 35) perm16

theorem local13_entering_label : perm16.toFun 1 = (3 : Fin 4) := by decide

theorem local13_alternate_root : relabel (mutate (node 35) 2) perm16 = mutate (zeroPhase 5 1) 1 := by
  funext u v
  exact (show ∀ u v : Fin 4, (relabel (mutate (node 35) 2) perm16) u v = (mutate (zeroPhase 5 1) 1) u v from by decide) u v

theorem local13_alternate_core : relabel (mutate (node 35) 2) perm0 = node 47 := by
  funext u v
  exact (show ∀ u v : Fin 4, (relabel (mutate (node 35) 2) perm0) u v = (node 47) u v from by decide) u v

theorem local14_parent_identity : reverse (relabel (node 44) perm5) = mutate (zeroPhase 4 1) 1 := by
  funext u v
  exact (show ∀ u v : Fin 4, (reverse (relabel (node 44) perm5)) u v = (mutate (zeroPhase 4 1) 1) u v from by decide) u v

theorem zero4_parent1 : Target (mutate (zeroPhase 4 1) 1) := by
  rw [←local14_parent_identity]
  exact Target.reversed (Target.framed (Target.base 44) perm5)

theorem local14_entering_label : perm5.toFun 1 = (3 : Fin 4) := by decide

theorem local14_alternate_root : reverse (relabel (mutate (node 44) 0) perm5) = mutate (zeroPhase 4 0) 1 := by
  funext u v
  exact (show ∀ u v : Fin 4, (reverse (relabel (mutate (node 44) 0) perm5)) u v = (mutate (zeroPhase 4 0) 1) u v from by decide) u v

theorem local14_alternate_core : relabel (mutate (node 44) 0) perm8 = node 34 := by
  funext u v
  exact (show ∀ u v : Fin 4, (relabel (mutate (node 44) 0) perm8) u v = (node 34) u v from by decide) u v

theorem local15_parent_identity : relabel (node 47) perm16 = mutate (zeroPhase 5 1) 1 := by
  funext u v
  exact (show ∀ u v : Fin 4, (relabel (node 47) perm16) u v = (mutate (zeroPhase 5 1) 1) u v from by decide) u v

theorem zero5_parent1 : Target (mutate (zeroPhase 5 1) 1) := by
  rw [←local15_parent_identity]
  exact Target.framed (Target.base 47) perm16

theorem local15_entering_label : perm16.toFun 1 = (3 : Fin 4) := by decide

theorem local15_alternate_root : relabel (mutate (node 47) 2) perm16 = mutate (zeroPhase 5 0) 1 := by
  funext u v
  exact (show ∀ u v : Fin 4, (relabel (mutate (node 47) 2) perm16) u v = (mutate (zeroPhase 5 0) 1) u v from by decide) u v

theorem local15_alternate_core : relabel (mutate (node 47) 2) perm0 = node 35 := by
  funext u v
  exact (show ∀ u v : Fin 4, (relabel (mutate (node 47) 2) perm0) u v = (node 35) u v from by decide) u v

theorem zero_parent (j : Fin 6) (s : Fin 2) : Target (mutate (zeroPhase j s) 1) := by
  rcases fin6 j with rfl|rfl|rfl|rfl|rfl|rfl <;> rcases fin2 s with rfl|rfl
  · exact zero0_parent0
  · exact zero0_parent1
  · exact zero1_parent0
  · exact zero1_parent1
  · exact zero2_parent0
  · exact zero2_parent1
  · exact zero3_parent0
  · exact zero3_parent1
  · exact zero4_parent0
  · exact zero4_parent1
  · exact zero5_parent0
  · exact zero5_parent1

theorem pendant_parent (j : Fin 2) (s : Fin 2) : Target (mutate (pendantPhase j s) 1) := by
  rcases fin2 j with rfl|rfl <;> rcases fin2 s with rfl|rfl
  · exact pendant0_parent0
  · exact pendant0_parent1
  · exact pendant1_parent0
  · exact pendant1_parent1

def triangleWord (i : Fin 67) (r : Fin 4) : List (Fin 3) := match i.val,r.val with
  | 0,0 => [0]
  | 0,1 => []
  | 0,2 => [0]
  | 0,3 => []
  | 1,0 => []
  | 1,1 => [0]
  | 1,2 => []
  | 1,3 => []
  | 2,0 => []
  | 2,1 => []
  | 2,2 => [1, 0]
  | 2,3 => []
  | 3,0 => []
  | 3,1 => [0]
  | 3,2 => []
  | 3,3 => [1]
  | 4,0 => [0]
  | 4,1 => [0]
  | 4,2 => []
  | 4,3 => []
  | 5,0 => []
  | 5,1 => [0]
  | 5,2 => []
  | 5,3 => [1]
  | 6,0 => []
  | 6,1 => []
  | 6,2 => [0, 1, 0]
  | 6,3 => [0]
  | 7,0 => []
  | 7,1 => []
  | 7,2 => [1, 0]
  | 7,3 => []
  | 8,0 => []
  | 8,1 => []
  | 8,2 => [2, 1, 0]
  | 8,3 => []
  | 9,0 => []
  | 9,1 => []
  | 9,2 => []
  | 9,3 => [0, 1]
  | 10,0 => []
  | 10,1 => [1, 0]
  | 10,2 => []
  | 10,3 => [1]
  | 11,0 => []
  | 11,1 => []
  | 11,2 => []
  | 11,3 => []
  | 12,0 => []
  | 12,1 => []
  | 12,2 => [1]
  | 12,3 => []
  | 13,0 => []
  | 13,1 => [1, 0]
  | 13,2 => []
  | 13,3 => []
  | 14,0 => []
  | 14,1 => []
  | 14,2 => []
  | 14,3 => [0]
  | 15,0 => []
  | 15,1 => [0]
  | 15,2 => [0, 1, 0]
  | 15,3 => []
  | 16,0 => []
  | 16,1 => []
  | 16,2 => [2, 1, 0]
  | 16,3 => []
  | 17,0 => []
  | 17,1 => [0]
  | 17,2 => [0, 2, 1, 0]
  | 17,3 => []
  | 18,0 => []
  | 18,1 => []
  | 18,2 => [1, 2, 1, 0]
  | 18,3 => [1]
  | 19,0 => []
  | 19,1 => [0, 1, 0]
  | 19,2 => []
  | 19,3 => [1]
  | 20,0 => []
  | 20,1 => [2, 1, 0]
  | 20,2 => []
  | 20,3 => []
  | 21,0 => []
  | 21,1 => [0]
  | 21,2 => [0, 1]
  | 21,3 => []
  | 22,0 => []
  | 22,1 => []
  | 22,2 => [2, 1]
  | 22,3 => [2]
  | 23,0 => [0]
  | 23,1 => []
  | 23,2 => []
  | 23,3 => [0]
  | 24,0 => [0]
  | 24,1 => []
  | 24,2 => [1, 0, 1, 0]
  | 24,3 => []
  | 25,0 => []
  | 25,1 => []
  | 25,2 => [0, 2, 1, 0]
  | 25,3 => [0]
  | 26,0 => [0]
  | 26,1 => []
  | 26,2 => [1, 2, 1, 0]
  | 26,3 => []
  | 27,0 => [0]
  | 27,1 => []
  | 27,2 => [1, 0, 2, 1, 0]
  | 27,3 => []
  | 28,0 => []
  | 28,1 => []
  | 28,2 => []
  | 28,3 => [2]
  | 29,0 => []
  | 29,1 => []
  | 29,2 => []
  | 29,3 => [1]
  | 30,0 => []
  | 30,1 => [0]
  | 30,2 => []
  | 30,3 => []
  | 31,0 => []
  | 31,1 => [0, 2, 1, 0]
  | 31,2 => [0]
  | 31,3 => []
  | 32,0 => [0]
  | 32,1 => [1, 2, 1, 0]
  | 32,2 => []
  | 32,3 => []
  | 33,0 => []
  | 33,1 => []
  | 33,2 => [1, 0, 1]
  | 33,3 => [1]
  | 34,0 => []
  | 34,1 => []
  | 34,2 => [0, 2, 1]
  | 34,3 => [2]
  | 35,0 => []
  | 35,1 => []
  | 35,2 => [1, 2, 1]
  | 35,3 => [2]
  | 36,0 => [0]
  | 36,1 => []
  | 36,2 => [0]
  | 36,3 => []
  | 37,0 => []
  | 37,1 => []
  | 37,2 => [0, 1, 0, 1, 0]
  | 37,3 => [0]
  | 38,0 => []
  | 38,1 => [0]
  | 38,2 => [0, 1, 2, 1, 0]
  | 38,3 => []
  | 39,0 => []
  | 39,1 => []
  | 39,2 => [0, 1, 0, 2, 1, 0]
  | 39,3 => [0]
  | 40,0 => [0]
  | 40,1 => [1]
  | 40,2 => []
  | 40,3 => []
  | 41,0 => []
  | 41,1 => []
  | 41,2 => [1]
  | 41,3 => [2]
  | 42,0 => []
  | 42,1 => [0]
  | 42,2 => []
  | 42,3 => [1]
  | 43,0 => [1]
  | 43,1 => [0]
  | 43,2 => []
  | 43,3 => []
  | 44,0 => [0]
  | 44,1 => []
  | 44,2 => []
  | 44,3 => []
  | 45,0 => []
  | 45,1 => [1, 0, 2, 1, 0]
  | 45,2 => []
  | 45,3 => [2]
  | 46,0 => []
  | 46,1 => [0, 1, 2, 1, 0]
  | 46,2 => []
  | 46,3 => [0]
  | 47,0 => []
  | 47,1 => []
  | 47,2 => [1]
  | 47,3 => []
  | 48,0 => []
  | 48,1 => [1]
  | 48,2 => []
  | 48,3 => [1]
  | 49,0 => [0]
  | 49,1 => [1]
  | 49,2 => []
  | 49,3 => []
  | 50,0 => [1]
  | 50,1 => []
  | 50,2 => []
  | 50,3 => [0]
  | 51,0 => []
  | 51,1 => []
  | 51,2 => [1, 0, 1, 2, 1, 0]
  | 51,3 => [1]
  | 52,0 => [1]
  | 52,1 => [0]
  | 52,2 => []
  | 52,3 => []
  | 53,0 => [1]
  | 53,1 => []
  | 53,2 => []
  | 53,3 => [0]
  | 54,0 => []
  | 54,1 => [1]
  | 54,2 => [0]
  | 54,3 => []
  | 55,0 => []
  | 55,1 => [0, 1]
  | 55,2 => []
  | 55,3 => [1]
  | 56,0 => [0]
  | 56,1 => [1]
  | 56,2 => []
  | 56,3 => []
  | 57,0 => []
  | 57,1 => []
  | 57,2 => [1]
  | 57,3 => [2]
  | 58,0 => [0]
  | 58,1 => []
  | 58,2 => []
  | 58,3 => [0]
  | 59,0 => []
  | 59,1 => [0]
  | 59,2 => [1]
  | 59,3 => []
  | 60,0 => [0, 1]
  | 60,1 => []
  | 60,2 => []
  | 60,3 => [0]
  | 61,0 => []
  | 61,1 => [1]
  | 61,2 => []
  | 61,3 => [1]
  | 62,0 => [1]
  | 62,1 => []
  | 62,2 => [1]
  | 62,3 => []
  | 63,0 => [0, 1]
  | 63,1 => []
  | 63,2 => []
  | 63,3 => [0]
  | 64,0 => [0, 1]
  | 64,1 => []
  | 64,2 => []
  | 64,3 => [0]
  | 65,0 => [1, 0]
  | 65,1 => []
  | 65,2 => []
  | 65,3 => [0]
  | 66,0 => []
  | 66,1 => [0, 1]
  | 66,2 => []
  | _,_ => [1]

def triangleRank (i : Fin 67) (r : Fin 4) (j : Fin 3) : Nat :=
  match i.val,r.val,j.val with
  | 0,0,0 => 1
  | 0,0,1 => 0
  | 0,0,2 => 2
  | 0,1,0 => 1
  | 0,1,1 => 0
  | 0,1,2 => 2
  | 0,2,0 => 1
  | 0,2,1 => 2
  | 0,2,2 => 0
  | 0,3,0 => 2
  | 0,3,1 => 0
  | 0,3,2 => 1
  | 1,0,0 => 0
  | 1,0,1 => 1
  | 1,0,2 => 2
  | 1,1,0 => 1
  | 1,1,1 => 0
  | 1,1,2 => 2
  | 1,2,0 => 1
  | 1,2,1 => 2
  | 1,2,2 => 0
  | 1,3,0 => 0
  | 1,3,1 => 1
  | 1,3,2 => 2
  | 2,0,0 => 1
  | 2,0,1 => 0
  | 2,0,2 => 2
  | 2,1,0 => 2
  | 2,1,1 => 0
  | 2,1,2 => 1
  | 2,2,0 => 1
  | 2,2,1 => 2
  | 2,2,2 => 0
  | 2,3,0 => 1
  | 2,3,1 => 2
  | 2,3,2 => 0
  | 3,0,0 => 1
  | 3,0,1 => 0
  | 3,0,2 => 2
  | 3,1,0 => 1
  | 3,1,1 => 0
  | 3,1,2 => 2
  | 3,2,0 => 2
  | 3,2,1 => 0
  | 3,2,2 => 1
  | 3,3,0 => 0
  | 3,3,1 => 1
  | 3,3,2 => 2
  | 4,0,0 => 1
  | 4,0,1 => 2
  | 4,0,2 => 0
  | 4,1,0 => 1
  | 4,1,1 => 2
  | 4,1,2 => 0
  | 4,2,0 => 0
  | 4,2,1 => 1
  | 4,2,2 => 2
  | 4,3,0 => 1
  | 4,3,1 => 2
  | 4,3,2 => 0
  | 5,0,0 => 0
  | 5,0,1 => 2
  | 5,0,2 => 1
  | 5,1,0 => 1
  | 5,1,1 => 2
  | 5,1,2 => 0
  | 5,2,0 => 0
  | 5,2,1 => 1
  | 5,2,2 => 2
  | 5,3,0 => 2
  | 5,3,1 => 1
  | 5,3,2 => 0
  | 6,0,0 => 2
  | 6,0,1 => 0
  | 6,0,2 => 1
  | 6,1,0 => 0
  | 6,1,1 => 1
  | 6,1,2 => 2
  | 6,2,0 => 1
  | 6,2,1 => 2
  | 6,2,2 => 0
  | 6,3,0 => 1
  | 6,3,1 => 2
  | 6,3,2 => 0
  | 7,0,0 => 0
  | 7,0,1 => 1
  | 7,0,2 => 2
  | 7,1,0 => 1
  | 7,1,1 => 2
  | 7,1,2 => 0
  | 7,2,0 => 1
  | 7,2,1 => 2
  | 7,2,2 => 0
  | 7,3,0 => 0
  | 7,3,1 => 1
  | 7,3,2 => 2
  | 8,0,0 => 2
  | 8,0,1 => 0
  | 8,0,2 => 1
  | 8,1,0 => 1
  | 8,1,1 => 0
  | 8,1,2 => 2
  | 8,2,0 => 1
  | 8,2,1 => 2
  | 8,2,2 => 0
  | 8,3,0 => 2
  | 8,3,1 => 1
  | 8,3,2 => 0
  | 9,0,0 => 0
  | 9,0,1 => 1
  | 9,0,2 => 2
  | 9,1,0 => 1
  | 9,1,1 => 0
  | 9,1,2 => 2
  | 9,2,0 => 0
  | 9,2,1 => 1
  | 9,2,2 => 2
  | 9,3,0 => 0
  | 9,3,1 => 1
  | 9,3,2 => 2
  | 10,0,0 => 0
  | 10,0,1 => 2
  | 10,0,2 => 1
  | 10,1,0 => 1
  | 10,1,1 => 0
  | 10,1,2 => 2
  | 10,2,0 => 0
  | 10,2,1 => 1
  | 10,2,2 => 2
  | 10,3,0 => 2
  | 10,3,1 => 1
  | 10,3,2 => 0
  | 11,0,0 => 2
  | 11,0,1 => 1
  | 11,0,2 => 0
  | 11,1,0 => 0
  | 11,1,1 => 2
  | 11,1,2 => 1
  | 11,2,0 => 1
  | 11,2,1 => 0
  | 11,2,2 => 2
  | 11,3,0 => 2
  | 11,3,1 => 1
  | 11,3,2 => 0
  | 12,0,0 => 1
  | 12,0,1 => 2
  | 12,0,2 => 0
  | 12,1,0 => 1
  | 12,1,1 => 0
  | 12,1,2 => 2
  | 12,2,0 => 0
  | 12,2,1 => 1
  | 12,2,2 => 2
  | 12,3,0 => 2
  | 12,3,1 => 0
  | 12,3,2 => 1
  | 13,0,0 => 1
  | 13,0,1 => 0
  | 13,0,2 => 2
  | 13,1,0 => 1
  | 13,1,1 => 2
  | 13,1,2 => 0
  | 13,2,0 => 2
  | 13,2,1 => 0
  | 13,2,2 => 1
  | 13,3,0 => 0
  | 13,3,1 => 2
  | 13,3,2 => 1
  | 14,0,0 => 1
  | 14,0,1 => 2
  | 14,0,2 => 0
  | 14,1,0 => 1
  | 14,1,1 => 0
  | 14,1,2 => 2
  | 14,2,0 => 0
  | 14,2,1 => 2
  | 14,2,2 => 1
  | 14,3,0 => 1
  | 14,3,1 => 0
  | 14,3,2 => 2
  | 15,0,0 => 1
  | 15,0,1 => 2
  | 15,0,2 => 0
  | 15,1,0 => 1
  | 15,1,1 => 2
  | 15,1,2 => 0
  | 15,2,0 => 1
  | 15,2,1 => 2
  | 15,2,2 => 0
  | 15,3,0 => 2
  | 15,3,1 => 0
  | 15,3,2 => 1
  | 16,0,0 => 1
  | 16,0,1 => 2
  | 16,0,2 => 0
  | 16,1,0 => 0
  | 16,1,1 => 1
  | 16,1,2 => 2
  | 16,2,0 => 1
  | 16,2,1 => 2
  | 16,2,2 => 0
  | 16,3,0 => 1
  | 16,3,1 => 0
  | 16,3,2 => 2
  | 17,0,0 => 1
  | 17,0,1 => 0
  | 17,0,2 => 2
  | 17,1,0 => 1
  | 17,1,1 => 0
  | 17,1,2 => 2
  | 17,2,0 => 1
  | 17,2,1 => 2
  | 17,2,2 => 0
  | 17,3,0 => 0
  | 17,3,1 => 2
  | 17,3,2 => 1
  | 18,0,0 => 0
  | 18,0,1 => 1
  | 18,0,2 => 2
  | 18,1,0 => 2
  | 18,1,1 => 0
  | 18,1,2 => 1
  | 18,2,0 => 1
  | 18,2,1 => 2
  | 18,2,2 => 0
  | 18,3,0 => 2
  | 18,3,1 => 1
  | 18,3,2 => 0
  | 19,0,0 => 1
  | 19,0,1 => 0
  | 19,0,2 => 2
  | 19,1,0 => 1
  | 19,1,1 => 0
  | 19,1,2 => 2
  | 19,2,0 => 2
  | 19,2,1 => 0
  | 19,2,2 => 1
  | 19,3,0 => 0
  | 19,3,1 => 1
  | 19,3,2 => 2
  | 20,0,0 => 0
  | 20,0,1 => 1
  | 20,0,2 => 2
  | 20,1,0 => 1
  | 20,1,1 => 0
  | 20,1,2 => 2
  | 20,2,0 => 1
  | 20,2,1 => 2
  | 20,2,2 => 0
  | 20,3,0 => 0
  | 20,3,1 => 1
  | 20,3,2 => 2
  | 21,0,0 => 0
  | 21,0,1 => 1
  | 21,0,2 => 2
  | 21,1,0 => 1
  | 21,1,1 => 0
  | 21,1,2 => 2
  | 21,2,0 => 0
  | 21,2,1 => 1
  | 21,2,2 => 2
  | 21,3,0 => 0
  | 21,3,1 => 1
  | 21,3,2 => 2
  | 22,0,0 => 0
  | 22,0,1 => 1
  | 22,0,2 => 2
  | 22,1,0 => 2
  | 22,1,1 => 0
  | 22,1,2 => 1
  | 22,2,0 => 0
  | 22,2,1 => 1
  | 22,2,2 => 2
  | 22,3,0 => 0
  | 22,3,1 => 2
  | 22,3,2 => 1
  | 23,0,0 => 1
  | 23,0,1 => 2
  | 23,0,2 => 0
  | 23,1,0 => 0
  | 23,1,1 => 2
  | 23,1,2 => 1
  | 23,2,0 => 1
  | 23,2,1 => 0
  | 23,2,2 => 2
  | 23,3,0 => 1
  | 23,3,1 => 2
  | 23,3,2 => 0
  | 24,0,0 => 1
  | 24,0,1 => 2
  | 24,0,2 => 0
  | 24,1,0 => 2
  | 24,1,1 => 1
  | 24,1,2 => 0
  | 24,2,0 => 1
  | 24,2,1 => 2
  | 24,2,2 => 0
  | 24,3,0 => 1
  | 24,3,1 => 2
  | 24,3,2 => 0
  | 25,0,0 => 0
  | 25,0,1 => 1
  | 25,0,2 => 2
  | 25,1,0 => 2
  | 25,1,1 => 0
  | 25,1,2 => 1
  | 25,2,0 => 1
  | 25,2,1 => 2
  | 25,2,2 => 0
  | 25,3,0 => 1
  | 25,3,1 => 0
  | 25,3,2 => 2
  | 26,0,0 => 1
  | 26,0,1 => 2
  | 26,0,2 => 0
  | 26,1,0 => 1
  | 26,1,1 => 2
  | 26,1,2 => 0
  | 26,2,0 => 1
  | 26,2,1 => 2
  | 26,2,2 => 0
  | 26,3,0 => 0
  | 26,3,1 => 2
  | 26,3,2 => 1
  | 27,0,0 => 1
  | 27,0,1 => 0
  | 27,0,2 => 2
  | 27,1,0 => 0
  | 27,1,1 => 1
  | 27,1,2 => 2
  | 27,2,0 => 1
  | 27,2,1 => 2
  | 27,2,2 => 0
  | 27,3,0 => 1
  | 27,3,1 => 0
  | 27,3,2 => 2
  | 28,0,0 => 0
  | 28,0,1 => 2
  | 28,0,2 => 1
  | 28,1,0 => 2
  | 28,1,1 => 1
  | 28,1,2 => 0
  | 28,2,0 => 0
  | 28,2,1 => 1
  | 28,2,2 => 2
  | 28,3,0 => 0
  | 28,3,1 => 2
  | 28,3,2 => 1
  | 29,0,0 => 1
  | 29,0,1 => 0
  | 29,0,2 => 2
  | 29,1,0 => 1
  | 29,1,1 => 2
  | 29,1,2 => 0
  | 29,2,0 => 2
  | 29,2,1 => 0
  | 29,2,2 => 1
  | 29,3,0 => 0
  | 29,3,1 => 1
  | 29,3,2 => 2
  | 30,0,0 => 0
  | 30,0,1 => 1
  | 30,0,2 => 2
  | 30,1,0 => 1
  | 30,1,1 => 0
  | 30,1,2 => 2
  | 30,2,0 => 1
  | 30,2,1 => 2
  | 30,2,2 => 0
  | 30,3,0 => 0
  | 30,3,1 => 1
  | 30,3,2 => 2
  | 31,0,0 => 1
  | 31,0,1 => 2
  | 31,0,2 => 0
  | 31,1,0 => 1
  | 31,1,1 => 0
  | 31,1,2 => 2
  | 31,2,0 => 1
  | 31,2,1 => 2
  | 31,2,2 => 0
  | 31,3,0 => 2
  | 31,3,1 => 0
  | 31,3,2 => 1
  | 32,0,0 => 1
  | 32,0,1 => 2
  | 32,0,2 => 0
  | 32,1,0 => 1
  | 32,1,1 => 0
  | 32,1,2 => 2
  | 32,2,0 => 0
  | 32,2,1 => 1
  | 32,2,2 => 2
  | 32,3,0 => 1
  | 32,3,1 => 2
  | 32,3,2 => 0
  | 33,0,0 => 2
  | 33,0,1 => 0
  | 33,0,2 => 1
  | 33,1,0 => 0
  | 33,1,1 => 1
  | 33,1,2 => 2
  | 33,2,0 => 0
  | 33,2,1 => 1
  | 33,2,2 => 2
  | 33,3,0 => 0
  | 33,3,1 => 1
  | 33,3,2 => 2
  | 34,0,0 => 2
  | 34,0,1 => 0
  | 34,0,2 => 1
  | 34,1,0 => 0
  | 34,1,1 => 1
  | 34,1,2 => 2
  | 34,2,0 => 0
  | 34,2,1 => 1
  | 34,2,2 => 2
  | 34,3,0 => 2
  | 34,3,1 => 0
  | 34,3,2 => 1
  | 35,0,0 => 2
  | 35,0,1 => 0
  | 35,0,2 => 1
  | 35,1,0 => 0
  | 35,1,1 => 1
  | 35,1,2 => 2
  | 35,2,0 => 0
  | 35,2,1 => 1
  | 35,2,2 => 2
  | 35,3,0 => 2
  | 35,3,1 => 0
  | 35,3,2 => 1
  | 36,0,0 => 1
  | 36,0,1 => 2
  | 36,0,2 => 0
  | 36,1,0 => 2
  | 36,1,1 => 1
  | 36,1,2 => 0
  | 36,2,0 => 1
  | 36,2,1 => 0
  | 36,2,2 => 2
  | 36,3,0 => 1
  | 36,3,1 => 2
  | 36,3,2 => 0
  | 37,0,0 => 2
  | 37,0,1 => 1
  | 37,0,2 => 0
  | 37,1,0 => 0
  | 37,1,1 => 2
  | 37,1,2 => 1
  | 37,2,0 => 1
  | 37,2,1 => 2
  | 37,2,2 => 0
  | 37,3,0 => 1
  | 37,3,1 => 2
  | 37,3,2 => 0
  | 38,0,0 => 2
  | 38,0,1 => 1
  | 38,0,2 => 0
  | 38,1,0 => 1
  | 38,1,1 => 2
  | 38,1,2 => 0
  | 38,2,0 => 1
  | 38,2,1 => 2
  | 38,2,2 => 0
  | 38,3,0 => 2
  | 38,3,1 => 1
  | 38,3,2 => 0
  | 39,0,0 => 0
  | 39,0,1 => 1
  | 39,0,2 => 2
  | 39,1,0 => 2
  | 39,1,1 => 0
  | 39,1,2 => 1
  | 39,2,0 => 1
  | 39,2,1 => 2
  | 39,2,2 => 0
  | 39,3,0 => 1
  | 39,3,1 => 0
  | 39,3,2 => 2
  | 40,0,0 => 1
  | 40,0,1 => 2
  | 40,0,2 => 0
  | 40,1,0 => 0
  | 40,1,1 => 1
  | 40,1,2 => 2
  | 40,2,0 => 1
  | 40,2,1 => 0
  | 40,2,2 => 2
  | 40,3,0 => 2
  | 40,3,1 => 1
  | 40,3,2 => 0
  | 41,0,0 => 2
  | 41,0,1 => 1
  | 41,0,2 => 0
  | 41,1,0 => 0
  | 41,1,1 => 2
  | 41,1,2 => 1
  | 41,2,0 => 0
  | 41,2,1 => 1
  | 41,2,2 => 2
  | 41,3,0 => 2
  | 41,3,1 => 0
  | 41,3,2 => 1
  | 42,0,0 => 0
  | 42,0,1 => 2
  | 42,0,2 => 1
  | 42,1,0 => 1
  | 42,1,1 => 2
  | 42,1,2 => 0
  | 42,2,0 => 0
  | 42,2,1 => 1
  | 42,2,2 => 2
  | 42,3,0 => 2
  | 42,3,1 => 1
  | 42,3,2 => 0
  | 43,0,0 => 0
  | 43,0,1 => 1
  | 43,0,2 => 2
  | 43,1,0 => 1
  | 43,1,1 => 2
  | 43,1,2 => 0
  | 43,2,0 => 0
  | 43,2,1 => 1
  | 43,2,2 => 2
  | 43,3,0 => 1
  | 43,3,1 => 2
  | 43,3,2 => 0
  | 44,0,0 => 1
  | 44,0,1 => 2
  | 44,0,2 => 0
  | 44,1,0 => 2
  | 44,1,1 => 1
  | 44,1,2 => 0
  | 44,2,0 => 0
  | 44,2,1 => 1
  | 44,2,2 => 2
  | 44,3,0 => 1
  | 44,3,1 => 2
  | 44,3,2 => 0
  | 45,0,0 => 2
  | 45,0,1 => 0
  | 45,0,2 => 1
  | 45,1,0 => 1
  | 45,1,1 => 0
  | 45,1,2 => 2
  | 45,2,0 => 2
  | 45,2,1 => 1
  | 45,2,2 => 0
  | 45,3,0 => 2
  | 45,3,1 => 0
  | 45,3,2 => 1
  | 46,0,0 => 1
  | 46,0,1 => 0
  | 46,0,2 => 2
  | 46,1,0 => 1
  | 46,1,1 => 0
  | 46,1,2 => 2
  | 46,2,0 => 2
  | 46,2,1 => 0
  | 46,2,2 => 1
  | 46,3,0 => 1
  | 46,3,1 => 2
  | 46,3,2 => 0
  | 47,0,0 => 1
  | 47,0,1 => 2
  | 47,0,2 => 0
  | 47,1,0 => 1
  | 47,1,1 => 0
  | 47,1,2 => 2
  | 47,2,0 => 0
  | 47,2,1 => 1
  | 47,2,2 => 2
  | 47,3,0 => 2
  | 47,3,1 => 0
  | 47,3,2 => 1
  | 48,0,0 => 1
  | 48,0,1 => 2
  | 48,0,2 => 0
  | 48,1,0 => 0
  | 48,1,1 => 1
  | 48,1,2 => 2
  | 48,2,0 => 0
  | 48,2,1 => 2
  | 48,2,2 => 1
  | 48,3,0 => 2
  | 48,3,1 => 1
  | 48,3,2 => 0
  | 49,0,0 => 1
  | 49,0,1 => 0
  | 49,0,2 => 2
  | 49,1,0 => 2
  | 49,1,1 => 1
  | 49,1,2 => 0
  | 49,2,0 => 1
  | 49,2,1 => 2
  | 49,2,2 => 0
  | 49,3,0 => 0
  | 49,3,1 => 1
  | 49,3,2 => 2
  | 50,0,0 => 2
  | 50,0,1 => 1
  | 50,0,2 => 0
  | 50,1,0 => 1
  | 50,1,1 => 0
  | 50,1,2 => 2
  | 50,2,0 => 0
  | 50,2,1 => 2
  | 50,2,2 => 1
  | 50,3,0 => 1
  | 50,3,1 => 0
  | 50,3,2 => 2
  | 51,0,0 => 0
  | 51,0,1 => 2
  | 51,0,2 => 1
  | 51,1,0 => 2
  | 51,1,1 => 1
  | 51,1,2 => 0
  | 51,2,0 => 1
  | 51,2,1 => 2
  | 51,2,2 => 0
  | 51,3,0 => 2
  | 51,3,1 => 1
  | 51,3,2 => 0
  | 52,0,0 => 2
  | 52,0,1 => 1
  | 52,0,2 => 0
  | 52,1,0 => 1
  | 52,1,1 => 0
  | 52,1,2 => 2
  | 52,2,0 => 2
  | 52,2,1 => 1
  | 52,2,2 => 0
  | 52,3,0 => 1
  | 52,3,1 => 0
  | 52,3,2 => 2
  | 53,0,0 => 0
  | 53,0,1 => 1
  | 53,0,2 => 2
  | 53,1,0 => 1
  | 53,1,1 => 2
  | 53,1,2 => 0
  | 53,2,0 => 2
  | 53,2,1 => 0
  | 53,2,2 => 1
  | 53,3,0 => 1
  | 53,3,1 => 2
  | 53,3,2 => 0
  | 54,0,0 => 1
  | 54,0,1 => 0
  | 54,0,2 => 2
  | 54,1,0 => 2
  | 54,1,1 => 1
  | 54,1,2 => 0
  | 54,2,0 => 1
  | 54,2,1 => 0
  | 54,2,2 => 2
  | 54,3,0 => 0
  | 54,3,1 => 2
  | 54,3,2 => 1
  | 55,0,0 => 2
  | 55,0,1 => 0
  | 55,0,2 => 1
  | 55,1,0 => 0
  | 55,1,1 => 1
  | 55,1,2 => 2
  | 55,2,0 => 2
  | 55,2,1 => 1
  | 55,2,2 => 0
  | 55,3,0 => 0
  | 55,3,1 => 1
  | 55,3,2 => 2
  | 56,0,0 => 1
  | 56,0,1 => 0
  | 56,0,2 => 2
  | 56,1,0 => 2
  | 56,1,1 => 1
  | 56,1,2 => 0
  | 56,2,0 => 1
  | 56,2,1 => 2
  | 56,2,2 => 0
  | 56,3,0 => 0
  | 56,3,1 => 1
  | 56,3,2 => 2
  | 57,0,0 => 0
  | 57,0,1 => 1
  | 57,0,2 => 2
  | 57,1,0 => 2
  | 57,1,1 => 0
  | 57,1,2 => 1
  | 57,2,0 => 2
  | 57,2,1 => 1
  | 57,2,2 => 0
  | 57,3,0 => 0
  | 57,3,1 => 2
  | 57,3,2 => 1
  | 58,0,0 => 1
  | 58,0,1 => 0
  | 58,0,2 => 2
  | 58,1,0 => 2
  | 58,1,1 => 0
  | 58,1,2 => 1
  | 58,2,0 => 1
  | 58,2,1 => 2
  | 58,2,2 => 0
  | 58,3,0 => 1
  | 58,3,1 => 0
  | 58,3,2 => 2
  | 59,0,0 => 0
  | 59,0,1 => 1
  | 59,0,2 => 2
  | 59,1,0 => 1
  | 59,1,1 => 0
  | 59,1,2 => 2
  | 59,2,0 => 2
  | 59,2,1 => 1
  | 59,2,2 => 0
  | 59,3,0 => 0
  | 59,3,1 => 1
  | 59,3,2 => 2
  | 60,0,0 => 2
  | 60,0,1 => 1
  | 60,0,2 => 0
  | 60,1,0 => 0
  | 60,1,1 => 2
  | 60,1,2 => 1
  | 60,2,0 => 1
  | 60,2,1 => 0
  | 60,2,2 => 2
  | 60,3,0 => 1
  | 60,3,1 => 2
  | 60,3,2 => 0
  | 61,0,0 => 1
  | 61,0,1 => 0
  | 61,0,2 => 2
  | 61,1,0 => 2
  | 61,1,1 => 1
  | 61,1,2 => 0
  | 61,2,0 => 2
  | 61,2,1 => 0
  | 61,2,2 => 1
  | 61,3,0 => 0
  | 61,3,1 => 1
  | 61,3,2 => 2
  | 62,0,0 => 0
  | 62,0,1 => 1
  | 62,0,2 => 2
  | 62,1,0 => 1
  | 62,1,1 => 2
  | 62,1,2 => 0
  | 62,2,0 => 2
  | 62,2,1 => 1
  | 62,2,2 => 0
  | 62,3,0 => 0
  | 62,3,1 => 2
  | 62,3,2 => 1
  | 63,0,0 => 0
  | 63,0,1 => 1
  | 63,0,2 => 2
  | 63,1,0 => 2
  | 63,1,1 => 0
  | 63,1,2 => 1
  | 63,2,0 => 1
  | 63,2,1 => 2
  | 63,2,2 => 0
  | 63,3,0 => 1
  | 63,3,1 => 0
  | 63,3,2 => 2
  | 64,0,0 => 2
  | 64,0,1 => 1
  | 64,0,2 => 0
  | 64,1,0 => 0
  | 64,1,1 => 2
  | 64,1,2 => 1
  | 64,2,0 => 1
  | 64,2,1 => 0
  | 64,2,2 => 2
  | 64,3,0 => 1
  | 64,3,1 => 2
  | 64,3,2 => 0
  | 65,0,0 => 1
  | 65,0,1 => 0
  | 65,0,2 => 2
  | 65,1,0 => 1
  | 65,1,1 => 2
  | 65,1,2 => 0
  | 65,2,0 => 2
  | 65,2,1 => 0
  | 65,2,2 => 1
  | 65,3,0 => 1
  | 65,3,1 => 2
  | 65,3,2 => 0
  | 66,0,0 => 0
  | 66,0,1 => 2
  | 66,0,2 => 1
  | 66,1,0 => 2
  | 66,1,1 => 1
  | 66,1,2 => 0
  | 66,2,0 => 0
  | 66,2,1 => 1
  | 66,2,2 => 2
  | 66,3,0 => 2
  | 66,3,1 => 1
  | _,_,_ => 0

theorem triangle_witness0 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 0) (TriangleRegions.deleteVertex r))
      (triangleWord 0 r)) := by
  refine ⟨triangleRank 0 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 0) (TriangleRegions.deleteVertex r))
      (triangleWord 0 r) a b → triangleRank 0 r a < triangleRank 0 r b from by decide) r

theorem triangle_witness1 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 1) (TriangleRegions.deleteVertex r))
      (triangleWord 1 r)) := by
  refine ⟨triangleRank 1 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 1) (TriangleRegions.deleteVertex r))
      (triangleWord 1 r) a b → triangleRank 1 r a < triangleRank 1 r b from by decide) r

theorem triangle_witness2 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 2) (TriangleRegions.deleteVertex r))
      (triangleWord 2 r)) := by
  refine ⟨triangleRank 2 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 2) (TriangleRegions.deleteVertex r))
      (triangleWord 2 r) a b → triangleRank 2 r a < triangleRank 2 r b from by decide) r

theorem triangle_witness3 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 3) (TriangleRegions.deleteVertex r))
      (triangleWord 3 r)) := by
  refine ⟨triangleRank 3 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 3) (TriangleRegions.deleteVertex r))
      (triangleWord 3 r) a b → triangleRank 3 r a < triangleRank 3 r b from by decide) r

theorem triangle_witness4 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 4) (TriangleRegions.deleteVertex r))
      (triangleWord 4 r)) := by
  refine ⟨triangleRank 4 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 4) (TriangleRegions.deleteVertex r))
      (triangleWord 4 r) a b → triangleRank 4 r a < triangleRank 4 r b from by decide) r

theorem triangle_witness5 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 5) (TriangleRegions.deleteVertex r))
      (triangleWord 5 r)) := by
  refine ⟨triangleRank 5 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 5) (TriangleRegions.deleteVertex r))
      (triangleWord 5 r) a b → triangleRank 5 r a < triangleRank 5 r b from by decide) r

theorem triangle_witness6 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 6) (TriangleRegions.deleteVertex r))
      (triangleWord 6 r)) := by
  refine ⟨triangleRank 6 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 6) (TriangleRegions.deleteVertex r))
      (triangleWord 6 r) a b → triangleRank 6 r a < triangleRank 6 r b from by decide) r

theorem triangle_witness7 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 7) (TriangleRegions.deleteVertex r))
      (triangleWord 7 r)) := by
  refine ⟨triangleRank 7 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 7) (TriangleRegions.deleteVertex r))
      (triangleWord 7 r) a b → triangleRank 7 r a < triangleRank 7 r b from by decide) r

theorem triangle_witness8 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 8) (TriangleRegions.deleteVertex r))
      (triangleWord 8 r)) := by
  refine ⟨triangleRank 8 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 8) (TriangleRegions.deleteVertex r))
      (triangleWord 8 r) a b → triangleRank 8 r a < triangleRank 8 r b from by decide) r

theorem triangle_witness9 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 9) (TriangleRegions.deleteVertex r))
      (triangleWord 9 r)) := by
  refine ⟨triangleRank 9 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 9) (TriangleRegions.deleteVertex r))
      (triangleWord 9 r) a b → triangleRank 9 r a < triangleRank 9 r b from by decide) r

theorem triangle_witness10 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 10) (TriangleRegions.deleteVertex r))
      (triangleWord 10 r)) := by
  refine ⟨triangleRank 10 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 10) (TriangleRegions.deleteVertex r))
      (triangleWord 10 r) a b → triangleRank 10 r a < triangleRank 10 r b from by decide) r

theorem triangle_witness11 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 11) (TriangleRegions.deleteVertex r))
      (triangleWord 11 r)) := by
  refine ⟨triangleRank 11 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 11) (TriangleRegions.deleteVertex r))
      (triangleWord 11 r) a b → triangleRank 11 r a < triangleRank 11 r b from by decide) r

theorem triangle_witness12 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 12) (TriangleRegions.deleteVertex r))
      (triangleWord 12 r)) := by
  refine ⟨triangleRank 12 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 12) (TriangleRegions.deleteVertex r))
      (triangleWord 12 r) a b → triangleRank 12 r a < triangleRank 12 r b from by decide) r

theorem triangle_witness13 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 13) (TriangleRegions.deleteVertex r))
      (triangleWord 13 r)) := by
  refine ⟨triangleRank 13 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 13) (TriangleRegions.deleteVertex r))
      (triangleWord 13 r) a b → triangleRank 13 r a < triangleRank 13 r b from by decide) r

theorem triangle_witness14 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 14) (TriangleRegions.deleteVertex r))
      (triangleWord 14 r)) := by
  refine ⟨triangleRank 14 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 14) (TriangleRegions.deleteVertex r))
      (triangleWord 14 r) a b → triangleRank 14 r a < triangleRank 14 r b from by decide) r

theorem triangle_witness15 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 15) (TriangleRegions.deleteVertex r))
      (triangleWord 15 r)) := by
  refine ⟨triangleRank 15 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 15) (TriangleRegions.deleteVertex r))
      (triangleWord 15 r) a b → triangleRank 15 r a < triangleRank 15 r b from by decide) r

theorem triangle_witness16 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 16) (TriangleRegions.deleteVertex r))
      (triangleWord 16 r)) := by
  refine ⟨triangleRank 16 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 16) (TriangleRegions.deleteVertex r))
      (triangleWord 16 r) a b → triangleRank 16 r a < triangleRank 16 r b from by decide) r

theorem triangle_witness17 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 17) (TriangleRegions.deleteVertex r))
      (triangleWord 17 r)) := by
  refine ⟨triangleRank 17 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 17) (TriangleRegions.deleteVertex r))
      (triangleWord 17 r) a b → triangleRank 17 r a < triangleRank 17 r b from by decide) r

theorem triangle_witness18 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 18) (TriangleRegions.deleteVertex r))
      (triangleWord 18 r)) := by
  refine ⟨triangleRank 18 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 18) (TriangleRegions.deleteVertex r))
      (triangleWord 18 r) a b → triangleRank 18 r a < triangleRank 18 r b from by decide) r

theorem triangle_witness19 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 19) (TriangleRegions.deleteVertex r))
      (triangleWord 19 r)) := by
  refine ⟨triangleRank 19 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 19) (TriangleRegions.deleteVertex r))
      (triangleWord 19 r) a b → triangleRank 19 r a < triangleRank 19 r b from by decide) r

theorem triangle_witness20 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 20) (TriangleRegions.deleteVertex r))
      (triangleWord 20 r)) := by
  refine ⟨triangleRank 20 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 20) (TriangleRegions.deleteVertex r))
      (triangleWord 20 r) a b → triangleRank 20 r a < triangleRank 20 r b from by decide) r

theorem triangle_witness21 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 21) (TriangleRegions.deleteVertex r))
      (triangleWord 21 r)) := by
  refine ⟨triangleRank 21 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 21) (TriangleRegions.deleteVertex r))
      (triangleWord 21 r) a b → triangleRank 21 r a < triangleRank 21 r b from by decide) r

theorem triangle_witness22 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 22) (TriangleRegions.deleteVertex r))
      (triangleWord 22 r)) := by
  refine ⟨triangleRank 22 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 22) (TriangleRegions.deleteVertex r))
      (triangleWord 22 r) a b → triangleRank 22 r a < triangleRank 22 r b from by decide) r

theorem triangle_witness23 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 23) (TriangleRegions.deleteVertex r))
      (triangleWord 23 r)) := by
  refine ⟨triangleRank 23 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 23) (TriangleRegions.deleteVertex r))
      (triangleWord 23 r) a b → triangleRank 23 r a < triangleRank 23 r b from by decide) r

theorem triangle_witness24 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 24) (TriangleRegions.deleteVertex r))
      (triangleWord 24 r)) := by
  refine ⟨triangleRank 24 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 24) (TriangleRegions.deleteVertex r))
      (triangleWord 24 r) a b → triangleRank 24 r a < triangleRank 24 r b from by decide) r

theorem triangle_witness25 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 25) (TriangleRegions.deleteVertex r))
      (triangleWord 25 r)) := by
  refine ⟨triangleRank 25 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 25) (TriangleRegions.deleteVertex r))
      (triangleWord 25 r) a b → triangleRank 25 r a < triangleRank 25 r b from by decide) r

theorem triangle_witness26 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 26) (TriangleRegions.deleteVertex r))
      (triangleWord 26 r)) := by
  refine ⟨triangleRank 26 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 26) (TriangleRegions.deleteVertex r))
      (triangleWord 26 r) a b → triangleRank 26 r a < triangleRank 26 r b from by decide) r

theorem triangle_witness27 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 27) (TriangleRegions.deleteVertex r))
      (triangleWord 27 r)) := by
  refine ⟨triangleRank 27 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 27) (TriangleRegions.deleteVertex r))
      (triangleWord 27 r) a b → triangleRank 27 r a < triangleRank 27 r b from by decide) r

theorem triangle_witness28 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 28) (TriangleRegions.deleteVertex r))
      (triangleWord 28 r)) := by
  refine ⟨triangleRank 28 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 28) (TriangleRegions.deleteVertex r))
      (triangleWord 28 r) a b → triangleRank 28 r a < triangleRank 28 r b from by decide) r

theorem triangle_witness29 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 29) (TriangleRegions.deleteVertex r))
      (triangleWord 29 r)) := by
  refine ⟨triangleRank 29 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 29) (TriangleRegions.deleteVertex r))
      (triangleWord 29 r) a b → triangleRank 29 r a < triangleRank 29 r b from by decide) r

theorem triangle_witness30 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 30) (TriangleRegions.deleteVertex r))
      (triangleWord 30 r)) := by
  refine ⟨triangleRank 30 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 30) (TriangleRegions.deleteVertex r))
      (triangleWord 30 r) a b → triangleRank 30 r a < triangleRank 30 r b from by decide) r

theorem triangle_witness31 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 31) (TriangleRegions.deleteVertex r))
      (triangleWord 31 r)) := by
  refine ⟨triangleRank 31 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 31) (TriangleRegions.deleteVertex r))
      (triangleWord 31 r) a b → triangleRank 31 r a < triangleRank 31 r b from by decide) r

theorem triangle_witness32 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 32) (TriangleRegions.deleteVertex r))
      (triangleWord 32 r)) := by
  refine ⟨triangleRank 32 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 32) (TriangleRegions.deleteVertex r))
      (triangleWord 32 r) a b → triangleRank 32 r a < triangleRank 32 r b from by decide) r

theorem triangle_witness33 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 33) (TriangleRegions.deleteVertex r))
      (triangleWord 33 r)) := by
  refine ⟨triangleRank 33 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 33) (TriangleRegions.deleteVertex r))
      (triangleWord 33 r) a b → triangleRank 33 r a < triangleRank 33 r b from by decide) r

theorem triangle_witness34 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 34) (TriangleRegions.deleteVertex r))
      (triangleWord 34 r)) := by
  refine ⟨triangleRank 34 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 34) (TriangleRegions.deleteVertex r))
      (triangleWord 34 r) a b → triangleRank 34 r a < triangleRank 34 r b from by decide) r

theorem triangle_witness35 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 35) (TriangleRegions.deleteVertex r))
      (triangleWord 35 r)) := by
  refine ⟨triangleRank 35 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 35) (TriangleRegions.deleteVertex r))
      (triangleWord 35 r) a b → triangleRank 35 r a < triangleRank 35 r b from by decide) r

theorem triangle_witness36 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 36) (TriangleRegions.deleteVertex r))
      (triangleWord 36 r)) := by
  refine ⟨triangleRank 36 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 36) (TriangleRegions.deleteVertex r))
      (triangleWord 36 r) a b → triangleRank 36 r a < triangleRank 36 r b from by decide) r

theorem triangle_witness37 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 37) (TriangleRegions.deleteVertex r))
      (triangleWord 37 r)) := by
  refine ⟨triangleRank 37 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 37) (TriangleRegions.deleteVertex r))
      (triangleWord 37 r) a b → triangleRank 37 r a < triangleRank 37 r b from by decide) r

theorem triangle_witness38 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 38) (TriangleRegions.deleteVertex r))
      (triangleWord 38 r)) := by
  refine ⟨triangleRank 38 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 38) (TriangleRegions.deleteVertex r))
      (triangleWord 38 r) a b → triangleRank 38 r a < triangleRank 38 r b from by decide) r

theorem triangle_witness39 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 39) (TriangleRegions.deleteVertex r))
      (triangleWord 39 r)) := by
  refine ⟨triangleRank 39 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 39) (TriangleRegions.deleteVertex r))
      (triangleWord 39 r) a b → triangleRank 39 r a < triangleRank 39 r b from by decide) r

theorem triangle_witness40 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 40) (TriangleRegions.deleteVertex r))
      (triangleWord 40 r)) := by
  refine ⟨triangleRank 40 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 40) (TriangleRegions.deleteVertex r))
      (triangleWord 40 r) a b → triangleRank 40 r a < triangleRank 40 r b from by decide) r

theorem triangle_witness41 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 41) (TriangleRegions.deleteVertex r))
      (triangleWord 41 r)) := by
  refine ⟨triangleRank 41 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 41) (TriangleRegions.deleteVertex r))
      (triangleWord 41 r) a b → triangleRank 41 r a < triangleRank 41 r b from by decide) r

theorem triangle_witness42 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 42) (TriangleRegions.deleteVertex r))
      (triangleWord 42 r)) := by
  refine ⟨triangleRank 42 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 42) (TriangleRegions.deleteVertex r))
      (triangleWord 42 r) a b → triangleRank 42 r a < triangleRank 42 r b from by decide) r

theorem triangle_witness43 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 43) (TriangleRegions.deleteVertex r))
      (triangleWord 43 r)) := by
  refine ⟨triangleRank 43 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 43) (TriangleRegions.deleteVertex r))
      (triangleWord 43 r) a b → triangleRank 43 r a < triangleRank 43 r b from by decide) r

theorem triangle_witness44 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 44) (TriangleRegions.deleteVertex r))
      (triangleWord 44 r)) := by
  refine ⟨triangleRank 44 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 44) (TriangleRegions.deleteVertex r))
      (triangleWord 44 r) a b → triangleRank 44 r a < triangleRank 44 r b from by decide) r

theorem triangle_witness45 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 45) (TriangleRegions.deleteVertex r))
      (triangleWord 45 r)) := by
  refine ⟨triangleRank 45 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 45) (TriangleRegions.deleteVertex r))
      (triangleWord 45 r) a b → triangleRank 45 r a < triangleRank 45 r b from by decide) r

theorem triangle_witness46 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 46) (TriangleRegions.deleteVertex r))
      (triangleWord 46 r)) := by
  refine ⟨triangleRank 46 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 46) (TriangleRegions.deleteVertex r))
      (triangleWord 46 r) a b → triangleRank 46 r a < triangleRank 46 r b from by decide) r

theorem triangle_witness47 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 47) (TriangleRegions.deleteVertex r))
      (triangleWord 47 r)) := by
  refine ⟨triangleRank 47 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 47) (TriangleRegions.deleteVertex r))
      (triangleWord 47 r) a b → triangleRank 47 r a < triangleRank 47 r b from by decide) r

theorem triangle_witness48 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 48) (TriangleRegions.deleteVertex r))
      (triangleWord 48 r)) := by
  refine ⟨triangleRank 48 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 48) (TriangleRegions.deleteVertex r))
      (triangleWord 48 r) a b → triangleRank 48 r a < triangleRank 48 r b from by decide) r

theorem triangle_witness49 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 49) (TriangleRegions.deleteVertex r))
      (triangleWord 49 r)) := by
  refine ⟨triangleRank 49 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 49) (TriangleRegions.deleteVertex r))
      (triangleWord 49 r) a b → triangleRank 49 r a < triangleRank 49 r b from by decide) r

theorem triangle_witness50 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 50) (TriangleRegions.deleteVertex r))
      (triangleWord 50 r)) := by
  refine ⟨triangleRank 50 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 50) (TriangleRegions.deleteVertex r))
      (triangleWord 50 r) a b → triangleRank 50 r a < triangleRank 50 r b from by decide) r

theorem triangle_witness51 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 51) (TriangleRegions.deleteVertex r))
      (triangleWord 51 r)) := by
  refine ⟨triangleRank 51 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 51) (TriangleRegions.deleteVertex r))
      (triangleWord 51 r) a b → triangleRank 51 r a < triangleRank 51 r b from by decide) r

theorem triangle_witness52 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 52) (TriangleRegions.deleteVertex r))
      (triangleWord 52 r)) := by
  refine ⟨triangleRank 52 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 52) (TriangleRegions.deleteVertex r))
      (triangleWord 52 r) a b → triangleRank 52 r a < triangleRank 52 r b from by decide) r

theorem triangle_witness53 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 53) (TriangleRegions.deleteVertex r))
      (triangleWord 53 r)) := by
  refine ⟨triangleRank 53 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 53) (TriangleRegions.deleteVertex r))
      (triangleWord 53 r) a b → triangleRank 53 r a < triangleRank 53 r b from by decide) r

theorem triangle_witness54 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 54) (TriangleRegions.deleteVertex r))
      (triangleWord 54 r)) := by
  refine ⟨triangleRank 54 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 54) (TriangleRegions.deleteVertex r))
      (triangleWord 54 r) a b → triangleRank 54 r a < triangleRank 54 r b from by decide) r

theorem triangle_witness55 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 55) (TriangleRegions.deleteVertex r))
      (triangleWord 55 r)) := by
  refine ⟨triangleRank 55 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 55) (TriangleRegions.deleteVertex r))
      (triangleWord 55 r) a b → triangleRank 55 r a < triangleRank 55 r b from by decide) r

theorem triangle_witness56 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 56) (TriangleRegions.deleteVertex r))
      (triangleWord 56 r)) := by
  refine ⟨triangleRank 56 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 56) (TriangleRegions.deleteVertex r))
      (triangleWord 56 r) a b → triangleRank 56 r a < triangleRank 56 r b from by decide) r

theorem triangle_witness57 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 57) (TriangleRegions.deleteVertex r))
      (triangleWord 57 r)) := by
  refine ⟨triangleRank 57 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 57) (TriangleRegions.deleteVertex r))
      (triangleWord 57 r) a b → triangleRank 57 r a < triangleRank 57 r b from by decide) r

theorem triangle_witness58 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 58) (TriangleRegions.deleteVertex r))
      (triangleWord 58 r)) := by
  refine ⟨triangleRank 58 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 58) (TriangleRegions.deleteVertex r))
      (triangleWord 58 r) a b → triangleRank 58 r a < triangleRank 58 r b from by decide) r

theorem triangle_witness59 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 59) (TriangleRegions.deleteVertex r))
      (triangleWord 59 r)) := by
  refine ⟨triangleRank 59 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 59) (TriangleRegions.deleteVertex r))
      (triangleWord 59 r) a b → triangleRank 59 r a < triangleRank 59 r b from by decide) r

theorem triangle_witness60 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 60) (TriangleRegions.deleteVertex r))
      (triangleWord 60 r)) := by
  refine ⟨triangleRank 60 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 60) (TriangleRegions.deleteVertex r))
      (triangleWord 60 r) a b → triangleRank 60 r a < triangleRank 60 r b from by decide) r

theorem triangle_witness61 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 61) (TriangleRegions.deleteVertex r))
      (triangleWord 61 r)) := by
  refine ⟨triangleRank 61 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 61) (TriangleRegions.deleteVertex r))
      (triangleWord 61 r) a b → triangleRank 61 r a < triangleRank 61 r b from by decide) r

theorem triangle_witness62 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 62) (TriangleRegions.deleteVertex r))
      (triangleWord 62 r)) := by
  refine ⟨triangleRank 62 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 62) (TriangleRegions.deleteVertex r))
      (triangleWord 62 r) a b → triangleRank 62 r a < triangleRank 62 r b from by decide) r

theorem triangle_witness63 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 63) (TriangleRegions.deleteVertex r))
      (triangleWord 63 r)) := by
  refine ⟨triangleRank 63 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 63) (TriangleRegions.deleteVertex r))
      (triangleWord 63 r) a b → triangleRank 63 r a < triangleRank 63 r b from by decide) r

theorem triangle_witness64 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 64) (TriangleRegions.deleteVertex r))
      (triangleWord 64 r)) := by
  refine ⟨triangleRank 64 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 64) (TriangleRegions.deleteVertex r))
      (triangleWord 64 r) a b → triangleRank 64 r a < triangleRank 64 r b from by decide) r

theorem triangle_witness65 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 65) (TriangleRegions.deleteVertex r))
      (triangleWord 65 r)) := by
  refine ⟨triangleRank 65 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 65) (TriangleRegions.deleteVertex r))
      (triangleWord 65 r) a b → triangleRank 65 r a < triangleRank 65 r b from by decide) r

theorem triangle_witness66 (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node 66) (TriangleRegions.deleteVertex r))
      (triangleWord 66 r)) := by
  refine ⟨triangleRank 66 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (node 66) (TriangleRegions.deleteVertex r))
      (triangleWord 66 r) a b → triangleRank 66 r a < triangleRank 66 r b from by decide) r

theorem triangle_witness (i : Fin 67) (r : Fin 4) :
    Acyclic (applyWord (TriangleRegions.restrict (node i) (TriangleRegions.deleteVertex r))
      (triangleWord i r)) := by
  rcases fin67 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact triangle_witness0 r
  · exact triangle_witness1 r
  · exact triangle_witness2 r
  · exact triangle_witness3 r
  · exact triangle_witness4 r
  · exact triangle_witness5 r
  · exact triangle_witness6 r
  · exact triangle_witness7 r
  · exact triangle_witness8 r
  · exact triangle_witness9 r
  · exact triangle_witness10 r
  · exact triangle_witness11 r
  · exact triangle_witness12 r
  · exact triangle_witness13 r
  · exact triangle_witness14 r
  · exact triangle_witness15 r
  · exact triangle_witness16 r
  · exact triangle_witness17 r
  · exact triangle_witness18 r
  · exact triangle_witness19 r
  · exact triangle_witness20 r
  · exact triangle_witness21 r
  · exact triangle_witness22 r
  · exact triangle_witness23 r
  · exact triangle_witness24 r
  · exact triangle_witness25 r
  · exact triangle_witness26 r
  · exact triangle_witness27 r
  · exact triangle_witness28 r
  · exact triangle_witness29 r
  · exact triangle_witness30 r
  · exact triangle_witness31 r
  · exact triangle_witness32 r
  · exact triangle_witness33 r
  · exact triangle_witness34 r
  · exact triangle_witness35 r
  · exact triangle_witness36 r
  · exact triangle_witness37 r
  · exact triangle_witness38 r
  · exact triangle_witness39 r
  · exact triangle_witness40 r
  · exact triangle_witness41 r
  · exact triangle_witness42 r
  · exact triangle_witness43 r
  · exact triangle_witness44 r
  · exact triangle_witness45 r
  · exact triangle_witness46 r
  · exact triangle_witness47 r
  · exact triangle_witness48 r
  · exact triangle_witness49 r
  · exact triangle_witness50 r
  · exact triangle_witness51 r
  · exact triangle_witness52 r
  · exact triangle_witness53 r
  · exact triangle_witness54 r
  · exact triangle_witness55 r
  · exact triangle_witness56 r
  · exact triangle_witness57 r
  · exact triangle_witness58 r
  · exact triangle_witness59 r
  · exact triangle_witness60 r
  · exact triangle_witness61 r
  · exact triangle_witness62 r
  · exact triangle_witness63 r
  · exact triangle_witness64 r
  · exact triangle_witness65 r
  · exact triangle_witness66 r

theorem all_triangles (i : Fin 67) : TriangleRegions.AllTrianglesMA (node i) := by
  apply TriangleRegions.allTrianglesMA_of_deletions
  intro r
  exact ⟨triangleWord i r,triangle_witness i r⟩

theorem strip0_root_triangles : TriangleRegions.AllTrianglesMA (stripPhase 0 0) := by
  rw [←strip0_identification]
  exact TriangleRegions.triangles_relabel _ perm6 (all_triangles 43)

theorem strip1_root_triangles : TriangleRegions.AllTrianglesMA (stripPhase 1 0) := by
  rw [←strip1_identification]
  exact TriangleRegions.triangles_reverse _ (relabel_skew _ perm0 (all_skew 49)) (TriangleRegions.triangles_relabel _ perm0 (all_triangles 49))

theorem strip2_root_triangles : TriangleRegions.AllTrianglesMA (stripPhase 2 0) := by
  rw [←strip2_identification]
  exact TriangleRegions.triangles_relabel _ perm8 (all_triangles 54)

theorem strip3_root_triangles : TriangleRegions.AllTrianglesMA (stripPhase 3 0) := by
  rw [←strip3_identification]
  exact TriangleRegions.triangles_reverse _ (relabel_skew _ perm0 (all_skew 56)) (TriangleRegions.triangles_relabel _ perm0 (all_triangles 56))

theorem strip4_root_triangles : TriangleRegions.AllTrianglesMA (stripPhase 4 0) := by
  rw [←strip4_identification]
  exact TriangleRegions.triangles_relabel _ perm14 (all_triangles 59)

theorem strip5_root_triangles : TriangleRegions.AllTrianglesMA (stripPhase 5 0) := by
  rw [←strip5_identification]
  exact TriangleRegions.triangles_reverse _ (relabel_skew _ perm2 (all_skew 62)) (TriangleRegions.triangles_relabel _ perm2 (all_triangles 62))

theorem strip_root_triangles (j : Fin 6) : TriangleRegions.AllTrianglesMA (stripPhase j 0) := by
  rcases fin6 j with rfl|rfl|rfl|rfl|rfl|rfl
  · exact strip0_root_triangles
  · exact strip1_root_triangles
  · exact strip2_root_triangles
  · exact strip3_root_triangles
  · exact strip4_root_triangles
  · exact strip5_root_triangles

def zeroTriangleWord (j : Fin 6) (s : Fin 2) (r : Fin 4) : List (Fin 3) :=
  match j.val,s.val,r.val with
  | 0,0,0 => [0, 2, 1, 0]
  | 0,0,1 => []
  | 0,0,2 => []
  | 0,0,3 => []
  | 0,1,0 => [0]
  | 0,1,1 => [0]
  | 0,1,2 => []
  | 0,1,3 => []
  | 1,0,0 => [0, 2, 0, 2, 0]
  | 1,0,1 => []
  | 1,0,2 => []
  | 1,0,3 => []
  | 1,1,0 => [0]
  | 1,1,1 => [0]
  | 1,1,2 => []
  | 1,1,3 => []
  | 2,0,0 => [0, 2, 1, 0]
  | 2,0,1 => []
  | 2,0,2 => []
  | 2,0,3 => []
  | 2,1,0 => [0, 2]
  | 2,1,1 => [0]
  | 2,1,2 => []
  | 2,1,3 => []
  | 3,0,0 => [0, 2, 0, 1, 0]
  | 3,0,1 => []
  | 3,0,2 => []
  | 3,0,3 => []
  | 3,1,0 => [0]
  | 3,1,1 => [0]
  | 3,1,2 => []
  | 3,1,3 => []
  | 4,0,0 => [0, 2, 0, 1]
  | 4,0,1 => []
  | 4,0,2 => []
  | 4,0,3 => []
  | 4,1,0 => [0, 2]
  | 4,1,1 => [0]
  | 4,1,2 => []
  | 4,1,3 => []
  | 5,0,0 => [0, 2, 0, 2]
  | 5,0,1 => []
  | 5,0,2 => []
  | 5,0,3 => []
  | 5,1,0 => [0, 2]
  | 5,1,1 => [0]
  | 5,1,2 => []
  | _,_,_ => []

def zeroTriangleRank (j : Fin 6) (s : Fin 2) (r : Fin 4) (v : Fin 3) : Nat :=
  match j.val,s.val,r.val,v.val with
  | 0,0,0,0 => 1
  | 0,0,0,1 => 2
  | 0,0,0,2 => 0
  | 0,0,1,0 => 1
  | 0,0,1,1 => 0
  | 0,0,1,2 => 2
  | 0,0,2,0 => 0
  | 0,0,2,1 => 2
  | 0,0,2,2 => 1
  | 0,0,3,0 => 2
  | 0,0,3,1 => 0
  | 0,0,3,2 => 1
  | 0,1,0,0 => 1
  | 0,1,0,1 => 0
  | 0,1,0,2 => 2
  | 0,1,1,0 => 1
  | 0,1,1,1 => 0
  | 0,1,1,2 => 2
  | 0,1,2,0 => 1
  | 0,1,2,1 => 2
  | 0,1,2,2 => 0
  | 0,1,3,0 => 0
  | 0,1,3,1 => 1
  | 0,1,3,2 => 2
  | 1,0,0,0 => 1
  | 1,0,0,1 => 0
  | 1,0,0,2 => 2
  | 1,0,1,0 => 1
  | 1,0,1,1 => 0
  | 1,0,1,2 => 2
  | 1,0,2,0 => 0
  | 1,0,2,1 => 2
  | 1,0,2,2 => 1
  | 1,0,3,0 => 2
  | 1,0,3,1 => 0
  | 1,0,3,2 => 1
  | 1,1,0,0 => 1
  | 1,1,0,1 => 0
  | 1,1,0,2 => 2
  | 1,1,1,0 => 1
  | 1,1,1,1 => 0
  | 1,1,1,2 => 2
  | 1,1,2,0 => 1
  | 1,1,2,1 => 2
  | 1,1,2,2 => 0
  | 1,1,3,0 => 0
  | 1,1,3,1 => 1
  | 1,1,3,2 => 2
  | 2,0,0,0 => 1
  | 2,0,0,1 => 2
  | 2,0,0,2 => 0
  | 2,0,1,0 => 1
  | 2,0,1,1 => 0
  | 2,0,1,2 => 2
  | 2,0,2,0 => 0
  | 2,0,2,1 => 2
  | 2,0,2,2 => 1
  | 2,0,3,0 => 2
  | 2,0,3,1 => 0
  | 2,0,3,2 => 1
  | 2,1,0,0 => 2
  | 2,1,0,1 => 0
  | 2,1,0,2 => 1
  | 2,1,1,0 => 1
  | 2,1,1,1 => 0
  | 2,1,1,2 => 2
  | 2,1,2,0 => 1
  | 2,1,2,1 => 2
  | 2,1,2,2 => 0
  | 2,1,3,0 => 0
  | 2,1,3,1 => 1
  | 2,1,3,2 => 2
  | 3,0,0,0 => 1
  | 3,0,0,1 => 0
  | 3,0,0,2 => 2
  | 3,0,1,0 => 1
  | 3,0,1,1 => 0
  | 3,0,1,2 => 2
  | 3,0,2,0 => 0
  | 3,0,2,1 => 2
  | 3,0,2,2 => 1
  | 3,0,3,0 => 2
  | 3,0,3,1 => 0
  | 3,0,3,2 => 1
  | 3,1,0,0 => 1
  | 3,1,0,1 => 0
  | 3,1,0,2 => 2
  | 3,1,1,0 => 1
  | 3,1,1,1 => 0
  | 3,1,1,2 => 2
  | 3,1,2,0 => 1
  | 3,1,2,1 => 2
  | 3,1,2,2 => 0
  | 3,1,3,0 => 0
  | 3,1,3,1 => 1
  | 3,1,3,2 => 2
  | 4,0,0,0 => 0
  | 4,0,0,1 => 1
  | 4,0,0,2 => 2
  | 4,0,1,0 => 1
  | 4,0,1,1 => 0
  | 4,0,1,2 => 2
  | 4,0,2,0 => 0
  | 4,0,2,1 => 2
  | 4,0,2,2 => 1
  | 4,0,3,0 => 2
  | 4,0,3,1 => 0
  | 4,0,3,2 => 1
  | 4,1,0,0 => 2
  | 4,1,0,1 => 0
  | 4,1,0,2 => 1
  | 4,1,1,0 => 1
  | 4,1,1,1 => 0
  | 4,1,1,2 => 2
  | 4,1,2,0 => 1
  | 4,1,2,1 => 2
  | 4,1,2,2 => 0
  | 4,1,3,0 => 0
  | 4,1,3,1 => 1
  | 4,1,3,2 => 2
  | 5,0,0,0 => 2
  | 5,0,0,1 => 0
  | 5,0,0,2 => 1
  | 5,0,1,0 => 1
  | 5,0,1,1 => 0
  | 5,0,1,2 => 2
  | 5,0,2,0 => 0
  | 5,0,2,1 => 2
  | 5,0,2,2 => 1
  | 5,0,3,0 => 2
  | 5,0,3,1 => 0
  | 5,0,3,2 => 1
  | 5,1,0,0 => 2
  | 5,1,0,1 => 0
  | 5,1,0,2 => 1
  | 5,1,1,0 => 1
  | 5,1,1,1 => 0
  | 5,1,1,2 => 2
  | 5,1,2,0 => 1
  | 5,1,2,1 => 2
  | 5,1,2,2 => 0
  | 5,1,3,0 => 0
  | 5,1,3,1 => 1
  | _,_,_,_ => 2

theorem zero_triangles0_0 : TriangleRegions.AllTrianglesMA (zeroPhase 0 0) := by
  apply TriangleRegions.allTrianglesMA_of_deletions
  intro r
  refine ⟨zeroTriangleWord 0 0 r, zeroTriangleRank 0 0 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (zeroPhase 0 0) (TriangleRegions.deleteVertex r))
      (zeroTriangleWord 0 0 r) a b →
      zeroTriangleRank 0 0 r a < zeroTriangleRank 0 0 r b from by decide) r

theorem zero_triangles0_1 : TriangleRegions.AllTrianglesMA (zeroPhase 0 1) := by
  apply TriangleRegions.allTrianglesMA_of_deletions
  intro r
  refine ⟨zeroTriangleWord 0 1 r, zeroTriangleRank 0 1 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (zeroPhase 0 1) (TriangleRegions.deleteVertex r))
      (zeroTriangleWord 0 1 r) a b →
      zeroTriangleRank 0 1 r a < zeroTriangleRank 0 1 r b from by decide) r

theorem zero_triangles1_0 : TriangleRegions.AllTrianglesMA (zeroPhase 1 0) := by
  apply TriangleRegions.allTrianglesMA_of_deletions
  intro r
  refine ⟨zeroTriangleWord 1 0 r, zeroTriangleRank 1 0 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (zeroPhase 1 0) (TriangleRegions.deleteVertex r))
      (zeroTriangleWord 1 0 r) a b →
      zeroTriangleRank 1 0 r a < zeroTriangleRank 1 0 r b from by decide) r

theorem zero_triangles1_1 : TriangleRegions.AllTrianglesMA (zeroPhase 1 1) := by
  apply TriangleRegions.allTrianglesMA_of_deletions
  intro r
  refine ⟨zeroTriangleWord 1 1 r, zeroTriangleRank 1 1 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (zeroPhase 1 1) (TriangleRegions.deleteVertex r))
      (zeroTriangleWord 1 1 r) a b →
      zeroTriangleRank 1 1 r a < zeroTriangleRank 1 1 r b from by decide) r

theorem zero_triangles2_0 : TriangleRegions.AllTrianglesMA (zeroPhase 2 0) := by
  apply TriangleRegions.allTrianglesMA_of_deletions
  intro r
  refine ⟨zeroTriangleWord 2 0 r, zeroTriangleRank 2 0 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (zeroPhase 2 0) (TriangleRegions.deleteVertex r))
      (zeroTriangleWord 2 0 r) a b →
      zeroTriangleRank 2 0 r a < zeroTriangleRank 2 0 r b from by decide) r

theorem zero_triangles2_1 : TriangleRegions.AllTrianglesMA (zeroPhase 2 1) := by
  apply TriangleRegions.allTrianglesMA_of_deletions
  intro r
  refine ⟨zeroTriangleWord 2 1 r, zeroTriangleRank 2 1 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (zeroPhase 2 1) (TriangleRegions.deleteVertex r))
      (zeroTriangleWord 2 1 r) a b →
      zeroTriangleRank 2 1 r a < zeroTriangleRank 2 1 r b from by decide) r

theorem zero_triangles3_0 : TriangleRegions.AllTrianglesMA (zeroPhase 3 0) := by
  apply TriangleRegions.allTrianglesMA_of_deletions
  intro r
  refine ⟨zeroTriangleWord 3 0 r, zeroTriangleRank 3 0 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (zeroPhase 3 0) (TriangleRegions.deleteVertex r))
      (zeroTriangleWord 3 0 r) a b →
      zeroTriangleRank 3 0 r a < zeroTriangleRank 3 0 r b from by decide) r

theorem zero_triangles3_1 : TriangleRegions.AllTrianglesMA (zeroPhase 3 1) := by
  apply TriangleRegions.allTrianglesMA_of_deletions
  intro r
  refine ⟨zeroTriangleWord 3 1 r, zeroTriangleRank 3 1 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (zeroPhase 3 1) (TriangleRegions.deleteVertex r))
      (zeroTriangleWord 3 1 r) a b →
      zeroTriangleRank 3 1 r a < zeroTriangleRank 3 1 r b from by decide) r

theorem zero_triangles4_0 : TriangleRegions.AllTrianglesMA (zeroPhase 4 0) := by
  apply TriangleRegions.allTrianglesMA_of_deletions
  intro r
  refine ⟨zeroTriangleWord 4 0 r, zeroTriangleRank 4 0 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (zeroPhase 4 0) (TriangleRegions.deleteVertex r))
      (zeroTriangleWord 4 0 r) a b →
      zeroTriangleRank 4 0 r a < zeroTriangleRank 4 0 r b from by decide) r

theorem zero_triangles4_1 : TriangleRegions.AllTrianglesMA (zeroPhase 4 1) := by
  apply TriangleRegions.allTrianglesMA_of_deletions
  intro r
  refine ⟨zeroTriangleWord 4 1 r, zeroTriangleRank 4 1 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (zeroPhase 4 1) (TriangleRegions.deleteVertex r))
      (zeroTriangleWord 4 1 r) a b →
      zeroTriangleRank 4 1 r a < zeroTriangleRank 4 1 r b from by decide) r

theorem zero_triangles5_0 : TriangleRegions.AllTrianglesMA (zeroPhase 5 0) := by
  apply TriangleRegions.allTrianglesMA_of_deletions
  intro r
  refine ⟨zeroTriangleWord 5 0 r, zeroTriangleRank 5 0 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (zeroPhase 5 0) (TriangleRegions.deleteVertex r))
      (zeroTriangleWord 5 0 r) a b →
      zeroTriangleRank 5 0 r a < zeroTriangleRank 5 0 r b from by decide) r

theorem zero_triangles5_1 : TriangleRegions.AllTrianglesMA (zeroPhase 5 1) := by
  apply TriangleRegions.allTrianglesMA_of_deletions
  intro r
  refine ⟨zeroTriangleWord 5 1 r, zeroTriangleRank 5 1 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (zeroPhase 5 1) (TriangleRegions.deleteVertex r))
      (zeroTriangleWord 5 1 r) a b →
      zeroTriangleRank 5 1 r a < zeroTriangleRank 5 1 r b from by decide) r

theorem zero_triangles (j : Fin 6) (s : Fin 2) :
    TriangleRegions.AllTrianglesMA (zeroPhase j s) := by
  rcases fin6 j with rfl|rfl|rfl|rfl|rfl|rfl <;> rcases fin2 s with rfl|rfl
  · exact zero_triangles0_0
  · exact zero_triangles0_1
  · exact zero_triangles1_0
  · exact zero_triangles1_1
  · exact zero_triangles2_0
  · exact zero_triangles2_1
  · exact zero_triangles3_0
  · exact zero_triangles3_1
  · exact zero_triangles4_0
  · exact zero_triangles4_1
  · exact zero_triangles5_0
  · exact zero_triangles5_1

def pendantTriangleWord (j : Fin 2) (s : Fin 2) (r : Fin 4) : List (Fin 3) :=
  match j.val,s.val,r.val with
  | 0,0,0 => [0, 2, 0]
  | 0,0,1 => []
  | 0,0,2 => []
  | 0,0,3 => []
  | 0,1,0 => [0, 2, 0]
  | 0,1,1 => []
  | 0,1,2 => []
  | 0,1,3 => []
  | 1,0,0 => [0, 2, 1]
  | 1,0,1 => []
  | 1,0,2 => []
  | 1,0,3 => []
  | 1,1,0 => [0, 2, 1]
  | 1,1,1 => []
  | 1,1,2 => []
  | _,_,_ => []

def pendantTriangleRank (j : Fin 2) (s : Fin 2) (r : Fin 4) (v : Fin 3) : Nat :=
  match j.val,s.val,r.val,v.val with
  | 0,0,0,0 => 1
  | 0,0,0,1 => 0
  | 0,0,0,2 => 2
  | 0,0,1,0 => 0
  | 0,0,1,1 => 1
  | 0,0,1,2 => 2
  | 0,0,2,0 => 0
  | 0,0,2,1 => 2
  | 0,0,2,2 => 1
  | 0,0,3,0 => 0
  | 0,0,3,1 => 1
  | 0,0,3,2 => 2
  | 0,1,0,0 => 1
  | 0,1,0,1 => 0
  | 0,1,0,2 => 2
  | 0,1,1,0 => 2
  | 0,1,1,1 => 0
  | 0,1,1,2 => 1
  | 0,1,2,0 => 1
  | 0,1,2,1 => 2
  | 0,1,2,2 => 0
  | 0,1,3,0 => 0
  | 0,1,3,1 => 1
  | 0,1,3,2 => 2
  | 1,0,0,0 => 2
  | 1,0,0,1 => 1
  | 1,0,0,2 => 0
  | 1,0,1,0 => 0
  | 1,0,1,1 => 1
  | 1,0,1,2 => 2
  | 1,0,2,0 => 0
  | 1,0,2,1 => 2
  | 1,0,2,2 => 1
  | 1,0,3,0 => 0
  | 1,0,3,1 => 1
  | 1,0,3,2 => 2
  | 1,1,0,0 => 2
  | 1,1,0,1 => 1
  | 1,1,0,2 => 0
  | 1,1,1,0 => 2
  | 1,1,1,1 => 0
  | 1,1,1,2 => 1
  | 1,1,2,0 => 1
  | 1,1,2,1 => 2
  | 1,1,2,2 => 0
  | 1,1,3,0 => 0
  | 1,1,3,1 => 1
  | _,_,_,_ => 2

theorem pendant_triangles0_0 : TriangleRegions.AllTrianglesMA (pendantPhase 0 0) := by
  apply TriangleRegions.allTrianglesMA_of_deletions
  intro r
  refine ⟨pendantTriangleWord 0 0 r, pendantTriangleRank 0 0 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (pendantPhase 0 0) (TriangleRegions.deleteVertex r))
      (pendantTriangleWord 0 0 r) a b →
      pendantTriangleRank 0 0 r a < pendantTriangleRank 0 0 r b from by decide) r

theorem pendant_triangles0_1 : TriangleRegions.AllTrianglesMA (pendantPhase 0 1) := by
  apply TriangleRegions.allTrianglesMA_of_deletions
  intro r
  refine ⟨pendantTriangleWord 0 1 r, pendantTriangleRank 0 1 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (pendantPhase 0 1) (TriangleRegions.deleteVertex r))
      (pendantTriangleWord 0 1 r) a b →
      pendantTriangleRank 0 1 r a < pendantTriangleRank 0 1 r b from by decide) r

theorem pendant_triangles1_0 : TriangleRegions.AllTrianglesMA (pendantPhase 1 0) := by
  apply TriangleRegions.allTrianglesMA_of_deletions
  intro r
  refine ⟨pendantTriangleWord 1 0 r, pendantTriangleRank 1 0 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (pendantPhase 1 0) (TriangleRegions.deleteVertex r))
      (pendantTriangleWord 1 0 r) a b →
      pendantTriangleRank 1 0 r a < pendantTriangleRank 1 0 r b from by decide) r

theorem pendant_triangles1_1 : TriangleRegions.AllTrianglesMA (pendantPhase 1 1) := by
  apply TriangleRegions.allTrianglesMA_of_deletions
  intro r
  refine ⟨pendantTriangleWord 1 1 r, pendantTriangleRank 1 1 r,?_⟩
  exact (show ∀ r : Fin 4, ∀ a b : Fin 3,
    0 < applyWord (TriangleRegions.restrict (pendantPhase 1 1) (TriangleRegions.deleteVertex r))
      (pendantTriangleWord 1 1 r) a b →
      pendantTriangleRank 1 1 r a < pendantTriangleRank 1 1 r b from by decide) r

theorem pendant_triangles (j : Fin 2) (s : Fin 2) :
    TriangleRegions.AllTrianglesMA (pendantPhase j s) := by
  rcases fin2 j with rfl|rfl <;> rcases fin2 s with rfl|rfl
  · exact pendant_triangles0_0
  · exact pendant_triangles0_1
  · exact pendant_triangles1_0
  · exact pendant_triangles1_1

theorem printed_identification : node 0 = ClassSeparation.printed 2 := rfl

end QuiverProofs.E3Core
