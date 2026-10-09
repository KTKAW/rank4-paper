import QuiverProofs.Forks

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace QuiverProofs.ForkCertificates
open Forks

def perm0 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | _ => 3), (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | _ => 3), by decide, by decide⟩

def perm1 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | _ => 2), (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | _ => 2), by decide, by decide⟩

def perm2 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | _ => 3), (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | _ => 3), by decide, by decide⟩

def perm3 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | _ => 1), (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | _ => 2), by decide, by decide⟩

def perm4 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | _ => 2), (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | _ => 1), by decide, by decide⟩

def perm5 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | _ => 1), (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | _ => 1), by decide, by decide⟩

def perm6 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | _ => 3), (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | _ => 3), by decide, by decide⟩

def perm7 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | _ => 2), (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | _ => 2), by decide, by decide⟩

def perm8 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 0 | _ => 3), (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 1 | _ => 3), by decide, by decide⟩

def perm9 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | _ => 0), (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | _ => 2), by decide, by decide⟩

def perm10 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 0 | _ => 2), (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 3 | _ => 1), by decide, by decide⟩

def perm11 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | _ => 0), (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | _ => 1), by decide, by decide⟩

def perm12 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 1 | _ => 3), (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 0 | _ => 3), by decide, by decide⟩

def perm13 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 3 | _ => 1), (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 0 | _ => 2), by decide, by decide⟩

def perm14 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | _ => 3), (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | _ => 3), by decide, by decide⟩

def perm15 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 3 | _ => 0), (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 0 | _ => 2), by decide, by decide⟩

def perm16 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | _ => 1), (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | _ => 1), by decide, by decide⟩

def perm17 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | _ => 0), (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | _ => 1), by decide, by decide⟩

def perm18 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | _ => 2), (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | _ => 0), by decide, by decide⟩

def perm19 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | _ => 1), (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | _ => 0), by decide, by decide⟩

def perm20 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 0 | _ => 2), (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 3 | _ => 0), by decide, by decide⟩

def perm21 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | _ => 0), (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | _ => 0), by decide, by decide⟩

def perm22 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | _ => 1), (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | _ => 0), by decide, by decide⟩

def perm23 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | _ => 0), (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | _ => 0), by decide, by decide⟩

namespace Core00
def node (i : Fin 1) : Matrix 4 := match i.val with
  | _ => (ofSix (-4) (-13) (3) (-11) (-7) (-7))

theorem cyclic0 : ¬ Acyclic (node 0) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge0_0 : FramedCore node (mutate (node 0) 0) ∨ IsFork (mutate (node 0) 0) 0 := by
  right
  have he : relabel (mutate (node 0) 0) perm5 = template (3) (13) (4) (32) (5) (11) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 0) 0) perm5 u v = template (3) (13) (4) (32) (5) (11) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 0) 0) perm5) 0 := by
    rw [he]; exact IsFork.basic (3) (13) (4) (32) (5) (11) (by unfold Domain; decide)
  exact fork_of_relabel perm5 hf

theorem edge0_1 : FramedCore node (mutate (node 0) 1) ∨ IsFork (mutate (node 0) 1) 1 := by
  right
  have he : relabel (mutate (node 0) 1) perm7 = template (4) (7) (11) (25) (57) (7) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 0) 1) perm7 u v = template (4) (7) (11) (25) (57) (7) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 0) 1) perm7) 0 := by
    rw [he]; exact IsFork.basic (4) (7) (11) (25) (57) (7) (by unfold Domain; decide)
  exact fork_of_relabel perm7 hf

theorem edge0_2 : FramedCore node (mutate (node 0) 2) ∨ IsFork (mutate (node 0) 2) 2 := by
  right
  have he : relabel (reverse (mutate (node 0) 2)) perm16 = template (7) (13) (11) (88) (84) (4) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 0) 2)) perm16 u v = template (7) (13) (11) (88) (84) (4) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 0) 2)) perm16) 0 := by
    rw [he]; exact IsFork.basic (7) (13) (11) (88) (84) (4) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm16 hf)

theorem edge0_3 : FramedCore node (mutate (node 0) 3) ∨ IsFork (mutate (node 0) 3) 3 := by
  right
  have he : relabel (reverse (mutate (node 0) 3)) perm18 = template (3) (7) (7) (17) (8) (11) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 0) 3)) perm18 u v = template (3) (7) (7) (17) (8) (11) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 0) 3)) perm18) 0 := by
    rw [he]; exact IsFork.basic (3) (7) (7) (17) (8) (11) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm18 hf)

theorem all_cyclic : ∀ i, ¬ Acyclic (node i) := by
  intro i
  have hi : i = 0 := by omega
  rcases hi with rfl
  · exact cyclic0

theorem all_edges : ∀ i k, FramedCore node (mutate (node i) k) ∨ IsFork (mutate (node i) k) k := by
  intro i k
  have hi : i = 0 := by omega
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hi with rfl <;>
    rcases hk with rfl | rfl | rfl | rfl
  · exact edge0_0
  · exact edge0_1
  · exact edge0_2
  · exact edge0_3

theorem nma : ¬ MutationAcyclic (ofSix (-4) (-13) (3) (-11) (-7) (-7)) :=
  framed_core_NMA node all_cyclic all_edges 0
end Core00

namespace Core01
def node (i : Fin 2) : Matrix 4 := match i.val with
  | 0 => (ofSix (-5) (-9) (3) (-11) (-6) (-4))
  | _ => (ofSix (13) (3) (-3) (-11) (6) (4))

theorem cyclic0 : ¬ Acyclic (node 0) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge0_0 : FramedCore node (mutate (node 0) 0) ∨ IsFork (mutate (node 0) 0) 0 := by
  right
  have he : relabel (mutate (node 0) 0) perm5 = template (3) (9) (5) (23) (9) (11) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 0) 0) perm5 u v = template (3) (9) (5) (23) (9) (11) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 0) 0) perm5) 0 := by
    rw [he]; exact IsFork.basic (3) (9) (5) (23) (9) (11) (by unfold Domain; decide)
  exact fork_of_relabel perm5 hf

theorem edge0_1 : FramedCore node (mutate (node 0) 1) ∨ IsFork (mutate (node 0) 1) 1 := by
  right
  have he : relabel (mutate (node 0) 1) perm7 = template (5) (6) (11) (27) (64) (4) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 0) 1) perm7 u v = template (5) (6) (11) (27) (64) (4) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 0) 1) perm7) 0 := by
    rw [he]; exact IsFork.basic (5) (6) (11) (27) (64) (4) (by unfold Domain; decide)
  exact fork_of_relabel perm7 hf

theorem edge0_2 : FramedCore node (mutate (node 0) 2) ∨ IsFork (mutate (node 0) 2) 2 := by
  right
  have he : relabel (reverse (mutate (node 0) 2)) perm16 = template (4) (9) (11) (33) (50) (5) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 0) 2)) perm16 u v = template (4) (9) (11) (33) (50) (5) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 0) 2)) perm16) 0 := by
    rw [he]; exact IsFork.basic (4) (9) (11) (33) (50) (5) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm16 hf)

theorem edge0_3 : FramedCore node (mutate (node 0) 3) ∨ IsFork (mutate (node 0) 3) 3 := by
  left; refine ⟨1, perm0, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 3 u v = relabel (node 1) perm0 u v from by decide) u v

theorem cyclic1 : ¬ Acyclic (node 1) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 1 (by decide)
  have h1 := hr 1 3 (by decide)
  have h2 := hr 3 0 (by decide)
  omega

theorem edge1_0 : FramedCore node (mutate (node 1) 0) ∨ IsFork (mutate (node 1) 0) 0 := by
  right
  have he : relabel (reverse (mutate (node 1) 0)) perm4 = template (3) (13) (3) (33) (5) (11) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 1) 0)) perm4 u v = template (3) (13) (3) (33) (5) (11) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 1) 0)) perm4) 0 := by
    rw [he]; exact IsFork.basic (3) (13) (3) (33) (5) (11) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm4 hf)

theorem edge1_1 : FramedCore node (mutate (node 1) 1) ∨ IsFork (mutate (node 1) 1) 1 := by
  right
  have he : relabel (mutate (node 1) 1) perm10 = template (6) (13) (11) (75) (70) (3) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 1) 1) perm10 u v = template (6) (13) (11) (75) (70) (3) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 1) 1) perm10) 0 := by
    rw [he]; exact IsFork.basic (6) (13) (11) (75) (70) (3) (by unfold Domain; decide)
  exact fork_of_relabel perm10 hf

theorem edge1_2 : FramedCore node (mutate (node 1) 2) ∨ IsFork (mutate (node 1) 2) 2 := by
  right
  have he : relabel (reverse (mutate (node 1) 2)) perm13 = template (3) (4) (11) (9) (46) (6) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 1) 2)) perm13 u v = template (3) (4) (11) (9) (46) (6) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 1) 2)) perm13) 0 := by
    rw [he]; exact IsFork.basic (3) (4) (11) (9) (46) (6) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm13 hf)

theorem edge1_3 : FramedCore node (mutate (node 1) 3) ∨ IsFork (mutate (node 1) 3) 3 := by
  left; refine ⟨0, perm0, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 1) 3 u v = relabel (node 0) perm0 u v from by decide) u v

theorem all_cyclic : ∀ i, ¬ Acyclic (node i) := by
  intro i
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  · exact cyclic0
  · exact cyclic1

theorem all_edges : ∀ i k, FramedCore node (mutate (node i) k) ∨ IsFork (mutate (node i) k) k := by
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

theorem nma : ¬ MutationAcyclic (ofSix (-5) (-9) (3) (-11) (-6) (-4)) :=
  framed_core_NMA node all_cyclic all_edges 0
end Core01

namespace Core02
def node (i : Fin 1) : Matrix 4 := match i.val with
  | _ => (ofSix (-7) (-15) (2) (-9) (-7) (-15))

theorem cyclic0 : ¬ Acyclic (node 0) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge0_0 : FramedCore node (mutate (node 0) 0) ∨ IsFork (mutate (node 0) 0) 0 := by
  left; refine ⟨0, perm21, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 0 u v = relabel (node 0) perm21 u v from by decide) u v

theorem edge0_1 : FramedCore node (mutate (node 0) 1) ∨ IsFork (mutate (node 0) 1) 1 := by
  right
  have he : relabel (mutate (node 0) 1) perm7 = template (7) (7) (9) (47) (78) (15) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 0) 1) perm7 u v = template (7) (7) (9) (47) (78) (15) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 0) 1) perm7) 0 := by
    rw [he]; exact IsFork.basic (7) (7) (9) (47) (78) (15) (by unfold Domain; decide)
  exact fork_of_relabel perm7 hf

theorem edge0_2 : FramedCore node (mutate (node 0) 2) ∨ IsFork (mutate (node 0) 2) 2 := by
  right
  have he : relabel (reverse (mutate (node 0) 2)) perm16 = template (15) (15) (9) (223) (142) (7) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 0) 2)) perm16 u v = template (15) (15) (9) (223) (142) (7) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 0) 2)) perm16) 0 := by
    rw [he]; exact IsFork.basic (15) (15) (9) (223) (142) (7) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm16 hf)

theorem edge0_3 : FramedCore node (mutate (node 0) 3) ∨ IsFork (mutate (node 0) 3) 3 := by
  left; refine ⟨0, perm21, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 3 u v = relabel (node 0) perm21 u v from by decide) u v

theorem all_cyclic : ∀ i, ¬ Acyclic (node i) := by
  intro i
  have hi : i = 0 := by omega
  rcases hi with rfl
  · exact cyclic0

theorem all_edges : ∀ i k, FramedCore node (mutate (node i) k) ∨ IsFork (mutate (node i) k) k := by
  intro i k
  have hi : i = 0 := by omega
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hi with rfl <;>
    rcases hk with rfl | rfl | rfl | rfl
  · exact edge0_0
  · exact edge0_1
  · exact edge0_2
  · exact edge0_3

theorem nma : ¬ MutationAcyclic (ofSix (-7) (-15) (2) (-9) (-7) (-15)) :=
  framed_core_NMA node all_cyclic all_edges 0
end Core02

namespace Core03
def node (i : Fin 3) : Matrix 4 := match i.val with
  | 0 => (ofSix (-6) (-8) (3) (-8) (-13) (-4))
  | 1 => (ofSix (6) (8) (-3) (-8) (5) (20))
  | _ => (ofSix (33) (4) (-3) (-8) (13) (4))

theorem cyclic0 : ¬ Acyclic (node 0) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge0_0 : FramedCore node (mutate (node 0) 0) ∨ IsFork (mutate (node 0) 0) 0 := by
  left; refine ⟨1, perm0, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 0 u v = relabel (node 1) perm0 u v from by decide) u v

theorem edge0_1 : FramedCore node (mutate (node 0) 1) ∨ IsFork (mutate (node 0) 1) 1 := by
  right
  have he : relabel (mutate (node 0) 1) perm7 = template (6) (13) (8) (75) (56) (4) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 0) 1) perm7 u v = template (6) (13) (8) (75) (56) (4) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 0) 1) perm7) 0 := by
    rw [he]; exact IsFork.basic (6) (13) (8) (75) (56) (4) (by unfold Domain; decide)
  exact fork_of_relabel perm7 hf

theorem edge0_2 : FramedCore node (mutate (node 0) 2) ∨ IsFork (mutate (node 0) 2) 2 := by
  right
  have he : relabel (reverse (mutate (node 0) 2)) perm16 = template (4) (8) (8) (29) (45) (6) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 0) 2)) perm16 u v = template (4) (8) (8) (29) (45) (6) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 0) 2)) perm16) 0 := by
    rw [he]; exact IsFork.basic (4) (8) (8) (29) (45) (6) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm16 hf)

theorem edge0_3 : FramedCore node (mutate (node 0) 3) ∨ IsFork (mutate (node 0) 3) 3 := by
  left; refine ⟨2, perm0, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 3 u v = relabel (node 2) perm0 u v from by decide) u v

theorem cyclic1 : ¬ Acyclic (node 1) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 1 (by decide)
  have h1 := hr 1 3 (by decide)
  have h2 := hr 3 0 (by decide)
  omega

theorem edge1_0 : FramedCore node (mutate (node 1) 0) ∨ IsFork (mutate (node 1) 0) 0 := by
  left; refine ⟨0, perm0, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 1) 0 u v = relabel (node 0) perm0 u v from by decide) u v

theorem edge1_1 : FramedCore node (mutate (node 1) 1) ∨ IsFork (mutate (node 1) 1) 1 := by
  right
  have he : relabel (mutate (node 1) 1) perm10 = template (5) (6) (8) (27) (60) (8) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 1) 1) perm10 u v = template (5) (6) (8) (27) (60) (8) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 1) 1) perm10) 0 := by
    rw [he]; exact IsFork.basic (5) (6) (8) (27) (60) (8) (by unfold Domain; decide)
  exact fork_of_relabel perm10 hf

theorem edge1_2 : FramedCore node (mutate (node 1) 2) ∨ IsFork (mutate (node 1) 2) 2 := by
  right
  have he : relabel (reverse (mutate (node 1) 2)) perm13 = template (8) (20) (8) (157) (70) (5) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 1) 2)) perm13 u v = template (8) (20) (8) (157) (70) (5) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 1) 2)) perm13) 0 := by
    rw [he]; exact IsFork.basic (8) (20) (8) (157) (70) (5) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm13 hf)

theorem edge1_3 : FramedCore node (mutate (node 1) 3) ∨ IsFork (mutate (node 1) 3) 3 := by
  right
  have he : relabel (mutate (node 1) 3) perm19 = template (3) (20) (5) (52) (9) (8) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 1) 3) perm19 u v = template (3) (20) (5) (52) (9) (8) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 1) 3) perm19) 0 := by
    rw [he]; exact IsFork.basic (3) (20) (5) (52) (9) (8) (by unfold Domain; decide)
  exact fork_of_relabel perm19 hf

theorem cyclic2 : ¬ Acyclic (node 2) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 1 (by decide)
  have h1 := hr 1 3 (by decide)
  have h2 := hr 3 0 (by decide)
  omega

theorem edge2_0 : FramedCore node (mutate (node 2) 0) ∨ IsFork (mutate (node 2) 0) 0 := by
  right
  have he : relabel (reverse (mutate (node 2) 0)) perm4 = template (3) (33) (4) (86) (8) (8) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 2) 0)) perm4 u v = template (3) (33) (4) (86) (8) (8) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 2) 0)) perm4) 0 := by
    rw [he]; exact IsFork.basic (3) (33) (4) (86) (8) (8) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm4 hf)

theorem edge2_1 : FramedCore node (mutate (node 2) 1) ∨ IsFork (mutate (node 2) 1) 1 := by
  right
  have he : relabel (mutate (node 2) 1) perm10 = template (13) (33) (8) (426) (108) (4) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 2) 1) perm10 u v = template (13) (33) (8) (426) (108) (4) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 2) 1) perm10) 0 := by
    rw [he]; exact IsFork.basic (13) (33) (8) (426) (108) (4) (by unfold Domain; decide)
  exact fork_of_relabel perm10 hf

theorem edge2_2 : FramedCore node (mutate (node 2) 2) ∨ IsFork (mutate (node 2) 2) 2 := by
  right
  have he : relabel (reverse (mutate (node 2) 2)) perm13 = template (4) (4) (8) (13) (65) (13) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 2) 2)) perm13 u v = template (4) (4) (8) (13) (65) (13) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 2) 2)) perm13) 0 := by
    rw [he]; exact IsFork.basic (4) (4) (8) (13) (65) (13) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm13 hf)

theorem edge2_3 : FramedCore node (mutate (node 2) 3) ∨ IsFork (mutate (node 2) 3) 3 := by
  left; refine ⟨0, perm0, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 2) 3 u v = relabel (node 0) perm0 u v from by decide) u v

theorem all_cyclic : ∀ i, ¬ Acyclic (node i) := by
  intro i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl
  · exact cyclic0
  · exact cyclic1
  · exact cyclic2

theorem all_edges : ∀ i k, FramedCore node (mutate (node i) k) ∨ IsFork (mutate (node i) k) k := by
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

theorem nma : ¬ MutationAcyclic (ofSix (-6) (-8) (3) (-8) (-13) (-4)) :=
  framed_core_NMA node all_cyclic all_edges 0
end Core03

namespace Core04
def node (i : Fin 4) : Matrix 4 := match i.val with
  | 0 => (ofSix (-3) (-15) (3) (-7) (-6) (-6))
  | 1 => (ofSix (3) (15) (-3) (-7) (3) (39))
  | 2 => (ofSix (15) (3) (-3) (-7) (6) (6))
  | _ => (ofSix (-15) (-3) (3) (-7) (-39) (-3))

theorem cyclic0 : ¬ Acyclic (node 0) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge0_0 : FramedCore node (mutate (node 0) 0) ∨ IsFork (mutate (node 0) 0) 0 := by
  left; refine ⟨1, perm0, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 0 u v = relabel (node 1) perm0 u v from by decide) u v

theorem edge0_1 : FramedCore node (mutate (node 0) 1) ∨ IsFork (mutate (node 0) 1) 1 := by
  right
  have he : relabel (mutate (node 0) 1) perm7 = template (3) (6) (7) (15) (36) (6) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 0) 1) perm7 u v = template (3) (6) (7) (15) (36) (6) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 0) 1) perm7) 0 := by
    rw [he]; exact IsFork.basic (3) (6) (7) (15) (36) (6) (by unfold Domain; decide)
  exact fork_of_relabel perm7 hf

theorem edge0_2 : FramedCore node (mutate (node 0) 2) ∨ IsFork (mutate (node 0) 2) 2 := by
  right
  have he : relabel (reverse (mutate (node 0) 2)) perm16 = template (6) (15) (7) (87) (48) (3) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 0) 2)) perm16 u v = template (6) (15) (7) (87) (48) (3) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 0) 2)) perm16) 0 := by
    rw [he]; exact IsFork.basic (6) (15) (7) (87) (48) (3) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm16 hf)

theorem edge0_3 : FramedCore node (mutate (node 0) 3) ∨ IsFork (mutate (node 0) 3) 3 := by
  left; refine ⟨2, perm0, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 3 u v = relabel (node 2) perm0 u v from by decide) u v

theorem cyclic1 : ¬ Acyclic (node 1) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 1 (by decide)
  have h1 := hr 1 3 (by decide)
  have h2 := hr 3 0 (by decide)
  omega

theorem edge1_0 : FramedCore node (mutate (node 1) 0) ∨ IsFork (mutate (node 1) 0) 0 := by
  left; refine ⟨0, perm0, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 1) 0 u v = relabel (node 0) perm0 u v from by decide) u v

theorem edge1_1 : FramedCore node (mutate (node 1) 1) ∨ IsFork (mutate (node 1) 1) 1 := by
  right
  have he : relabel (mutate (node 1) 1) perm10 = template (3) (3) (7) (6) (60) (15) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 1) 1) perm10 u v = template (3) (3) (7) (6) (60) (15) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 1) 1) perm10) 0 := by
    rw [he]; exact IsFork.basic (3) (3) (7) (6) (60) (15) (by unfold Domain; decide)
  exact fork_of_relabel perm10 hf

theorem edge1_2 : FramedCore node (mutate (node 1) 2) ∨ IsFork (mutate (node 1) 2) 2 := by
  right
  have he : relabel (reverse (mutate (node 1) 2)) perm13 = template (15) (39) (7) (582) (108) (3) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 1) 2)) perm13 u v = template (15) (39) (7) (582) (108) (3) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 1) 2)) perm13) 0 := by
    rw [he]; exact IsFork.basic (15) (39) (7) (582) (108) (3) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm13 hf)

theorem edge1_3 : FramedCore node (mutate (node 1) 3) ∨ IsFork (mutate (node 1) 3) 3 := by
  right
  have he : relabel (mutate (node 1) 3) perm19 = template (3) (39) (3) (102) (6) (7) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 1) 3) perm19 u v = template (3) (39) (3) (102) (6) (7) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 1) 3) perm19) 0 := by
    rw [he]; exact IsFork.basic (3) (39) (3) (102) (6) (7) (by unfold Domain; decide)
  exact fork_of_relabel perm19 hf

theorem cyclic2 : ¬ Acyclic (node 2) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 1 (by decide)
  have h1 := hr 1 3 (by decide)
  have h2 := hr 3 0 (by decide)
  omega

theorem edge2_0 : FramedCore node (mutate (node 2) 0) ∨ IsFork (mutate (node 2) 0) 0 := by
  left; refine ⟨3, perm0, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 2) 0 u v = relabel (node 3) perm0 u v from by decide) u v

theorem edge2_1 : FramedCore node (mutate (node 2) 1) ∨ IsFork (mutate (node 2) 1) 1 := by
  right
  have he : relabel (mutate (node 2) 1) perm10 = template (6) (15) (7) (87) (48) (3) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 2) 1) perm10 u v = template (6) (15) (7) (87) (48) (3) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 2) 1) perm10) 0 := by
    rw [he]; exact IsFork.basic (6) (15) (7) (87) (48) (3) (by unfold Domain; decide)
  exact fork_of_relabel perm10 hf

theorem edge2_2 : FramedCore node (mutate (node 2) 2) ∨ IsFork (mutate (node 2) 2) 2 := by
  right
  have he : relabel (reverse (mutate (node 2) 2)) perm13 = template (3) (6) (7) (15) (36) (6) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 2) 2)) perm13 u v = template (3) (6) (7) (15) (36) (6) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 2) 2)) perm13) 0 := by
    rw [he]; exact IsFork.basic (3) (6) (7) (15) (36) (6) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm13 hf)

theorem edge2_3 : FramedCore node (mutate (node 2) 3) ∨ IsFork (mutate (node 2) 3) 3 := by
  left; refine ⟨0, perm0, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 2) 3 u v = relabel (node 0) perm0 u v from by decide) u v

theorem cyclic3 : ¬ Acyclic (node 3) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge3_0 : FramedCore node (mutate (node 3) 0) ∨ IsFork (mutate (node 3) 0) 0 := by
  left; refine ⟨2, perm0, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 3) 0 u v = relabel (node 2) perm0 u v from by decide) u v

theorem edge3_1 : FramedCore node (mutate (node 3) 1) ∨ IsFork (mutate (node 3) 1) 1 := by
  right
  have he : relabel (mutate (node 3) 1) perm7 = template (15) (39) (7) (582) (108) (3) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 3) 1) perm7 u v = template (15) (39) (7) (582) (108) (3) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 3) 1) perm7) 0 := by
    rw [he]; exact IsFork.basic (15) (39) (7) (582) (108) (3) (by unfold Domain; decide)
  exact fork_of_relabel perm7 hf

theorem edge3_2 : FramedCore node (mutate (node 3) 2) ∨ IsFork (mutate (node 3) 2) 2 := by
  right
  have he : relabel (reverse (mutate (node 3) 2)) perm16 = template (3) (3) (7) (6) (60) (15) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 3) 2)) perm16 u v = template (3) (3) (7) (6) (60) (15) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 3) 2)) perm16) 0 := by
    rw [he]; exact IsFork.basic (3) (3) (7) (6) (60) (15) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm16 hf)

theorem edge3_3 : FramedCore node (mutate (node 3) 3) ∨ IsFork (mutate (node 3) 3) 3 := by
  right
  have he : relabel (reverse (mutate (node 3) 3)) perm18 = template (3) (39) (3) (102) (6) (7) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 3) 3)) perm18 u v = template (3) (39) (3) (102) (6) (7) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 3) 3)) perm18) 0 := by
    rw [he]; exact IsFork.basic (3) (39) (3) (102) (6) (7) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm18 hf)

theorem all_cyclic : ∀ i, ¬ Acyclic (node i) := by
  intro i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases hi with rfl | rfl | rfl | rfl
  · exact cyclic0
  · exact cyclic1
  · exact cyclic2
  · exact cyclic3

theorem all_edges : ∀ i k, FramedCore node (mutate (node i) k) ∨ IsFork (mutate (node i) k) k := by
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

theorem nma : ¬ MutationAcyclic (ofSix (-3) (-15) (3) (-7) (-6) (-6)) :=
  framed_core_NMA node all_cyclic all_edges 0
end Core04

namespace Core05
def node (i : Fin 1) : Matrix 4 := match i.val with
  | _ => (ofSix (-7) (-6) (2) (-4) (-7) (-6))

theorem cyclic0 : ¬ Acyclic (node 0) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge0_0 : FramedCore node (mutate (node 0) 0) ∨ IsFork (mutate (node 0) 0) 0 := by
  left; refine ⟨0, perm21, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 0 u v = relabel (node 0) perm21 u v from by decide) u v

theorem edge0_1 : FramedCore node (mutate (node 0) 1) ∨ IsFork (mutate (node 0) 1) 1 := by
  right
  have he : relabel (mutate (node 0) 1) perm7 = template (7) (7) (4) (47) (34) (6) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 0) 1) perm7 u v = template (7) (7) (4) (47) (34) (6) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 0) 1) perm7) 0 := by
    rw [he]; exact IsFork.basic (7) (7) (4) (47) (34) (6) (by unfold Domain; decide)
  exact fork_of_relabel perm7 hf

theorem edge0_2 : FramedCore node (mutate (node 0) 2) ∨ IsFork (mutate (node 0) 2) 2 := by
  right
  have he : relabel (reverse (mutate (node 0) 2)) perm16 = template (6) (6) (4) (34) (31) (7) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 0) 2)) perm16 u v = template (6) (6) (4) (34) (31) (7) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 0) 2)) perm16) 0 := by
    rw [he]; exact IsFork.basic (6) (6) (4) (34) (31) (7) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm16 hf)

theorem edge0_3 : FramedCore node (mutate (node 0) 3) ∨ IsFork (mutate (node 0) 3) 3 := by
  left; refine ⟨0, perm21, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 3 u v = relabel (node 0) perm21 u v from by decide) u v

theorem all_cyclic : ∀ i, ¬ Acyclic (node i) := by
  intro i
  have hi : i = 0 := by omega
  rcases hi with rfl
  · exact cyclic0

theorem all_edges : ∀ i k, FramedCore node (mutate (node i) k) ∨ IsFork (mutate (node i) k) k := by
  intro i k
  have hi : i = 0 := by omega
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hi with rfl <;>
    rcases hk with rfl | rfl | rfl | rfl
  · exact edge0_0
  · exact edge0_1
  · exact edge0_2
  · exact edge0_3

theorem nma : ¬ MutationAcyclic (ofSix (-7) (-6) (2) (-4) (-7) (-6)) :=
  framed_core_NMA node all_cyclic all_edges 0
end Core05

namespace Core06
def node (i : Fin 3) : Matrix 4 := match i.val with
  | 0 => (ofSix (-7) (-15) (3) (-7) (-10) (-6))
  | 1 => (ofSix (23) (3) (-3) (-7) (10) (6))
  | _ => (ofSix (-23) (-3) (3) (-7) (-59) (-3))

theorem cyclic0 : ¬ Acyclic (node 0) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge0_0 : FramedCore node (mutate (node 0) 0) ∨ IsFork (mutate (node 0) 0) 0 := by
  right
  have he : relabel (mutate (node 0) 0) perm5 = template (3) (15) (7) (39) (11) (7) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 0) 0) perm5 u v = template (3) (15) (7) (39) (11) (7) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 0) 0) perm5) 0 := by
    rw [he]; exact IsFork.basic (3) (15) (7) (39) (11) (7) (by unfold Domain; decide)
  exact fork_of_relabel perm5 hf

theorem edge0_1 : FramedCore node (mutate (node 0) 1) ∨ IsFork (mutate (node 0) 1) 1 := by
  right
  have he : relabel (mutate (node 0) 1) perm7 = template (7) (10) (7) (67) (64) (6) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 0) 1) perm7 u v = template (7) (10) (7) (67) (64) (6) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 0) 1) perm7) 0 := by
    rw [he]; exact IsFork.basic (7) (10) (7) (67) (64) (6) (by unfold Domain; decide)
  exact fork_of_relabel perm7 hf

theorem edge0_2 : FramedCore node (mutate (node 0) 2) ∨ IsFork (mutate (node 0) 2) 2 := by
  right
  have he : relabel (reverse (mutate (node 0) 2)) perm16 = template (6) (15) (7) (87) (52) (7) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 0) 2)) perm16 u v = template (6) (15) (7) (87) (52) (7) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 0) 2)) perm16) 0 := by
    rw [he]; exact IsFork.basic (6) (15) (7) (87) (52) (7) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm16 hf)

theorem edge0_3 : FramedCore node (mutate (node 0) 3) ∨ IsFork (mutate (node 0) 3) 3 := by
  left; refine ⟨1, perm0, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 3 u v = relabel (node 1) perm0 u v from by decide) u v

theorem cyclic1 : ¬ Acyclic (node 1) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 1 (by decide)
  have h1 := hr 1 3 (by decide)
  have h2 := hr 3 0 (by decide)
  omega

theorem edge1_0 : FramedCore node (mutate (node 1) 0) ∨ IsFork (mutate (node 1) 0) 0 := by
  left; refine ⟨2, perm0, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 1) 0 u v = relabel (node 2) perm0 u v from by decide) u v

theorem edge1_1 : FramedCore node (mutate (node 1) 1) ∨ IsFork (mutate (node 1) 1) 1 := by
  right
  have he : relabel (mutate (node 1) 1) perm10 = template (10) (23) (7) (227) (76) (3) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 1) 1) perm10 u v = template (10) (23) (7) (227) (76) (3) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 1) 1) perm10) 0 := by
    rw [he]; exact IsFork.basic (10) (23) (7) (227) (76) (3) (by unfold Domain; decide)
  exact fork_of_relabel perm10 hf

theorem edge1_2 : FramedCore node (mutate (node 1) 2) ∨ IsFork (mutate (node 1) 2) 2 := by
  right
  have he : relabel (reverse (mutate (node 1) 2)) perm13 = template (3) (6) (7) (15) (44) (10) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 1) 2)) perm13 u v = template (3) (6) (7) (15) (44) (10) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 1) 2)) perm13) 0 := by
    rw [he]; exact IsFork.basic (3) (6) (7) (15) (44) (10) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm13 hf)

theorem edge1_3 : FramedCore node (mutate (node 1) 3) ∨ IsFork (mutate (node 1) 3) 3 := by
  left; refine ⟨0, perm0, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 1) 3 u v = relabel (node 0) perm0 u v from by decide) u v

theorem cyclic2 : ¬ Acyclic (node 2) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge2_0 : FramedCore node (mutate (node 2) 0) ∨ IsFork (mutate (node 2) 0) 0 := by
  left; refine ⟨1, perm0, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 2) 0 u v = relabel (node 1) perm0 u v from by decide) u v

theorem edge2_1 : FramedCore node (mutate (node 2) 1) ∨ IsFork (mutate (node 2) 1) 1 := by
  right
  have he : relabel (mutate (node 2) 1) perm7 = template (23) (59) (7) (1354) (164) (3) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 2) 1) perm7 u v = template (23) (59) (7) (1354) (164) (3) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 2) 1) perm7) 0 := by
    rw [he]; exact IsFork.basic (23) (59) (7) (1354) (164) (3) (by unfold Domain; decide)
  exact fork_of_relabel perm7 hf

theorem edge2_2 : FramedCore node (mutate (node 2) 2) ∨ IsFork (mutate (node 2) 2) 2 := by
  right
  have he : relabel (reverse (mutate (node 2) 2)) perm16 = template (3) (3) (7) (6) (80) (23) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 2) 2)) perm16 u v = template (3) (3) (7) (6) (80) (23) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 2) 2)) perm16) 0 := by
    rw [he]; exact IsFork.basic (3) (3) (7) (6) (80) (23) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm16 hf)

theorem edge2_3 : FramedCore node (mutate (node 2) 3) ∨ IsFork (mutate (node 2) 3) 3 := by
  right
  have he : relabel (reverse (mutate (node 2) 3)) perm18 = template (3) (59) (3) (154) (6) (7) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 2) 3)) perm18 u v = template (3) (59) (3) (154) (6) (7) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 2) 3)) perm18) 0 := by
    rw [he]; exact IsFork.basic (3) (59) (3) (154) (6) (7) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm18 hf)

theorem all_cyclic : ∀ i, ¬ Acyclic (node i) := by
  intro i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl
  · exact cyclic0
  · exact cyclic1
  · exact cyclic2

theorem all_edges : ∀ i k, FramedCore node (mutate (node i) k) ∨ IsFork (mutate (node i) k) k := by
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

theorem nma : ¬ MutationAcyclic (ofSix (-7) (-15) (3) (-7) (-10) (-6)) :=
  framed_core_NMA node all_cyclic all_edges 0
end Core06

namespace Core07
def node (i : Fin 1) : Matrix 4 := match i.val with
  | _ => (ofSix (-5) (-8) (2) (-5) (-5) (-8))

theorem cyclic0 : ¬ Acyclic (node 0) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge0_0 : FramedCore node (mutate (node 0) 0) ∨ IsFork (mutate (node 0) 0) 0 := by
  left; refine ⟨0, perm21, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 0 u v = relabel (node 0) perm21 u v from by decide) u v

theorem edge0_1 : FramedCore node (mutate (node 0) 1) ∨ IsFork (mutate (node 0) 1) 1 := by
  right
  have he : relabel (mutate (node 0) 1) perm7 = template (5) (5) (5) (23) (33) (8) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 0) 1) perm7 u v = template (5) (5) (5) (23) (33) (8) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 0) 1) perm7) 0 := by
    rw [he]; exact IsFork.basic (5) (5) (5) (23) (33) (8) (by unfold Domain; decide)
  exact fork_of_relabel perm7 hf

theorem edge0_2 : FramedCore node (mutate (node 0) 2) ∨ IsFork (mutate (node 0) 2) 2 := by
  right
  have he : relabel (reverse (mutate (node 0) 2)) perm16 = template (8) (8) (5) (62) (45) (5) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 0) 2)) perm16 u v = template (8) (8) (5) (62) (45) (5) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 0) 2)) perm16) 0 := by
    rw [he]; exact IsFork.basic (8) (8) (5) (62) (45) (5) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm16 hf)

theorem edge0_3 : FramedCore node (mutate (node 0) 3) ∨ IsFork (mutate (node 0) 3) 3 := by
  left; refine ⟨0, perm21, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 3 u v = relabel (node 0) perm21 u v from by decide) u v

theorem all_cyclic : ∀ i, ¬ Acyclic (node i) := by
  intro i
  have hi : i = 0 := by omega
  rcases hi with rfl
  · exact cyclic0

theorem all_edges : ∀ i k, FramedCore node (mutate (node i) k) ∨ IsFork (mutate (node i) k) k := by
  intro i k
  have hi : i = 0 := by omega
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hi with rfl <;>
    rcases hk with rfl | rfl | rfl | rfl
  · exact edge0_0
  · exact edge0_1
  · exact edge0_2
  · exact edge0_3

theorem nma : ¬ MutationAcyclic (ofSix (-5) (-8) (2) (-5) (-5) (-8)) :=
  framed_core_NMA node all_cyclic all_edges 0
end Core07

namespace Core08
def node (i : Fin 1) : Matrix 4 := match i.val with
  | _ => (ofSix (-9) (-12) (2) (-3) (-9) (-12))

theorem cyclic0 : ¬ Acyclic (node 0) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge0_0 : FramedCore node (mutate (node 0) 0) ∨ IsFork (mutate (node 0) 0) 0 := by
  left; refine ⟨0, perm21, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 0 u v = relabel (node 0) perm21 u v from by decide) u v

theorem edge0_1 : FramedCore node (mutate (node 0) 1) ∨ IsFork (mutate (node 0) 1) 1 := by
  right
  have he : relabel (mutate (node 0) 1) perm7 = template (9) (9) (3) (79) (39) (12) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 0) 1) perm7 u v = template (9) (9) (3) (79) (39) (12) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 0) 1) perm7) 0 := by
    rw [he]; exact IsFork.basic (9) (9) (3) (79) (39) (12) (by unfold Domain; decide)
  exact fork_of_relabel perm7 hf

theorem edge0_2 : FramedCore node (mutate (node 0) 2) ∨ IsFork (mutate (node 0) 2) 2 := by
  right
  have he : relabel (reverse (mutate (node 0) 2)) perm16 = template (12) (12) (3) (142) (45) (9) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 0) 2)) perm16 u v = template (12) (12) (3) (142) (45) (9) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 0) 2)) perm16) 0 := by
    rw [he]; exact IsFork.basic (12) (12) (3) (142) (45) (9) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm16 hf)

theorem edge0_3 : FramedCore node (mutate (node 0) 3) ∨ IsFork (mutate (node 0) 3) 3 := by
  left; refine ⟨0, perm21, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 3 u v = relabel (node 0) perm21 u v from by decide) u v

theorem all_cyclic : ∀ i, ¬ Acyclic (node i) := by
  intro i
  have hi : i = 0 := by omega
  rcases hi with rfl
  · exact cyclic0

theorem all_edges : ∀ i k, FramedCore node (mutate (node i) k) ∨ IsFork (mutate (node i) k) k := by
  intro i k
  have hi : i = 0 := by omega
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hi with rfl <;>
    rcases hk with rfl | rfl | rfl | rfl
  · exact edge0_0
  · exact edge0_1
  · exact edge0_2
  · exact edge0_3

theorem nma : ¬ MutationAcyclic (ofSix (-9) (-12) (2) (-3) (-9) (-12)) :=
  framed_core_NMA node all_cyclic all_edges 0
end Core08

namespace Core09
def node (i : Fin 1) : Matrix 4 := match i.val with
  | _ => (ofSix (-6) (-3) (2) (-6) (-6) (-3))

theorem cyclic0 : ¬ Acyclic (node 0) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge0_0 : FramedCore node (mutate (node 0) 0) ∨ IsFork (mutate (node 0) 0) 0 := by
  left; refine ⟨0, perm21, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 0 u v = relabel (node 0) perm21 u v from by decide) u v

theorem edge0_1 : FramedCore node (mutate (node 0) 1) ∨ IsFork (mutate (node 0) 1) 1 := by
  right
  have he : relabel (mutate (node 0) 1) perm7 = template (6) (6) (6) (34) (39) (3) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 0) 1) perm7 u v = template (6) (6) (6) (34) (39) (3) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 0) 1) perm7) 0 := by
    rw [he]; exact IsFork.basic (6) (6) (6) (34) (39) (3) (by unfold Domain; decide)
  exact fork_of_relabel perm7 hf

theorem edge0_2 : FramedCore node (mutate (node 0) 2) ∨ IsFork (mutate (node 0) 2) 2 := by
  right
  have he : relabel (reverse (mutate (node 0) 2)) perm16 = template (3) (3) (6) (7) (24) (6) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 0) 2)) perm16 u v = template (3) (3) (6) (7) (24) (6) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 0) 2)) perm16) 0 := by
    rw [he]; exact IsFork.basic (3) (3) (6) (7) (24) (6) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm16 hf)

theorem edge0_3 : FramedCore node (mutate (node 0) 3) ∨ IsFork (mutate (node 0) 3) 3 := by
  left; refine ⟨0, perm21, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 3 u v = relabel (node 0) perm21 u v from by decide) u v

theorem all_cyclic : ∀ i, ¬ Acyclic (node i) := by
  intro i
  have hi : i = 0 := by omega
  rcases hi with rfl
  · exact cyclic0

theorem all_edges : ∀ i k, FramedCore node (mutate (node i) k) ∨ IsFork (mutate (node i) k) k := by
  intro i k
  have hi : i = 0 := by omega
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hi with rfl <;>
    rcases hk with rfl | rfl | rfl | rfl
  · exact edge0_0
  · exact edge0_1
  · exact edge0_2
  · exact edge0_3

theorem nma : ¬ MutationAcyclic (ofSix (-6) (-3) (2) (-6) (-6) (-3)) :=
  framed_core_NMA node all_cyclic all_edges 0
end Core09

namespace Core10
def node (i : Fin 2) : Matrix 4 := match i.val with
  | 0 => (ofSix (-4) (-5) (3) (-15) (-9) (-5))
  | _ => (ofSix (4) (5) (-3) (-15) (3) (10))

theorem cyclic0 : ¬ Acyclic (node 0) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge0_0 : FramedCore node (mutate (node 0) 0) ∨ IsFork (mutate (node 0) 0) 0 := by
  left; refine ⟨1, perm0, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 0 u v = relabel (node 1) perm0 u v from by decide) u v

theorem edge0_1 : FramedCore node (mutate (node 0) 1) ∨ IsFork (mutate (node 0) 1) 1 := by
  right
  have he : relabel (mutate (node 0) 1) perm7 = template (4) (9) (15) (33) (65) (5) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 0) 1) perm7 u v = template (4) (9) (15) (33) (65) (5) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 0) 1) perm7) 0 := by
    rw [he]; exact IsFork.basic (4) (9) (15) (33) (65) (5) (by unfold Domain; decide)
  exact fork_of_relabel perm7 hf

theorem edge0_2 : FramedCore node (mutate (node 0) 2) ∨ IsFork (mutate (node 0) 2) 2 := by
  right
  have he : relabel (reverse (mutate (node 0) 2)) perm16 = template (5) (5) (15) (22) (84) (4) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 0) 2)) perm16 u v = template (5) (5) (15) (22) (84) (4) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 0) 2)) perm16) 0 := by
    rw [he]; exact IsFork.basic (5) (5) (15) (22) (84) (4) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm16 hf)

theorem edge0_3 : FramedCore node (mutate (node 0) 3) ∨ IsFork (mutate (node 0) 3) 3 := by
  right
  have he : relabel (reverse (mutate (node 0) 3)) perm18 = template (3) (9) (5) (23) (10) (15) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 0) 3)) perm18 u v = template (3) (9) (5) (23) (10) (15) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 0) 3)) perm18) 0 := by
    rw [he]; exact IsFork.basic (3) (9) (5) (23) (10) (15) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm18 hf)

theorem cyclic1 : ¬ Acyclic (node 1) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 1 (by decide)
  have h1 := hr 1 3 (by decide)
  have h2 := hr 3 0 (by decide)
  omega

theorem edge1_0 : FramedCore node (mutate (node 1) 0) ∨ IsFork (mutate (node 1) 0) 0 := by
  left; refine ⟨0, perm0, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 1) 0 u v = relabel (node 0) perm0 u v from by decide) u v

theorem edge1_1 : FramedCore node (mutate (node 1) 1) ∨ IsFork (mutate (node 1) 1) 1 := by
  right
  have he : relabel (mutate (node 1) 1) perm10 = template (3) (4) (15) (9) (55) (5) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 1) 1) perm10 u v = template (3) (4) (15) (9) (55) (5) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 1) 1) perm10) 0 := by
    rw [he]; exact IsFork.basic (3) (4) (15) (9) (55) (5) (by unfold Domain; decide)
  exact fork_of_relabel perm10 hf

theorem edge1_2 : FramedCore node (mutate (node 1) 2) ∨ IsFork (mutate (node 1) 2) 2 := by
  right
  have he : relabel (reverse (mutate (node 1) 2)) perm13 = template (5) (10) (15) (47) (79) (3) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 1) 2)) perm13 u v = template (5) (10) (15) (47) (79) (3) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 1) 2)) perm13) 0 := by
    rw [he]; exact IsFork.basic (5) (10) (15) (47) (79) (3) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm13 hf)

theorem edge1_3 : FramedCore node (mutate (node 1) 3) ∨ IsFork (mutate (node 1) 3) 3 := by
  right
  have he : relabel (mutate (node 1) 3) perm19 = template (3) (10) (3) (25) (5) (15) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 1) 3) perm19 u v = template (3) (10) (3) (25) (5) (15) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 1) 3) perm19) 0 := by
    rw [he]; exact IsFork.basic (3) (10) (3) (25) (5) (15) (by unfold Domain; decide)
  exact fork_of_relabel perm19 hf

theorem all_cyclic : ∀ i, ¬ Acyclic (node i) := by
  intro i
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  · exact cyclic0
  · exact cyclic1

theorem all_edges : ∀ i k, FramedCore node (mutate (node i) k) ∨ IsFork (mutate (node i) k) k := by
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

theorem nma : ¬ MutationAcyclic (ofSix (-4) (-5) (3) (-15) (-9) (-5)) :=
  framed_core_NMA node all_cyclic all_edges 0
end Core10

namespace Core11
def node (i : Fin 2) : Matrix 4 := match i.val with
  | 0 => (ofSix (-5) (-4) (3) (-15) (-11) (-6))
  | _ => (ofSix (5) (4) (-3) (-15) (4) (6))

theorem cyclic0 : ¬ Acyclic (node 0) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge0_0 : FramedCore node (mutate (node 0) 0) ∨ IsFork (mutate (node 0) 0) 0 := by
  left; refine ⟨1, perm0, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 0 u v = relabel (node 1) perm0 u v from by decide) u v

theorem edge0_1 : FramedCore node (mutate (node 0) 1) ∨ IsFork (mutate (node 0) 1) 1 := by
  right
  have he : relabel (mutate (node 0) 1) perm7 = template (5) (11) (15) (52) (79) (6) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 0) 1) perm7 u v = template (5) (11) (15) (52) (79) (6) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 0) 1) perm7) 0 := by
    rw [he]; exact IsFork.basic (5) (11) (15) (52) (79) (6) (by unfold Domain; decide)
  exact fork_of_relabel perm7 hf

theorem edge0_2 : FramedCore node (mutate (node 0) 2) ∨ IsFork (mutate (node 0) 2) 2 := by
  right
  have he : relabel (reverse (mutate (node 0) 2)) perm16 = template (6) (4) (15) (21) (101) (5) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 0) 2)) perm16 u v = template (6) (4) (15) (21) (101) (5) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 0) 2)) perm16) 0 := by
    rw [he]; exact IsFork.basic (6) (4) (15) (21) (101) (5) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm16 hf)

theorem edge0_3 : FramedCore node (mutate (node 0) 3) ∨ IsFork (mutate (node 0) 3) 3 := by
  right
  have he : relabel (reverse (mutate (node 0) 3)) perm18 = template (3) (11) (6) (28) (14) (15) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 0) 3)) perm18 u v = template (3) (11) (6) (28) (14) (15) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 0) 3)) perm18) 0 := by
    rw [he]; exact IsFork.basic (3) (11) (6) (28) (14) (15) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm18 hf)

theorem cyclic1 : ¬ Acyclic (node 1) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 1 (by decide)
  have h1 := hr 1 3 (by decide)
  have h2 := hr 3 0 (by decide)
  omega

theorem edge1_0 : FramedCore node (mutate (node 1) 0) ∨ IsFork (mutate (node 1) 0) 0 := by
  left; refine ⟨0, perm0, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 1) 0 u v = relabel (node 0) perm0 u v from by decide) u v

theorem edge1_1 : FramedCore node (mutate (node 1) 1) ∨ IsFork (mutate (node 1) 1) 1 := by
  right
  have he : relabel (mutate (node 1) 1) perm10 = template (4) (5) (15) (17) (66) (4) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 1) 1) perm10 u v = template (4) (5) (15) (17) (66) (4) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 1) 1) perm10) 0 := by
    rw [he]; exact IsFork.basic (4) (5) (15) (17) (66) (4) (by unfold Domain; decide)
  exact fork_of_relabel perm10 hf

theorem edge1_2 : FramedCore node (mutate (node 1) 2) ∨ IsFork (mutate (node 1) 2) 2 := by
  right
  have he : relabel (reverse (mutate (node 1) 2)) perm13 = template (4) (6) (15) (21) (65) (4) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 1) 2)) perm13 u v = template (4) (6) (15) (21) (65) (4) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 1) 2)) perm13) 0 := by
    rw [he]; exact IsFork.basic (4) (6) (15) (21) (65) (4) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm13 hf)

theorem edge1_3 : FramedCore node (mutate (node 1) 3) ∨ IsFork (mutate (node 1) 3) 3 := by
  right
  have he : relabel (mutate (node 1) 3) perm19 = template (3) (6) (4) (14) (7) (15) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 1) 3) perm19 u v = template (3) (6) (4) (14) (7) (15) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 1) 3) perm19) 0 := by
    rw [he]; exact IsFork.basic (3) (6) (4) (14) (7) (15) (by unfold Domain; decide)
  exact fork_of_relabel perm19 hf

theorem all_cyclic : ∀ i, ¬ Acyclic (node i) := by
  intro i
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  · exact cyclic0
  · exact cyclic1

theorem all_edges : ∀ i k, FramedCore node (mutate (node i) k) ∨ IsFork (mutate (node i) k) k := by
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

theorem nma : ¬ MutationAcyclic (ofSix (-5) (-4) (3) (-15) (-11) (-6)) :=
  framed_core_NMA node all_cyclic all_edges 0
end Core11

namespace Core12
def node (i : Fin 2) : Matrix 4 := match i.val with
  | 0 => (ofSix (-8) (-6) (3) (-12) (-12) (-3))
  | _ => (ofSix (28) (3) (-3) (-12) (12) (3))

theorem cyclic0 : ¬ Acyclic (node 0) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge0_0 : FramedCore node (mutate (node 0) 0) ∨ IsFork (mutate (node 0) 0) 0 := by
  right
  have he : relabel (mutate (node 0) 0) perm5 = template (3) (6) (8) (15) (12) (12) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 0) 0) perm5 u v = template (3) (6) (8) (15) (12) (12) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 0) 0) perm5) 0 := by
    rw [he]; exact IsFork.basic (3) (6) (8) (15) (12) (12) (by unfold Domain; decide)
  exact fork_of_relabel perm5 hf

theorem edge0_1 : FramedCore node (mutate (node 0) 1) ∨ IsFork (mutate (node 0) 1) 1 := by
  right
  have he : relabel (mutate (node 0) 1) perm7 = template (8) (12) (12) (93) (102) (3) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 0) 1) perm7 u v = template (8) (12) (12) (93) (102) (3) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 0) 1) perm7) 0 := by
    rw [he]; exact IsFork.basic (8) (12) (12) (93) (102) (3) (by unfold Domain; decide)
  exact fork_of_relabel perm7 hf

theorem edge0_2 : FramedCore node (mutate (node 0) 2) ∨ IsFork (mutate (node 0) 2) 2 := by
  right
  have he : relabel (reverse (mutate (node 0) 2)) perm16 = template (3) (6) (12) (15) (48) (8) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 0) 2)) perm16 u v = template (3) (6) (12) (15) (48) (8) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 0) 2)) perm16) 0 := by
    rw [he]; exact IsFork.basic (3) (6) (12) (15) (48) (8) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm16 hf)

theorem edge0_3 : FramedCore node (mutate (node 0) 3) ∨ IsFork (mutate (node 0) 3) 3 := by
  left; refine ⟨1, perm0, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 3 u v = relabel (node 1) perm0 u v from by decide) u v

theorem cyclic1 : ¬ Acyclic (node 1) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 1 (by decide)
  have h1 := hr 1 3 (by decide)
  have h2 := hr 3 0 (by decide)
  omega

theorem edge1_0 : FramedCore node (mutate (node 1) 0) ∨ IsFork (mutate (node 1) 0) 0 := by
  right
  have he : relabel (reverse (mutate (node 1) 0)) perm4 = template (3) (28) (3) (72) (6) (12) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 1) 0)) perm4 u v = template (3) (28) (3) (72) (6) (12) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 1) 0)) perm4) 0 := by
    rw [he]; exact IsFork.basic (3) (28) (3) (72) (6) (12) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm4 hf)

theorem edge1_1 : FramedCore node (mutate (node 1) 1) ∨ IsFork (mutate (node 1) 1) 1 := by
  right
  have he : relabel (mutate (node 1) 1) perm10 = template (12) (28) (12) (333) (147) (3) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 1) 1) perm10 u v = template (12) (28) (12) (333) (147) (3) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 1) 1) perm10) 0 := by
    rw [he]; exact IsFork.basic (12) (28) (12) (333) (147) (3) (by unfold Domain; decide)
  exact fork_of_relabel perm10 hf

theorem edge1_2 : FramedCore node (mutate (node 1) 2) ∨ IsFork (mutate (node 1) 2) 2 := by
  right
  have he : relabel (reverse (mutate (node 1) 2)) perm13 = template (3) (3) (12) (6) (64) (12) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 1) 2)) perm13 u v = template (3) (3) (12) (6) (64) (12) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 1) 2)) perm13) 0 := by
    rw [he]; exact IsFork.basic (3) (3) (12) (6) (64) (12) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm13 hf)

theorem edge1_3 : FramedCore node (mutate (node 1) 3) ∨ IsFork (mutate (node 1) 3) 3 := by
  left; refine ⟨0, perm0, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 1) 3 u v = relabel (node 0) perm0 u v from by decide) u v

theorem all_cyclic : ∀ i, ¬ Acyclic (node i) := by
  intro i
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  · exact cyclic0
  · exact cyclic1

theorem all_edges : ∀ i k, FramedCore node (mutate (node i) k) ∨ IsFork (mutate (node i) k) k := by
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

theorem nma : ¬ MutationAcyclic (ofSix (-8) (-6) (3) (-12) (-12) (-3)) :=
  framed_core_NMA node all_cyclic all_edges 0
end Core12

namespace Core13
def node (i : Fin 2) : Matrix 4 := match i.val with
  | 0 => (ofSix (-7) (-11) (3) (-12) (-9) (-5))
  | _ => (ofSix (20) (4) (-3) (-12) (9) (5))

theorem cyclic0 : ¬ Acyclic (node 0) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge0_0 : FramedCore node (mutate (node 0) 0) ∨ IsFork (mutate (node 0) 0) 0 := by
  right
  have he : relabel (mutate (node 0) 0) perm5 = template (3) (11) (7) (28) (12) (12) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 0) 0) perm5 u v = template (3) (11) (7) (28) (12) (12) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 0) 0) perm5) 0 := by
    rw [he]; exact IsFork.basic (3) (11) (7) (28) (12) (12) (by unfold Domain; decide)
  exact fork_of_relabel perm5 hf

theorem edge0_1 : FramedCore node (mutate (node 0) 1) ∨ IsFork (mutate (node 0) 1) 1 := by
  right
  have he : relabel (mutate (node 0) 1) perm7 = template (7) (9) (12) (60) (95) (5) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 0) 1) perm7 u v = template (7) (9) (12) (60) (95) (5) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 0) 1) perm7) 0 := by
    rw [he]; exact IsFork.basic (7) (9) (12) (60) (95) (5) (by unfold Domain; decide)
  exact fork_of_relabel perm7 hf

theorem edge0_2 : FramedCore node (mutate (node 0) 2) ∨ IsFork (mutate (node 0) 2) 2 := by
  right
  have he : relabel (reverse (mutate (node 0) 2)) perm16 = template (5) (11) (12) (52) (69) (7) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 0) 2)) perm16 u v = template (5) (11) (12) (52) (69) (7) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 0) 2)) perm16) 0 := by
    rw [he]; exact IsFork.basic (5) (11) (12) (52) (69) (7) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm16 hf)

theorem edge0_3 : FramedCore node (mutate (node 0) 3) ∨ IsFork (mutate (node 0) 3) 3 := by
  left; refine ⟨1, perm0, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 3 u v = relabel (node 1) perm0 u v from by decide) u v

theorem cyclic1 : ¬ Acyclic (node 1) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 1 (by decide)
  have h1 := hr 1 3 (by decide)
  have h2 := hr 3 0 (by decide)
  omega

theorem edge1_0 : FramedCore node (mutate (node 1) 0) ∨ IsFork (mutate (node 1) 0) 0 := by
  right
  have he : relabel (reverse (mutate (node 1) 0)) perm4 = template (3) (20) (4) (51) (7) (12) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 1) 0)) perm4 u v = template (3) (20) (4) (51) (7) (12) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 1) 0)) perm4) 0 := by
    rw [he]; exact IsFork.basic (3) (20) (4) (51) (7) (12) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm4 hf)

theorem edge1_1 : FramedCore node (mutate (node 1) 1) ∨ IsFork (mutate (node 1) 1) 1 := by
  right
  have he : relabel (mutate (node 1) 1) perm10 = template (9) (20) (12) (177) (113) (4) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 1) 1) perm10 u v = template (9) (20) (12) (177) (113) (4) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 1) 1) perm10) 0 := by
    rw [he]; exact IsFork.basic (9) (20) (12) (177) (113) (4) (by unfold Domain; decide)
  exact fork_of_relabel perm10 hf

theorem edge1_2 : FramedCore node (mutate (node 1) 2) ∨ IsFork (mutate (node 1) 2) 2 := by
  right
  have he : relabel (reverse (mutate (node 1) 2)) perm13 = template (4) (5) (12) (17) (68) (9) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 1) 2)) perm13 u v = template (4) (5) (12) (17) (68) (9) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 1) 2)) perm13) 0 := by
    rw [he]; exact IsFork.basic (4) (5) (12) (17) (68) (9) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm13 hf)

theorem edge1_3 : FramedCore node (mutate (node 1) 3) ∨ IsFork (mutate (node 1) 3) 3 := by
  left; refine ⟨0, perm0, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 1) 3 u v = relabel (node 0) perm0 u v from by decide) u v

theorem all_cyclic : ∀ i, ¬ Acyclic (node i) := by
  intro i
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  · exact cyclic0
  · exact cyclic1

theorem all_edges : ∀ i k, FramedCore node (mutate (node i) k) ∨ IsFork (mutate (node i) k) k := by
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

theorem nma : ¬ MutationAcyclic (ofSix (-7) (-11) (3) (-12) (-9) (-5)) :=
  framed_core_NMA node all_cyclic all_edges 0
end Core13

namespace Core14
def node (i : Fin 1) : Matrix 4 := match i.val with
  | _ => (ofSix (-5) (-11) (3) (-14) (-9) (-7))

theorem cyclic0 : ¬ Acyclic (node 0) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge0_0 : FramedCore node (mutate (node 0) 0) ∨ IsFork (mutate (node 0) 0) 0 := by
  right
  have he : relabel (mutate (node 0) 0) perm5 = template (3) (11) (5) (26) (6) (14) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 0) 0) perm5 u v = template (3) (11) (5) (26) (6) (14) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 0) 0) perm5) 0 := by
    rw [he]; exact IsFork.basic (3) (11) (5) (26) (6) (14) (by unfold Domain; decide)
  exact fork_of_relabel perm5 hf

theorem edge0_1 : FramedCore node (mutate (node 0) 1) ∨ IsFork (mutate (node 0) 1) 1 := by
  right
  have he : relabel (mutate (node 0) 1) perm7 = template (5) (9) (14) (42) (81) (7) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 0) 1) perm7 u v = template (5) (9) (14) (42) (81) (7) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 0) 1) perm7) 0 := by
    rw [he]; exact IsFork.basic (5) (9) (14) (42) (81) (7) (by unfold Domain; decide)
  exact fork_of_relabel perm7 hf

theorem edge0_2 : FramedCore node (mutate (node 0) 2) ∨ IsFork (mutate (node 0) 2) 2 := by
  right
  have he : relabel (reverse (mutate (node 0) 2)) perm16 = template (7) (11) (14) (74) (107) (5) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 0) 2)) perm16 u v = template (7) (11) (14) (74) (107) (5) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 0) 2)) perm16) 0 := by
    rw [he]; exact IsFork.basic (7) (11) (14) (74) (107) (5) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm16 hf)

theorem edge0_3 : FramedCore node (mutate (node 0) 3) ∨ IsFork (mutate (node 0) 3) 3 := by
  right
  have he : relabel (reverse (mutate (node 0) 3)) perm18 = template (3) (9) (7) (22) (10) (14) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 0) 3)) perm18 u v = template (3) (9) (7) (22) (10) (14) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 0) 3)) perm18) 0 := by
    rw [he]; exact IsFork.basic (3) (9) (7) (22) (10) (14) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm18 hf)

theorem all_cyclic : ∀ i, ¬ Acyclic (node i) := by
  intro i
  have hi : i = 0 := by omega
  rcases hi with rfl
  · exact cyclic0

theorem all_edges : ∀ i k, FramedCore node (mutate (node i) k) ∨ IsFork (mutate (node i) k) k := by
  intro i k
  have hi : i = 0 := by omega
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hi with rfl <;>
    rcases hk with rfl | rfl | rfl | rfl
  · exact edge0_0
  · exact edge0_1
  · exact edge0_2
  · exact edge0_3

theorem nma : ¬ MutationAcyclic (ofSix (-5) (-11) (3) (-14) (-9) (-7)) :=
  framed_core_NMA node all_cyclic all_edges 0
end Core14

namespace Core15
def node (i : Fin 1) : Matrix 4 := match i.val with
  | _ => (ofSix (-3) (-3) (2) (-9) (-3) (-3))

theorem cyclic0 : ¬ Acyclic (node 0) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge0_0 : FramedCore node (mutate (node 0) 0) ∨ IsFork (mutate (node 0) 0) 0 := by
  left; refine ⟨0, perm21, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 0 u v = relabel (node 0) perm21 u v from by decide) u v

theorem edge0_1 : FramedCore node (mutate (node 0) 1) ∨ IsFork (mutate (node 0) 1) 1 := by
  right
  have he : relabel (mutate (node 0) 1) perm7 = template (3) (3) (9) (7) (30) (3) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 0) 1) perm7 u v = template (3) (3) (9) (7) (30) (3) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 0) 1) perm7) 0 := by
    rw [he]; exact IsFork.basic (3) (3) (9) (7) (30) (3) (by unfold Domain; decide)
  exact fork_of_relabel perm7 hf

theorem edge0_2 : FramedCore node (mutate (node 0) 2) ∨ IsFork (mutate (node 0) 2) 2 := by
  right
  have he : relabel (reverse (mutate (node 0) 2)) perm16 = template (3) (3) (9) (7) (30) (3) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 0) 2)) perm16 u v = template (3) (3) (9) (7) (30) (3) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 0) 2)) perm16) 0 := by
    rw [he]; exact IsFork.basic (3) (3) (9) (7) (30) (3) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm16 hf)

theorem edge0_3 : FramedCore node (mutate (node 0) 3) ∨ IsFork (mutate (node 0) 3) 3 := by
  left; refine ⟨0, perm21, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 3 u v = relabel (node 0) perm21 u v from by decide) u v

theorem all_cyclic : ∀ i, ¬ Acyclic (node i) := by
  intro i
  have hi : i = 0 := by omega
  rcases hi with rfl
  · exact cyclic0

theorem all_edges : ∀ i k, FramedCore node (mutate (node i) k) ∨ IsFork (mutate (node i) k) k := by
  intro i k
  have hi : i = 0 := by omega
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hi with rfl <;>
    rcases hk with rfl | rfl | rfl | rfl
  · exact edge0_0
  · exact edge0_1
  · exact edge0_2
  · exact edge0_3

theorem nma : ¬ MutationAcyclic (ofSix (-3) (-3) (2) (-9) (-3) (-3)) :=
  framed_core_NMA node all_cyclic all_edges 0
end Core15

namespace Core16
def node (i : Fin 1) : Matrix 4 := match i.val with
  | _ => (ofSix (-13) (-8) (2) (-7) (-13) (-8))

theorem cyclic0 : ¬ Acyclic (node 0) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge0_0 : FramedCore node (mutate (node 0) 0) ∨ IsFork (mutate (node 0) 0) 0 := by
  left; refine ⟨0, perm21, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 0 u v = relabel (node 0) perm21 u v from by decide) u v

theorem edge0_1 : FramedCore node (mutate (node 0) 1) ∨ IsFork (mutate (node 0) 1) 1 := by
  right
  have he : relabel (mutate (node 0) 1) perm7 = template (13) (13) (7) (167) (99) (8) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 0) 1) perm7 u v = template (13) (13) (7) (167) (99) (8) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 0) 1) perm7) 0 := by
    rw [he]; exact IsFork.basic (13) (13) (7) (167) (99) (8) (by unfold Domain; decide)
  exact fork_of_relabel perm7 hf

theorem edge0_2 : FramedCore node (mutate (node 0) 2) ∨ IsFork (mutate (node 0) 2) 2 := by
  right
  have he : relabel (reverse (mutate (node 0) 2)) perm16 = template (8) (8) (7) (62) (69) (13) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 0) 2)) perm16 u v = template (8) (8) (7) (62) (69) (13) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 0) 2)) perm16) 0 := by
    rw [he]; exact IsFork.basic (8) (8) (7) (62) (69) (13) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm16 hf)

theorem edge0_3 : FramedCore node (mutate (node 0) 3) ∨ IsFork (mutate (node 0) 3) 3 := by
  left; refine ⟨0, perm21, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 3 u v = relabel (node 0) perm21 u v from by decide) u v

theorem all_cyclic : ∀ i, ¬ Acyclic (node i) := by
  intro i
  have hi : i = 0 := by omega
  rcases hi with rfl
  · exact cyclic0

theorem all_edges : ∀ i k, FramedCore node (mutate (node i) k) ∨ IsFork (mutate (node i) k) k := by
  intro i k
  have hi : i = 0 := by omega
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hi with rfl <;>
    rcases hk with rfl | rfl | rfl | rfl
  · exact edge0_0
  · exact edge0_1
  · exact edge0_2
  · exact edge0_3

theorem nma : ¬ MutationAcyclic (ofSix (-13) (-8) (2) (-7) (-13) (-8)) :=
  framed_core_NMA node all_cyclic all_edges 0
end Core16

namespace Core17
def node (i : Fin 2) : Matrix 4 := match i.val with
  | 0 => (ofSix (-3) (-3) (3) (-14) (-6) (-3))
  | _ => (ofSix (3) (3) (-3) (-14) (3) (6))

theorem cyclic0 : ¬ Acyclic (node 0) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge0_0 : FramedCore node (mutate (node 0) 0) ∨ IsFork (mutate (node 0) 0) 0 := by
  left; refine ⟨1, perm0, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 0 u v = relabel (node 1) perm0 u v from by decide) u v

theorem edge0_1 : FramedCore node (mutate (node 0) 1) ∨ IsFork (mutate (node 0) 1) 1 := by
  right
  have he : relabel (mutate (node 0) 1) perm7 = template (3) (6) (14) (15) (45) (3) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 0) 1) perm7 u v = template (3) (6) (14) (15) (45) (3) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 0) 1) perm7) 0 := by
    rw [he]; exact IsFork.basic (3) (6) (14) (15) (45) (3) (by unfold Domain; decide)
  exact fork_of_relabel perm7 hf

theorem edge0_2 : FramedCore node (mutate (node 0) 2) ∨ IsFork (mutate (node 0) 2) 2 := by
  right
  have he : relabel (reverse (mutate (node 0) 2)) perm16 = template (3) (3) (14) (6) (48) (3) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 0) 2)) perm16 u v = template (3) (3) (14) (6) (48) (3) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 0) 2)) perm16) 0 := by
    rw [he]; exact IsFork.basic (3) (3) (14) (6) (48) (3) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm16 hf)

theorem edge0_3 : FramedCore node (mutate (node 0) 3) ∨ IsFork (mutate (node 0) 3) 3 := by
  right
  have he : relabel (reverse (mutate (node 0) 3)) perm18 = template (3) (6) (3) (15) (6) (14) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 0) 3)) perm18 u v = template (3) (6) (3) (15) (6) (14) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 0) 3)) perm18) 0 := by
    rw [he]; exact IsFork.basic (3) (6) (3) (15) (6) (14) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm18 hf)

theorem cyclic1 : ¬ Acyclic (node 1) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 1 (by decide)
  have h1 := hr 1 3 (by decide)
  have h2 := hr 3 0 (by decide)
  omega

theorem edge1_0 : FramedCore node (mutate (node 1) 0) ∨ IsFork (mutate (node 1) 0) 0 := by
  left; refine ⟨0, perm0, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 1) 0 u v = relabel (node 0) perm0 u v from by decide) u v

theorem edge1_1 : FramedCore node (mutate (node 1) 1) ∨ IsFork (mutate (node 1) 1) 1 := by
  right
  have he : relabel (mutate (node 1) 1) perm10 = template (3) (3) (14) (6) (48) (3) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 1) 1) perm10 u v = template (3) (3) (14) (6) (48) (3) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 1) 1) perm10) 0 := by
    rw [he]; exact IsFork.basic (3) (3) (14) (6) (48) (3) (by unfold Domain; decide)
  exact fork_of_relabel perm10 hf

theorem edge1_2 : FramedCore node (mutate (node 1) 2) ∨ IsFork (mutate (node 1) 2) 2 := by
  right
  have he : relabel (reverse (mutate (node 1) 2)) perm13 = template (3) (6) (14) (15) (45) (3) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 1) 2)) perm13 u v = template (3) (6) (14) (15) (45) (3) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 1) 2)) perm13) 0 := by
    rw [he]; exact IsFork.basic (3) (6) (14) (15) (45) (3) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm13 hf)

theorem edge1_3 : FramedCore node (mutate (node 1) 3) ∨ IsFork (mutate (node 1) 3) 3 := by
  right
  have he : relabel (mutate (node 1) 3) perm19 = template (3) (6) (3) (15) (6) (14) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 1) 3) perm19 u v = template (3) (6) (3) (15) (6) (14) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 1) 3) perm19) 0 := by
    rw [he]; exact IsFork.basic (3) (6) (3) (15) (6) (14) (by unfold Domain; decide)
  exact fork_of_relabel perm19 hf

theorem all_cyclic : ∀ i, ¬ Acyclic (node i) := by
  intro i
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  · exact cyclic0
  · exact cyclic1

theorem all_edges : ∀ i k, FramedCore node (mutate (node i) k) ∨ IsFork (mutate (node i) k) k := by
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

theorem nma : ¬ MutationAcyclic (ofSix (-3) (-3) (3) (-14) (-6) (-3)) :=
  framed_core_NMA node all_cyclic all_edges 0
end Core17

namespace Core18
def node (i : Fin 2) : Matrix 4 := match i.val with
  | 0 => (ofSix (-3) (-11) (3) (-12) (-6) (-8))
  | _ => (ofSix (3) (11) (-3) (-12) (3) (25))

theorem cyclic0 : ¬ Acyclic (node 0) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge0_0 : FramedCore node (mutate (node 0) 0) ∨ IsFork (mutate (node 0) 0) 0 := by
  left; refine ⟨1, perm0, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 0 u v = relabel (node 1) perm0 u v from by decide) u v

theorem edge0_1 : FramedCore node (mutate (node 0) 1) ∨ IsFork (mutate (node 0) 1) 1 := by
  right
  have he : relabel (mutate (node 0) 1) perm7 = template (3) (6) (12) (15) (47) (8) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 0) 1) perm7 u v = template (3) (6) (12) (15) (47) (8) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 0) 1) perm7) 0 := by
    rw [he]; exact IsFork.basic (3) (6) (12) (15) (47) (8) (by unfold Domain; decide)
  exact fork_of_relabel perm7 hf

theorem edge0_2 : FramedCore node (mutate (node 0) 2) ∨ IsFork (mutate (node 0) 2) 2 := by
  right
  have he : relabel (reverse (mutate (node 0) 2)) perm16 = template (8) (11) (12) (85) (102) (3) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 0) 2)) perm16 u v = template (8) (11) (12) (85) (102) (3) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 0) 2)) perm16) 0 := by
    rw [he]; exact IsFork.basic (8) (11) (12) (85) (102) (3) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm16 hf)

theorem edge0_3 : FramedCore node (mutate (node 0) 3) ∨ IsFork (mutate (node 0) 3) 3 := by
  right
  have he : relabel (reverse (mutate (node 0) 3)) perm18 = template (3) (6) (8) (15) (13) (12) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 0) 3)) perm18 u v = template (3) (6) (8) (15) (13) (12) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 0) 3)) perm18) 0 := by
    rw [he]; exact IsFork.basic (3) (6) (8) (15) (13) (12) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm18 hf)

theorem cyclic1 : ¬ Acyclic (node 1) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 1 (by decide)
  have h1 := hr 1 3 (by decide)
  have h2 := hr 3 0 (by decide)
  omega

theorem edge1_0 : FramedCore node (mutate (node 1) 0) ∨ IsFork (mutate (node 1) 0) 0 := by
  left; refine ⟨0, perm0, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 1) 0 u v = relabel (node 0) perm0 u v from by decide) u v

theorem edge1_1 : FramedCore node (mutate (node 1) 1) ∨ IsFork (mutate (node 1) 1) 1 := by
  right
  have he : relabel (mutate (node 1) 1) perm10 = template (3) (3) (12) (6) (61) (11) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 1) 1) perm10 u v = template (3) (3) (12) (6) (61) (11) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 1) 1) perm10) 0 := by
    rw [he]; exact IsFork.basic (3) (3) (12) (6) (61) (11) (by unfold Domain; decide)
  exact fork_of_relabel perm10 hf

theorem edge1_2 : FramedCore node (mutate (node 1) 2) ∨ IsFork (mutate (node 1) 2) 2 := by
  right
  have he : relabel (reverse (mutate (node 1) 2)) perm13 = template (11) (25) (12) (272) (135) (3) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 1) 2)) perm13 u v = template (11) (25) (12) (272) (135) (3) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 1) 2)) perm13) 0 := by
    rw [he]; exact IsFork.basic (11) (25) (12) (272) (135) (3) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm13 hf)

theorem edge1_3 : FramedCore node (mutate (node 1) 3) ∨ IsFork (mutate (node 1) 3) 3 := by
  right
  have he : relabel (mutate (node 1) 3) perm19 = template (3) (25) (3) (64) (6) (12) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 1) 3) perm19 u v = template (3) (25) (3) (64) (6) (12) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 1) 3) perm19) 0 := by
    rw [he]; exact IsFork.basic (3) (25) (3) (64) (6) (12) (by unfold Domain; decide)
  exact fork_of_relabel perm19 hf

theorem all_cyclic : ∀ i, ¬ Acyclic (node i) := by
  intro i
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  · exact cyclic0
  · exact cyclic1

theorem all_edges : ∀ i k, FramedCore node (mutate (node i) k) ∨ IsFork (mutate (node i) k) k := by
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

theorem nma : ¬ MutationAcyclic (ofSix (-3) (-11) (3) (-12) (-6) (-8)) :=
  framed_core_NMA node all_cyclic all_edges 0
end Core18

namespace Core19
def node (i : Fin 1) : Matrix 4 := match i.val with
  | _ => (ofSix (-5) (-10) (2) (-11) (-5) (-10))

theorem cyclic0 : ¬ Acyclic (node 0) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge0_0 : FramedCore node (mutate (node 0) 0) ∨ IsFork (mutate (node 0) 0) 0 := by
  left; refine ⟨0, perm21, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 0 u v = relabel (node 0) perm21 u v from by decide) u v

theorem edge0_1 : FramedCore node (mutate (node 0) 1) ∨ IsFork (mutate (node 0) 1) 1 := by
  right
  have he : relabel (mutate (node 0) 1) perm7 = template (5) (5) (11) (23) (65) (10) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 0) 1) perm7 u v = template (5) (5) (11) (23) (65) (10) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 0) 1) perm7) 0 := by
    rw [he]; exact IsFork.basic (5) (5) (11) (23) (65) (10) (by unfold Domain; decide)
  exact fork_of_relabel perm7 hf

theorem edge0_2 : FramedCore node (mutate (node 0) 2) ∨ IsFork (mutate (node 0) 2) 2 := by
  right
  have he : relabel (reverse (mutate (node 0) 2)) perm16 = template (10) (10) (11) (98) (115) (5) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 0) 2)) perm16 u v = template (10) (10) (11) (98) (115) (5) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 0) 2)) perm16) 0 := by
    rw [he]; exact IsFork.basic (10) (10) (11) (98) (115) (5) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm16 hf)

theorem edge0_3 : FramedCore node (mutate (node 0) 3) ∨ IsFork (mutate (node 0) 3) 3 := by
  left; refine ⟨0, perm21, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 3 u v = relabel (node 0) perm21 u v from by decide) u v

theorem all_cyclic : ∀ i, ¬ Acyclic (node i) := by
  intro i
  have hi : i = 0 := by omega
  rcases hi with rfl
  · exact cyclic0

theorem all_edges : ∀ i k, FramedCore node (mutate (node i) k) ∨ IsFork (mutate (node i) k) k := by
  intro i k
  have hi : i = 0 := by omega
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hi with rfl <;>
    rcases hk with rfl | rfl | rfl | rfl
  · exact edge0_0
  · exact edge0_1
  · exact edge0_2
  · exact edge0_3

theorem nma : ¬ MutationAcyclic (ofSix (-5) (-10) (2) (-11) (-5) (-10)) :=
  framed_core_NMA node all_cyclic all_edges 0
end Core19

namespace Core20
def node (i : Fin 2) : Matrix 4 := match i.val with
  | 0 => (ofSix (-4) (-8) (3) (-11) (-6) (-4))
  | _ => (ofSix (14) (4) (-3) (-11) (6) (4))

theorem cyclic0 : ¬ Acyclic (node 0) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge0_0 : FramedCore node (mutate (node 0) 0) ∨ IsFork (mutate (node 0) 0) 0 := by
  right
  have he : relabel (mutate (node 0) 0) perm5 = template (3) (8) (4) (20) (6) (11) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 0) 0) perm5 u v = template (3) (8) (4) (20) (6) (11) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 0) 0) perm5) 0 := by
    rw [he]; exact IsFork.basic (3) (8) (4) (20) (6) (11) (by unfold Domain; decide)
  exact fork_of_relabel perm5 hf

theorem edge0_1 : FramedCore node (mutate (node 0) 1) ∨ IsFork (mutate (node 0) 1) 1 := by
  right
  have he : relabel (mutate (node 0) 1) perm7 = template (4) (6) (11) (21) (52) (4) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 0) 1) perm7 u v = template (4) (6) (11) (21) (52) (4) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 0) 1) perm7) 0 := by
    rw [he]; exact IsFork.basic (4) (6) (11) (21) (52) (4) (by unfold Domain; decide)
  exact fork_of_relabel perm7 hf

theorem edge0_2 : FramedCore node (mutate (node 0) 2) ∨ IsFork (mutate (node 0) 2) 2 := by
  right
  have he : relabel (reverse (mutate (node 0) 2)) perm16 = template (4) (8) (11) (29) (50) (4) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 0) 2)) perm16 u v = template (4) (8) (11) (29) (50) (4) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 0) 2)) perm16) 0 := by
    rw [he]; exact IsFork.basic (4) (8) (11) (29) (50) (4) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm16 hf)

theorem edge0_3 : FramedCore node (mutate (node 0) 3) ∨ IsFork (mutate (node 0) 3) 3 := by
  left; refine ⟨1, perm0, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 3 u v = relabel (node 1) perm0 u v from by decide) u v

theorem cyclic1 : ¬ Acyclic (node 1) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 1 (by decide)
  have h1 := hr 1 3 (by decide)
  have h2 := hr 3 0 (by decide)
  omega

theorem edge1_0 : FramedCore node (mutate (node 1) 0) ∨ IsFork (mutate (node 1) 0) 0 := by
  right
  have he : relabel (reverse (mutate (node 1) 0)) perm4 = template (3) (14) (4) (36) (8) (11) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 1) 0)) perm4 u v = template (3) (14) (4) (36) (8) (11) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 1) 0)) perm4) 0 := by
    rw [he]; exact IsFork.basic (3) (14) (4) (36) (8) (11) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm4 hf)

theorem edge1_1 : FramedCore node (mutate (node 1) 1) ∨ IsFork (mutate (node 1) 1) 1 := by
  right
  have he : relabel (mutate (node 1) 1) perm10 = template (6) (14) (11) (81) (70) (4) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 1) 1) perm10 u v = template (6) (14) (11) (81) (70) (4) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 1) 1) perm10) 0 := by
    rw [he]; exact IsFork.basic (6) (14) (11) (81) (70) (4) (by unfold Domain; decide)
  exact fork_of_relabel perm10 hf

theorem edge1_2 : FramedCore node (mutate (node 1) 2) ∨ IsFork (mutate (node 1) 2) 2 := by
  right
  have he : relabel (reverse (mutate (node 1) 2)) perm13 = template (4) (4) (11) (13) (58) (6) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 1) 2)) perm13 u v = template (4) (4) (11) (13) (58) (6) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 1) 2)) perm13) 0 := by
    rw [he]; exact IsFork.basic (4) (4) (11) (13) (58) (6) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm13 hf)

theorem edge1_3 : FramedCore node (mutate (node 1) 3) ∨ IsFork (mutate (node 1) 3) 3 := by
  left; refine ⟨0, perm0, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 1) 3 u v = relabel (node 0) perm0 u v from by decide) u v

theorem all_cyclic : ∀ i, ¬ Acyclic (node i) := by
  intro i
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  · exact cyclic0
  · exact cyclic1

theorem all_edges : ∀ i k, FramedCore node (mutate (node i) k) ∨ IsFork (mutate (node i) k) k := by
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

theorem nma : ¬ MutationAcyclic (ofSix (-4) (-8) (3) (-11) (-6) (-4)) :=
  framed_core_NMA node all_cyclic all_edges 0
end Core20

namespace Core21
def node (i : Fin 1) : Matrix 4 := match i.val with
  | _ => (ofSix (-4) (-6) (2) (-11) (-4) (-6))

theorem cyclic0 : ¬ Acyclic (node 0) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge0_0 : FramedCore node (mutate (node 0) 0) ∨ IsFork (mutate (node 0) 0) 0 := by
  left; refine ⟨0, perm21, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 0 u v = relabel (node 0) perm21 u v from by decide) u v

theorem edge0_1 : FramedCore node (mutate (node 0) 1) ∨ IsFork (mutate (node 0) 1) 1 := by
  right
  have he : relabel (mutate (node 0) 1) perm7 = template (4) (4) (11) (14) (50) (6) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 0) 1) perm7 u v = template (4) (4) (11) (14) (50) (6) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 0) 1) perm7) 0 := by
    rw [he]; exact IsFork.basic (4) (4) (11) (14) (50) (6) (by unfold Domain; decide)
  exact fork_of_relabel perm7 hf

theorem edge0_2 : FramedCore node (mutate (node 0) 2) ∨ IsFork (mutate (node 0) 2) 2 := by
  right
  have he : relabel (reverse (mutate (node 0) 2)) perm16 = template (6) (6) (11) (34) (70) (4) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 0) 2)) perm16 u v = template (6) (6) (11) (34) (70) (4) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 0) 2)) perm16) 0 := by
    rw [he]; exact IsFork.basic (6) (6) (11) (34) (70) (4) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm16 hf)

theorem edge0_3 : FramedCore node (mutate (node 0) 3) ∨ IsFork (mutate (node 0) 3) 3 := by
  left; refine ⟨0, perm21, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 3 u v = relabel (node 0) perm21 u v from by decide) u v

theorem all_cyclic : ∀ i, ¬ Acyclic (node i) := by
  intro i
  have hi : i = 0 := by omega
  rcases hi with rfl
  · exact cyclic0

theorem all_edges : ∀ i k, FramedCore node (mutate (node i) k) ∨ IsFork (mutate (node i) k) k := by
  intro i k
  have hi : i = 0 := by omega
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hi with rfl <;>
    rcases hk with rfl | rfl | rfl | rfl
  · exact edge0_0
  · exact edge0_1
  · exact edge0_2
  · exact edge0_3

theorem nma : ¬ MutationAcyclic (ofSix (-4) (-6) (2) (-11) (-4) (-6)) :=
  framed_core_NMA node all_cyclic all_edges 0
end Core21

namespace Core22
def node (i : Fin 1) : Matrix 4 := match i.val with
  | _ => (ofSix (-15) (-13) (2) (-4) (-15) (-13))

theorem cyclic0 : ¬ Acyclic (node 0) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge0_0 : FramedCore node (mutate (node 0) 0) ∨ IsFork (mutate (node 0) 0) 0 := by
  left; refine ⟨0, perm21, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 0 u v = relabel (node 0) perm21 u v from by decide) u v

theorem edge0_1 : FramedCore node (mutate (node 0) 1) ∨ IsFork (mutate (node 0) 1) 1 := by
  right
  have he : relabel (mutate (node 0) 1) perm7 = template (15) (15) (4) (223) (73) (13) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 0) 1) perm7 u v = template (15) (15) (4) (223) (73) (13) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 0) 1) perm7) 0 := by
    rw [he]; exact IsFork.basic (15) (15) (4) (223) (73) (13) (by unfold Domain; decide)
  exact fork_of_relabel perm7 hf

theorem edge0_2 : FramedCore node (mutate (node 0) 2) ∨ IsFork (mutate (node 0) 2) 2 := by
  right
  have he : relabel (reverse (mutate (node 0) 2)) perm16 = template (13) (13) (4) (167) (67) (15) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 0) 2)) perm16 u v = template (13) (13) (4) (167) (67) (15) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 0) 2)) perm16) 0 := by
    rw [he]; exact IsFork.basic (13) (13) (4) (167) (67) (15) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm16 hf)

theorem edge0_3 : FramedCore node (mutate (node 0) 3) ∨ IsFork (mutate (node 0) 3) 3 := by
  left; refine ⟨0, perm21, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 3 u v = relabel (node 0) perm21 u v from by decide) u v

theorem all_cyclic : ∀ i, ¬ Acyclic (node i) := by
  intro i
  have hi : i = 0 := by omega
  rcases hi with rfl
  · exact cyclic0

theorem all_edges : ∀ i k, FramedCore node (mutate (node i) k) ∨ IsFork (mutate (node i) k) k := by
  intro i k
  have hi : i = 0 := by omega
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hi with rfl <;>
    rcases hk with rfl | rfl | rfl | rfl
  · exact edge0_0
  · exact edge0_1
  · exact edge0_2
  · exact edge0_3

theorem nma : ¬ MutationAcyclic (ofSix (-15) (-13) (2) (-4) (-15) (-13)) :=
  framed_core_NMA node all_cyclic all_edges 0
end Core22

namespace Core23
def node (i : Fin 3) : Matrix 4 := match i.val with
  | 0 => (ofSix (-5) (-6) (3) (-11) (-11) (-3))
  | 1 => (ofSix (5) (6) (-3) (-11) (4) (15))
  | _ => (ofSix (28) (3) (-3) (-11) (11) (3))

theorem cyclic0 : ¬ Acyclic (node 0) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge0_0 : FramedCore node (mutate (node 0) 0) ∨ IsFork (mutate (node 0) 0) 0 := by
  left; refine ⟨1, perm0, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 0 u v = relabel (node 1) perm0 u v from by decide) u v

theorem edge0_1 : FramedCore node (mutate (node 0) 1) ∨ IsFork (mutate (node 0) 1) 1 := by
  right
  have he : relabel (mutate (node 0) 1) perm7 = template (5) (11) (11) (52) (61) (3) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 0) 1) perm7 u v = template (5) (11) (11) (52) (61) (3) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 0) 1) perm7) 0 := by
    rw [he]; exact IsFork.basic (5) (11) (11) (52) (61) (3) (by unfold Domain; decide)
  exact fork_of_relabel perm7 hf

theorem edge0_2 : FramedCore node (mutate (node 0) 2) ∨ IsFork (mutate (node 0) 2) 2 := by
  right
  have he : relabel (reverse (mutate (node 0) 2)) perm16 = template (3) (6) (11) (15) (44) (5) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 0) 2)) perm16 u v = template (3) (6) (11) (15) (44) (5) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 0) 2)) perm16) 0 := by
    rw [he]; exact IsFork.basic (3) (6) (11) (15) (44) (5) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm16 hf)

theorem edge0_3 : FramedCore node (mutate (node 0) 3) ∨ IsFork (mutate (node 0) 3) 3 := by
  left; refine ⟨2, perm0, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 3 u v = relabel (node 2) perm0 u v from by decide) u v

theorem cyclic1 : ¬ Acyclic (node 1) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 1 (by decide)
  have h1 := hr 1 3 (by decide)
  have h2 := hr 3 0 (by decide)
  omega

theorem edge1_0 : FramedCore node (mutate (node 1) 0) ∨ IsFork (mutate (node 1) 0) 0 := by
  left; refine ⟨0, perm0, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 1) 0 u v = relabel (node 0) perm0 u v from by decide) u v

theorem edge1_1 : FramedCore node (mutate (node 1) 1) ∨ IsFork (mutate (node 1) 1) 1 := by
  right
  have he : relabel (mutate (node 1) 1) perm10 = template (4) (5) (11) (17) (59) (6) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 1) 1) perm10 u v = template (4) (5) (11) (17) (59) (6) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 1) 1) perm10) 0 := by
    rw [he]; exact IsFork.basic (4) (5) (11) (17) (59) (6) (by unfold Domain; decide)
  exact fork_of_relabel perm10 hf

theorem edge1_2 : FramedCore node (mutate (node 1) 2) ∨ IsFork (mutate (node 1) 2) 2 := by
  right
  have he : relabel (reverse (mutate (node 1) 2)) perm13 = template (6) (15) (11) (87) (71) (4) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 1) 2)) perm13 u v = template (6) (15) (11) (87) (71) (4) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 1) 2)) perm13) 0 := by
    rw [he]; exact IsFork.basic (6) (15) (11) (87) (71) (4) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm13 hf)

theorem edge1_3 : FramedCore node (mutate (node 1) 3) ∨ IsFork (mutate (node 1) 3) 3 := by
  right
  have he : relabel (mutate (node 1) 3) perm19 = template (3) (15) (4) (39) (7) (11) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 1) 3) perm19 u v = template (3) (15) (4) (39) (7) (11) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 1) 3) perm19) 0 := by
    rw [he]; exact IsFork.basic (3) (15) (4) (39) (7) (11) (by unfold Domain; decide)
  exact fork_of_relabel perm19 hf

theorem cyclic2 : ¬ Acyclic (node 2) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 1 (by decide)
  have h1 := hr 1 3 (by decide)
  have h2 := hr 3 0 (by decide)
  omega

theorem edge2_0 : FramedCore node (mutate (node 2) 0) ∨ IsFork (mutate (node 2) 0) 0 := by
  right
  have he : relabel (reverse (mutate (node 2) 0)) perm4 = template (3) (28) (3) (73) (6) (11) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 2) 0)) perm4 u v = template (3) (28) (3) (73) (6) (11) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 2) 0)) perm4) 0 := by
    rw [he]; exact IsFork.basic (3) (28) (3) (73) (6) (11) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm4 hf)

theorem edge2_1 : FramedCore node (mutate (node 2) 1) ∨ IsFork (mutate (node 2) 1) 1 := by
  right
  have he : relabel (mutate (node 2) 1) perm10 = template (11) (28) (11) (305) (124) (3) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 2) 1) perm10 u v = template (11) (28) (11) (305) (124) (3) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 2) 1) perm10) 0 := by
    rw [he]; exact IsFork.basic (11) (28) (11) (305) (124) (3) (by unfold Domain; decide)
  exact fork_of_relabel perm10 hf

theorem edge2_2 : FramedCore node (mutate (node 2) 2) ∨ IsFork (mutate (node 2) 2) 2 := by
  right
  have he : relabel (reverse (mutate (node 2) 2)) perm13 = template (3) (3) (11) (6) (61) (11) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 2) 2)) perm13 u v = template (3) (3) (11) (6) (61) (11) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 2) 2)) perm13) 0 := by
    rw [he]; exact IsFork.basic (3) (3) (11) (6) (61) (11) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm13 hf)

theorem edge2_3 : FramedCore node (mutate (node 2) 3) ∨ IsFork (mutate (node 2) 3) 3 := by
  left; refine ⟨0, perm0, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 2) 3 u v = relabel (node 0) perm0 u v from by decide) u v

theorem all_cyclic : ∀ i, ¬ Acyclic (node i) := by
  intro i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl
  · exact cyclic0
  · exact cyclic1
  · exact cyclic2

theorem all_edges : ∀ i k, FramedCore node (mutate (node i) k) ∨ IsFork (mutate (node i) k) k := by
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

theorem nma : ¬ MutationAcyclic (ofSix (-5) (-6) (3) (-11) (-11) (-3)) :=
  framed_core_NMA node all_cyclic all_edges 0
end Core23

namespace Core24
def node (i : Fin 1) : Matrix 4 := match i.val with
  | _ => (ofSix (-10) (-14) (2) (-13) (-10) (-14))

theorem cyclic0 : ¬ Acyclic (node 0) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge0_0 : FramedCore node (mutate (node 0) 0) ∨ IsFork (mutate (node 0) 0) 0 := by
  left; refine ⟨0, perm21, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 0 u v = relabel (node 0) perm21 u v from by decide) u v

theorem edge0_1 : FramedCore node (mutate (node 0) 1) ∨ IsFork (mutate (node 0) 1) 1 := by
  right
  have he : relabel (mutate (node 0) 1) perm7 = template (10) (10) (13) (98) (144) (14) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 0) 1) perm7 u v = template (10) (10) (13) (98) (144) (14) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 0) 1) perm7) 0 := by
    rw [he]; exact IsFork.basic (10) (10) (13) (98) (144) (14) (by unfold Domain; decide)
  exact fork_of_relabel perm7 hf

theorem edge0_2 : FramedCore node (mutate (node 0) 2) ∨ IsFork (mutate (node 0) 2) 2 := by
  right
  have he : relabel (reverse (mutate (node 0) 2)) perm16 = template (14) (14) (13) (194) (192) (10) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 0) 2)) perm16 u v = template (14) (14) (13) (194) (192) (10) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 0) 2)) perm16) 0 := by
    rw [he]; exact IsFork.basic (14) (14) (13) (194) (192) (10) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm16 hf)

theorem edge0_3 : FramedCore node (mutate (node 0) 3) ∨ IsFork (mutate (node 0) 3) 3 := by
  left; refine ⟨0, perm21, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 3 u v = relabel (node 0) perm21 u v from by decide) u v

theorem all_cyclic : ∀ i, ¬ Acyclic (node i) := by
  intro i
  have hi : i = 0 := by omega
  rcases hi with rfl
  · exact cyclic0

theorem all_edges : ∀ i k, FramedCore node (mutate (node i) k) ∨ IsFork (mutate (node i) k) k := by
  intro i k
  have hi : i = 0 := by omega
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hi with rfl <;>
    rcases hk with rfl | rfl | rfl | rfl
  · exact edge0_0
  · exact edge0_1
  · exact edge0_2
  · exact edge0_3

theorem nma : ¬ MutationAcyclic (ofSix (-10) (-14) (2) (-13) (-10) (-14)) :=
  framed_core_NMA node all_cyclic all_edges 0
end Core24

namespace Core25
def node (i : Fin 2) : Matrix 4 := match i.val with
  | 0 => (ofSix (-6) (-11) (3) (-11) (-8) (-5))
  | _ => (ofSix (18) (4) (-3) (-11) (8) (5))

theorem cyclic0 : ¬ Acyclic (node 0) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge0_0 : FramedCore node (mutate (node 0) 0) ∨ IsFork (mutate (node 0) 0) 0 := by
  right
  have he : relabel (mutate (node 0) 0) perm5 = template (3) (11) (6) (28) (10) (11) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 0) 0) perm5 u v = template (3) (11) (6) (28) (10) (11) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 0) 0) perm5) 0 := by
    rw [he]; exact IsFork.basic (3) (11) (6) (28) (10) (11) (by unfold Domain; decide)
  exact fork_of_relabel perm5 hf

theorem edge0_1 : FramedCore node (mutate (node 0) 1) ∨ IsFork (mutate (node 0) 1) 1 := by
  right
  have he : relabel (mutate (node 0) 1) perm7 = template (6) (8) (11) (45) (77) (5) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 0) 1) perm7 u v = template (6) (8) (11) (45) (77) (5) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 0) 1) perm7) 0 := by
    rw [he]; exact IsFork.basic (6) (8) (11) (45) (77) (5) (by unfold Domain; decide)
  exact fork_of_relabel perm7 hf

theorem edge0_2 : FramedCore node (mutate (node 0) 2) ∨ IsFork (mutate (node 0) 2) 2 := by
  right
  have he : relabel (reverse (mutate (node 0) 2)) perm16 = template (5) (11) (11) (52) (63) (6) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 0) 2)) perm16 u v = template (5) (11) (11) (52) (63) (6) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 0) 2)) perm16) 0 := by
    rw [he]; exact IsFork.basic (5) (11) (11) (52) (63) (6) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm16 hf)

theorem edge0_3 : FramedCore node (mutate (node 0) 3) ∨ IsFork (mutate (node 0) 3) 3 := by
  left; refine ⟨1, perm0, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 3 u v = relabel (node 1) perm0 u v from by decide) u v

theorem cyclic1 : ¬ Acyclic (node 1) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 1 (by decide)
  have h1 := hr 1 3 (by decide)
  have h2 := hr 3 0 (by decide)
  omega

theorem edge1_0 : FramedCore node (mutate (node 1) 0) ∨ IsFork (mutate (node 1) 0) 0 := by
  right
  have he : relabel (reverse (mutate (node 1) 0)) perm4 = template (3) (18) (4) (46) (7) (11) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 1) 0)) perm4 u v = template (3) (18) (4) (46) (7) (11) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 1) 0)) perm4) 0 := by
    rw [he]; exact IsFork.basic (3) (18) (4) (46) (7) (11) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm4 hf)

theorem edge1_1 : FramedCore node (mutate (node 1) 1) ∨ IsFork (mutate (node 1) 1) 1 := by
  right
  have he : relabel (mutate (node 1) 1) perm10 = template (8) (18) (11) (141) (93) (4) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 1) 1) perm10 u v = template (8) (18) (11) (141) (93) (4) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 1) 1) perm10) 0 := by
    rw [he]; exact IsFork.basic (8) (18) (11) (141) (93) (4) (by unfold Domain; decide)
  exact fork_of_relabel perm10 hf

theorem edge1_2 : FramedCore node (mutate (node 1) 2) ∨ IsFork (mutate (node 1) 2) 2 := by
  right
  have he : relabel (reverse (mutate (node 1) 2)) perm13 = template (4) (5) (11) (17) (62) (8) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 1) 2)) perm13 u v = template (4) (5) (11) (17) (62) (8) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 1) 2)) perm13) 0 := by
    rw [he]; exact IsFork.basic (4) (5) (11) (17) (62) (8) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm13 hf)

theorem edge1_3 : FramedCore node (mutate (node 1) 3) ∨ IsFork (mutate (node 1) 3) 3 := by
  left; refine ⟨0, perm0, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 1) 3 u v = relabel (node 0) perm0 u v from by decide) u v

theorem all_cyclic : ∀ i, ¬ Acyclic (node i) := by
  intro i
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  · exact cyclic0
  · exact cyclic1

theorem all_edges : ∀ i k, FramedCore node (mutate (node i) k) ∨ IsFork (mutate (node i) k) k := by
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

theorem nma : ¬ MutationAcyclic (ofSix (-6) (-11) (3) (-11) (-8) (-5)) :=
  framed_core_NMA node all_cyclic all_edges 0
end Core25

namespace Core26
def node (i : Fin 1) : Matrix 4 := match i.val with
  | _ => (ofSix (-7) (-13) (2) (-6) (-7) (-13))

theorem cyclic0 : ¬ Acyclic (node 0) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge0_0 : FramedCore node (mutate (node 0) 0) ∨ IsFork (mutate (node 0) 0) 0 := by
  left; refine ⟨0, perm21, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 0 u v = relabel (node 0) perm21 u v from by decide) u v

theorem edge0_1 : FramedCore node (mutate (node 0) 1) ∨ IsFork (mutate (node 0) 1) 1 := by
  right
  have he : relabel (mutate (node 0) 1) perm7 = template (7) (7) (6) (47) (55) (13) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 0) 1) perm7 u v = template (7) (7) (6) (47) (55) (13) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 0) 1) perm7) 0 := by
    rw [he]; exact IsFork.basic (7) (7) (6) (47) (55) (13) (by unfold Domain; decide)
  exact fork_of_relabel perm7 hf

theorem edge0_2 : FramedCore node (mutate (node 0) 2) ∨ IsFork (mutate (node 0) 2) 2 := by
  right
  have he : relabel (reverse (mutate (node 0) 2)) perm16 = template (13) (13) (6) (167) (85) (7) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 0) 2)) perm16 u v = template (13) (13) (6) (167) (85) (7) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 0) 2)) perm16) 0 := by
    rw [he]; exact IsFork.basic (13) (13) (6) (167) (85) (7) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm16 hf)

theorem edge0_3 : FramedCore node (mutate (node 0) 3) ∨ IsFork (mutate (node 0) 3) 3 := by
  left; refine ⟨0, perm21, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 3 u v = relabel (node 0) perm21 u v from by decide) u v

theorem all_cyclic : ∀ i, ¬ Acyclic (node i) := by
  intro i
  have hi : i = 0 := by omega
  rcases hi with rfl
  · exact cyclic0

theorem all_edges : ∀ i k, FramedCore node (mutate (node i) k) ∨ IsFork (mutate (node i) k) k := by
  intro i k
  have hi : i = 0 := by omega
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hi with rfl <;>
    rcases hk with rfl | rfl | rfl | rfl
  · exact edge0_0
  · exact edge0_1
  · exact edge0_2
  · exact edge0_3

theorem nma : ¬ MutationAcyclic (ofSix (-7) (-13) (2) (-6) (-7) (-13)) :=
  framed_core_NMA node all_cyclic all_edges 0
end Core26

namespace Core27
def node (i : Fin 1) : Matrix 4 := match i.val with
  | _ => (ofSix (-6) (-8) (2) (-11) (-6) (-8))

theorem cyclic0 : ¬ Acyclic (node 0) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge0_0 : FramedCore node (mutate (node 0) 0) ∨ IsFork (mutate (node 0) 0) 0 := by
  left; refine ⟨0, perm21, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 0 u v = relabel (node 0) perm21 u v from by decide) u v

theorem edge0_1 : FramedCore node (mutate (node 0) 1) ∨ IsFork (mutate (node 0) 1) 1 := by
  right
  have he : relabel (mutate (node 0) 1) perm7 = template (6) (6) (11) (34) (74) (8) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 0) 1) perm7 u v = template (6) (6) (11) (34) (74) (8) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 0) 1) perm7) 0 := by
    rw [he]; exact IsFork.basic (6) (6) (11) (34) (74) (8) (by unfold Domain; decide)
  exact fork_of_relabel perm7 hf

theorem edge0_2 : FramedCore node (mutate (node 0) 2) ∨ IsFork (mutate (node 0) 2) 2 := by
  right
  have he : relabel (reverse (mutate (node 0) 2)) perm16 = template (8) (8) (11) (62) (94) (6) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 0) 2)) perm16 u v = template (8) (8) (11) (62) (94) (6) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 0) 2)) perm16) 0 := by
    rw [he]; exact IsFork.basic (8) (8) (11) (62) (94) (6) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm16 hf)

theorem edge0_3 : FramedCore node (mutate (node 0) 3) ∨ IsFork (mutate (node 0) 3) 3 := by
  left; refine ⟨0, perm21, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 3 u v = relabel (node 0) perm21 u v from by decide) u v

theorem all_cyclic : ∀ i, ¬ Acyclic (node i) := by
  intro i
  have hi : i = 0 := by omega
  rcases hi with rfl
  · exact cyclic0

theorem all_edges : ∀ i k, FramedCore node (mutate (node i) k) ∨ IsFork (mutate (node i) k) k := by
  intro i k
  have hi : i = 0 := by omega
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hi with rfl <;>
    rcases hk with rfl | rfl | rfl | rfl
  · exact edge0_0
  · exact edge0_1
  · exact edge0_2
  · exact edge0_3

theorem nma : ¬ MutationAcyclic (ofSix (-6) (-8) (2) (-11) (-6) (-8)) :=
  framed_core_NMA node all_cyclic all_edges 0
end Core27

namespace Core28
def node (i : Fin 1) : Matrix 4 := match i.val with
  | _ => (ofSix (-3) (-4) (2) (-11) (-3) (-4))

theorem cyclic0 : ¬ Acyclic (node 0) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge0_0 : FramedCore node (mutate (node 0) 0) ∨ IsFork (mutate (node 0) 0) 0 := by
  left; refine ⟨0, perm21, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 0 u v = relabel (node 0) perm21 u v from by decide) u v

theorem edge0_1 : FramedCore node (mutate (node 0) 1) ∨ IsFork (mutate (node 0) 1) 1 := by
  right
  have he : relabel (mutate (node 0) 1) perm7 = template (3) (3) (11) (7) (37) (4) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 0) 1) perm7 u v = template (3) (3) (11) (7) (37) (4) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 0) 1) perm7) 0 := by
    rw [he]; exact IsFork.basic (3) (3) (11) (7) (37) (4) (by unfold Domain; decide)
  exact fork_of_relabel perm7 hf

theorem edge0_2 : FramedCore node (mutate (node 0) 2) ∨ IsFork (mutate (node 0) 2) 2 := by
  right
  have he : relabel (reverse (mutate (node 0) 2)) perm16 = template (4) (4) (11) (14) (47) (3) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 0) 2)) perm16 u v = template (4) (4) (11) (14) (47) (3) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 0) 2)) perm16) 0 := by
    rw [he]; exact IsFork.basic (4) (4) (11) (14) (47) (3) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm16 hf)

theorem edge0_3 : FramedCore node (mutate (node 0) 3) ∨ IsFork (mutate (node 0) 3) 3 := by
  left; refine ⟨0, perm21, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 3 u v = relabel (node 0) perm21 u v from by decide) u v

theorem all_cyclic : ∀ i, ¬ Acyclic (node i) := by
  intro i
  have hi : i = 0 := by omega
  rcases hi with rfl
  · exact cyclic0

theorem all_edges : ∀ i k, FramedCore node (mutate (node i) k) ∨ IsFork (mutate (node i) k) k := by
  intro i k
  have hi : i = 0 := by omega
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hi with rfl <;>
    rcases hk with rfl | rfl | rfl | rfl
  · exact edge0_0
  · exact edge0_1
  · exact edge0_2
  · exact edge0_3

theorem nma : ¬ MutationAcyclic (ofSix (-3) (-4) (2) (-11) (-3) (-4)) :=
  framed_core_NMA node all_cyclic all_edges 0
end Core28

namespace Core29
def node (i : Fin 1) : Matrix 4 := match i.val with
  | _ => (ofSix (-7) (-5) (3) (-14) (-12) (-3))

theorem cyclic0 : ¬ Acyclic (node 0) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge0_0 : FramedCore node (mutate (node 0) 0) ∨ IsFork (mutate (node 0) 0) 0 := by
  right
  have he : relabel (mutate (node 0) 0) perm5 = template (3) (5) (7) (12) (9) (14) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 0) 0) perm5 u v = template (3) (5) (7) (12) (9) (14) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 0) 0) perm5) 0 := by
    rw [he]; exact IsFork.basic (3) (5) (7) (12) (9) (14) (by unfold Domain; decide)
  exact fork_of_relabel perm5 hf

theorem edge0_1 : FramedCore node (mutate (node 0) 1) ∨ IsFork (mutate (node 0) 1) 1 := by
  right
  have he : relabel (mutate (node 0) 1) perm7 = template (7) (12) (14) (81) (103) (3) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 0) 1) perm7 u v = template (7) (12) (14) (81) (103) (3) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 0) 1) perm7) 0 := by
    rw [he]; exact IsFork.basic (7) (12) (14) (81) (103) (3) (by unfold Domain; decide)
  exact fork_of_relabel perm7 hf

theorem edge0_2 : FramedCore node (mutate (node 0) 2) ∨ IsFork (mutate (node 0) 2) 2 := by
  right
  have he : relabel (reverse (mutate (node 0) 2)) perm16 = template (3) (5) (14) (12) (54) (7) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 0) 2)) perm16 u v = template (3) (5) (14) (12) (54) (7) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 0) 2)) perm16) 0 := by
    rw [he]; exact IsFork.basic (3) (5) (14) (12) (54) (7) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm16 hf)

theorem edge0_3 : FramedCore node (mutate (node 0) 3) ∨ IsFork (mutate (node 0) 3) 3 := by
  right
  have he : relabel (reverse (mutate (node 0) 3)) perm18 = template (3) (12) (3) (29) (4) (14) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 0) 3)) perm18 u v = template (3) (12) (3) (29) (4) (14) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 0) 3)) perm18) 0 := by
    rw [he]; exact IsFork.basic (3) (12) (3) (29) (4) (14) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm18 hf)

theorem all_cyclic : ∀ i, ¬ Acyclic (node i) := by
  intro i
  have hi : i = 0 := by omega
  rcases hi with rfl
  · exact cyclic0

theorem all_edges : ∀ i k, FramedCore node (mutate (node i) k) ∨ IsFork (mutate (node i) k) k := by
  intro i k
  have hi : i = 0 := by omega
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hi with rfl <;>
    rcases hk with rfl | rfl | rfl | rfl
  · exact edge0_0
  · exact edge0_1
  · exact edge0_2
  · exact edge0_3

theorem nma : ¬ MutationAcyclic (ofSix (-7) (-5) (3) (-14) (-12) (-3)) :=
  framed_core_NMA node all_cyclic all_edges 0
end Core29

namespace Core30
def node (i : Fin 1) : Matrix 4 := match i.val with
  | _ => (ofSix (-9) (-4) (2) (-7) (-9) (-4))

theorem cyclic0 : ¬ Acyclic (node 0) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge0_0 : FramedCore node (mutate (node 0) 0) ∨ IsFork (mutate (node 0) 0) 0 := by
  left; refine ⟨0, perm21, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 0 u v = relabel (node 0) perm21 u v from by decide) u v

theorem edge0_1 : FramedCore node (mutate (node 0) 1) ∨ IsFork (mutate (node 0) 1) 1 := by
  right
  have he : relabel (mutate (node 0) 1) perm7 = template (9) (9) (7) (79) (67) (4) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 0) 1) perm7 u v = template (9) (9) (7) (79) (67) (4) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 0) 1) perm7) 0 := by
    rw [he]; exact IsFork.basic (9) (9) (7) (79) (67) (4) (by unfold Domain; decide)
  exact fork_of_relabel perm7 hf

theorem edge0_2 : FramedCore node (mutate (node 0) 2) ∨ IsFork (mutate (node 0) 2) 2 := by
  right
  have he : relabel (reverse (mutate (node 0) 2)) perm16 = template (4) (4) (7) (14) (37) (9) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 0) 2)) perm16 u v = template (4) (4) (7) (14) (37) (9) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 0) 2)) perm16) 0 := by
    rw [he]; exact IsFork.basic (4) (4) (7) (14) (37) (9) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm16 hf)

theorem edge0_3 : FramedCore node (mutate (node 0) 3) ∨ IsFork (mutate (node 0) 3) 3 := by
  left; refine ⟨0, perm21, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 3 u v = relabel (node 0) perm21 u v from by decide) u v

theorem all_cyclic : ∀ i, ¬ Acyclic (node i) := by
  intro i
  have hi : i = 0 := by omega
  rcases hi with rfl
  · exact cyclic0

theorem all_edges : ∀ i k, FramedCore node (mutate (node i) k) ∨ IsFork (mutate (node i) k) k := by
  intro i k
  have hi : i = 0 := by omega
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hi with rfl <;>
    rcases hk with rfl | rfl | rfl | rfl
  · exact edge0_0
  · exact edge0_1
  · exact edge0_2
  · exact edge0_3

theorem nma : ¬ MutationAcyclic (ofSix (-9) (-4) (2) (-7) (-9) (-4)) :=
  framed_core_NMA node all_cyclic all_edges 0
end Core30

namespace Core31
def node (i : Fin 3) : Matrix 4 := match i.val with
  | 0 => (ofSix (-4) (-15) (3) (-9) (-3) (-6))
  | 1 => (ofSix (5) (3) (-3) (-9) (3) (6))
  | _ => (ofSix (-5) (-3) (3) (-9) (-12) (-3))

theorem cyclic0 : ¬ Acyclic (node 0) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge0_0 : FramedCore node (mutate (node 0) 0) ∨ IsFork (mutate (node 0) 0) 0 := by
  right
  have he : relabel (mutate (node 0) 0) perm5 = template (3) (15) (4) (39) (9) (9) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 0) 0) perm5 u v = template (3) (15) (4) (39) (9) (9) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 0) 0) perm5) 0 := by
    rw [he]; exact IsFork.basic (3) (15) (4) (39) (9) (9) (by unfold Domain; decide)
  exact fork_of_relabel perm5 hf

theorem edge0_1 : FramedCore node (mutate (node 0) 1) ∨ IsFork (mutate (node 0) 1) 1 := by
  right
  have he : relabel (mutate (node 0) 1) perm7 = template (4) (3) (9) (9) (51) (6) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 0) 1) perm7 u v = template (4) (3) (9) (9) (51) (6) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 0) 1) perm7) 0 := by
    rw [he]; exact IsFork.basic (4) (3) (9) (9) (51) (6) (by unfold Domain; decide)
  exact fork_of_relabel perm7 hf

theorem edge0_2 : FramedCore node (mutate (node 0) 2) ∨ IsFork (mutate (node 0) 2) 2 := by
  right
  have he : relabel (reverse (mutate (node 0) 2)) perm16 = template (6) (15) (9) (87) (57) (4) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 0) 2)) perm16 u v = template (6) (15) (9) (87) (57) (4) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 0) 2)) perm16) 0 := by
    rw [he]; exact IsFork.basic (6) (15) (9) (87) (57) (4) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm16 hf)

theorem edge0_3 : FramedCore node (mutate (node 0) 3) ∨ IsFork (mutate (node 0) 3) 3 := by
  left; refine ⟨1, perm0, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 3 u v = relabel (node 1) perm0 u v from by decide) u v

theorem cyclic1 : ¬ Acyclic (node 1) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 1 (by decide)
  have h1 := hr 1 3 (by decide)
  have h2 := hr 3 0 (by decide)
  omega

theorem edge1_0 : FramedCore node (mutate (node 1) 0) ∨ IsFork (mutate (node 1) 0) 0 := by
  left; refine ⟨2, perm0, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 1) 0 u v = relabel (node 2) perm0 u v from by decide) u v

theorem edge1_1 : FramedCore node (mutate (node 1) 1) ∨ IsFork (mutate (node 1) 1) 1 := by
  right
  have he : relabel (mutate (node 1) 1) perm10 = template (3) (5) (9) (12) (33) (3) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 1) 1) perm10 u v = template (3) (5) (9) (12) (33) (3) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 1) 1) perm10) 0 := by
    rw [he]; exact IsFork.basic (3) (5) (9) (12) (33) (3) (by unfold Domain; decide)
  exact fork_of_relabel perm10 hf

theorem edge1_2 : FramedCore node (mutate (node 1) 2) ∨ IsFork (mutate (node 1) 2) 2 := by
  right
  have he : relabel (reverse (mutate (node 1) 2)) perm13 = template (3) (6) (9) (15) (32) (3) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 1) 2)) perm13 u v = template (3) (6) (9) (15) (32) (3) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 1) 2)) perm13) 0 := by
    rw [he]; exact IsFork.basic (3) (6) (9) (15) (32) (3) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm13 hf)

theorem edge1_3 : FramedCore node (mutate (node 1) 3) ∨ IsFork (mutate (node 1) 3) 3 := by
  left; refine ⟨0, perm0, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 1) 3 u v = relabel (node 0) perm0 u v from by decide) u v

theorem cyclic2 : ¬ Acyclic (node 2) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge2_0 : FramedCore node (mutate (node 2) 0) ∨ IsFork (mutate (node 2) 0) 0 := by
  left; refine ⟨1, perm0, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 2) 0 u v = relabel (node 1) perm0 u v from by decide) u v

theorem edge2_1 : FramedCore node (mutate (node 2) 1) ∨ IsFork (mutate (node 2) 1) 1 := by
  right
  have he : relabel (mutate (node 2) 1) perm7 = template (5) (12) (9) (57) (48) (3) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 2) 1) perm7 u v = template (5) (12) (9) (57) (48) (3) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 2) 1) perm7) 0 := by
    rw [he]; exact IsFork.basic (5) (12) (9) (57) (48) (3) (by unfold Domain; decide)
  exact fork_of_relabel perm7 hf

theorem edge2_2 : FramedCore node (mutate (node 2) 2) ∨ IsFork (mutate (node 2) 2) 2 := by
  right
  have he : relabel (reverse (mutate (node 2) 2)) perm16 = template (3) (3) (9) (6) (39) (5) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 2) 2)) perm16 u v = template (3) (3) (9) (6) (39) (5) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 2) 2)) perm16) 0 := by
    rw [he]; exact IsFork.basic (3) (3) (9) (6) (39) (5) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm16 hf)

theorem edge2_3 : FramedCore node (mutate (node 2) 3) ∨ IsFork (mutate (node 2) 3) 3 := by
  right
  have he : relabel (reverse (mutate (node 2) 3)) perm18 = template (3) (12) (3) (31) (6) (9) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 2) 3)) perm18 u v = template (3) (12) (3) (31) (6) (9) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 2) 3)) perm18) 0 := by
    rw [he]; exact IsFork.basic (3) (12) (3) (31) (6) (9) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm18 hf)

theorem all_cyclic : ∀ i, ¬ Acyclic (node i) := by
  intro i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl
  · exact cyclic0
  · exact cyclic1
  · exact cyclic2

theorem all_edges : ∀ i k, FramedCore node (mutate (node i) k) ∨ IsFork (mutate (node i) k) k := by
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

theorem nma : ¬ MutationAcyclic (ofSix (-4) (-15) (3) (-9) (-3) (-6)) :=
  framed_core_NMA node all_cyclic all_edges 0
end Core31

namespace Core32
def node (i : Fin 1) : Matrix 4 := match i.val with
  | _ => (ofSix (-3) (-3) (2) (-15) (-3) (-3))

theorem cyclic0 : ¬ Acyclic (node 0) := by
  rintro ⟨rank, hr⟩
  have h0 := hr 0 3 (by decide)
  have h1 := hr 3 1 (by decide)
  have h2 := hr 1 0 (by decide)
  omega

theorem edge0_0 : FramedCore node (mutate (node 0) 0) ∨ IsFork (mutate (node 0) 0) 0 := by
  left; refine ⟨0, perm21, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 0 u v = relabel (node 0) perm21 u v from by decide) u v

theorem edge0_1 : FramedCore node (mutate (node 0) 1) ∨ IsFork (mutate (node 0) 1) 1 := by
  right
  have he : relabel (mutate (node 0) 1) perm7 = template (3) (3) (15) (7) (48) (3) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (mutate (node 0) 1) perm7 u v = template (3) (3) (15) (7) (48) (3) u v from by decide) u v
  have hf : IsFork (relabel (mutate (node 0) 1) perm7) 0 := by
    rw [he]; exact IsFork.basic (3) (3) (15) (7) (48) (3) (by unfold Domain; decide)
  exact fork_of_relabel perm7 hf

theorem edge0_2 : FramedCore node (mutate (node 0) 2) ∨ IsFork (mutate (node 0) 2) 2 := by
  right
  have he : relabel (reverse (mutate (node 0) 2)) perm16 = template (3) (3) (15) (7) (48) (3) := by
    funext u v
    exact (show ∀ u v : Fin 4, relabel (reverse (mutate (node 0) 2)) perm16 u v = template (3) (3) (15) (7) (48) (3) u v from by decide) u v
  have hf : IsFork (relabel (reverse (mutate (node 0) 2)) perm16) 0 := by
    rw [he]; exact IsFork.basic (3) (3) (15) (7) (48) (3) (by unfold Domain; decide)
  exact fork_of_reverse (fork_of_relabel perm16 hf)

theorem edge0_3 : FramedCore node (mutate (node 0) 3) ∨ IsFork (mutate (node 0) 3) 3 := by
  left; refine ⟨0, perm21, ?_⟩
  funext u v
  exact (show ∀ u v : Fin 4, mutate (node 0) 3 u v = relabel (node 0) perm21 u v from by decide) u v

theorem all_cyclic : ∀ i, ¬ Acyclic (node i) := by
  intro i
  have hi : i = 0 := by omega
  rcases hi with rfl
  · exact cyclic0

theorem all_edges : ∀ i k, FramedCore node (mutate (node i) k) ∨ IsFork (mutate (node i) k) k := by
  intro i k
  have hi : i = 0 := by omega
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hi with rfl <;>
    rcases hk with rfl | rfl | rfl | rfl
  · exact edge0_0
  · exact edge0_1
  · exact edge0_2
  · exact edge0_3

theorem nma : ¬ MutationAcyclic (ofSix (-3) (-3) (2) (-15) (-3) (-3)) :=
  framed_core_NMA node all_cyclic all_edges 0
end Core32

end QuiverProofs.ForkCertificates
