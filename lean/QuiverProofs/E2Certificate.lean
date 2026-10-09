import QuiverProofs.E2StripOrbit

namespace QuiverProofs.E2Certificate
open E2Strip TriangleRegions Regions Forks RegionCells RegionSemantics

def node (i : Fin 8) : Matrix 4 := match i.val with
  | 0 => ofSix (-2) (-1) (1) (-1) (1) (-2)
  | 1 => ofSix (2) (1) (-1) (-1) (3) (-1)
  | 2 => ofSix (-2) (1) (5) (1) (-3) (2)
  | 3 => ofSix (2) (-1) (-5) (3) (7) (2)
  | 4 => ofSix (-2) (-1) (7) (-1) (-1) (-2)
  | 5 => ofSix (-1) (1) (-5) (-3) (13) (-2)
  | 6 => ofSix (2) (1) (-7) (-1) (13) (5)
  | _ => ofSix (1) (-2) (-5) (3) (-13) (37)

private theorem fin8 (i : Fin 8) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 := by omega
private theorem fin6 (i : Fin 6) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 := by omega
private theorem fin4 (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega

inductive Center : Matrix 4 → Prop
  | finite (i : Fin 8) : Center (node i)
  | strip (n : Nat) (s : Fin 6) : Center (strip n s)
  | framed {Q : Matrix 4} : Center Q → (p : Relabeling 4) → Center (relabel Q p)
  | reversed {Q : Matrix 4} : Center Q → Center (reverse Q)

def frame0123 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | _ => 3),(fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | _ => 3),by decide,by decide⟩

def frame1032 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | _ => 2),(fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | _ => 2),by decide,by decide⟩

def frame0132 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | _ => 2),(fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | _ => 2),by decide,by decide⟩

def frame3120 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | _ => 0),(fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | _ => 0),by decide,by decide⟩

def frame2103 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | _ => 3),(fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | _ => 3),by decide,by decide⟩

def frame3012 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | _ => 2),(fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | _ => 0),by decide,by decide⟩

def frame3210 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | _ => 0),(fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | _ => 0),by decide,by decide⟩

def frame3102 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 0 | _ => 2),(fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 3 | _ => 0),by decide,by decide⟩

def frame1203 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 0 | _ => 3),(fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 1 | _ => 3),by decide,by decide⟩

def frame3201 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | _ => 1),(fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | _ => 0),by decide,by decide⟩

def frame1023 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | _ => 3),(fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | _ => 3),by decide,by decide⟩

def frame2013 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 1 | _ => 3),(fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 0 | _ => 3),by decide,by decide⟩

theorem node_skew (i : Fin 8) : SkewSymmetric (node i) := by
  rcases fin8 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact ofSix_skew _ _ _ _ _ _

theorem node_cyclic (i : Fin 8) : ¬ Acyclic (node i) := by
  rcases fin8 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · rintro ⟨rank,hr⟩
    have h0 := hr 0 3 (by decide)
    have h1 := hr 3 2 (by decide)
    have h2 := hr 2 0 (by decide)
    omega
  · rintro ⟨rank,hr⟩
    have h0 := hr 0 1 (by decide)
    have h1 := hr 1 3 (by decide)
    have h2 := hr 3 0 (by decide)
    omega
  · rintro ⟨rank,hr⟩
    have h0 := hr 0 3 (by decide)
    have h1 := hr 3 1 (by decide)
    have h2 := hr 1 0 (by decide)
    omega
  · rintro ⟨rank,hr⟩
    have h0 := hr 0 1 (by decide)
    have h1 := hr 1 2 (by decide)
    have h2 := hr 2 0 (by decide)
    omega
  · rintro ⟨rank,hr⟩
    have h0 := hr 0 3 (by decide)
    have h1 := hr 3 1 (by decide)
    have h2 := hr 1 0 (by decide)
    omega
  · rintro ⟨rank,hr⟩
    have h0 := hr 0 2 (by decide)
    have h1 := hr 2 1 (by decide)
    have h2 := hr 1 0 (by decide)
    omega
  · rintro ⟨rank,hr⟩
    have h0 := hr 0 1 (by decide)
    have h1 := hr 1 3 (by decide)
    have h2 := hr 3 0 (by decide)
    omega
  · rintro ⟨rank,hr⟩
    have h0 := hr 0 1 (by decide)
    have h1 := hr 1 2 (by decide)
    have h2 := hr 2 0 (by decide)
    omega

theorem node_triangles (i : Fin 8) : AllTrianglesMA (node i) := by
  apply allTrianglesMA_of_deletions
  intro r
  rcases fin8 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    rcases fin4 r with rfl|rfl|rfl|rfl
  · refine ⟨[0], (fun i => match i.val with | 0 => 1 | 1 => 2 | _ => 0), ?_⟩
    decide
  · refine ⟨[0], (fun i => match i.val with | 0 => 1 | 1 => 2 | _ => 0), ?_⟩
    decide
  · refine ⟨[], (fun i => match i.val with | 0 => 1 | 1 => 0 | _ => 2), ?_⟩
    decide
  · refine ⟨[], (fun i => match i.val with | 0 => 2 | 1 => 1 | _ => 0), ?_⟩
    decide
  · refine ⟨[1], (fun i => match i.val with | 0 => 0 | 1 => 1 | _ => 2), ?_⟩
    decide
  · refine ⟨[], (fun i => match i.val with | 0 => 1 | 1 => 2 | _ => 0), ?_⟩
    decide
  · refine ⟨[0], (fun i => match i.val with | 0 => 1 | 1 => 0 | _ => 2), ?_⟩
    decide
  · refine ⟨[], (fun i => match i.val with | 0 => 0 | 1 => 2 | _ => 1), ?_⟩
    decide
  · refine ⟨[1], (fun i => match i.val with | 0 => 2 | 1 => 1 | _ => 0), ?_⟩
    decide
  · refine ⟨[], (fun i => match i.val with | 0 => 0 | 1 => 1 | _ => 2), ?_⟩
    decide
  · refine ⟨[1,0], (fun i => match i.val with | 0 => 1 | 1 => 0 | _ => 2), ?_⟩
    decide
  · refine ⟨[], (fun i => match i.val with | 0 => 1 | 1 => 0 | _ => 2), ?_⟩
    decide
  · refine ⟨[], (fun i => match i.val with | 0 => 0 | 1 => 1 | _ => 2), ?_⟩
    decide
  · refine ⟨[], (fun i => match i.val with | 0 => 2 | 1 => 0 | _ => 1), ?_⟩
    decide
  · refine ⟨[0,1,0], (fun i => match i.val with | 0 => 1 | 1 => 0 | _ => 2), ?_⟩
    decide
  · refine ⟨[0], (fun i => match i.val with | 0 => 1 | 1 => 0 | _ => 2), ?_⟩
    decide
  · refine ⟨[], (fun i => match i.val with | 0 => 2 | 1 => 1 | _ => 0), ?_⟩
    decide
  · refine ⟨[1], (fun i => match i.val with | 0 => 0 | 1 => 1 | _ => 2), ?_⟩
    decide
  · refine ⟨[1], (fun i => match i.val with | 0 => 0 | 1 => 1 | _ => 2), ?_⟩
    decide
  · refine ⟨[], (fun i => match i.val with | 0 => 2 | 1 => 1 | _ => 0), ?_⟩
    decide
  · refine ⟨[1], (fun i => match i.val with | 0 => 0 | 1 => 1 | _ => 2), ?_⟩
    decide
  · refine ⟨[], (fun i => match i.val with | 0 => 1 | 1 => 2 | _ => 0), ?_⟩
    decide
  · refine ⟨[], (fun i => match i.val with | 0 => 2 | 1 => 0 | _ => 1), ?_⟩
    decide
  · refine ⟨[0], (fun i => match i.val with | 0 => 1 | 1 => 2 | _ => 0), ?_⟩
    decide
  · refine ⟨[], (fun i => match i.val with | 0 => 1 | 1 => 0 | _ => 2), ?_⟩
    decide
  · refine ⟨[1], (fun i => match i.val with | 0 => 2 | 1 => 1 | _ => 0), ?_⟩
    decide
  · refine ⟨[0,1], (fun i => match i.val with | 0 => 0 | 1 => 1 | _ => 2), ?_⟩
    decide
  · refine ⟨[], (fun i => match i.val with | 0 => 0 | 1 => 2 | _ => 1), ?_⟩
    decide
  · refine ⟨[0,1], (fun i => match i.val with | 0 => 0 | 1 => 1 | _ => 2), ?_⟩
    decide
  · refine ⟨[], (fun i => match i.val with | 0 => 2 | 1 => 0 | _ => 1), ?_⟩
    decide
  · refine ⟨[], (fun i => match i.val with | 0 => 1 | 1 => 2 | _ => 0), ?_⟩
    decide
  · refine ⟨[0], (fun i => match i.val with | 0 => 1 | 1 => 0 | _ => 2), ?_⟩
    decide

theorem core_0_0 : Center (mutate (node 0) 0) ∨ IsFork (mutate (node 0) 0) 0 ∨ IsRoot (mutate (node 0) 0) 0 := by
  have heq : mutate (node 0) 0 = relabel (node 1) frame0123.symm := by
    funext i j
    revert i j
    decide
  rw [heq]
  left
  exact Center.framed (Center.finite 1) frame0123.symm

theorem core_0_1 : Center (mutate (node 0) 1) ∨ IsFork (mutate (node 0) 1) 1 ∨ IsRoot (mutate (node 0) 1) 1 := by
  have heq : mutate (node 0) 1 = reverse (relabel (node 1) frame1032.symm) := by
    funext i j
    revert i j
    decide
  rw [heq]
  left
  exact Center.reversed (Center.framed (Center.finite 1) frame1032.symm)

theorem core_0_2 : Center (mutate (node 0) 2) ∨ IsFork (mutate (node 0) 2) 2 ∨ IsRoot (mutate (node 0) 2) 2 := by
  have heq : mutate (node 0) 2 = relabel (node 0) frame0132.symm := by
    funext i j
    revert i j
    decide
  rw [heq]
  left
  exact Center.framed (Center.finite 0) frame0132.symm

theorem core_0_3 : Center (mutate (node 0) 3) ∨ IsFork (mutate (node 0) 3) 3 ∨ IsRoot (mutate (node 0) 3) 3 := by
  have heq : mutate (node 0) 3 = relabel (node 0) frame0132.symm := by
    funext i j
    revert i j
    decide
  rw [heq]
  left
  exact Center.framed (Center.finite 0) frame0132.symm

theorem core_1_0 : Center (mutate (node 1) 0) ∨ IsFork (mutate (node 1) 0) 0 ∨ IsRoot (mutate (node 1) 0) 0 := by
  have heq : mutate (node 1) 0 = relabel (node 0) frame0123.symm := by
    funext i j
    revert i j
    decide
  rw [heq]
  left
  exact Center.framed (Center.finite 0) frame0123.symm

theorem core_1_1 : Center (mutate (node 1) 1) ∨ IsFork (mutate (node 1) 1) 1 ∨ IsRoot (mutate (node 1) 1) 1 := by
  have heq : mutate (node 1) 1 = relabel (node 2) frame0123.symm := by
    funext i j
    revert i j
    decide
  rw [heq]
  left
  exact Center.framed (Center.finite 2) frame0123.symm

theorem core_1_2 : Center (mutate (node 1) 2) ∨ IsFork (mutate (node 1) 2) 2 ∨ IsRoot (mutate (node 1) 2) 2 := by
  have heq : mutate (node 1) 2 = reverse (relabel (node 1) frame3120.symm) := by
    funext i j
    revert i j
    decide
  rw [heq]
  left
  exact Center.reversed (Center.framed (Center.finite 1) frame3120.symm)

theorem core_1_3 : Center (mutate (node 1) 3) ∨ IsFork (mutate (node 1) 3) 3 ∨ IsRoot (mutate (node 1) 3) 3 := by
  have heq : mutate (node 1) 3 = reverse (relabel (node 1) frame2103.symm) := by
    funext i j
    revert i j
    decide
  rw [heq]
  left
  exact Center.reversed (Center.framed (Center.finite 1) frame2103.symm)

theorem core_2_0 : Center (mutate (node 2) 0) ∨ IsFork (mutate (node 2) 0) 0 ∨ IsRoot (mutate (node 2) 0) 0 := by
  have heq : mutate (node 2) 0 = relabel (node 3) frame0123.symm := by
    funext i j
    revert i j
    decide
  rw [heq]
  left
  exact Center.framed (Center.finite 3) frame0123.symm

theorem core_2_1 : Center (mutate (node 2) 1) ∨ IsFork (mutate (node 2) 1) 1 ∨ IsRoot (mutate (node 2) 1) 1 := by
  have heq : mutate (node 2) 1 = relabel (node 1) frame0123.symm := by
    funext i j
    revert i j
    decide
  rw [heq]
  left
  exact Center.framed (Center.finite 1) frame0123.symm

theorem core_2_2 : Center (mutate (node 2) 2) ∨ IsFork (mutate (node 2) 2) 2 ∨ IsRoot (mutate (node 2) 2) 2 := by
  have heq : mutate (node 2) 2 = relabel (node 4) frame0123.symm := by
    funext i j
    revert i j
    decide
  rw [heq]
  left
  exact Center.framed (Center.finite 4) frame0123.symm

theorem core_2_3 : Center (mutate (node 2) 3) ∨ IsFork (mutate (node 2) 3) 3 ∨ IsRoot (mutate (node 2) 3) 3 := by
  have heq : relabel (reverse (mutate (node 2) 3)) frame3120 = root (3) (5) (13) (2) (5) 1 := by
    funext i j
    revert i j
    decide
  have hr : IsRoot (relabel (reverse (mutate (node 2) 3)) frame3120) 0 := by
    rw [heq]
    exact IsRoot.basic _ _ _ _ _ _ (by unfold Regions.Domain; decide) (Or.inr rfl)
  right; right
  exact root_of_reverse (root_of_relabel frame3120 hr)

theorem core_3_0 : Center (mutate (node 3) 0) ∨ IsFork (mutate (node 3) 0) 0 ∨ IsRoot (mutate (node 3) 0) 0 := by
  have heq : mutate (node 3) 0 = relabel (node 2) frame0123.symm := by
    funext i j
    revert i j
    decide
  rw [heq]
  left
  exact Center.framed (Center.finite 2) frame0123.symm

theorem core_3_1 : Center (mutate (node 3) 1) ∨ IsFork (mutate (node 3) 1) 1 ∨ IsRoot (mutate (node 3) 1) 1 := by
  have heq : relabel (reverse (mutate (node 3) 1)) frame1032 = template (2) (7) (3) (9) (5) (2) := by
    funext i j
    revert i j
    decide
  have hr : IsFork (relabel (reverse (mutate (node 3) 1)) frame1032) 0 := by
    rw [heq]
    exact IsFork.basic _ _ _ _ _ _ (by unfold Forks.Domain; decide)
  right; left
  exact fork_of_reverse (fork_of_relabel frame1032 hr)

theorem core_3_2 : Center (mutate (node 3) 2) ∨ IsFork (mutate (node 3) 2) 2 ∨ IsRoot (mutate (node 3) 2) 2 := by
  have heq : mutate (node 3) 2 = relabel (node 5) frame0123.symm := by
    funext i j
    revert i j
    decide
  rw [heq]
  left
  exact Center.framed (Center.finite 5) frame0123.symm

theorem core_3_3 : Center (mutate (node 3) 3) ∨ IsFork (mutate (node 3) 3) 3 ∨ IsRoot (mutate (node 3) 3) 3 := by
  have heq : relabel (mutate (node 3) 3) frame3012 = template (5) (7) (2) (33) (11) (3) := by
    funext i j
    revert i j
    decide
  have hr : IsFork (relabel (mutate (node 3) 3) frame3012) 0 := by
    rw [heq]
    exact IsFork.basic _ _ _ _ _ _ (by unfold Forks.Domain; decide)
  right; left
  exact fork_of_relabel frame3012 hr

theorem core_4_0 : Center (mutate (node 4) 0) ∨ IsFork (mutate (node 4) 0) 0 ∨ IsRoot (mutate (node 4) 0) 0 := by
  have heq : mutate (node 4) 0 = relabel (node 6) frame0123.symm := by
    funext i j
    revert i j
    decide
  rw [heq]
  left
  exact Center.framed (Center.finite 6) frame0123.symm

theorem core_4_1 : Center (mutate (node 4) 1) ∨ IsFork (mutate (node 4) 1) 1 ∨ IsRoot (mutate (node 4) 1) 1 := by
  have heq : mutate (node 4) 1 = reverse (relabel (node 2) frame3210.symm) := by
    funext i j
    revert i j
    decide
  rw [heq]
  left
  exact Center.reversed (Center.framed (Center.finite 2) frame3210.symm)

theorem core_4_2 : Center (mutate (node 4) 2) ∨ IsFork (mutate (node 4) 2) 2 ∨ IsRoot (mutate (node 4) 2) 2 := by
  have heq : mutate (node 4) 2 = relabel (node 2) frame0123.symm := by
    funext i j
    revert i j
    decide
  rw [heq]
  left
  exact Center.framed (Center.finite 2) frame0123.symm

theorem core_4_3 : Center (mutate (node 4) 3) ∨ IsFork (mutate (node 4) 3) 3 ∨ IsRoot (mutate (node 4) 3) 3 := by
  have heq : mutate (node 4) 3 = reverse (relabel (node 6) frame3210.symm) := by
    funext i j
    revert i j
    decide
  rw [heq]
  left
  exact Center.reversed (Center.framed (Center.finite 6) frame3210.symm)

theorem core_5_0 : Center (mutate (node 5) 0) ∨ IsFork (mutate (node 5) 0) 0 ∨ IsRoot (mutate (node 5) 0) 0 := by
  have heq : mutate (node 5) 0 = relabel (node 6) frame2103.symm := by
    funext i j
    revert i j
    decide
  rw [heq]
  left
  exact Center.framed (Center.finite 6) frame2103.symm

theorem core_5_1 : Center (mutate (node 5) 1) ∨ IsFork (mutate (node 5) 1) 1 ∨ IsRoot (mutate (node 5) 1) 1 := by
  have heq : mutate (node 5) 1 = relabel (node 7) frame0123.symm := by
    funext i j
    revert i j
    decide
  rw [heq]
  left
  exact Center.framed (Center.finite 7) frame0123.symm

theorem core_5_2 : Center (mutate (node 5) 2) ∨ IsFork (mutate (node 5) 2) 2 ∨ IsRoot (mutate (node 5) 2) 2 := by
  have heq : mutate (node 5) 2 = relabel (node 3) frame0123.symm := by
    funext i j
    revert i j
    decide
  rw [heq]
  left
  exact Center.framed (Center.finite 3) frame0123.symm

theorem core_5_3 : Center (mutate (node 5) 3) ∨ IsFork (mutate (node 5) 3) 3 ∨ IsRoot (mutate (node 5) 3) 3 := by
  have heq : relabel (mutate (node 5) 3) frame3102 = root (13) (66) (23) (5) (2) 1 := by
    funext i j
    revert i j
    decide
  have hr : IsRoot (relabel (mutate (node 5) 3) frame3102) 0 := by
    rw [heq]
    exact IsRoot.basic _ _ _ _ _ _ (by unfold Regions.Domain; decide) (Or.inr rfl)
  right; right
  exact root_of_relabel frame3102 hr

theorem core_6_0 : Center (mutate (node 6) 0) ∨ IsFork (mutate (node 6) 0) 0 ∨ IsRoot (mutate (node 6) 0) 0 := by
  have heq : mutate (node 6) 0 = relabel (node 4) frame0123.symm := by
    funext i j
    revert i j
    decide
  rw [heq]
  left
  exact Center.framed (Center.finite 4) frame0123.symm

theorem core_6_1 : Center (mutate (node 6) 1) ∨ IsFork (mutate (node 6) 1) 1 ∨ IsRoot (mutate (node 6) 1) 1 := by
  have heq : mutate (node 6) 1 = relabel (strip 0 1) frame1203.symm := by
    funext i j
    revert i j
    decide
  rw [heq]
  left
  exact Center.framed (Center.strip 0 1) frame1203.symm

theorem core_6_2 : Center (mutate (node 6) 2) ∨ IsFork (mutate (node 6) 2) 2 ∨ IsRoot (mutate (node 6) 2) 2 := by
  have heq : mutate (node 6) 2 = relabel (node 5) frame2103.symm := by
    funext i j
    revert i j
    decide
  rw [heq]
  left
  exact Center.framed (Center.finite 5) frame2103.symm

theorem core_6_3 : Center (mutate (node 6) 3) ∨ IsFork (mutate (node 6) 3) 3 ∨ IsRoot (mutate (node 6) 3) 3 := by
  have heq : relabel (reverse (mutate (node 6) 3)) frame3012 = root (7) (89) (34) (13) (5) 1 := by
    funext i j
    revert i j
    decide
  have hr : IsRoot (relabel (reverse (mutate (node 6) 3)) frame3012) 0 := by
    rw [heq]
    exact IsRoot.basic _ _ _ _ _ _ (by unfold Regions.Domain; decide) (Or.inr rfl)
  right; right
  exact root_of_reverse (root_of_relabel frame3012 hr)

theorem core_7_0 : Center (mutate (node 7) 0) ∨ IsFork (mutate (node 7) 0) 0 ∨ IsRoot (mutate (node 7) 0) 0 := by
  have heq : mutate (node 7) 0 = relabel (strip 0 2) frame0123.symm := by
    funext i j
    revert i j
    decide
  rw [heq]
  left
  exact Center.framed (Center.strip 0 2) frame0123.symm

theorem core_7_1 : Center (mutate (node 7) 1) ∨ IsFork (mutate (node 7) 1) 1 ∨ IsRoot (mutate (node 7) 1) 1 := by
  have heq : mutate (node 7) 1 = relabel (node 5) frame0123.symm := by
    funext i j
    revert i j
    decide
  rw [heq]
  left
  exact Center.framed (Center.finite 5) frame0123.symm

theorem core_7_2 : Center (mutate (node 7) 2) ∨ IsFork (mutate (node 7) 2) 2 ∨ IsRoot (mutate (node 7) 2) 2 := by
  have heq : relabel (reverse (mutate (node 7) 2)) frame2103 = template (3) (2) (37) (5) (98) (5) := by
    funext i j
    revert i j
    decide
  have hr : IsFork (relabel (reverse (mutate (node 7) 2)) frame2103) 0 := by
    rw [heq]
    exact IsFork.basic _ _ _ _ _ _ (by unfold Forks.Domain; decide)
  right; left
  exact fork_of_reverse (fork_of_relabel frame2103 hr)

theorem core_7_3 : Center (mutate (node 7) 3) ∨ IsFork (mutate (node 7) 3) 3 ∨ IsRoot (mutate (node 7) 3) 3 := by
  have heq : relabel (mutate (node 7) 3) frame3201 = root (37) (187) (478) (5) (13) 1 := by
    funext i j
    revert i j
    decide
  have hr : IsRoot (relabel (mutate (node 7) 3) frame3201) 0 := by
    rw [heq]
    exact IsRoot.basic _ _ _ _ _ _ (by unfold Regions.Domain; decide) (Or.inr rfl)
  right; right
  exact root_of_relabel frame3201 hr

theorem node_edges (i : Fin 8) (k : Fin 4) : Center (mutate (node i) k) ∨ IsFork (mutate (node i) k) k ∨ IsRoot (mutate (node i) k) k := by
  rcases fin8 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rcases fin4 k with rfl|rfl|rfl|rfl
  · exact core_0_0
  · exact core_0_1
  · exact core_0_2
  · exact core_0_3
  · exact core_1_0
  · exact core_1_1
  · exact core_1_2
  · exact core_1_3
  · exact core_2_0
  · exact core_2_1
  · exact core_2_2
  · exact core_2_3
  · exact core_3_0
  · exact core_3_1
  · exact core_3_2
  · exact core_3_3
  · exact core_4_0
  · exact core_4_1
  · exact core_4_2
  · exact core_4_3
  · exact core_5_0
  · exact core_5_1
  · exact core_5_2
  · exact core_5_3
  · exact core_6_0
  · exact core_6_1
  · exact core_6_2
  · exact core_6_3
  · exact core_7_0
  · exact core_7_1
  · exact core_7_2
  · exact core_7_3

theorem r0_identification : strip 0 0 = relabel (node 6) frame1203 := by
  funext i j
  revert i j
  decide

theorem r0_one : mutate (strip 0 0) 1 = relabel (node 5) frame1023.symm := by
  funext i j
  revert i j
  decide

theorem r0_two : mutate (strip 0 0) 2 = relabel (node 4) frame2013.symm := by
  funext i j
  revert i j
  decide

theorem q0_zero : mutate (strip 0 2) 0 = node 7 := by
  funext i j
  revert i j
  decide

/-- The 24 strip choices, with exactly three checked index-zero core returns. -/
theorem strip_edges (n : Nat) (s : Fin 6) (k : Fin 4) :
    Center (mutate (strip n s) k) ∨ IsFork (mutate (strip n s) k) k ∨
      IsRoot (mutate (strip n s) k) k := by
  have h := parameters_domain n
  rcases fin6 s with rfl|rfl|rfl|rfl|rfl|rfl <;> rcases fin4 k with rfl|rfl|rfl|rfl
  · rw [show mutate (strip n 0) 0=strip n 1 from r_zero _ _ _ h]
    exact Or.inl (Center.strip n 1)
  · cases n with
    | zero => rw [r0_one]; exact Or.inl (Center.framed (Center.finite 5) frame1023.symm)
    | succ n =>
      change Center (mutate (R (A (pa n) (pb n) (pc n)) (B (pa n) (pc n))
        (C (pa n) (pb n) (pc n))) 1) ∨ _
      rw [r_forward_one _ _ _ (parameters_domain n)]
      exact Or.inl (Center.framed (Center.strip n 4) E2Strip.frame0213)
  · cases n with
    | zero => rw [r0_two]; exact Or.inl (Center.framed (Center.finite 4) frame2013.symm)
    | succ n =>
      change Center (mutate (R (A (pa n) (pb n) (pc n)) (B (pa n) (pc n))
        (C (pa n) (pb n) (pc n))) 2) ∨ _
      rw [r_forward_two _ _ _ (parameters_domain n)]
      exact Or.inl (Center.strip n 2)
  · exact Or.inr (Or.inr (r_3_root _ _ _ h))
  · rw [show mutate (strip n 1) 0=strip n 0 from p_zero _ _ _ h]
    exact Or.inl (Center.strip n 0)
  · rw [show mutate (strip n 1) 1=strip n 2 from p_one _ _ _ h]
    exact Or.inl (Center.strip n 2)
  · rw [show mutate (strip n 1) 2=strip n 3 from p_two _ _ _ h]
    exact Or.inl (Center.strip n 3)
  · exact Or.inr (Or.inr (p_3_root _ _ _ h))
  · cases n with
    | zero => rw [q0_zero]; exact Or.inl (Center.finite 7)
    | succ n =>
      change Center (mutate (Q (A (pa n) (pb n) (pc n)) (B (pa n) (pc n))
        (C (pa n) (pb n) (pc n))) 0) ∨ _
      rw [q_forward_zero _ _ _ (parameters_domain n)]
      exact Or.inl (Center.framed (Center.strip n 5) E2Strip.frame2013)
  · rw [show mutate (strip n 2) 1=strip n 1 from q_one _ _ _ h]
    exact Or.inl (Center.strip n 1)
  · rw [show mutate (strip n 2) 2=strip (n+1) 0 from q_two _ _ _ h]
    exact Or.inl (Center.strip (n+1) 0)
  · exact Or.inr (Or.inl (q_3_fork _ _ _ h))
  · exact Or.inr (Or.inl (s_0_fork _ _ _ h))
  · rw [show mutate (strip n 3) 1=strip n 4 from s_one _ _ _ h]
    exact Or.inl (Center.strip n 4)
  · rw [show mutate (strip n 3) 2=strip n 1 from s_two _ _ _ h]
    exact Or.inl (Center.strip n 1)
  · exact Or.inr (Or.inl (s_3_fork _ _ _ h))
  · rw [show mutate (strip n 4) 0=strip n 5 from t_zero _ _ _ h]
    exact Or.inl (Center.strip n 5)
  · rw [show mutate (strip n 4) 1=strip n 3 from t_one _ _ _ h]
    exact Or.inl (Center.strip n 3)
  · have heq : mutate (strip n 4) 2=relabel (strip (n+1) 0) E2Strip.frame0213.symm := by
      rw [show strip (n+1) 0=relabel (mutate (strip n 4) 2) E2Strip.frame0213 from
        (t_two _ _ _ h).symm,relabel_inverse]
    rw [heq]
    exact Or.inl (Center.framed (Center.strip (n+1) 0) E2Strip.frame0213.symm)
  · exact Or.inr (Or.inr (t_3_root _ _ _ h))
  · rw [show mutate (strip n 5) 0=strip n 4 from v_zero _ _ _ h]
    exact Or.inl (Center.strip n 4)
  · exact Or.inr (Or.inl (v_1_fork _ _ _ h))
  · have heq : mutate (strip n 5) 2=relabel (strip (n+1) 2) E2Strip.frame2013.symm := by
      rw [show strip (n+1) 2=relabel (mutate (strip n 5) 2) E2Strip.frame2013 from
        (v_two _ _ _ h).symm,relabel_inverse]
    rw [heq]
    exact Or.inl (Center.framed (Center.strip (n+1) 2) E2Strip.frame2013.symm)
  · exact Or.inr (Or.inr (v_3_root _ _ _ h))

theorem center_skew {M : Matrix 4} (h : Center M) : SkewSymmetric M := by
  induction h with
  | finite i => exact node_skew i
  | strip n s => exact strip_skew n s
  | framed _ p ih => exact relabel_skew _ p ih
  | reversed _ ih => exact reverse_skew _ ih

theorem center_cyclic {M : Matrix 4} (h : Center M) : ¬ Acyclic M := by
  induction h with
  | finite i => exact node_cyclic i
  | strip n s => exact strip_cyclic n s
  | framed _ p ih => exact fun ha => ih ((acyclic_relabel_iff _ p).mp ha)
  | reversed h ih => exact fun ha => ih ((acyclic_reverse_iff _ (center_skew h)).mp ha)

theorem center_triangles {M : Matrix 4} (h : Center M) : AllTrianglesMA M := by
  have hr : AllTrianglesMA (strip 0 0) := by
    rw [r0_identification]
    exact triangles_relabel _ frame1203 (node_triangles 6)
  induction h with
  | finite i => exact node_triangles i
  | strip n s => exact strip_triangles hr n s
  | framed _ p ih => exact triangles_relabel _ p ih
  | reversed h ih => exact triangles_reverse _ (center_skew h) ih

theorem center_edges {M : Matrix 4} (h : Center M) (k : Fin 4) :
    Center (mutate M k) ∨ IsFork (mutate M k) k ∨ IsRoot (mutate M k) k := by
  induction h generalizing k with
  | finite i => exact node_edges i k
  | strip n s => exact strip_edges n s k
  | framed h p ih =>
    rw [mutate_relabel]
    rcases ih (p.toFun k) with hc|hf|hr
    · exact Or.inl (Center.framed hc p)
    · exact Or.inr (Or.inl (by simpa only [p.left_inv] using IsFork.relabelled hf p))
    · exact Or.inr (Or.inr (by simpa only [p.left_inv] using IsRoot.relabelled hr p))
  | reversed h ih =>
    rw [mutate_reverse]
    rcases ih k with hc|hf|hr
    · exact Or.inl (Center.reversed hc)
    · exact Or.inr (Or.inl (IsFork.reversed hf))
    · exact Or.inr (Or.inr (IsRoot.reversed hr))

/-- The exact printed E2 has no acyclic descendant under any finite mutation word. -/
theorem E2_NMA : ¬ MutationAcyclic (ofSix (-2) (-1) 1 (-1) 1 (-2)) := by
  exact region_NMA root_cells_exist Center (fun _ h => center_skew h)
    (fun _ h => center_cyclic h) (fun _ h k => center_edges h k) (node 0) (Center.finite 0)

/-- Every induced triangle of every mutation descendant of the exact E2 is MA. -/
theorem E2_global_triangle_avoidance (word : List (Fin 4)) :
    AllTrianglesMA (applyWord (ofSix (-2) (-1) 1 (-1) 1 (-2)) word) := by
  exact region_all_triangles_MA Center (fun _ h => center_skew h)
    (fun _ h => center_triangles h) (fun _ h k => center_edges h k) (node 0) (Center.finite 0) word

end QuiverProofs.E2Certificate
