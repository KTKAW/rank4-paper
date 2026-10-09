import QuiverProofs.RankThree
import QuiverProofs.RegionCells

/-! Global triangle avoidance in the recursively attached fork, diamond,
and unit-pentagon regions. Every induced triangle is quantified by its
injective vertex map; no numerical triangle test is substituted for MA. -/
namespace QuiverProofs.TriangleRegions
open Forks Regions RegionSemantics RegionCells

/-- Restriction to the ordered vertices of an induced subquiver. -/
def restrict {m n : Nat} (Q : Matrix n) (e : Fin m → Fin n) : Matrix m :=
  fun i j => Q (e i) (e j)

def AllTrianglesMA (Q : Matrix 4) : Prop :=
  ∀ e : Fin 3 → Fin 4, Function.Injective e → MutationAcyclic (restrict Q e)

/-- A ranking after deletion of the specified vertex. -/
def DeletionAcyclic (Q : Matrix 4) (r : Fin 4) : Prop :=
  ∃ rank : Fin 4 → Nat, ∀ i j, i≠r → j≠r → 0 < Q i j → rank i < rank j

private theorem fin4 (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega

theorem restrict_skew {m n : Nat} (Q : Matrix n) (e : Fin m → Fin n)
    (h : SkewSymmetric Q) : SkewSymmetric (restrict Q e) := fun i j => h (e i) (e j)

theorem restrict_mutate {m n : Nat} (Q : Matrix n) (e : Fin m → Fin n)
    (he : Function.Injective e) (k : Fin m) :
    restrict (mutate Q (e k)) e = mutate (restrict Q e) k := by
  funext i j
  have hi : e i=e k ↔ i=k := ⟨fun h => he h,congrArg e⟩
  have hj : e j=e k ↔ j=k := ⟨fun h => he h,congrArg e⟩
  simp only [restrict,mutate,hi,hj]

theorem triangles_relabel (Q : Matrix 4) (p : Relabeling 4) (h : AllTrianglesMA Q) :
    AllTrianglesMA (relabel Q p) := by
  intro e he
  exact h (p.toFun ∘ e) (fun _ _ hh => he (p.injective hh))

theorem triangles_relabel_iff (Q : Matrix 4) (p : Relabeling 4) :
    AllTrianglesMA (relabel Q p) ↔ AllTrianglesMA Q := by
  constructor
  · intro h
    have hh := triangles_relabel _ p.symm h
    rwa [relabel_inverse] at hh
  · exact triangles_relabel Q p

theorem triangles_reverse (Q : Matrix 4) (hQ : SkewSymmetric Q) (h : AllTrianglesMA Q) :
    AllTrianglesMA (reverse Q) := by
  intro e he
  exact (MA_reverse_iff (restrict Q e) (restrict_skew Q e hQ)).mpr (h e he)

theorem triangles_reverse_iff (Q : Matrix 4) (hQ : SkewSymmetric Q) :
    AllTrianglesMA (reverse Q) ↔ AllTrianglesMA Q := by
  constructor
  · intro h
    have hh := triangles_reverse _ (reverse_skew _ hQ) h
    rwa [reverse_involutive] at hh
  · exact triangles_reverse Q hQ

theorem retained_triangle_transfer (Q : Matrix 4) (r : Fin 4)
    (h : AllTrianglesMA (mutate Q r)) (e : Fin 3 → Fin 4)
    (he : Function.Injective e) (k : Fin 3) (hk : e k=r) :
    MutationAcyclic (restrict Q e) := by
  have hh := h e he
  rw [←hk,restrict_mutate Q e he k] at hh
  exact (mutationAcyclic_iff _ k).mp hh

theorem deletion_triangle_transfer (Q : Matrix 4) (r : Fin 4)
    (hdel : DeletionAcyclic Q r) (h : AllTrianglesMA (mutate Q r)) :
    AllTrianglesMA Q := by
  intro e he
  by_cases hh : ∃ k, e k=r
  · obtain ⟨k,hk⟩ := hh
    exact retained_triangle_transfer Q r h e he k hk
  · obtain ⟨rank,hr⟩ := hdel
    apply acyclic_is_mutationAcyclic
    exact ⟨rank ∘ e,fun i j hij => hr _ _ (by intro h; exact hh ⟨i,h⟩)
      (by intro h; exact hh ⟨j,h⟩) hij⟩

theorem deletion_relabel (Q : Matrix 4) (r : Fin 4) (p : Relabeling 4)
    (h : DeletionAcyclic Q r) : DeletionAcyclic (relabel Q p) (p.invFun r) := by
  obtain ⟨rank,hr⟩ := h
  refine ⟨rank ∘ p.toFun,?_⟩
  intro i j hi hj hij
  apply hr _ _ ?_ ?_ hij
  · intro hh
    have hh' := congrArg p.invFun hh
    simp only [p.left_inv] at hh'
    exact hi hh'
  · intro hh
    have hh' := congrArg p.invFun hh
    simp only [p.left_inv] at hh'
    exact hj hh'

theorem deletion_reverse (Q : Matrix 4) (r : Fin 4) (hQ : SkewSymmetric Q)
    (h : DeletionAcyclic Q r) : DeletionAcyclic (reverse Q) r := by
  obtain ⟨rank,hr⟩ := h
  obtain ⟨bound,hbound⟩ := finite_rank_bound 4 rank
  refine ⟨fun i => bound-rank i,?_⟩
  intro i j hi hj hij
  have hji : 0 < Q j i := by have := hQ i j; simp only [reverse] at hij; omega
  have hlt := hr j i hj hi hji
  have hb := hbound i
  have hc := hbound j
  change bound-rank i < bound-rank j
  omega

theorem fork_deletion {Q : Matrix 4} {r : Fin 4} (h : IsFork Q r) :
    DeletionAcyclic Q r := by
  induction h with
  | basic a b c d e f h =>
    obtain ⟨ha,hb,hc,had,hbd,hae,hce,hf⟩ := h
    refine ⟨fun i => match i.val with | 1 => 2 | 3 => 1 | _ => 0,?_⟩
    intro i j hi hj hij
    rcases fin4 i with rfl | rfl | rfl | rfl <;>
      rcases fin4 j with rfl | rfl | rfl | rfl <;>
      simp_all [Forks.template,ofSix] <;> omega
  | relabelled h p ih => exact deletion_relabel _ _ p ih
  | reversed h ih => exact deletion_reverse _ _ (fork_skew h) ih

theorem fork_triangle_transfer {Q : Matrix 4} {r : Fin 4} (h : IsFork Q r)
    (ht : AllTrianglesMA (mutate Q r)) : AllTrianglesMA Q :=
  deletion_triangle_transfer Q r (fork_deletion h) ht

theorem root_deletion (A B C D E ε : Int) (h : Regions.Domain A B C D E) (hε : 0 ≤ ε) :
    DeletionAcyclic (root A B C D E ε) 0 := by
  have hp := parameter_bounds A B C D E h
  obtain ⟨hA,hD,hE,hAB,hDB,hAC,hEC⟩ := h
  unfold H J L0 L at hp
  refine ⟨fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | _ => 3,?_⟩
  intro i j hi hj hij
  rcases fin4 i with rfl | rfl | rfl | rfl <;>
    rcases fin4 j with rfl | rfl | rfl | rfl <;>
    simp_all [root,ofSix] <;> omega

theorem diamond_w2_deletion (A B C D E : Int) (h : Regions.Domain A B C D E) :
    DeletionAcyclic (diamondW2 A B C D E) 2 := by
  have hp := parameter_bounds A B C D E h
  obtain ⟨hA,hD,hE,hAB,hDB,hAC,hEC⟩ := h
  unfold H J L0 L at hp
  refine ⟨fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 0 | _ => 1,?_⟩
  intro i j hi hj hij
  rcases fin4 i with rfl | rfl | rfl | rfl <;>
    rcases fin4 j with rfl | rfl | rfl | rfl <;>
    simp_all [diamondW2,H,ofSix] <;> omega

theorem diamond_w3_deletion (A B C D E : Int) (h : Regions.Domain A B C D E) :
    DeletionAcyclic (diamondW3 A B C D E) 3 := by
  have hp := parameter_bounds A B C D E h
  obtain ⟨hA,hD,hE,hAB,hDB,hAC,hEC⟩ := h
  unfold H J L0 L at hp
  refine ⟨fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 1 | _ => 0,?_⟩
  intro i j hi hj hij
  rcases fin4 i with rfl | rfl | rfl | rfl <;>
    rcases fin4 j with rfl | rfl | rfl | rfl <;>
    simp_all [diamondW3,J,ofSix] <;> omega

theorem unit_w_deletion (A B C D E : Int) (h : Regions.Domain A B C D E) :
    DeletionAcyclic (unitW A B C D E) 2 := by
  have hp := parameter_bounds A B C D E h
  obtain ⟨hA,hD,hE,hAB,hDB,hAC,hEC⟩ := h
  unfold H J L0 L at hp
  refine ⟨fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 0 | _ => 1,?_⟩
  intro i j hi hj hij
  rcases fin4 i with rfl | rfl | rfl | rfl <;>
    rcases fin4 j with rfl | rfl | rfl | rfl <;>
    simp_all [unitW,H,ofSix] <;> omega

theorem unit_wp_deletion (A B C D E : Int) (h : Regions.Domain A B C D E) :
    DeletionAcyclic (unitWP A B C D E) 2 := by
  have hp := parameter_bounds A B C D E h
  obtain ⟨hA,hD,hE,hAB,hDB,hAC,hEC⟩ := h
  unfold H J L0 L at hp
  refine ⟨fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 0 | _ => 1,?_⟩
  intro i j hi hj hij
  rcases fin4 i with rfl | rfl | rfl | rfl <;>
    rcases fin4 j with rfl | rfl | rfl | rfl <;>
    simp_all [unitWP,J,ofSix] <;> omega

theorem unit_t_deletion (A B C D E : Int) (h : Regions.Domain A B C D E) :
    DeletionAcyclic (unitT A B C D E) 3 := by
  have hp := parameter_bounds A B C D E h
  obtain ⟨hA,hD,hE,hAB,hDB,hAC,hEC⟩ := h
  unfold H J L0 L at hp
  refine ⟨fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | _ => 0,?_⟩
  intro i j hi hj hij
  rcases fin4 i with rfl | rfl | rfl | rfl <;>
    rcases fin4 j with rfl | rfl | rfl | rfl <;>
    simp_all [unitT,L,ofSix] <;> omega

theorem unit_tp_deletion (A B C D E : Int) (h : Regions.Domain A B C D E) :
    DeletionAcyclic (unitTP A B C D E) 3 := by
  have hp := parameter_bounds A B C D E h
  obtain ⟨hA,hD,hE,hAB,hDB,hAC,hEC⟩ := h
  unfold H J L0 L at hp
  refine ⟨fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | _ => 0,?_⟩
  intro i j hi hj hij
  rcases fin4 i with rfl | rfl | rfl | rfl <;>
    rcases fin4 j with rfl | rfl | rfl | rfl <;>
    simp_all [unitTP,L,ofSix] <;> omega

private theorem triangle_hits_special (e : Fin 3 → Fin 4) (he : Function.Injective e) :
    ∃ k, e k=2 ∨ e k=3 := by
  by_cases h0 : e 0=2 ∨ e 0=3
  · exact ⟨0,h0⟩
  by_cases h1 : e 1=2 ∨ e 1=3
  · exact ⟨1,h1⟩
  by_cases h2 : e 2=2 ∨ e 2=3
  · exact ⟨2,h2⟩
  have h01 : e 0≠e 1 := by intro hh; have := he hh; omega
  have h02 : e 0≠e 2 := by intro hh; have := he hh; omega
  have h12 : e 1≠e 2 := by intro hh; have := he hh; omega
  omega

theorem two_special_transfer (Q : Matrix 4)
    (h2 : AllTrianglesMA (mutate Q 2)) (h3 : AllTrianglesMA (mutate Q 3)) :
    AllTrianglesMA Q := by
  intro e he
  obtain ⟨k,hk|hk⟩ := triangle_hits_special e he
  · exact retained_triangle_transfer Q 2 h2 e he k hk
  · exact retained_triangle_transfer Q 3 h3 e he k hk

/-- Every triangle in a cell can descend, using mutations retained in that
triangle, to an MA parent triangle or an acyclic deletion. -/
def CellTransfer (c : Cell) : Prop :=
  AllTrianglesMA (mutate (c.state c.rootIndex) c.returnVertex) →
    ∀ i, AllTrianglesMA (c.state i)

theorem diamond_transfer (A B C D E : Int) (h : Regions.Domain A B C D E) :
    CellTransfer (diamondCell A B C D E h) := by
  intro hp i
  have hr : AllTrianglesMA (root A B C D E 0) :=
    deletion_triangle_transfer _ 0 (root_deletion A B C D E 0 h (by decide)) hp
  have hw2 : AllTrianglesMA (diamondW2 A B C D E) := by
    apply deletion_triangle_transfer _ 2 (diamond_w2_deletion A B C D E h)
    rw [diamond_w2_two A B C D E h]
    exact hr
  have hw3 : AllTrianglesMA (diamondW3 A B C D E) := by
    apply deletion_triangle_transfer _ 3 (diamond_w3_deletion A B C D E h)
    rw [diamond_w3_three A B C D E h]
    exact hr
  rcases fin4 i with rfl | rfl | rfl | rfl
  · exact hr
  · exact hw2
  · exact hw3
  · change AllTrianglesMA (diamondT A B C D E)
    apply two_special_transfer
    · rw [diamond_t_two A B C D E h]; exact hw3
    · rw [diamond_t_three A B C D E h]; exact hw2

theorem unit_transfer (A B C D E : Int) (h : Regions.Domain A B C D E) :
    CellTransfer (unitCell A B C D E h) := by
  intro hp i
  change Fin 10 at i
  have hr : AllTrianglesMA (root A B C D E 1) :=
    deletion_triangle_transfer _ 0 (root_deletion A B C D E 1 h (by decide)) hp
  have hw : AllTrianglesMA (unitW A B C D E) := by
    apply deletion_triangle_transfer _ 2 (unit_w_deletion A B C D E h)
    rw [unit_w_two A B C D E h]
    exact hr
  have hwp : AllTrianglesMA (unitWP A B C D E) := by
    apply deletion_triangle_transfer _ 2 (unit_wp_deletion A B C D E h)
    rw [unit_wp_two A B C D E h,←root_special_swap]
    exact triangles_relabel _ _ hr
  have ht : AllTrianglesMA (unitT A B C D E) := by
    apply deletion_triangle_transfer _ 3 (unit_t_deletion A B C D E h)
    rw [unit_t_three A B C D E h]
    exact hw
  have htp : AllTrianglesMA (unitTP A B C D E) := by
    apply deletion_triangle_transfer _ 3 (unit_tp_deletion A B C D E h)
    rw [unit_tp_three A B C D E h]
    exact hwp
  have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 := by omega
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hr
  · exact hw
  · exact ht
  · exact htp
  · exact hwp
  · exact triangles_relabel _ _ hr
  · exact triangles_relabel _ _ hw
  · exact triangles_relabel _ _ ht
  · exact triangles_relabel _ _ htp
  · exact triangles_relabel _ _ hwp


theorem cellRelabel_transfer (c : Cell) (p : Relabeling 4) (h : CellTransfer c) :
    CellTransfer (cellRelabel c p) := by
  intro hp i
  change AllTrianglesMA (mutate (relabel (c.state c.rootIndex) p) (p.invFun c.returnVertex)) at hp
  rw [mutate_relabel,p.right_inv] at hp
  have hparent := (triangles_relabel_iff _ p).mp hp
  exact triangles_relabel _ p (h hparent i)

theorem cellReverse_transfer (c : Cell) (h : CellTransfer c) :
    CellTransfer (cellReverse c) := by
  intro hp i
  change AllTrianglesMA (mutate (reverse (c.state c.rootIndex)) c.returnVertex) at hp
  rw [mutate_reverse] at hp
  have hs := mutation_preserves_skew _ c.returnVertex (c.skew c.rootIndex)
  have hparent := (triangles_reverse_iff _ hs).mp hp
  exact triangles_reverse _ (c.skew i) (h hparent i)

/-- The cell chooser carries the additional parent-to-triangle proof. -/
theorem root_triangle_cells (Q : Matrix 4) (r : Fin 4) (h : IsRoot Q r) :
    ∃ c : Cell, c.state c.rootIndex=Q ∧ c.returnVertex=r ∧ CellTransfer c := by
  induction h with
  | basic A B C D E ε h hε =>
    rcases hε with rfl | rfl
    · exact ⟨diamondCell A B C D E h,rfl,rfl,diamond_transfer A B C D E h⟩
    · exact ⟨unitCell A B C D E h,rfl,rfl,unit_transfer A B C D E h⟩
  | @relabelled Q r h p ih =>
    obtain ⟨c,heq,hret,ht⟩ := ih
    refine ⟨cellRelabel c p,?_,?_,cellRelabel_transfer c p ht⟩
    · change relabel (c.state c.rootIndex) p = relabel Q p
      rw [heq]
    · change p.invFun c.returnVertex = p.invFun r
      rw [hret]
  | @reversed Q r h ih =>
    obtain ⟨c,heq,hret,ht⟩ := ih
    refine ⟨cellReverse c,?_,hret,cellReverse_transfer c ht⟩
    change reverse (c.state c.rootIndex) = reverse Q
    rw [heq]

/-- Finite addressed regions in which each attached cell carries its
proved triangle transfer. This distinguishes the enriched theorem from
unrestricted abstract Cell packages used only for NMA soundness. -/
inductive TriangleSafe (core : Matrix 4 → Prop) : Matrix 4 → Prop
  | central {Q : Matrix 4} : core Q → TriangleSafe core Q
  | fork {Q : Matrix 4} (r : Fin 4) : TriangleSafe core Q → IsFork (mutate Q r) r →
      TriangleSafe core (mutate Q r)
  | cell (c : Cell) : CellTransfer c →
      TriangleSafe core (mutate (c.state c.rootIndex) c.returnVertex) →
      (i : Fin c.size) → TriangleSafe core (c.state i)
  | framed {Q : Matrix 4} : TriangleSafe core Q → (p : Relabeling 4) →
      TriangleSafe core (relabel Q p)
  | reversed {Q : Matrix 4} : TriangleSafe core Q → TriangleSafe core (reverse Q)

theorem triangleSafe_skew (core : Matrix 4 → Prop) (hs : ∀ Q, core Q → SkewSymmetric Q)
    {Q : Matrix 4} (h : TriangleSafe core Q) : SkewSymmetric Q := by
  induction h with
  | central h => exact hs _ h
  | fork _ _ hf _ => exact fork_skew hf
  | cell c _ _ i _ => exact c.skew i
  | framed _ p ih => exact relabel_skew _ p ih
  | reversed _ ih => exact reverse_skew _ ih

theorem triangleSafe_triangles (core : Matrix 4 → Prop)
    (hs : ∀ Q, core Q → SkewSymmetric Q) (ht : ∀ Q, core Q → AllTrianglesMA Q)
    {Q : Matrix 4} (h : TriangleSafe core Q) : AllTrianglesMA Q := by
  induction h with
  | central h => exact ht _ h
  | fork r _ hf ih =>
    apply fork_triangle_transfer hf
    simpa only [mutation_involutive] using ih
  | cell c hc _ i ih => exact hc ih i
  | framed _ p ih => exact triangles_relabel _ p ih
  | reversed h ih => exact triangles_reverse _ (triangleSafe_skew core hs h) ih

theorem triangleSafe_attach_root (core : Matrix 4 → Prop) {Q : Matrix 4}
    (h : TriangleSafe core Q) (r : Fin 4) (hr : IsRoot (mutate Q r) r) :
    TriangleSafe core (mutate Q r) := by
  obtain ⟨c,heq,hret,ht⟩ := root_triangle_cells _ r hr
  have hp : TriangleSafe core (mutate (c.state c.rootIndex) c.returnVertex) := by
    rw [heq,hret,mutation_involutive]
    exact h
  simpa only [heq] using TriangleSafe.cell c ht hp c.rootIndex

theorem triangleSafe_closed (core : Matrix 4 → Prop)
    (he : ∀ Q, core Q → ∀ k, core (mutate Q k) ∨
      IsFork (mutate Q k) k ∨ IsRoot (mutate Q k) k)
    {Q : Matrix 4} (h : TriangleSafe core Q) (k : Fin 4) :
    TriangleSafe core (mutate Q k) := by
  induction h generalizing k with
  | central h =>
    rcases he _ h k with hc | hf | hr
    · exact TriangleSafe.central hc
    · exact TriangleSafe.fork k (TriangleSafe.central h) hf
    · exact triangleSafe_attach_root core (TriangleSafe.central h) k hr
  | @fork Q r h hf ih =>
    by_cases hk : k=r
    · subst k; simpa only [mutation_involutive] using h
    · exact TriangleSafe.fork k (TriangleSafe.fork r h hf) (fork_continuation hf k hk)
  | cell c ht h i ih =>
    rcases c.edges i k with ⟨j,hj⟩ | ⟨p,hp⟩ | hf | hr
    · rw [hj]; exact TriangleSafe.cell c ht h j
    · rw [hp]; exact TriangleSafe.framed h p
    · exact TriangleSafe.fork k (TriangleSafe.cell c ht h i) hf
    · exact triangleSafe_attach_root core (TriangleSafe.cell c ht h i) k hr
  | @framed Q h p ih =>
    rw [mutate_relabel]
    exact TriangleSafe.framed (ih (p.toFun k)) p
  | reversed h ih =>
    rw [mutate_reverse]
    exact TriangleSafe.reversed (ih k)

/-- Global triangle avoidance: every induced triangle at every finite mutation
word is mutation-acyclic whenever the checked finite core has that property. -/
theorem region_all_triangles_MA (core : Matrix 4 → Prop)
    (hs : ∀ Q, core Q → SkewSymmetric Q) (ht : ∀ Q, core Q → AllTrianglesMA Q)
    (he : ∀ Q, core Q → ∀ k, core (mutate Q k) ∨
      IsFork (mutate Q k) k ∨ IsRoot (mutate Q k) k)
    (Q : Matrix 4) (hQ : core Q) (word : List (Fin 4)) :
    AllTrianglesMA (applyWord Q word) := by
  have allWords : ∀ w, ∀ B, TriangleSafe core B → TriangleSafe core (applyWord B w) := by
    intro w
    induction w with
    | nil => intro B h; exact h
    | cons k ks ih => intro B h; exact ih _ (triangleSafe_closed core he h k)
  exact triangleSafe_triangles core hs ht (allWords word Q (TriangleSafe.central hQ))

/-- The same theorem for a finite core with all relabelings included. -/
theorem framed_region_all_triangles_MA {m : Nat} (node : Fin m → Matrix 4)
    (hs : ∀ i, SkewSymmetric (node i)) (ht : ∀ i, AllTrianglesMA (node i))
    (he : ∀ i k, FramedCore node (mutate (node i) k) ∨
      IsFork (mutate (node i) k) k ∨ IsRoot (mutate (node i) k) k)
    (i : Fin m) (word : List (Fin 4)) : AllTrianglesMA (applyWord (node i) word) := by
  apply region_all_triangles_MA (FramedCore node)
  · intro Q h; obtain ⟨j,p,rfl⟩ := h; exact relabel_skew _ p (hs j)
  · intro Q h; obtain ⟨j,p,rfl⟩ := h; exact triangles_relabel _ p (ht j)
  · intro Q h k
    obtain ⟨j,p,rfl⟩ := h
    rw [mutate_relabel]
    rcases he j (p.toFun k) with hc | hf | hr
    · exact Or.inl (framed_relabel node hc p)
    · exact Or.inr (Or.inl (by simpa only [p.left_inv] using IsFork.relabelled hf p))
    · exact Or.inr (Or.inr (by simpa only [p.left_inv] using IsRoot.relabelled hr p))
  · exact ⟨i,.identity 4,rfl⟩


/-- Increasing enumeration of the three vertices other than r. -/
def deleteVertex (r : Fin 4) (i : Fin 3) : Fin 4 :=
  match r.val,i.val with
  | 0,0 => 1 | 0,1 => 2 | 0,_ => 3
  | 1,0 => 0 | 1,1 => 2 | 1,_ => 3
  | 2,0 => 0 | 2,1 => 1 | 2,_ => 3
  | _,0 => 0 | _,1 => 1 | _,_ => 2

theorem deleteVertex_injective (r : Fin 4) : Function.Injective (deleteVertex r) := by
  intro i j heq
  have hi : i=0 ∨ i=1 ∨ i=2 := by omega
  have hj : j=0 ∨ j=1 ∨ j=2 := by omega
  rcases fin4 r with rfl | rfl | rfl | rfl <;>
    rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;>
    simp_all [deleteVertex]

private def perm012 : Relabeling 3 :=
  ⟨fun i => match i.val with | 0 => 0 | 1 => 1 | _ => 2, fun i => match i.val with | 0 => 0 | 1 => 1 | _ => 2, by decide, by decide⟩

private def perm021 : Relabeling 3 :=
  ⟨fun i => match i.val with | 0 => 0 | 1 => 2 | _ => 1, fun i => match i.val with | 0 => 0 | 1 => 2 | _ => 1, by decide, by decide⟩

private def perm102 : Relabeling 3 :=
  ⟨fun i => match i.val with | 0 => 1 | 1 => 0 | _ => 2, fun i => match i.val with | 0 => 1 | 1 => 0 | _ => 2, by decide, by decide⟩

private def perm120 : Relabeling 3 :=
  ⟨fun i => match i.val with | 0 => 1 | 1 => 2 | _ => 0, fun i => match i.val with | 0 => 2 | 1 => 0 | _ => 1, by decide, by decide⟩

private def perm201 : Relabeling 3 :=
  ⟨fun i => match i.val with | 0 => 2 | 1 => 0 | _ => 1, fun i => match i.val with | 0 => 1 | 1 => 2 | _ => 0, by decide, by decide⟩

private def perm210 : Relabeling 3 :=
  ⟨fun i => match i.val with | 0 => 2 | 1 => 1 | _ => 0, fun i => match i.val with | 0 => 2 | 1 => 1 | _ => 0, by decide, by decide⟩

private theorem embedding_deletion_frame (e : Fin 3 → Fin 4) (he : Function.Injective e) :
    ∃ r : Fin 4, ∃ p : Relabeling 3, ∀ i, e i=deleteVertex r (p.toFun i) := by
  rcases fin4 (e 0) with h0 | h0 | h0 | h0 <;>
    rcases fin4 (e 1) with h1 | h1 | h1 | h1 <;>
    rcases fin4 (e 2) with h2 | h2 | h2 | h2
  · have hh : e 0=e 1 := by omega
    have := he hh
    omega
  · have hh : e 0=e 1 := by omega
    have := he hh
    omega
  · have hh : e 0=e 1 := by omega
    have := he hh
    omega
  · have hh : e 0=e 1 := by omega
    have := he hh
    omega
  · have hh : e 0=e 2 := by omega
    have := he hh
    omega
  · have hh : e 1=e 2 := by omega
    have := he hh
    omega
  · refine ⟨3,perm012,?_⟩
    intro i
    have hi : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases hi with rfl | rfl | rfl <;> simp [deleteVertex,perm012,h0,h1,h2]
  · refine ⟨2,perm012,?_⟩
    intro i
    have hi : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases hi with rfl | rfl | rfl <;> simp [deleteVertex,perm012,h0,h1,h2]
  · have hh : e 0=e 2 := by omega
    have := he hh
    omega
  · refine ⟨3,perm021,?_⟩
    intro i
    have hi : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases hi with rfl | rfl | rfl <;> simp [deleteVertex,perm021,h0,h1,h2]
  · have hh : e 1=e 2 := by omega
    have := he hh
    omega
  · refine ⟨1,perm012,?_⟩
    intro i
    have hi : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases hi with rfl | rfl | rfl <;> simp [deleteVertex,perm012,h0,h1,h2]
  · have hh : e 0=e 2 := by omega
    have := he hh
    omega
  · refine ⟨2,perm021,?_⟩
    intro i
    have hi : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases hi with rfl | rfl | rfl <;> simp [deleteVertex,perm021,h0,h1,h2]
  · refine ⟨1,perm021,?_⟩
    intro i
    have hi : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases hi with rfl | rfl | rfl <;> simp [deleteVertex,perm021,h0,h1,h2]
  · have hh : e 1=e 2 := by omega
    have := he hh
    omega
  · have hh : e 1=e 2 := by omega
    have := he hh
    omega
  · have hh : e 0=e 2 := by omega
    have := he hh
    omega
  · refine ⟨3,perm102,?_⟩
    intro i
    have hi : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases hi with rfl | rfl | rfl <;> simp [deleteVertex,perm102,h0,h1,h2]
  · refine ⟨2,perm102,?_⟩
    intro i
    have hi : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases hi with rfl | rfl | rfl <;> simp [deleteVertex,perm102,h0,h1,h2]
  · have hh : e 0=e 1 := by omega
    have := he hh
    omega
  · have hh : e 0=e 1 := by omega
    have := he hh
    omega
  · have hh : e 0=e 1 := by omega
    have := he hh
    omega
  · have hh : e 0=e 1 := by omega
    have := he hh
    omega
  · refine ⟨3,perm120,?_⟩
    intro i
    have hi : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases hi with rfl | rfl | rfl <;> simp [deleteVertex,perm120,h0,h1,h2]
  · have hh : e 0=e 2 := by omega
    have := he hh
    omega
  · have hh : e 1=e 2 := by omega
    have := he hh
    omega
  · refine ⟨0,perm012,?_⟩
    intro i
    have hi : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases hi with rfl | rfl | rfl <;> simp [deleteVertex,perm012,h0,h1,h2]
  · refine ⟨2,perm120,?_⟩
    intro i
    have hi : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases hi with rfl | rfl | rfl <;> simp [deleteVertex,perm120,h0,h1,h2]
  · have hh : e 0=e 2 := by omega
    have := he hh
    omega
  · refine ⟨0,perm021,?_⟩
    intro i
    have hi : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases hi with rfl | rfl | rfl <;> simp [deleteVertex,perm021,h0,h1,h2]
  · have hh : e 1=e 2 := by omega
    have := he hh
    omega
  · have hh : e 1=e 2 := by omega
    have := he hh
    omega
  · refine ⟨3,perm201,?_⟩
    intro i
    have hi : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases hi with rfl | rfl | rfl <;> simp [deleteVertex,perm201,h0,h1,h2]
  · have hh : e 0=e 2 := by omega
    have := he hh
    omega
  · refine ⟨1,perm102,?_⟩
    intro i
    have hi : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases hi with rfl | rfl | rfl <;> simp [deleteVertex,perm102,h0,h1,h2]
  · refine ⟨3,perm210,?_⟩
    intro i
    have hi : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases hi with rfl | rfl | rfl <;> simp [deleteVertex,perm210,h0,h1,h2]
  · have hh : e 1=e 2 := by omega
    have := he hh
    omega
  · have hh : e 0=e 2 := by omega
    have := he hh
    omega
  · refine ⟨0,perm102,?_⟩
    intro i
    have hi : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases hi with rfl | rfl | rfl <;> simp [deleteVertex,perm102,h0,h1,h2]
  · have hh : e 0=e 1 := by omega
    have := he hh
    omega
  · have hh : e 0=e 1 := by omega
    have := he hh
    omega
  · have hh : e 0=e 1 := by omega
    have := he hh
    omega
  · have hh : e 0=e 1 := by omega
    have := he hh
    omega
  · refine ⟨1,perm120,?_⟩
    intro i
    have hi : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases hi with rfl | rfl | rfl <;> simp [deleteVertex,perm120,h0,h1,h2]
  · refine ⟨0,perm120,?_⟩
    intro i
    have hi : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases hi with rfl | rfl | rfl <;> simp [deleteVertex,perm120,h0,h1,h2]
  · have hh : e 0=e 2 := by omega
    have := he hh
    omega
  · have hh : e 1=e 2 := by omega
    have := he hh
    omega
  · have hh : e 1=e 2 := by omega
    have := he hh
    omega
  · refine ⟨2,perm201,?_⟩
    intro i
    have hi : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases hi with rfl | rfl | rfl <;> simp [deleteVertex,perm201,h0,h1,h2]
  · refine ⟨1,perm201,?_⟩
    intro i
    have hi : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases hi with rfl | rfl | rfl <;> simp [deleteVertex,perm201,h0,h1,h2]
  · have hh : e 0=e 2 := by omega
    have := he hh
    omega
  · refine ⟨2,perm210,?_⟩
    intro i
    have hi : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases hi with rfl | rfl | rfl <;> simp [deleteVertex,perm210,h0,h1,h2]
  · have hh : e 1=e 2 := by omega
    have := he hh
    omega
  · refine ⟨0,perm201,?_⟩
    intro i
    have hi : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases hi with rfl | rfl | rfl <;> simp [deleteVertex,perm201,h0,h1,h2]
  · have hh : e 0=e 2 := by omega
    have := he hh
    omega
  · refine ⟨1,perm210,?_⟩
    intro i
    have hi : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases hi with rfl | rfl | rfl <;> simp [deleteVertex,perm210,h0,h1,h2]
  · refine ⟨0,perm210,?_⟩
    intro i
    have hi : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases hi with rfl | rfl | rfl <;> simp [deleteVertex,perm210,h0,h1,h2]
  · have hh : e 1=e 2 := by omega
    have := he hh
    omega
  · have hh : e 0=e 2 := by omega
    have := he hh
    omega
  · have hh : e 0=e 1 := by omega
    have := he hh
    omega
  · have hh : e 0=e 1 := by omega
    have := he hh
    omega
  · have hh : e 0=e 1 := by omega
    have := he hh
    omega
  · have hh : e 0=e 1 := by omega
    have := he hh
    omega

/-- Four sorted deletion checks cover every induced triangle and vertex order. -/
theorem allTrianglesMA_of_deletions (Q : Matrix 4)
    (h : ∀ r, MutationAcyclic (restrict Q (deleteVertex r))) : AllTrianglesMA Q := by
  intro e he
  obtain ⟨r,p,hp⟩ := embedding_deletion_frame e he
  have heq : restrict Q e = relabel (restrict Q (deleteVertex r)) p := by
    funext i j
    simp only [restrict,relabel,hp]
  rw [heq]
  exact (MA_relabel_iff _ p).mpr (h r)

theorem allTrianglesMA_iff_deletions (Q : Matrix 4) :
    AllTrianglesMA Q ↔ ∀ r, MutationAcyclic (restrict Q (deleteVertex r)) :=
  ⟨fun h r => h _ (deleteVertex_injective r),allTrianglesMA_of_deletions Q⟩

/-- A convenient six-coordinate interface for the four semantic triangle checks. -/
theorem ofSix_allTrianglesMA (a b c d e f : Int)
    (h0 : MutationAcyclic (cycleThree d f (-e)))
    (h1 : MutationAcyclic (cycleThree b f (-c)))
    (h2 : MutationAcyclic (cycleThree a e (-c)))
    (h3 : MutationAcyclic (cycleThree a d (-b))) :
    AllTrianglesMA (ofSix a b c d e f) := by
  apply allTrianglesMA_of_deletions
  intro r
  have h₀ : restrict (ofSix a b c d e f) (deleteVertex 0) = cycleThree d f (-e) := by
    funext i j
    have hi : i=0 ∨ i=1 ∨ i=2 := by omega
    have hj : j=0 ∨ j=1 ∨ j=2 := by omega
    rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;>
      simp [restrict,deleteVertex,ofSix,cycleThree]
  have h₁ : restrict (ofSix a b c d e f) (deleteVertex 1) = cycleThree b f (-c) := by
    funext i j
    have hi : i=0 ∨ i=1 ∨ i=2 := by omega
    have hj : j=0 ∨ j=1 ∨ j=2 := by omega
    rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;>
      simp [restrict,deleteVertex,ofSix,cycleThree]
  have h₂ : restrict (ofSix a b c d e f) (deleteVertex 2) = cycleThree a e (-c) := by
    funext i j
    have hi : i=0 ∨ i=1 ∨ i=2 := by omega
    have hj : j=0 ∨ j=1 ∨ j=2 := by omega
    rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;>
      simp [restrict,deleteVertex,ofSix,cycleThree]
  have h₃ : restrict (ofSix a b c d e f) (deleteVertex 3) = cycleThree a d (-b) := by
    funext i j
    have hi : i=0 ∨ i=1 ∨ i=2 := by omega
    have hj : j=0 ∨ j=1 ∨ j=2 := by omega
    rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;>
      simp [restrict,deleteVertex,ofSix,cycleThree]
  rcases fin4 r with rfl | rfl | rfl | rfl
  · rw [h₀]; exact h0
  · rw [h₁]; exact h1
  · rw [h₂]; exact h2
  · rw [h₃]; exact h3

end QuiverProofs.TriangleRegions
