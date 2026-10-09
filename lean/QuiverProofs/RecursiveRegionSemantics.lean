import QuiverProofs.Pendant
import QuiverProofs.TriangleRegions

namespace QuiverProofs.RecursiveRegions
open Forks Regions RegionSemantics TriangleRegions

universe u v

/-- A region presents all its states and every entrance parent explicitly. -/
structure RegionData (R : Type u) where
  Index : R → Type v
  parentCount : R → Nat
  state : (r : R) → Index r → Matrix 4
  parent : (r : R) → Fin (parentCount r) → Matrix 4
  skew : ∀ r i, SkewSymmetric (state r i)
  parent_skew : ∀ r p, SkewSymmetric (parent r p)
  cyclic : ∀ r i, ¬ Acyclic (state r i)

/-- Addresses use only displayed states, displayed parents and symmetries. -/
inductive LocalAddress {R : Type u} (D : RegionData.{u,v} R) (r : R)
    (allowed : D.Index r → Prop) : Matrix 4 → Prop
  | node (i : D.Index r) : allowed i → LocalAddress D r allowed (D.state r i)
  | parent (p : Fin (D.parentCount r)) : LocalAddress D r allowed (D.parent r p)
  | framed {B : Matrix 4} : LocalAddress D r allowed B → (p : Relabeling 4) →
      LocalAddress D r allowed (relabel B p)
  | reversed {B : Matrix 4} : LocalAddress D r allowed B →
      LocalAddress D r allowed (reverse B)

/-- A recursive attachment must wire every child parent to an actual local
address. In particular a two-parent N/D region cannot be entered with only one
parent supplied. -/
def LocalEdge {R : Type u} (D : RegionData.{u,v} R) (r : R)
    (B : Matrix 4) (k : Fin 4) : Prop :=
  LocalAddress D r (fun _ => True) B ∨
  IsFork B k ∨ IsRoot B k ∨
  ∃ child : R, LocalAddress D child (fun _ => True) B ∧
    ∀ p, LocalAddress D r (fun _ => True) (D.parent child p)

structure RegionRules {R : Type u} (D : RegionData.{u,v} R) : Prop where
  edges : ∀ r i k, LocalEdge D r (mutate (D.state r i) k) k

/-- The rank concerns a retained-triangle descent inside one region, not an
arbitrary mutation word or the depth of the recursively attached regions. -/
structure TriangleRules {R : Type u} (D : RegionData.{u,v} R) where
  rank : (r : R) → D.Index r → Nat
  descent : ∀ r i, AllTrianglesMA (D.state r i) ∨
    ∃ k, Pendant.DeletionMA (D.state r i) k ∧
      LocalAddress D r (fun j => rank r j < rank r i) (mutate (D.state r i) k)

end QuiverProofs.RecursiveRegions

namespace QuiverProofs.RecursiveRegions
open Forks Regions RegionSemantics TriangleRegions
universe u v
variable {R : Type u} (D : RegionData.{u,v} R)

theorem LocalAddress.skew {r : R} {allowed : D.Index r → Prop} {B : Matrix 4}
    (h : LocalAddress D r allowed B) : SkewSymmetric B := by
  induction h with
  | node i _ => exact D.skew r i
  | parent p => exact D.parent_skew r p
  | framed _ p ih => exact relabel_skew _ p ih
  | reversed _ ih => exact reverse_skew _ ih

theorem LocalAddress.triangles {r : R} {allowed : D.Index r → Prop} {B : Matrix 4}
    (h : LocalAddress D r allowed B)
    (hs : ∀ i, allowed i → AllTrianglesMA (D.state r i))
    (hp : ∀ p, AllTrianglesMA (D.parent r p)) : AllTrianglesMA B := by
  induction h with
  | node i hi => exact hs i hi
  | parent p => exact hp p
  | framed _ p ih => exact triangles_relabel _ p ih
  | reversed h ih => exact triangles_reverse _ (LocalAddress.skew D h) ih

theorem deletionMA_transfer (Q : Matrix 4) (r : Fin 4)
    (hdel : Pendant.DeletionMA Q r) (h : AllTrianglesMA (mutate Q r)) :
    AllTrianglesMA Q := by
  intro e he
  by_cases hh : ∃ k, e k = r
  · obtain ⟨k,hk⟩ := hh
    exact retained_triangle_transfer Q r h e he k hk
  · exact hdel e he (fun i hi => hh ⟨i,hi⟩)

/-- Local retained-triangle descent discharges a region from all its entrance
parents, using well-founded induction on the supplied natural-number rank. -/
theorem region_triangles (tri : TriangleRules D) (r : R)
    (hp : ∀ p, AllTrianglesMA (D.parent r p)) (i : D.Index r) :
    AllTrianglesMA (D.state r i) := by
  have step : ∀ n, ∀ i : D.Index r, tri.rank r i = n →
      AllTrianglesMA (D.state r i) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro i hi
      rcases tri.descent r i with ht | ⟨k,hd,ha⟩
      · exact ht
      · apply deletionMA_transfer _ k hd
        apply LocalAddress.triangles D ha _ hp
        intro j hj
        exact ih (tri.rank r j) (by simpa only [hi] using hj) j rfl
  exact step (tri.rank r i) i rfl

/-- Finite derivations of safety. Region attachment explicitly carries a safe
address for every entrance parent. Cell attachments carry their independently
proved triangle transfer, which is unused by the NMA theorem. -/
inductive Safe (core : Matrix 4 → Prop) : Matrix 4 → Prop
  | central {B : Matrix 4} : core B → Safe core B
  | fork {B : Matrix 4} (r : Fin 4) : Safe core B → IsFork (mutate B r) r →
      Safe core (mutate B r)
  | cell (c : Cell) : CellTransfer c →
      Safe core (mutate (c.state c.rootIndex) c.returnVertex) →
      (i : Fin c.size) → Safe core (c.state i)
  | region (r : R) : (∀ p, Safe core (D.parent r p)) →
      (i : D.Index r) → Safe core (D.state r i)
  | framed {B : Matrix 4} : Safe core B → (p : Relabeling 4) → Safe core (relabel B p)
  | reversed {B : Matrix 4} : Safe core B → Safe core (reverse B)

theorem safe_skew (core : Matrix 4 → Prop) (hc : ∀ B, core B → SkewSymmetric B)
    {B : Matrix 4} (h : Safe D core B) : SkewSymmetric B := by
  induction h with
  | central h => exact hc _ h
  | fork _ _ hf _ => exact fork_skew hf
  | cell c _ _ i _ => exact c.skew i
  | region r _ i _ => exact D.skew r i
  | framed _ p ih => exact relabel_skew _ p ih
  | reversed _ ih => exact reverse_skew _ ih

theorem safe_cyclic (core : Matrix 4 → Prop)
    (hs : ∀ B, core B → SkewSymmetric B) (hc : ∀ B, core B → ¬ Acyclic B)
    {B : Matrix 4} (h : Safe D core B) : ¬ Acyclic B := by
  induction h with
  | central h => exact hc _ h
  | fork _ _ hf _ => exact fork_cyclic hf
  | cell c _ _ i _ => exact c.cyclic i
  | region r _ i _ => exact D.cyclic r i
  | framed _ p ih => exact fun ha => ih ((acyclic_relabel_iff _ p).mp ha)
  | reversed h ih => exact fun ha => ih ((acyclic_reverse_iff _ (safe_skew D core hs h)).mp ha)

theorem safe_triangles (tri : TriangleRules D) (core : Matrix 4 → Prop)
    (hs : ∀ B, core B → SkewSymmetric B) (ht : ∀ B, core B → AllTrianglesMA B)
    {B : Matrix 4} (h : Safe D core B) : AllTrianglesMA B := by
  induction h with
  | central h => exact ht _ h
  | fork r _ hf ih =>
    apply fork_triangle_transfer hf
    simpa only [mutation_involutive] using ih
  | cell c hc _ i ih => exact hc ih i
  | region r _ i ih => exact region_triangles D tri r ih i
  | framed _ p ih => exact triangles_relabel _ p ih
  | reversed h ih => exact triangles_reverse _ (safe_skew D core hs h) ih

theorem attach_root (core : Matrix 4 → Prop) {B : Matrix 4}
    (h : Safe D core B) (r : Fin 4) (hr : IsRoot (mutate B r) r) :
    Safe D core (mutate B r) := by
  obtain ⟨c,heq,hret,ht⟩ := root_triangle_cells _ r hr
  have hp : Safe D core (mutate (c.state c.rootIndex) c.returnVertex) := by
    rw [heq,hret,mutation_involutive]
    exact h
  simpa only [heq] using Safe.cell c ht hp c.rootIndex

theorem LocalAddress.safe (core : Matrix 4 → Prop) {r : R}
    {allowed : D.Index r → Prop} {B : Matrix 4} (h : LocalAddress D r allowed B)
    (hs : ∀ i, allowed i → Safe D core (D.state r i))
    (hp : ∀ p, Safe D core (D.parent r p)) : Safe D core B := by
  induction h with
  | node i hi => exact hs i hi
  | parent p => exact hp p
  | framed _ p ih => exact Safe.framed ih p
  | reversed _ ih => exact Safe.reversed ih

theorem localEdge_safe (core : Matrix 4 → Prop) (r : R)
    (hp : ∀ p, Safe D core (D.parent r p)) (i : D.Index r) (k : Fin 4)
    (he : LocalEdge D r (mutate (D.state r i) k) k) :
    Safe D core (mutate (D.state r i) k) := by
  have hn : ∀ j, True → Safe D core (D.state r j) := fun j _ => Safe.region r hp j
  rcases he with ha | hf | hr | ⟨child,ha,hcp⟩
  · exact LocalAddress.safe D core ha hn hp
  · exact Safe.fork k (Safe.region r hp i) hf
  · exact attach_root D core (Safe.region r hp i) k hr
  · have hchild : ∀ p, Safe D core (D.parent child p) :=
      fun p => LocalAddress.safe D core (hcp p) hn hp
    exact LocalAddress.safe D core ha (fun j _ => Safe.region child hchild j) hchild

theorem safe_closed (rules : RegionRules D) (core : Matrix 4 → Prop)
    (he : ∀ B, core B → ∀ k, Safe D core (mutate B k))
    {B : Matrix 4} (h : Safe D core B) (k : Fin 4) : Safe D core (mutate B k) := by
  induction h generalizing k with
  | central h => exact he _ h k
  | @fork B r h hf ih =>
    by_cases hk : k = r
    · subst k; simpa only [mutation_involutive] using h
    · exact Safe.fork k (Safe.fork r h hf) (fork_continuation hf k hk)
  | cell c ht h i ih =>
    rcases c.edges i k with ⟨j,hj⟩ | ⟨p,hp⟩ | hf | hr
    · rw [hj]; exact Safe.cell c ht h j
    · rw [hp]; exact Safe.framed h p
    · exact Safe.fork k (Safe.cell c ht h i) hf
    · exact attach_root D core (Safe.cell c ht h i) k hr
  | region r hp i ih => exact localEdge_safe D core r hp i k (rules.edges r i k)
  | @framed B h p ih =>
    rw [mutate_relabel]
    exact Safe.framed (ih (p.toFun k)) p
  | reversed h ih =>
    rw [mutate_reverse]
    exact Safe.reversed (ih k)

theorem safe_all_words (rules : RegionRules D) (core : Matrix 4 → Prop)
    (he : ∀ B, core B → ∀ k, Safe D core (mutate B k))
    (word : List (Fin 4)) {B : Matrix 4} (h : Safe D core B) :
    Safe D core (applyWord B word) := by
  induction word generalizing B with
  | nil => exact h
  | cons k ks ih => exact ih (safe_closed D rules core he h k)

/-- Every finite mutation word stays inside the cyclic recursive grammar. -/
theorem safe_NMA (rules : RegionRules D) (core : Matrix 4 → Prop)
    (hs : ∀ B, core B → SkewSymmetric B) (hc : ∀ B, core B → ¬ Acyclic B)
    (he : ∀ B, core B → ∀ k, Safe D core (mutate B k))
    {B : Matrix 4} (h : Safe D core B) : ¬ MutationAcyclic B := by
  rintro ⟨word,ha⟩
  exact safe_cyclic D core hs hc (safe_all_words D rules core he word h) ha

/-- Triangle avoidance holds along all words once the separate local descent
rules and central triangle certificates have been checked. -/
theorem safe_global_triangle_avoidance (rules : RegionRules D) (tri : TriangleRules D)
    (core : Matrix 4 → Prop)
    (hs : ∀ B, core B → SkewSymmetric B) (ht : ∀ B, core B → AllTrianglesMA B)
    (he : ∀ B, core B → ∀ k, Safe D core (mutate B k))
    {B : Matrix 4} (h : Safe D core B) (word : List (Fin 4)) :
    AllTrianglesMA (applyWord B word) :=
  safe_triangles D tri core hs ht (safe_all_words D rules core he word h)

end QuiverProofs.RecursiveRegions

namespace QuiverProofs.RecursiveRegions
open Forks Regions TriangleRegions
universe u v w z

/-- An exact embedding of region presentations. Both directions on parents
are explicit so child attachment cannot lose an entrance obligation. -/
structure RegionEmbedding {R : Type u} {S : Type w}
    (D : RegionData.{u,v} R) (E : RegionData.{w,z} S) where
  map : R → S
  index : (r : R) → D.Index r → E.Index (map r)
  indexBack : (r : R) → E.Index (map r) → D.Index r
  index_left : ∀ r i, indexBack r (index r i) = i
  index_right : ∀ r j, index r (indexBack r j) = j
  parent : (r : R) → Fin (D.parentCount r) → Fin (E.parentCount (map r))
  parentBack : (r : R) → Fin (E.parentCount (map r)) → Fin (D.parentCount r)
  state_eq : ∀ r i, E.state (map r) (index r i) = D.state r i
  parent_eq : ∀ r p, E.parent (map r) (parent r p) = D.parent r p
  parentBack_eq : ∀ r p, D.parent r (parentBack r p) = E.parent (map r) p

variable {R : Type u} {S : Type w} {D : RegionData.{u,v} R} {E : RegionData.{w,z} S}

theorem RegionEmbedding.state_back (f : RegionEmbedding D E) (r : R)
    (j : E.Index (f.map r)) : E.state (f.map r) j = D.state r (f.indexBack r j) := by
  rw [←f.state_eq, f.index_right]

theorem LocalAddress.map (f : RegionEmbedding D E) {r : R}
    {allowed : D.Index r → Prop} {target : E.Index (f.map r) → Prop}
    {B : Matrix 4} (h : LocalAddress D r allowed B)
    (ha : ∀ i, allowed i → target (f.index r i)) : LocalAddress E (f.map r) target B := by
  induction h with
  | node i hi =>
    rw [←f.state_eq]
    exact LocalAddress.node _ (ha i hi)
  | parent p =>
    rw [←f.parent_eq]
    exact LocalAddress.parent _
  | framed _ p ih => exact LocalAddress.framed ih p
  | reversed _ ih => exact LocalAddress.reversed ih

theorem LocalEdge.map (f : RegionEmbedding D E) {r : R} {B : Matrix 4} {k : Fin 4}
    (h : LocalEdge D r B k) : LocalEdge E (f.map r) B k := by
  rcases h with ha | hf | hr | ⟨child,ha,hp⟩
  · exact Or.inl (LocalAddress.map f ha (fun _ _ => True.intro))
  · exact Or.inr (Or.inl hf)
  · exact Or.inr (Or.inr (Or.inl hr))
  · refine Or.inr (Or.inr (Or.inr ⟨f.map child,?_,?_⟩))
    · exact LocalAddress.map f ha (fun _ _ => True.intro)
    · intro p
      rw [←f.parentBack_eq]
      exact LocalAddress.map f (hp (f.parentBack child p)) (fun _ _ => True.intro)

/-- Safety derivations are portable between exact region presentations. -/
theorem Safe.map (f : RegionEmbedding D E) {core : Matrix 4 → Prop} {B : Matrix 4}
    (h : Safe D core B) : Safe E core B := by
  induction h with
  | central h => exact Safe.central h
  | fork r _ hf ih => exact Safe.fork r ih hf
  | cell c ht _ i ih => exact Safe.cell c ht ih i
  | region r _ i ih =>
    rw [←f.state_eq]
    apply Safe.region (f.map r)
    intro p
    rw [←f.parentBack_eq]
    exact ih (f.parentBack r p)
  | framed _ p ih => exact Safe.framed ih p
  | reversed _ ih => exact Safe.reversed ih

theorem RegionEmbedding.edges (f : RegionEmbedding D E) (rules : RegionRules D)
    (r : R) (j : E.Index (f.map r)) (k : Fin 4) :
    LocalEdge E (f.map r) (mutate (E.state (f.map r) j) k) k := by
  rw [f.state_back]
  exact LocalEdge.map f (rules.edges r (f.indexBack r j) k)

theorem RegionEmbedding.descent (f : RegionEmbedding D E) (tri : TriangleRules D)
    (targetRank : (s : S) → E.Index s → Nat)
    (hrank : ∀ r i, targetRank (f.map r) (f.index r i) = tri.rank r i)
    (r : R) (j : E.Index (f.map r)) :
    AllTrianglesMA (E.state (f.map r) j) ∨
    ∃ k, Pendant.DeletionMA (E.state (f.map r) j) k ∧
      LocalAddress E (f.map r) (fun i => targetRank (f.map r) i < targetRank (f.map r) j)
        (mutate (E.state (f.map r) j) k) := by
  have hj : targetRank (f.map r) j = tri.rank r (f.indexBack r j) := by
    rw [←hrank, f.index_right]
  rw [f.state_back]
  rcases tri.descent r (f.indexBack r j) with ht | ⟨k,hd,ha⟩
  · exact Or.inl ht
  · refine Or.inr ⟨k,hd,LocalAddress.map f ha ?_⟩
    intro i hi
    simpa only [hrank,hj] using hi

/-- Disjoint union of presentations; cross-family edges can be proved directly
against this data after the independent families have been embedded. -/
def RegionData.sum {R : Type u} {S : Type w}
    (D : RegionData.{u,v} R) (E : RegionData.{w,v} S) : RegionData (R ⊕ S) where
  Index := fun s => match s with | .inl r => D.Index r | .inr t => E.Index t
  parentCount := fun s => match s with | .inl r => D.parentCount r | .inr t => E.parentCount t
  state := fun s => match s with | .inl r => D.state r | .inr t => E.state t
  parent := fun s => match s with | .inl r => D.parent r | .inr t => E.parent t
  skew := fun s => match s with | .inl r => D.skew r | .inr t => E.skew t
  parent_skew := fun s => match s with | .inl r => D.parent_skew r | .inr t => E.parent_skew t
  cyclic := fun s => match s with | .inl r => D.cyclic r | .inr t => E.cyclic t

def RegionData.inl {R : Type u} {S : Type w}
    (D : RegionData.{u,v} R) (E : RegionData.{w,v} S) : RegionEmbedding D (D.sum E) where
  map := Sum.inl
  index := fun _ i => i
  indexBack := fun _ i => i
  index_left := fun _ _ => rfl
  index_right := fun _ _ => rfl
  parent := fun _ p => p
  parentBack := fun _ p => p
  state_eq := fun _ _ => rfl
  parent_eq := fun _ _ => rfl
  parentBack_eq := fun _ _ => rfl

def RegionData.inr {R : Type u} {S : Type w}
    (D : RegionData.{u,v} R) (E : RegionData.{w,v} S) : RegionEmbedding E (D.sum E) where
  map := Sum.inr
  index := fun _ i => i
  indexBack := fun _ i => i
  index_left := fun _ _ => rfl
  index_right := fun _ _ => rfl
  parent := fun _ p => p
  parentBack := fun _ p => p
  state_eq := fun _ _ => rfl
  parent_eq := fun _ _ => rfl
  parentBack_eq := fun _ _ => rfl

def RegionRules.sum {R : Type u} {S : Type w}
    {D : RegionData.{u,v} R} {E : RegionData.{w,v} S}
    (hD : RegionRules D) (hE : RegionRules E) : RegionRules (D.sum E) where
  edges := by
    intro r i k
    cases r with
    | inl r => exact (D.inl E).edges hD r i k
    | inr s => exact (D.inr E).edges hE s i k

def TriangleRules.sum {R : Type u} {S : Type w}
    {D : RegionData.{u,v} R} {E : RegionData.{w,v} S}
    (hD : TriangleRules D) (hE : TriangleRules E) : TriangleRules (D.sum E) where
  rank := fun r => match r with | .inl s => hD.rank s | .inr s => hE.rank s
  descent := by
    intro r i
    cases r with
    | inl r => exact (D.inl E).descent hD (fun r => match r with | .inl s => hD.rank s | .inr s => hE.rank s) (fun _ _ => rfl) r i
    | inr s => exact (D.inr E).descent hE (fun r => match r with | .inl s => hD.rank s | .inr s => hE.rank s) (fun _ _ => rfl) s i

end QuiverProofs.RecursiveRegions
