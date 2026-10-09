import QuiverProofs.PendantTransitions

/-! Finite-address semantics for the pendant extension. The constructors keep
both parent orientations, inherited L0 cells, and every label/reversal frame.
The theorems here concern mathematical transition records, not Python parsing. -/
namespace QuiverProofs.PendantLanguage
open Forks Regions RegionSemantics RegionCells TriangleRegions PendantSquare PendantNormalization

inductive Safe (core : Matrix 4 → Prop) : Matrix 4 → Prop
  | central {Q : Matrix 4} : core Q → Safe core Q
  | fork {Q : Matrix 4} (r : Fin 4) : Safe core Q → IsFork (mutate Q r) r →
      Safe core (mutate Q r)
  | cell (c : Cell) : CellTransfer c →
      Safe core (mutate (c.state c.rootIndex) c.returnVertex) →
      (i : Fin c.size) → Safe core (c.state i)
  | pendant (c d x y : Int) : Domain c d x y →
      (∀ ε, Sign ε → Safe core (mutate (state c d x y ε) 1)) →
      ∀ ε, Sign ε → Safe core (state c d x y ε)
  | framed {Q : Matrix 4} : Safe core Q → (p : Relabeling 4) → Safe core (relabel Q p)
  | reversed {Q : Matrix 4} : Safe core Q → Safe core (reverse Q)

theorem safe_skew (core : Matrix 4 → Prop) (hs : ∀ Q, core Q → SkewSymmetric Q)
    {Q : Matrix 4} (h : Safe core Q) : SkewSymmetric Q := by
  induction h with
  | central h => exact hs _ h
  | fork _ _ hf _ => exact fork_skew hf
  | cell c _ _ i _ => exact c.skew i
  | pendant c d x y _ _ ε _ _ => exact ofSix_skew _ _ _ _ _ _
  | framed _ p ih => exact relabel_skew _ p ih
  | reversed _ ih => exact reverse_skew _ ih

theorem safe_cyclic (core : Matrix 4 → Prop)
    (hs : ∀ Q, core Q → SkewSymmetric Q) (hc : ∀ Q, core Q → ¬ Acyclic Q)
    {Q : Matrix 4} (h : Safe core Q) : ¬ Acyclic Q := by
  induction h with
  | central h => exact hc _ h
  | fork _ _ hf _ => exact fork_cyclic hf
  | cell c _ _ i _ => exact c.cyclic i
  | pendant c d x y hd _ ε _ _ => exact cyclic c d x y ε hd
  | framed _ p ih => exact fun ha => ih ((acyclic_relabel_iff _ p).mp ha)
  | reversed h ih => exact fun ha => ih ((acyclic_reverse_iff _ (safe_skew core hs h)).mp ha)

/-- Triangle soundness uses its own parent-to-triangle induction. -/
theorem safe_triangles (core : Matrix 4 → Prop)
    (hs : ∀ Q, core Q → SkewSymmetric Q) (ht : ∀ Q, core Q → AllTrianglesMA Q)
    {Q : Matrix 4} (h : Safe core Q) : AllTrianglesMA Q := by
  induction h with
  | central h => exact ht _ h
  | fork r _ hf ih =>
    apply fork_triangle_transfer hf
    simpa only [mutation_involutive] using ih
  | cell c hc _ i ih => exact hc ih i
  | pendant c d x y hd _ ε hε ih => exact triangle_transfer c d x y ε hd hε (ih ε hε)
  | framed _ p ih => exact triangles_relabel _ p ih
  | reversed h ih => exact triangles_reverse _ (safe_skew core hs h) ih

theorem attach_root (core : Matrix 4 → Prop) {Q : Matrix 4}
    (h : Safe core Q) (r : Fin 4) (hr : IsRoot (mutate Q r) r) :
    Safe core (mutate Q r) := by
  obtain ⟨c,heq,hret,ht⟩ := root_triangle_cells _ r hr
  have hp : Safe core (mutate (c.state c.rootIndex) c.returnVertex) := by
    rw [heq,hret,mutation_involutive]
    exact h
  simpa only [heq] using Safe.cell c ht hp c.rootIndex

private theorem swap12_twice (Q : Matrix 4) : relabel (relabel Q swap12) swap12 = Q := by
  funext i j
  have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  have hj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
  rcases hi with rfl|rfl|rfl|rfl <;> rcases hj with rfl|rfl|rfl|rfl <;> rfl

/-- Inward mutation from the normalized child recovers the actual framed parent. -/
theorem child_parent (c d x y ε : Int) (h : Domain c d x y) :
    mutate (state c d y (d*y-x) ε) 1 = relabel (state c d x y ε) swap12 := by
  rw [←child_frame c d x y ε h,mutate_relabel]
  change relabel (mutate (mutate (state c d x y ε) 2) 2) swap12 = _
  rw [mutation_involutive]

/-- Both parent records are retained while moving outward into a child square. -/
theorem pendant_child (core : Matrix 4 → Prop) (c d x y : Int)
    (hd : Domain c d x y)
    (hp : ∀ ε, Sign ε → Safe core (mutate (state c d x y ε) 1))
    (ε : Int) (hε : Sign ε) : Safe core (mutate (state c d x y ε) 2) := by
  have hc : Safe core (state c d y (d*y-x) ε) := by
    apply Safe.pendant c d y (d*y-x) (child_domain c d x y hd) _ ε hε
    intro η hη
    rw [child_parent c d x y η hd]
    exact Safe.framed (Safe.pendant c d x y hd hp η hη) swap12
  have hf := Safe.framed hc swap12
  rw [←child_frame c d x y ε hd,swap12_twice] at hf
  exact hf

/-- Closure once each finite-core edge has a checked finite address. -/
theorem safe_closed (core : Matrix 4 → Prop)
    (he : ∀ Q, core Q → ∀ k, Safe core (mutate Q k))
    {Q : Matrix 4} (h : Safe core Q) (k : Fin 4) : Safe core (mutate Q k) := by
  induction h generalizing k with
  | central h => exact he _ h k
  | @fork Q r h hf ih =>
    by_cases hk : k=r
    · subst k; simpa only [mutation_involutive] using h
    · exact Safe.fork k (Safe.fork r h hf) (fork_continuation hf k hk)
  | cell c ht h i ih =>
    rcases c.edges i k with ⟨j,hj⟩ | ⟨p,hp⟩ | hf | hr
    · rw [hj]; exact Safe.cell c ht h j
    · rw [hp]; exact Safe.framed h p
    · exact Safe.fork k (Safe.cell c ht h i) hf
    · exact attach_root core (Safe.cell c ht h i) k hr
  | pendant c d x y hd hp ε hε ih =>
    have hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases hk with rfl|rfl|rfl|rfl
    · rw [leaf]
      apply Safe.pendant c d x y hd hp
      rcases hε with rfl|rfl <;> unfold Sign <;> omega
    · exact hp ε hε
    · exact pendant_child core c d x y hd hp ε hε
    · exact attach_root core (Safe.pendant c d x y hd hp ε hε) 3
        (junction_isRoot c d x y ε hd hε)
  | @framed Q h p ih =>
    rw [mutate_relabel]
    exact Safe.framed (ih (p.toFun k)) p
  | reversed h ih =>
    rw [mutate_reverse]
    exact Safe.reversed (ih k)

theorem safe_word (core : Matrix 4 → Prop)
    (he : ∀ Q, core Q → ∀ k, Safe core (mutate Q k))
    (word : List (Fin 4)) {Q : Matrix 4} (h : Safe core Q) :
    Safe core (applyWord Q word) := by
  induction word generalizing Q with
  | nil => exact h
  | cons k ks ih => exact ih (safe_closed core he h k)

/-- All-word NMA soundness for the pendant region semantics. -/
theorem pendant_region_NMA (core : Matrix 4 → Prop)
    (hs : ∀ Q, core Q → SkewSymmetric Q) (hc : ∀ Q, core Q → ¬ Acyclic Q)
    (he : ∀ Q, core Q → ∀ k, Safe core (mutate Q k))
    (Q : Matrix 4) (hQ : core Q) : ¬ MutationAcyclic Q := by
  rintro ⟨word,ha⟩
  exact safe_cyclic core hs hc (safe_word core he word (Safe.central hQ)) ha

/-- Global triangle avoidance, separately from cyclicity of the full quiver. -/
theorem pendant_region_global_triangle_avoidance (core : Matrix 4 → Prop)
    (hs : ∀ Q, core Q → SkewSymmetric Q) (ht : ∀ Q, core Q → AllTrianglesMA Q)
    (he : ∀ Q, core Q → ∀ k, Safe core (mutate Q k))
    (Q : Matrix 4) (hQ : core Q) (word : List (Fin 4)) :
    AllTrianglesMA (applyWord Q word) :=
  safe_triangles core hs ht (safe_word core he word (Safe.central hQ))

/-- The unchanged L0 alternatives, or an explicitly framed pendant record
with both parent representatives and the actual entering return. -/
inductive Edge (core : Matrix 4 → Prop) (Q : Matrix 4) (k : Fin 4) : Prop
  | internal : core (mutate Q k) → Edge core Q k
  | fork : IsFork (mutate Q k) k → Edge core Q k
  | root : IsRoot (mutate Q k) k → Edge core Q k
  | pendant (c d x y ε : Int) (p : Relabeling 4) : Domain c d x y → Sign ε →
      p.invFun 1 = k → mutate Q k = relabel (state c d x y ε) p →
      (∀ η, Sign η → core (relabel (mutate (state c d x y η) 1) p)) → Edge core Q k
  | reversePendant (c d x y ε : Int) (p : Relabeling 4) : Domain c d x y → Sign ε →
      p.invFun 1 = k → mutate Q k = reverse (relabel (state c d x y ε) p) →
      (∀ η, Sign η → core (reverse (relabel (mutate (state c d x y η) 1) p))) →
      Edge core Q k

theorem edge_safe (core : Matrix 4 → Prop) {Q : Matrix 4} (hQ : core Q)
    {k : Fin 4} (h : Edge core Q k) : Safe core (mutate Q k) := by
  cases h with
  | internal h => exact Safe.central h
  | fork h => exact Safe.fork k (Safe.central hQ) h
  | root h => exact attach_root core (Safe.central hQ) k h
  | pendant c d x y ε p hd hε _ heq hp =>
    rw [heq]
    apply Safe.framed _ p
    apply Safe.pendant c d x y hd _ ε hε
    intro η hη
    have hh := Safe.framed (Safe.central (hp η hη)) p.symm
    simpa only [relabel_inverse] using hh
  | reversePendant c d x y ε p hd hε _ heq hp =>
    rw [heq]
    apply Safe.reversed
    apply Safe.framed _ p
    apply Safe.pendant c d x y hd _ ε hε
    intro η hη
    have hh := Safe.framed (Safe.reversed (Safe.central (hp η hη))) p.symm
    simpa only [reverse_involutive,relabel_inverse] using hh

/-- A finite mathematical pendant certificate: each of the four labeled
core mutations is represented by one exact transition record. -/
structure Certificate where
  size : Nat
  rootIndex : Fin size
  node : Fin size → Matrix 4
  skew : ∀ i, SkewSymmetric (node i)
  cyclic : ∀ i, ¬ Acyclic (node i)
  edges : ∀ i k, Edge (FramedCore node) (node i) k

private theorem certificate_core_skew (c : Certificate) :
    ∀ Q, FramedCore c.node Q → SkewSymmetric Q := by
  intro Q h
  obtain ⟨i,p,rfl⟩ := h
  exact relabel_skew _ p (c.skew i)

private theorem certificate_core_cyclic (c : Certificate) :
    ∀ Q, FramedCore c.node Q → ¬ Acyclic Q := by
  intro Q h
  obtain ⟨i,p,rfl⟩ := h
  exact fun ha => c.cyclic i ((acyclic_relabel_iff _ p).mp ha)

private theorem certificate_core_edges (c : Certificate) :
    ∀ Q, FramedCore c.node Q → ∀ k, Safe (FramedCore c.node) (mutate Q k) := by
  intro Q h k
  obtain ⟨i,p,rfl⟩ := h
  rw [mutate_relabel]
  exact Safe.framed (edge_safe (FramedCore c.node)
    ⟨i,.identity 4,rfl⟩ (c.edges i (p.toFun k))) p

/-- Soundness for every finite mathematical certificate, with no mutation-word cutoff. -/
theorem certificate_NMA (c : Certificate) (i : Fin c.size) :
    ¬ MutationAcyclic (c.node i) :=
  pendant_region_NMA (FramedCore c.node) (certificate_core_skew c)
    (certificate_core_cyclic c) (certificate_core_edges c) (c.node i) ⟨i,.identity 4,rfl⟩

/-- Every triangle of every descendant is MA when the finite core triangles are MA. -/
theorem certificate_global_triangle_avoidance (c : Certificate)
    (ht : ∀ i, AllTrianglesMA (c.node i)) (i : Fin c.size) (word : List (Fin 4)) :
    AllTrianglesMA (applyWord (c.node i) word) := by
  apply pendant_region_global_triangle_avoidance (FramedCore c.node)
    (certificate_core_skew c) _ (certificate_core_edges c) _ ⟨i,.identity 4,rfl⟩ word
  intro Q h
  obtain ⟨j,p,rfl⟩ := h
  exact triangles_relabel _ p (ht j)

private theorem square_safe (core : Matrix 4 → Prop) (c d x y ε : Int)
    (hd : Domain c d x y) (hε : Sign ε)
    (hp : Safe core (mutate (state c d x y ε) 1))
    (hflip : Safe core (mutate (mutate (state c d x y ε) 1) 0)) :
    Safe core (state c d x y ε) := by
  apply Safe.pendant c d x y hd _ ε hε
  intro η hη
  have he : η=ε ∨ η= -ε := by unfold Sign at *; omega
  rcases he with rfl|rfl
  · exact hp
  · rwa [parent_leaf_compatibility c d x y ε hd] at hflip

private theorem normalized_entry_safe (core : Matrix 4 → Prop) (N : Matrix 4)
    (c d x y ε : Int) (hd : Domain c d x y) (hε : Sign ε)
    (hform : N=state c d x y ε ∨ N=reverse (state c d x y ε))
    (hp : Safe core (mutate N 1)) (hflip : Safe core (mutate (mutate N 1) 0)) :
    Safe core N := by
  rcases hform with rfl|rfl
  · exact square_safe core c d x y ε hd hε hp hflip
  · apply Safe.reversed
    apply square_safe core c d x y ε hd hε
    · have hh := Safe.reversed hp
      simpa only [mutate_reverse,reverse_involutive] using hh
    · have hh := Safe.reversed hflip
      simpa only [mutate_reverse,reverse_involutive] using hh

/-- An original graph-theoretic pendant boundary is admitted from its two
actual parents. No normal-form completeness assumption is left to the caller. -/
theorem attach_graph_pendant (core : Matrix 4 → Prop) (Q : Matrix 4)
    (ell j k : Fin 4) (hp : Safe core Q) (hflip : Safe core (mutate Q ell))
    (hg : GraphPendant (mutate Q k) ell j k) : Safe core (mutate Q k) := by
  obtain ⟨p,c,d,x,y,ε,hp0,hp1,_,hd,hε,hform⟩ :=
    labeled_graph_normalization (mutate Q k) ell j k hg
  have hn : Safe core (relabel (mutate Q k) p) := by
    apply normalized_entry_safe core _ c d x y ε hd hε hform
    · rw [mutate_relabel,hp1,mutation_involutive]
      exact Safe.framed hp p
    · rw [mutate_relabel,hp1,mutation_involutive,mutate_relabel,hp0]
      exact Safe.framed hflip p
  have hh := Safe.framed hn p.symm
  simpa only [relabel_inverse] using hh

/-- The source language's four alternatives. The pendant rule requires the
other parent to belong to the same finite permutation-saturated core. -/
inductive GraphEdge (core : Matrix 4 → Prop) (Q : Matrix 4) (k : Fin 4) : Prop
  | internal : core (mutate Q k) → GraphEdge core Q k
  | fork : IsFork (mutate Q k) k → GraphEdge core Q k
  | root : IsRoot (mutate Q k) k → GraphEdge core Q k
  | pendant (ell j : Fin 4) : GraphPendant (mutate Q k) ell j k →
      core (mutate Q ell) → GraphEdge core Q k

theorem graph_edge_safe (core : Matrix 4 → Prop) {Q : Matrix 4} (hQ : core Q)
    {k : Fin 4} (h : GraphEdge core Q k) : Safe core (mutate Q k) := by
  cases h with
  | internal h => exact Safe.central h
  | fork h => exact Safe.fork k (Safe.central hQ) h
  | root h => exact attach_root core (Safe.central hQ) k h
  | pendant ell j hg hf =>
    exact attach_graph_pendant core Q ell j k (Safe.central hQ) (Safe.central hf) hg

/-- Exact finite mathematical `L_pend` certificates. In particular the other
parent is an explicit core representative with its new-to-old label frame. -/
structure GraphCertificate where
  size : Nat
  rootIndex : Fin size
  node : Fin size → Matrix 4
  skew : ∀ i, SkewSymmetric (node i)
  cyclic : ∀ i, ¬ Acyclic (node i)
  edges : ∀ i k, GraphEdge (FramedCore node) (node i) k

private theorem graph_certificate_core_edges (c : GraphCertificate) :
    ∀ Q, FramedCore c.node Q → ∀ k, Safe (FramedCore c.node) (mutate Q k) := by
  intro Q h k
  obtain ⟨i,p,rfl⟩ := h
  rw [mutate_relabel]
  exact Safe.framed (graph_edge_safe (FramedCore c.node)
    ⟨i,.identity 4,rfl⟩ (c.edges i (p.toFun k))) p

/-- Source theorem: every finite certificate in the original pendant language
proves semantic NMA, excluding every finite mutation word. -/
theorem L_pend_NMA (c : GraphCertificate) (i : Fin c.size) :
    ¬ MutationAcyclic (c.node i) := by
  apply pendant_region_NMA (FramedCore c.node) _ _
    (graph_certificate_core_edges c) (c.node i) ⟨i,.identity 4,rfl⟩
  · intro Q h
    obtain ⟨j,p,rfl⟩ := h
    exact relabel_skew _ p (c.skew j)
  · intro Q h
    obtain ⟨j,p,rfl⟩ := h
    exact fun ha => c.cyclic j ((acyclic_relabel_iff _ p).mp ha)

/-- Source theorem: the separate retained-triangle proof is global over all
mutation descendants and all injective triangle enumerations. -/
theorem L_pend_global_triangle_avoidance (c : GraphCertificate)
    (ht : ∀ i, AllTrianglesMA (c.node i)) (i : Fin c.size) (word : List (Fin 4)) :
    AllTrianglesMA (applyWord (c.node i) word) := by
  apply pendant_region_global_triangle_avoidance (FramedCore c.node) _ _
    (graph_certificate_core_edges c) _ ⟨i,.identity 4,rfl⟩ word
  · intro Q h
    obtain ⟨j,p,rfl⟩ := h
    exact relabel_skew _ p (c.skew j)
  · intro Q h
    obtain ⟨j,p,rfl⟩ := h
    exact triangles_relabel _ p (ht j)

/-- Every old L0 finite-core edge is retained verbatim; no old predicate is changed. -/
theorem L0_edge_embedding (core : Matrix 4 → Prop) (Q : Matrix 4) (k : Fin 4)
    (h : core (mutate Q k) ∨ IsFork (mutate Q k) k ∨ IsRoot (mutate Q k) k) :
    GraphEdge core Q k := by
  rcases h with hi|hf|hr
  · exact GraphEdge.internal hi
  · exact GraphEdge.fork hf
  · exact GraphEdge.root hr

private theorem word_reverse_cancel (Q : Matrix 4) (word : List (Fin 4)) :
    applyWord (applyWord Q word) word.reverse = Q := by
  induction word generalizing Q with
  | nil => rfl
  | cons k ks ih =>
    simp only [applyWord,List.reverse_cons,applyWord_append]
    rw [ih]
    exact mutation_involutive Q k

/-- An entry word and its checked label frame transfer NMA to the actual input. -/
theorem L_pend_entry_NMA (c : GraphCertificate) (i : Fin c.size)
    (Q : Matrix 4) (entry : List (Fin 4)) (p : Relabeling 4)
    (heq : applyWord Q entry = relabel (c.node i) p) : ¬ MutationAcyclic Q := by
  intro hQ
  have he := (mutationAcyclic_word_iff Q entry).mpr hQ
  rw [heq] at he
  exact L_pend_NMA c i ((MA_relabel_iff _ p).mp he)

/-- Entry transport preserves the full global quantifiers by reversing the
entry before the arbitrary tested mutation word. -/
theorem L_pend_entry_global_triangle_avoidance (c : GraphCertificate)
    (ht : ∀ i, AllTrianglesMA (c.node i)) (i : Fin c.size)
    (Q : Matrix 4) (entry : List (Fin 4)) (p : Relabeling 4)
    (heq : applyWord Q entry = relabel (c.node i) p) (word : List (Fin 4)) :
    AllTrianglesMA (applyWord Q word) := by
  have hback : Q = applyWord (relabel (c.node i) p) entry.reverse := by
    rw [←heq]
    exact (word_reverse_cancel Q entry).symm
  rw [hback,←applyWord_append,word_relabel]
  exact triangles_relabel _ p (L_pend_global_triangle_avoidance c ht i
    ((entry.reverse ++ word).map p.toFun))

end QuiverProofs.PendantLanguage
