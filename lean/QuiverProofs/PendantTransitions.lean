import QuiverProofs.PendantNormalization

/-! The full labeled graph-theoretic pendant-square transition lemma. -/
namespace QuiverProofs.PendantTransitions
open TriangleRegions Regions Pendant PendantSquare PendantNormalization

structure Transitions (Q : Matrix 4) (ell j r t : Fin 4) : Prop where
  leaf : GraphPendant (mutate Q ell) ell j r
  parent_compatibility : mutate (mutate Q r) ell = mutate (mutate Q ell) r
  child : GraphPendant (mutate Q t) ell j t
  child_compatibility : mutate (mutate Q t) ell = mutate (mutate Q ell) t
  junction : IsRoot (mutate Q j) j
  junction_zero : ∃ a b : Fin 4, a≠b ∧ mutate Q j a b=0

theorem normalized (c d x y ε : Int) (h : Domain c d x y) (hε : Sign ε) :
    Transitions (state c d x y ε) 0 3 1 2 := by
  refine ⟨?_,?_,?_,?_,junction_isRoot c d x y ε h hε,?_⟩
  · rw [PendantSquare.leaf]
    apply state_graphPendant c d x y (-ε) h
    rcases hε with rfl|rfl <;> unfold Sign <;> omega
  · rw [PendantSquare.leaf]
    exact parent_leaf_compatibility c d x y ε h
  · have hg : GraphPendant (relabel (mutate (state c d x y ε) 2) swap12) 0 3 1 := by
      rw [child_frame c d x y ε h]
      exact state_graphPendant c d y (d*y-x) ε (child_domain c d x y h) hε
    have hh := graphPendant_relabel _ 0 3 1 hg swap12.symm
    simpa only [relabel_inverse] using hh
  · rw [PendantSquare.leaf]
    exact child_leaf_compatibility c d x y ε h
  · rcases hε with rfl|rfl
    · refine ⟨0,2,by decide,?_⟩
      rw [junction_plus c d x y h]
      rfl
    · refine ⟨0,1,by decide,?_⟩
      rw [junction_minus c d x y h]
      rfl

theorem reversed (Q : Matrix 4) (ell j r t : Fin 4) (h : Transitions Q ell j r t) :
    Transitions (reverse Q) ell j r t := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · simpa only [mutate_reverse] using graphPendant_reverse _ ell j r h.leaf
  · simpa only [mutate_reverse] using congrArg reverse h.parent_compatibility
  · simpa only [mutate_reverse] using graphPendant_reverse _ ell j t h.child
  · simpa only [mutate_reverse] using congrArg reverse h.child_compatibility
  · simpa only [mutate_reverse] using IsRoot.reversed h.junction
  · obtain ⟨a,b,hab,hzero⟩ := h.junction_zero
    refine ⟨a,b,hab,?_⟩
    simp [mutate_reverse,reverse,hzero]

theorem relabeled (Q : Matrix 4) (ell j r t : Fin 4) (h : Transitions Q ell j r t)
    (p : Relabeling 4) :
    Transitions (relabel Q p) (p.invFun ell) (p.invFun j) (p.invFun r) (p.invFun t) := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · simpa only [mutate_relabel,p.right_inv] using graphPendant_relabel _ ell j r h.leaf p
  · simpa only [mutate_relabel,p.right_inv] using congrArg (fun B => relabel B p) h.parent_compatibility
  · simpa only [mutate_relabel,p.right_inv] using graphPendant_relabel _ ell j t h.child p
  · simpa only [mutate_relabel,p.right_inv] using congrArg (fun B => relabel B p) h.child_compatibility
  · simpa only [mutate_relabel,p.right_inv] using IsRoot.relabelled h.junction p
  · obtain ⟨a,b,hab,hzero⟩ := h.junction_zero
    refine ⟨p.invFun a,p.invFun b,?_,?_⟩
    · intro he
      have hh := congrArg p.toFun he
      exact hab (by simpa only [p.right_inv] using hh)
    · simp only [mutate_relabel,p.right_inv,relabel]
      simpa only [p.right_inv] using hzero

/-- Manuscript “All four transitions of a pendant square”, in its original
labeled graph hypotheses. The leaf and child squares include both orientations;
the equalities check both parent returns and both child leaf orientations. -/
theorem all_four_transitions (Q : Matrix 4) (ell j r : Fin 4)
    (h : GraphPendant Q ell j r) :
    ∃ t : Fin 4, t≠ell ∧ t≠j ∧ t≠r ∧
      Transitions Q ell j r t ∧
      mutate (mutate Q ell) ell=Q ∧ mutate (mutate Q r) r=Q ∧
      ¬ Acyclic Q ∧
      (∀ e : Fin 3 → Fin 4, Function.Injective e → ∀ k, e k=ell → Acyclic (restrict Q e)) := by
  obtain ⟨p,c,d,x,y,ε,hp0,hp1,hp3,hd,hε,hform⟩ := labeled_graph_normalization Q ell j r h
  have ht0 : p.toFun 2≠ell := by rw [←hp0]; intro he; have := p.injective he; omega
  have ht1 : p.toFun 2≠r := by rw [←hp1]; intro he; have := p.injective he; omega
  have ht3 : p.toFun 2≠j := by rw [←hp3]; intro he; have := p.injective he; omega
  have hn : Transitions (relabel Q p) 0 3 1 2 := by
    rcases hform with hh|hh
    · rw [hh]; exact normalized c d x y ε hd hε
    · rw [hh]; exact reversed _ 0 3 1 2 (normalized c d x y ε hd hε)
  have hh := relabeled (relabel Q p) 0 3 1 2 hn p.symm
  change Transitions (relabel (relabel Q p) p.symm)
    (p.toFun 0) (p.toFun 3) (p.toFun 1) (p.toFun 2) at hh
  rw [relabel_inverse,hp0,hp1,hp3] at hh
  refine ⟨p.toFun 2,ht0,ht3,ht1,hh,mutation_involutive Q ell,
    mutation_involutive Q r,?_,?_⟩
  · rintro ⟨rank,hrank⟩
    exact h.2.2.2.2.2.1 ⟨rank,fun i j _ _ hij => hrank i j hij⟩
  · intro e he k hk
    exact containing_leaf_acyclic Q h.1 ell j h.2.1 e he k hk

end QuiverProofs.PendantTransitions
