import QuiverProofs.WeakRegions

namespace QuiverProofs.WeakRegionSemantics
open WeakForks WeakRegions

/-- A finite cell with completely checked mutation transitions. The only
non-internal alternatives are framed returns and proved boundary predicates. -/
structure Cell where
  size : Nat
  rootIndex : Fin size
  state : Fin size → Matrix 4
  returnVertex : Fin 4
  skew : ∀ i, SkewSymmetric (state i)
  cyclic : ∀ i, ¬ Acyclic (state i)
  edges : ∀ i k,
    (∃ j, mutate (state i) k = state j) ∨
    (∃ p : Relabeling 4,
      mutate (state i) k = relabel (mutate (state rootIndex) returnVertex) p) ∨
    IsWeakFork (mutate (state i) k) k ∨ IsRoot (mutate (state i) k) k

/-- Finite addresses in the recursively attached cells. The same matrix may
have several addresses; injectivity and quotient-tree topology are unnecessary. -/
inductive Safe (core : Matrix 4 → Prop) : Matrix 4 → Prop
  | central {B : Matrix 4} : core B → Safe core B
  | fork {B : Matrix 4} (r : Fin 4) : Safe core B → IsWeakFork (mutate B r) r → Safe core (mutate B r)
  | cell (c : Cell) : Safe core (mutate (c.state c.rootIndex) c.returnVertex) →
      (i : Fin c.size) → Safe core (c.state i)
  | framed {B : Matrix 4} : Safe core B → (p : Relabeling 4) → Safe core (relabel B p)
  | reversed {B : Matrix 4} : Safe core B → Safe core (reverse B)

theorem safe_skew (core : Matrix 4 → Prop) (hc : ∀ B, core B → SkewSymmetric B)
    {B : Matrix 4} (h : Safe core B) : SkewSymmetric B := by
  induction h with
  | central h => exact hc _ h
  | fork _ _ hf _ => exact fork_skew hf
  | cell c _ i _ => exact c.skew i
  | framed _ p ih => exact relabel_skew _ p ih
  | reversed _ ih => exact reverse_skew _ ih

theorem safe_cyclic (core : Matrix 4 → Prop)
    (hs : ∀ B, core B → SkewSymmetric B) (hc : ∀ B, core B → ¬ Acyclic B)
    {B : Matrix 4} (h : Safe core B) : ¬ Acyclic B := by
  induction h with
  | central h => exact hc _ h
  | fork _ _ hf _ => exact fork_cyclic hf
  | cell c _ i _ => exact c.cyclic i
  | framed _ p ih => exact fun ha => ih ((acyclic_relabel_iff _ p).mp ha)
  | reversed h ih => exact fun ha => ih ((acyclic_reverse_iff _ (safe_skew core hs h)).mp ha)

def RootCellsExist : Prop :=
  ∀ (Q : Matrix 4) (r : Fin 4), IsRoot Q r →
    ∃ c : Cell, c.state c.rootIndex = Q ∧ c.returnVertex = r

theorem attach_root (hCells : RootCellsExist) (core : Matrix 4 → Prop)
    {B : Matrix 4} (h : Safe core B) (r : Fin 4) (hr : IsRoot (mutate B r) r) :
    Safe core (mutate B r) := by
  obtain ⟨c,heq,hret⟩ := hCells _ r hr
  have hparent : Safe core (mutate (c.state c.rootIndex) c.returnVertex) := by
    rw [heq,hret,mutation_involutive]
    exact h
  simpa only [heq] using Safe.cell c hparent c.rootIndex

theorem safe_closed (hCells : RootCellsExist) (core : Matrix 4 → Prop)
    (he : ∀ B, core B → ∀ k,
      core (mutate B k) ∨ IsWeakFork (mutate B k) k ∨ IsRoot (mutate B k) k)
    {B : Matrix 4} (h : Safe core B) (k : Fin 4) : Safe core (mutate B k) := by
  induction h generalizing k with
  | central h =>
    rcases he _ h k with hc | hf | hr
    · exact Safe.central hc
    · exact Safe.fork k (Safe.central h) hf
    · exact attach_root hCells core (Safe.central h) k hr
  | @fork B r h hf ih =>
    by_cases hk : k=r
    · subst k; simpa only [mutation_involutive] using h
    · exact Safe.fork k (Safe.fork r h hf) (fork_continuation hf k hk)
  | cell c h i ih =>
    rcases c.edges i k with ⟨j,hj⟩ | ⟨p,hp⟩ | hf | hr
    · rw [hj]; exact Safe.cell c h j
    · rw [hp]; exact Safe.framed h p
    · exact Safe.fork k (Safe.cell c h i) hf
    · exact attach_root hCells core (Safe.cell c h i) k hr
  | @framed B h p ih =>
    rw [mutate_relabel]
    exact Safe.framed (ih (p.toFun k)) p
  | reversed h ih =>
    rw [mutate_reverse]
    exact Safe.reversed (ih k)

/-- Universal NMA soundness of the region grammar. `RootCellsExist` is a
separate local-table obligation, discharged for the diamond/decagon packages
in WeakRegionCells.lean; it is not declared as an axiom. -/
theorem region_NMA (hCells : RootCellsExist) (core : Matrix 4 → Prop)
    (hs : ∀ B, core B → SkewSymmetric B) (hc : ∀ B, core B → ¬ Acyclic B)
    (he : ∀ B, core B → ∀ k,
      core (mutate B k) ∨ IsWeakFork (mutate B k) k ∨ IsRoot (mutate B k) k)
    (B : Matrix 4) (hB : core B) : ¬ MutationAcyclic B := by
  have allWords : ∀ word, ∀ C, Safe core C → Safe core (applyWord C word) := by
    intro word
    induction word with
    | nil => intro C h; exact h
    | cons k ks ih => intro C h; exact ih _ (safe_closed hCells core he h k)
  rintro ⟨word,ha⟩
  exact safe_cyclic core hs hc (allWords word B (Safe.central hB)) ha

theorem framed_region_NMA (hCells : RootCellsExist) {m : Nat}
    (node : Fin m → Matrix 4)
    (hs : ∀ i, SkewSymmetric (node i)) (hc : ∀ i, ¬ Acyclic (node i))
    (he : ∀ i k, FramedCore node (mutate (node i) k) ∨
      IsWeakFork (mutate (node i) k) k ∨ IsRoot (mutate (node i) k) k)
    (i : Fin m) : ¬ MutationAcyclic (node i) := by
  apply region_NMA hCells (FramedCore node)
  · intro B h; obtain ⟨j,p,rfl⟩ := h; exact relabel_skew _ p (hs j)
  · intro B h; obtain ⟨j,p,rfl⟩ := h
    exact fun ha => hc j ((acyclic_relabel_iff _ p).mp ha)
  · intro B h k
    obtain ⟨j,p,rfl⟩ := h
    rw [mutate_relabel]
    rcases he j (p.toFun k) with hcore | hfork | hroot
    · exact Or.inl (framed_relabel node hcore p)
    · exact Or.inr (Or.inl (by simpa only [p.left_inv] using IsWeakFork.relabelled hfork p))
    · exact Or.inr (Or.inr (by simpa only [p.left_inv] using IsRoot.relabelled hroot p))
  · exact ⟨i,.identity 4,rfl⟩

end QuiverProofs.WeakRegionSemantics
