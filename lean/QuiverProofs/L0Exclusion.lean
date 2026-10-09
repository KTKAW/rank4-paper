import QuiverProofs.CertificateSearch
import QuiverProofs.ExtendedWeakPairs
import QuiverProofs.E2Certificate
import QuiverProofs.Disconnected
import QuiverProofs.Invariants

/-! The fixed L0 certificate grammar implies a finite-core/fixed-exterior
cover. This connects the two-weak-pair obstruction to actual accepted Lean
certificate records, including arbitrary entry words. -/
namespace QuiverProofs.L0Exclusion
open Forks Regions RegionSemantics RegionCells ExtendedWeakPairs CertificateSearch

def CellExterior (c : Cell) : Prop := ∀ i, Exterior (c.state i)

theorem root_exterior_cells (Q : Matrix 4) (r : Fin 4) (h : IsRoot Q r) :
    ∃ c : Cell, c.state c.rootIndex=Q ∧ c.returnVertex=r ∧ CellExterior c := by
  induction h with
  | basic A B C D E ε h hε =>
    rcases hε with rfl|rfl
    · exact ⟨diamondCell A B C D E h,rfl,rfl,fun i => Exterior.diamond A B C D E h i⟩
    · exact ⟨unitCell A B C D E h,rfl,rfl,fun i => Exterior.unit A B C D E h i⟩
  | @relabelled Q r h p ih =>
    obtain ⟨c,heq,hret,he⟩ := ih
    refine ⟨cellRelabel c p,?_,?_,fun i => Exterior.framed (he i) p⟩
    · change relabel (c.state c.rootIndex) p = relabel Q p
      rw [heq]
    · change p.invFun c.returnVertex = p.invFun r
      rw [hret]
  | @reversed Q r h ih =>
    obtain ⟨c,heq,hret,he⟩ := ih
    refine ⟨cellReverse c,?_,hret,fun i => Exterior.reversed (he i)⟩
    change reverse (c.state c.rootIndex) = reverse Q
    rw [heq]

inductive Safe {m : Nat} (node : Fin m → Matrix 4) : Matrix 4 → Prop
  | central (i : Fin m) : Safe node (node i)
  | fork {Q : Matrix 4} (r : Fin 4) : Safe node Q → IsFork (mutate Q r) r → Safe node (mutate Q r)
  | cell (c : Cell) : CellExterior c →
      Safe node (mutate (c.state c.rootIndex) c.returnVertex) →
      (i : Fin c.size) → Safe node (c.state i)
  | framed {Q : Matrix 4} : Safe node Q → (p : Relabeling 4) → Safe node (relabel Q p)
  | reversed {Q : Matrix 4} : Safe node Q → Safe node (reverse Q)

def SignedCore {m : Nat} (node : Fin m → Matrix 4) (Q : Matrix 4) : Prop :=
  ∃ i, ∃ p : Relabeling 4, Q=relabel (node i) p ∨ Q=reverse (relabel (node i) p)

theorem safe_shapes {m : Nat} (node : Fin m → Matrix 4) {Q : Matrix 4}
    (h : Safe node Q) : SignedCore node Q ∨ Exterior Q := by
  induction h with
  | central i => exact Or.inl ⟨i,.identity 4,Or.inl rfl⟩
  | fork r _ hf _ => exact Or.inr (Exterior.fork r hf)
  | cell c he _ i _ => exact Or.inr (he i)
  | @framed Q _ p ih =>
    rcases ih with ⟨i,q,hq⟩|he
    · left
      rcases hq with rfl|rfl
      · exact ⟨i,q.trans p,Or.inl rfl⟩
      · exact ⟨i,q.trans p,Or.inr rfl⟩
    · exact Or.inr (Exterior.framed he p)
  | @reversed Q _ ih =>
    rcases ih with ⟨i,p,hp⟩|he
    · left
      rcases hp with rfl|rfl
      · exact ⟨i,p,Or.inr rfl⟩
      · exact ⟨i,p,Or.inl (reverse_involutive _)⟩
    · exact Or.inr (Exterior.reversed he)

theorem attach_root {m : Nat} (node : Fin m → Matrix 4) {Q : Matrix 4}
    (h : Safe node Q) (r : Fin 4) (hr : IsRoot (mutate Q r) r) : Safe node (mutate Q r) := by
  obtain ⟨c,heq,hret,ht⟩ := root_exterior_cells _ r hr
  have hp : Safe node (mutate (c.state c.rootIndex) c.returnVertex) := by
    rw [heq,hret,mutation_involutive]
    exact h
  simpa only [heq] using Safe.cell c ht hp c.rootIndex

theorem safe_closed {m : Nat} (node : Fin m → Matrix 4)
    (he : ∀ i k, FramedCore node (mutate (node i) k) ∨
      IsFork (mutate (node i) k) k ∨ IsRoot (mutate (node i) k) k)
    {Q : Matrix 4} (h : Safe node Q) (k : Fin 4) : Safe node (mutate Q k) := by
  induction h generalizing k with
  | central i =>
    rcases he i k with ⟨j,p,hj⟩|hf|hr
    · rw [hj]; exact Safe.framed (Safe.central j) p
    · exact Safe.fork k (Safe.central i) hf
    · exact attach_root node (Safe.central i) k hr
  | @fork Q r h hf ih =>
    by_cases hk : k=r
    · subst k; simpa only [mutation_involutive] using h
    · exact Safe.fork k (Safe.fork r h hf) (fork_continuation hf k hk)
  | cell c hc h i ih =>
    rcases c.edges i k with ⟨j,hj⟩|⟨p,hp⟩|hf|hr
    · rw [hj]; exact Safe.cell c hc h j
    · rw [hp]; exact Safe.framed h p
    · exact Safe.fork k (Safe.cell c hc h i) hf
    · exact attach_root node (Safe.cell c hc h i) k hr
  | framed h p ih =>
    rw [mutate_relabel]
    exact Safe.framed (ih (p.toFun k)) p
  | reversed h ih =>
    rw [mutate_reverse]
    exact Safe.reversed (ih k)

theorem safe_word {m : Nat} (node : Fin m → Matrix 4)
    (he : ∀ i k, FramedCore node (mutate (node i) k) ∨
      IsFork (mutate (node i) k) k ∨ IsRoot (mutate (node i) k) k)
    (word : List (Fin 4)) {Q : Matrix 4} (h : Safe node Q) : Safe node (applyWord Q word) := by
  induction word generalizing Q with
  | nil => exact h
  | cons k ks ih => exact ih (safe_closed node he h k)

private theorem word_reverse_cancel (Q : Matrix 4) (word : List (Fin 4)) :
    applyWord (applyWord Q word) word.reverse = Q := by
  induction word generalizing Q with
  | nil => rfl
  | cons k ks ih =>
    simp only [applyWord,List.reverse_cons,applyWord_append]
    rw [ih]
    exact mutation_involutive Q k

/-- Every accepted L0 object has precisely the source's finite-core/exterior
cover, including reversal and every possible finite entry word. -/
theorem accepted_implies_finite_cover (Q : Matrix 4) (c : RegionCertificate)
    (h : acceptCertificate Q c=true) : FiniteCoreExteriorCover Q := by
  obtain ⟨hentry,_,_,he⟩ := (acceptCertificate_iff Q c).mp h
  have he' := fun i k => edgeChecks_sound c.node i k (c.edge i k) (he i k)
  have hroot : Safe c.node Q := by
    have hh := safe_word c.node he' c.entry.reverse (Safe.central c.root)
    rw [←entriesEqual_eq hentry,word_reverse_cancel] at hh
    exact hh
  refine ⟨List.ofFn c.node ++ List.ofFn (fun i => reverse (c.node i)),?_⟩
  intro word
  rcases safe_shapes c.node (safe_word c.node he' word hroot) with ⟨i,p,hp⟩|hext
  · left
    rcases hp with hp|hp
    · refine ⟨c.node i,?_,p,hp⟩
      simp only [List.mem_append,List.mem_ofFn]
      exact Or.inl ⟨i,rfl⟩
    · refine ⟨reverse (c.node i),?_,p,hp⟩
      simp only [List.mem_append,List.mem_ofFn]
      exact Or.inr ⟨i,rfl⟩
  · exact Or.inr hext

/-- No finite object in the unchanged L0 certificate checker accepts E2. -/
theorem E2_no_L0_certificate (c : RegionCertificate) :
    acceptCertificate (ofSix (-2) (-1) 1 (-1) 1 (-2)) c ≠ true := by
  intro h
  exact E2_no_finite_core_exterior_cover (accepted_implies_finite_cover _ c h)

/-- The full printed E2 result: NMA, global triangle avoidance, and fixed-language exclusion. -/
theorem E2_counterexample :
    ¬ MutationAcyclic (ofSix (-2) (-1) 1 (-1) 1 (-2)) ∧
    (∀ word : List (Fin 4), TriangleRegions.AllTrianglesMA
      (applyWord (ofSix (-2) (-1) 1 (-1) 1 (-2)) word)) ∧
    (∀ c : RegionCertificate, acceptCertificate (ofSix (-2) (-1) 1 (-1) 1 (-2)) c ≠ true) :=
  ⟨E2Certificate.E2_NMA,E2Certificate.E2_global_triangle_avoidance,E2_no_L0_certificate⟩

/-- The same fixed-language obstruction for the exact printed E3 representative. -/
theorem E3_no_L0_certificate (c : RegionCertificate) :
    acceptCertificate (ofSix (-2) (-1) 1 1 (-2) 2) c ≠ true := by
  intro h
  exact E3_no_finite_core_exterior_cover (accepted_implies_finite_cover _ c h)

theorem E2_connected : ¬ DisconnectedSupport (ofSix (-2) (-1) 1 (-1) 1 (-2)) := by
  intro h
  have hc := disconnected_support_cut _ h
  simp [DisconnectedCut,ofSix] at hc

theorem E2_pfaffian : matrixPfaffian (ofSix (-2) (-1) 1 (-1) 1 (-2))=4 := by decide

end QuiverProofs.L0Exclusion
