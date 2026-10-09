import QuiverProofs.Disconnected
import QuiverProofs.TriangleRegions

/-! Pendant suborbits: universal mutation words avoiding the attachment vertex.
The deletion premise quantifies its three-vertex enumerations, so it is
independent of a choice of vertex order. -/
namespace QuiverProofs.Pendant
open TriangleRegions

/-- A genuine pendant vertex: its only nonzero edge is to `r`. -/
def At (Q : Matrix 4) (p r : Fin 4) : Prop :=
  p ≠ r ∧ Q p r ≠ 0 ∧ ∀ j, j ≠ r → Q p j = 0

/-- Mutation acyclicity of the three-vertex deletion, in every vertex order. -/
def DeletionMA (Q : Matrix 4) (p : Fin 4) : Prop :=
  ∀ e : Fin 3 → Fin 4, Function.Injective e → (∀ i, e i ≠ p) →
    MutationAcyclic (restrict Q e)

private theorem fin3 (i : Fin 3) : i=0 ∨ i=1 ∨ i=2 := by omega

/-- A skew triangle with an absent pair has no directed cycle. -/
theorem triangle_zero_acyclic (T : Matrix 3) (hT : SkewSymmetric T)
    (i j : Fin 3) (hne : i ≠ j) (hz : T i j = 0) : Acyclic T := by
  have hn : T = cycleThree (T 0 1) (T 1 2) (T 2 0) := by
    funext a b
    rcases fin3 a with rfl|rfl|rfl <;> rcases fin3 b with rfl|rfl|rfl <;>
      simp [cycleThree] <;> have := hT 0 0 <;> have := hT 1 1 <;>
      have := hT 2 2 <;> have := hT 0 2 <;> have := hT 1 0 <;>
      have := hT 2 1 <;> omega
  rw [hn]
  apply cycleThree_mixed_acyclic
  all_goals
    rcases fin3 i with rfl|rfl|rfl <;> rcases fin3 j with rfl|rfl|rfl
    all_goals have := hT 0 2; have := hT 1 0; have := hT 2 1; omega

/-- Every triangle containing the leaf is already acyclic. -/
theorem containing_leaf_acyclic (Q : Matrix 4) (hQ : SkewSymmetric Q)
    (p r : Fin 4) (hp : At Q p r) (e : Fin 3 → Fin 4)
    (he : Function.Injective e) (k : Fin 3) (hk : e k=p) :
    Acyclic (restrict Q e) := by
  obtain ⟨_,_,hz⟩ := hp
  have hex : ∃ j : Fin 3, j ≠ k ∧ e j ≠ r := by
    by_cases h : ∃ j : Fin 3, j ≠ k ∧ e j ≠ r
    · exact h
    apply False.elim
    have hbad : ∀ j : Fin 3, j ≠ k → e j = r := by grind
    rcases fin3 k with rfl|rfl|rfl
    · have h1 := hbad 1 (by decide); have h2 := hbad 2 (by decide)
      have := he (h1.trans h2.symm); omega
    · have h0 := hbad 0 (by decide); have h2 := hbad 2 (by decide)
      have := he (h0.trans h2.symm); omega
    · have h0 := hbad 0 (by decide); have h1 := hbad 1 (by decide)
      have := he (h0.trans h1.symm); omega
  obtain ⟨j,hjk,hjr⟩ := hex
  apply triangle_zero_acyclic _ (restrict_skew Q e hQ) k j (Ne.symm hjk)
  change Q (e k) (e j) = 0
  rw [hk]
  exact hz _ hjr

theorem triangles_of_deletion (Q : Matrix 4) (hQ : SkewSymmetric Q)
    (p r : Fin 4) (hp : At Q p r) (hd : DeletionMA Q p) : AllTrianglesMA Q := by
  intro e he
  by_cases h : ∃ k, e k=p
  · obtain ⟨k,hk⟩ := h
    exact acyclic_is_mutationAcyclic _ (containing_leaf_acyclic Q hQ p r hp e he k hk)
  · exact hd e he (by grind)

/-- Avoiding the attachment preserves the exact single neighbor and edge size. -/
theorem at_mutate (Q : Matrix 4)
    (p r : Fin 4) (hp : At Q p r) (k : Fin 4) (hkr : k ≠ r) :
    At (mutate Q k) p r := by
  obtain ⟨hpr,hn,hz⟩ := hp
  refine ⟨hpr,?_,?_⟩
  · by_cases hpk : p=k
    · subst k; simp [mutate,hn]
    · simp [mutate,hpk,Ne.symm hkr,hz k hkr,correction,hn]
  · intro j hjr
    by_cases hpk : p=k
    · subst k; simp [mutate,hz j hjr]
    · by_cases hjk : j=k
      · simp [mutate,hjk,hz k hkr]
      · simp [mutate,hpk,hjk,hz j hjr,hz k hkr,correction]

/-- Leaf mutation fixes the complementary induced triangle. -/
theorem leaf_mutation_restrict (Q : Matrix 4) (hQ : SkewSymmetric Q)
    (p r : Fin 4) (hp : At Q p r) (e : Fin 3 → Fin 4)
    (he : ∀ i, e i ≠ p) : restrict (mutate Q p) e = restrict Q e := by
  obtain ⟨hpr,_,hz⟩ := hp
  funext i j
  simp only [restrict,mutate,he i,he j,false_or,↓reduceIte]
  by_cases hir : e i=r
  · by_cases hjr : e j=r
    · rw [hir,hjr,hQ r p]
      simp [correction]
      grind
    · simp [hz _ hjr,correction]
  · have hip : Q (e i) p = 0 := by rw [hQ,hz _ hir]; omega
    simp [hip,correction]

private theorem image_complement (e : Fin 3 → Fin 4) (he : Function.Injective e)
    (p k : Fin 4) (hp : ∀ i, e i ≠ p) (hk : k ≠ p) : ∃ i, e i=k := by
  have h01 : e 0 ≠ e 1 := by intro h; have := he h; omega
  have h02 : e 0 ≠ e 2 := by intro h; have := he h; omega
  have h12 : e 1 ≠ e 2 := by intro h; have := he h; omega
  have hp0 := hp 0; have hp1 := hp 1; have hp2 := hp 2
  have : e 0=k ∨ e 1=k ∨ e 2=k := by omega
  rcases this with h|h|h
  · exact ⟨0,h⟩
  · exact ⟨1,h⟩
  · exact ⟨2,h⟩

theorem deletion_mutate (Q : Matrix 4) (hQ : SkewSymmetric Q)
    (p r : Fin 4) (hp : At Q p r) (hd : DeletionMA Q p)
    (k : Fin 4) : DeletionMA (mutate Q k) p := by
  intro e he hep
  by_cases hkp : k=p
  · subst k
    rw [leaf_mutation_restrict Q hQ p r hp e hep]
    exact hd e he hep
  · obtain ⟨i,hi⟩ := image_complement e he p k hep hkp
    rw [←hi,restrict_mutate Q e he i]
    exact (mutationAcyclic_iff _ i).mpr (hd e he hep)

/-- Manuscript `lem:structural-pendant-suborbit` (Pendant suborbits).
This quantifies over every finite word omitting the attachment vertex. -/
theorem pendant_suborbits (Q : Matrix 4) (hQ : SkewSymmetric Q)
    (p r : Fin 4) (hp : At Q p r) (hd : DeletionMA Q p)
    (word : List (Fin 4)) (hw : r ∉ word) :
    At (applyWord Q word) p r ∧ AllTrianglesMA (applyWord Q word) := by
  have aux : ∀ word : List (Fin 4), ∀ Q : Matrix 4,
      SkewSymmetric Q → At Q p r → DeletionMA Q p → r ∉ word →
      At (applyWord Q word) p r ∧ DeletionMA (applyWord Q word) p ∧
      SkewSymmetric (applyWord Q word) := by
    intro w
    induction w with
    | nil => intro Q hQ hp hd _; exact ⟨hp,hd,hQ⟩
    | cons k ks ih =>
      intro Q hQ hp hd hw
      have hkr : k ≠ r := by intro h; subst k; simp at hw
      have hrs : r ∉ ks := by simpa using (show r ≠ k ∧ r ∉ ks from by simpa using hw).2
      exact ih (mutate Q k) (mutation_preserves_skew Q k hQ)
        (at_mutate Q p r hp k hkr) (deletion_mutate Q hQ p r hp hd k) hrs
  obtain ⟨hp',hd',hQ'⟩ := aux word Q hQ hp hd hw
  exact ⟨hp',triangles_of_deletion _ hQ' p r hp' hd'⟩

/-- The same source theorem from one canonical induced deletion, rather than
from an enumeration-independent premise. -/
theorem pendant_suborbits_of_deletion (Q : Matrix 4) (hQ : SkewSymmetric Q)
    (p r : Fin 4) (hp : At Q p r)
    (hd : MutationAcyclic (restrict Q (deleteVertex p)))
    (word : List (Fin 4)) (hw : r ∉ word) :
    At (applyWord Q word) p r ∧ AllTrianglesMA (applyWord Q word) := by
  have havoid : ∀ p : Fin 4, ∀ i : Fin 3, deleteVertex p i ≠ p := by decide
  have hall : AllTrianglesMA Q := by
    apply allTrianglesMA_of_deletions
    intro s
    by_cases hsp : s=p
    · subst s; exact hd
    · obtain ⟨k,hk⟩ := image_complement (deleteVertex s)
        (deleteVertex_injective s) s p (havoid s) (Ne.symm hsp)
      exact acyclic_is_mutationAcyclic _ (containing_leaf_acyclic Q hQ p r hp
        (deleteVertex s) (deleteVertex_injective s) k hk)
  exact pendant_suborbits Q hQ p r hp (fun e he _ => hall e he) word hw

end QuiverProofs.Pendant
