import QuiverProofs.ProperMutation
import QuiverProofs.AcyclicTargets
import QuiverProofs.CensusConnectivity
import QuiverProofs.ClassSeparation

/-! Exact conditional interface for scalar proper-order exclusions.
The two external obligations below are propositions, never axioms. Uniqueness
of a totally proper class is not needed when every proper class is excluded. -/
namespace QuiverProofs.ProperObstructionSoundness
open ProperOrder ProperWiggle ProperMutation Census

def Topological (B : Matrix 4) (p : CyclicOrder) : Prop :=
  0 ≤ B (p.toFun 0) (p.toFun 1) ∧ 0 ≤ B (p.toFun 0) (p.toFun 2) ∧
  0 ≤ B (p.toFun 0) (p.toFun 3) ∧ 0 ≤ B (p.toFun 1) (p.toFun 2) ∧
  0 ≤ B (p.toFun 1) (p.toFun 3) ∧ 0 ≤ B (p.toFun 2) (p.toFun 3)

/-- Neville's existence conclusion in the project's exact semantics. -/
def MAHasTotalProper4 : Prop :=
  ∀ B : Matrix 4, SkewSymmetric B → MutationAcyclic B →
    ∃ p : CyclicOrder, TotalProper B p

/-- Identification of an arbitrary totally proper acyclic endpoint with
the cyclic class of a topological ordering. No inhabitant is asserted. -/
def EndpointTopological4 : Prop :=
  ∀ B : Matrix 4, SkewSymmetric B → Acyclic B →
    ∀ p : CyclicOrder, TotalProper B p →
      ∃ q : CyclicOrder, Topological B q ∧ WiggleEquivalent B p q

/-- The separate literature uniqueness assertion, recorded with its actual
quantifiers. It is deliberately absent from the scalar soundness hypotheses. -/
def TotalProperUnique4 : Prop :=
  ∀ B : Matrix 4, SkewSymmetric B → ∀ p q : CyclicOrder,
    TotalProper B p → TotalProper B q → WiggleEquivalent B p q

/-- The separate well-definedness assertion for chosen proper representatives. -/
def ProperMutationIndependent4 : Prop :=
  ∀ B : Matrix 4, SkewSymmetric B → ∀ p q r : CyclicOrder, ∀ k : Fin 4,
    ProperMutation B p k q → ProperMutation B p k r →
      WiggleEquivalent (mutate B k) q r

/-- The topological-order version of Neville's acyclic starting theorem. -/
def TopologicalTotalProper4 : Prop :=
  ∀ B : Matrix 4, SkewSymmetric B → Acyclic B →
    ∀ p : CyclicOrder, Topological B p → TotalProper B p

/-- Reverse a chronological word to undo it. No bound on word length. -/
theorem applyWord_undo {n : Nat} (B : Matrix n) (w : List (Fin n)) :
    applyWord (applyWord B w) w.reverse = B := by
  induction w generalizing B with
  | nil => rfl
  | cons k ks ih =>
    simp only [applyWord,List.reverse_cons,applyWord_append]
    rw [ih]
    exact mutation_involutive B k

/-- Acyclic topological total properness is enough for MA existence: lift
the reversed acyclicizing word from its endpoint. -/
theorem existence_of_topological_total (hTop : TopologicalTotalProper4) :
    MAHasTotalProper4 := by
  intro B hB hMA
  obtain ⟨w,hw⟩ := hMA
  have hC := word_preserves_skew B w hB
  obtain ⟨q,hq⟩ := AcyclicTargets.acyclic_has_topological_coordinates _ hC hw
  obtain ⟨p,_,hp⟩ := totalProper_lifts_word _ hC q (hTop _ hC hw q hq) w.reverse
  rw [applyWord_undo] at hp
  exact ⟨p,hp⟩

/-- Uniqueness together with topological total properness supplies the
endpoint bridge. Both inputs remain explicit unproved propositions. -/
theorem endpoint_of_unique_topological (hUnique : TotalProperUnique4)
    (hTop : TopologicalTotalProper4) : EndpointTopological4 := by
  intro B hB hA p hp
  obtain ⟨q,hq⟩ := AcyclicTargets.acyclic_has_topological_coordinates B hB hA
  exact ⟨q,hq,hUnique B hB p q hp (hTop B hB hA q hq)⟩

private theorem coloring_after_mutation (B : Matrix 4) (k : Fin 4)
    (s : Fin 4 → Bool) (h : RespectsEdges (mutate B k) s) :
    RespectsEdges B s := by
  intro i j hij
  by_cases hi : i = k
  · subst i
    exact h k j (by simpa [mutate] using hij)
  · by_cases hj : j = k
    · subst j
      exact h i k (by simpa [mutate] using hij)
    · by_cases hik : B i k = 0
      · exact h i j (by simpa [mutate, hi, hj, hik, correction] using hij)
      · by_cases hkj : B k j = 0
        · exact h i j (by simpa [mutate, hi, hj, hkj, correction] using hij)
        · have h1 := h i k (by simpa [mutate] using hik)
          have h2 := h k j (by simpa [mutate] using hkj)
          exact h1.trans h2

/-- Support connectedness is invariant under arbitrary matrix mutation;
the correction can only join vertices already joined through k. -/
theorem connected_mutation (B : Matrix 4) (k : Fin 4)
    (hB : ConnectedSupport B) : ConnectedSupport (mutate B k) := by
  apply (connected_iff_all_colorings _).mpr
  intro s hs
  exact (connected_iff_all_colorings B).mp hB s (coloring_after_mutation B k s hs)

theorem connected_applyWord (B : Matrix 4) (w : List (Fin 4))
    (hB : ConnectedSupport B) : ConnectedSupport (applyWord B w) := by
  induction w generalizing B with
  | nil => exact hB
  | cons k ks ih => exact ih (mutate B k) (connected_mutation B k hB)

/-- All-word scalar obstruction soundness under precisely two structural
bridges. Every proper cyclic class must be excluded; finite searches are not
used in this deduction. -/
theorem NMA_of_scalar_exclusion (hExist : MAHasTotalProper4)
    (hEndpoint : EndpointTopological4) (B : Matrix 4) (hB : SkewSymmetric B)
    (hconn : ConnectedSupport B)
    (hexclude : ∀ p : CyclicOrder, ProperClass B p →
      ∀ C : Matrix 4, SkewSymmetric C → ConnectedSupport C →
        ∀ q : CyclicOrder, Topological C q →
          orderMarkov C q = orderMarkov B p →
          matrixPfaffian C ^ 2 = matrixPfaffian B ^ 2 → False) :
    ¬ MutationAcyclic B := by
  intro hMA
  obtain ⟨p,hp⟩ := hExist B hB hMA
  obtain ⟨w,hw⟩ := hMA
  obtain ⟨r,htr,hpr⟩ := totalProper_lifts_word B hB p hp w
  have hC := word_preserves_skew B w hB
  obtain ⟨q,hq,hrq⟩ := hEndpoint _ hC hw r hpr
  have hM := transport_markov hB htr
  have hMq := ProperWiggleInvariants.markov_wiggle_invariant _ hC hrq
  exact hexclude p (totalProper_proper B p hp) _ hC (connected_applyWord B w hconn)
    q hq (hMq.symm.trans hM) (pfaffian_square_word B w hB)

end QuiverProofs.ProperObstructionSoundness
