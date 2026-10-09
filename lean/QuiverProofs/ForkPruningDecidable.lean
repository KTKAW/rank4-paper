import QuiverProofs.ForkPruning
import QuiverProofs.AcyclicTargets

namespace QuiverProofs.ForkPruning

private theorem four (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega

/-- A finite topological test, using the complete table of 24 permutations. -/
def FiniteAcyclic (B : Matrix 4) : Prop :=
  ∃ p : Fin 24, ∀ i j : Fin 4,
    0 < B ((Census.permutation p).toFun i) ((Census.permutation p).toFun j) → i.val < j.val

instance (B : Matrix 4) : Decidable (FiniteAcyclic B) := by
  unfold FiniteAcyclic
  infer_instance

theorem finiteAcyclic_iff (B : Matrix 4) (skew : SkewSymmetric B) :
    FiniteAcyclic B ↔ Acyclic B := by
  constructor
  · rintro ⟨p, topological⟩
    refine ⟨fun i => ((Census.permutation p).invFun i).val, ?_⟩
    intro i j arrow
    have h := topological ((Census.permutation p).invFun i) ((Census.permutation p).invFun j)
    apply h
    simpa only [(Census.permutation p).right_inv] using arrow
  · intro acyclic
    obtain ⟨p,h01,h02,h03,h12,h13,h23⟩ :=
      AcyclicTargets.acyclic_has_topological_coordinates B skew acyclic
    obtain ⟨index, eq⟩ := Census.permutation_exhaustive p
    refine ⟨index, ?_⟩
    intro i j arrow
    rw [← eq] at arrow
    have hs := skew (p.toFun i) (p.toFun j)
    rcases four i with rfl|rfl|rfl|rfl <;>
      rcases four j with rfl|rfl|rfl|rfl <;> simp at * <;> omega

def acyclicDecidable (B : Matrix 4) (skew : SkewSymmetric B) : Decidable (Acyclic B) :=
  decidable_of_iff (FiniteAcyclic B) (finiteAcyclic_iff B skew)

def mask (B : Matrix 4) (vertices : Fin 4 → Prop) [DecidablePred vertices] : Matrix 4 :=
  fun i j => if vertices i ∧ vertices j then B i j else 0

theorem mask_skew (B : Matrix 4) (skew : SkewSymmetric B)
    (vertices : Fin 4 → Prop) [DecidablePred vertices] : SkewSymmetric (mask B vertices) := by
  intro i j
  by_cases hi : vertices i <;> by_cases hj : vertices j <;>
    simp only [mask, hi, hj, and_self, and_true, and_false, ↓reduceIte, Int.neg_zero]
  exact skew i j

theorem mask_acyclic_iff (B : Matrix 4) (vertices : Fin 4 → Prop) [DecidablePred vertices] :
    Acyclic (mask B vertices) ↔ ForkDefinition.AcyclicOn B vertices := by
  constructor
  · rintro ⟨rank, h⟩
    refine ⟨rank, ?_⟩
    intro i j hi hj arrow
    apply h i j
    simpa only [mask, hi, hj, and_self, ↓reduceIte] using arrow
  · rintro ⟨rank, h⟩
    refine ⟨rank, ?_⟩
    intro i j arrow
    by_cases hi : vertices i <;> by_cases hj : vertices j <;>
      simp only [mask, hi, hj, and_self, and_true, and_false, ↓reduceIte] at arrow
    · exact h i j hi hj arrow
    all_goals omega

def acyclicOnDecidable (B : Matrix 4) (skew : SkewSymmetric B)
    (vertices : Fin 4 → Prop) [DecidablePred vertices] : Decidable (ForkDefinition.AcyclicOn B vertices) :=
  letI := acyclicDecidable (mask B vertices) (mask_skew B skew vertices)
  decidable_of_iff (Acyclic (mask B vertices)) (mask_acyclic_iff B vertices)

/-- Full reflection of the source graph-theoretic fork predicate, retaining the
actual return label. No sign/magnitude bound or supplied normal-form witness. -/
def graphForkDecidable (B : Matrix 4) (r : Fin 4) : Decidable (ForkDefinition.GraphFork B r) := by
  haveI : Decidable (SkewSymmetric B) := inferInstanceAs (Decidable (∀ i j, B i j = -B j i))
  by_cases skew : SkewSymmetric B
  · letI := acyclicDecidable B skew
    letI := acyclicOnDecidable B skew (fun i => 0 < B i r)
    letI := acyclicOnDecidable B skew (fun i => 0 < B r i)
    unfold ForkDefinition.GraphFork Cone.Abundant
    infer_instance
  · exact isFalse (fun h => skew h.1)

instance (B : Matrix 4) (k : Fin 4) : Decidable (Retained B k) :=
  letI := graphForkDecidable (mutate B k) k
  inferInstanceAs (Decidable (¬ ForkDefinition.GraphFork (mutate B k) k))

end QuiverProofs.ForkPruning
