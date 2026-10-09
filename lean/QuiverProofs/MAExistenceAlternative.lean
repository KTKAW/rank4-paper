import QuiverProofs.ProperEndpoint
import QuiverProofs.ProperMutationClass

/-! Order-construction and component boundary lemmas for the exact total-proper
existence problem. None of these declarations assumes total properness. -/
namespace QuiverProofs.MAExistenceAlternative
open ProperOrder ProperWiggle ProperMutation ProperObstructionSoundness
open ProperWiggleInvariants ProperMutationRepresentativeChoice Census

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

private theorem relabeling_ext (p q : CyclicOrder) (h : p.toFun = q.toFun) : p = q := by
  have hi : p.invFun = q.invFun := by
    funext i
    apply p.injective
    rw [p.right_inv, h, q.right_inv]
  cases p
  cases q
  simp_all

/-- The largest oriented support on which two linear orders both agree. -/
private def commonOrderMatrix (p q : CyclicOrder) : Matrix 4 := fun i j =>
  if p.invFun i < p.invFun j ∧ q.invFun i < q.invFun j then 1
  else if p.invFun j < p.invFun i ∧ q.invFun j < q.invFun i then -1 else 0

private theorem commonOrder_skew (p q : CyclicOrder) :
    SkewSymmetric (commonOrderMatrix p q) := by
  intro i j
  simp only [commonOrderMatrix]
  repeat' split <;> omega

private theorem topological_nonnegative (B : Matrix 4) (p : CyclicOrder)
    (hp : Topological B p) (i j : Fin 4) (hij : i < j) :
    0 ≤ B (p.toFun i) (p.toFun j) := by
  have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  have hj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
  rcases hi with rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl <;> first | omega | simp only [Topological] at hp; omega

private theorem commonOrder_zero (B : Matrix 4) (hB : SkewSymmetric B)
    (p q : CyclicOrder) (hp : Topological B p) (hq : Topological B q)
    (i j : Fin 4) (hz : commonOrderMatrix p q i j = 0) : B i j = 0 := by
  have pos : ∀ r : CyclicOrder, Topological B r → ∀ u v,
      r.invFun u < r.invFun v → 0 ≤ B u v := by
    intro r hr u v huv
    simpa only [r.right_inv] using topological_nonnegative B r hr _ _ huv
  by_cases he : i=j
  · subst i
    have := hB j j
    omega
  have hpne : p.invFun i ≠ p.invFun j := by
    intro h
    exact he (by rw [←p.right_inv i, ←p.right_inv j, h])
  have hqne : q.invFun i ≠ q.invFun j := by
    intro h
    exact he (by rw [←q.right_inv i, ←q.right_inv j, h])
  have hs := hB i j
  by_cases hij : p.invFun i < p.invFun j
  · have hqji : q.invFun j < q.invFun i := by
      by_cases hqij : q.invFun i < q.invFun j
      · simp [commonOrderMatrix, hij, hqij] at hz
      · omega
    have := pos p hp i j hij
    have := pos q hq j i hqji
    omega
  · have hpji : p.invFun j < p.invFun i := by omega
    have hqij : q.invFun i < q.invFun j := by
      by_cases hqji : q.invFun j < q.invFun i
      · simp [commonOrderMatrix, hij, hpji, hqji] at hz
      · omega
    have := pos p hp j i hpji
    have := pos q hq i j hqij
    omega

private theorem finite_commonOrder_component : ∀ a b : Fin 24,
    component (supportMask (commonOrderMatrix (permutation a) (permutation b)))
      (canonicalIndex a) =
    component (supportMask (commonOrderMatrix (permutation a) (permutation b)))
      (canonicalIndex b) := by decide

/-- Any two topological linear extensions differ by valid adjacent nonedge
swaps and rotations. The transfer includes zero edges and arbitrary weights. -/
theorem topological_orders_wiggle (B : Matrix 4) (hB : SkewSymmetric B)
    (p q : CyclicOrder) (hp : Topological B p) (hq : Topological B q) :
    WiggleEquivalent B p q := by
  obtain ⟨a,ha⟩ := permutation_exhaustive p
  obtain ⟨b,hb⟩ := permutation_exhaustive q
  have hep := relabeling_ext p (permutation a) ha
  have heq := relabeling_ext q (permutation b) hb
  subst p
  subst q
  have hw := (wiggle_iff_component _ (commonOrder_skew (permutation a) (permutation b))
    (permutation a) (permutation b) (canonicalIndex a) (canonicalIndex b)
    (canonical_index_correct a) (canonical_index_correct b)).mpr
      (finite_commonOrder_component a b)
  exact wiggle_zero_transfer _ B (commonOrder_zero B hB _ _ hp hq) hw

/-- A partition of vertices has no exchange entries between distinct blocks. -/
def BlockSeparated {n : Nat} {α : Type} (B : Matrix n) (block : Fin n → α) : Prop :=
  ∀ i j, block i ≠ block j → B i j = 0

/-- Mutation cannot create an edge between distinct support components.
This lemma uses no skew, connectedness, weight, or invertibility assumption. -/
theorem blockSeparated_mutation {n : Nat} {α : Type} (B : Matrix n)
    (block : Fin n → α) (h : BlockSeparated B block) (k : Fin n) :
    BlockSeparated (mutate B k) block := by
  intro i j hij
  have hz := h i j hij
  by_cases hk : i=k ∨ j=k
  · simp [mutate, hk, hz]
  · by_cases hik : block i = block k
    · have hkj : block k ≠ block j := by
        intro he
        exact hij (hik.trans he)
      simp [mutate, hk, hz, h k j hkj, correction]
    · simp [mutate, hk, hz, h i k hik, correction]

theorem blockSeparated_applyWord {n : Nat} {α : Type} (B : Matrix n)
    (block : Fin n → α) (h : BlockSeparated B block) (w : List (Fin n)) :
    BlockSeparated (applyWord B w) block := by
  induction w generalizing B with
  | nil => exact h
  | cons k ks ih => exact ih (mutate B k) (blockSeparated_mutation B block h k)

/-- Every vertex has at most one support neighbor; isolated vertices are allowed. -/
def MatchingSupport {n : Nat} (B : Matrix n) : Prop :=
  ∀ v u w, B v u ≠ 0 → B v w ≠ 0 → u=w

private theorem correction_opposite (x : Int) : correction x (-x) = 0 := by
  simp only [correction, Int.neg_neg]
  grind

private theorem matching_correction_zero {n : Nat} (B : Matrix n)
    (hB : SkewSymmetric B) (h : MatchingSupport B) (k i j : Fin n) :
    correction (B i k) (B k j) = 0 := by
  by_cases hi : B i k=0
  · simp [hi, correction]
  by_cases hj : B k j=0
  · simp [hj, correction]
  have hki : B k i ≠ 0 := by
    intro hz
    apply hi
    rw [hB i k, hz]
    rfl
  have he := h k i j hki hj
  subst j
  rw [hB k i]
  exact correction_opposite _

/-- On matching support, mutation changes only incident signs and preserves
the support exactly. Arbitrary integer edge weights are retained. -/
theorem matching_mutation_nonzero {n : Nat} (B : Matrix n)
    (hB : SkewSymmetric B) (h : MatchingSupport B) (k i j : Fin n) :
    mutate B k i j ≠ 0 ↔ B i j ≠ 0 := by
  by_cases hk : i=k ∨ j=k
  · simp [mutate, hk]
  · simp [mutate, hk, matching_correction_zero B hB h k i j]

theorem matchingSupport_mutation {n : Nat} (B : Matrix n)
    (hB : SkewSymmetric B) (h : MatchingSupport B) (k : Fin n) :
    MatchingSupport (mutate B k) := by
  intro v u w hvu hvw
  exact h v u w ((matching_mutation_nonzero B hB h k v u).mp hvu)
    ((matching_mutation_nonzero B hB h k v w).mp hvw)

theorem matchingSupport_applyWord {n : Nat} (B : Matrix n)
    (hB : SkewSymmetric B) (h : MatchingSupport B) (w : List (Fin n)) :
    MatchingSupport (applyWord B w) := by
  induction w generalizing B with
  | nil => exact h
  | cons k ks ih =>
      exact ih (mutate B k) (mutation_preserves_skew B k hB)
        (matchingSupport_mutation B hB h k)

theorem matchingSupport_proper (B : Matrix 4) (hB : SkewSymmetric B)
    (h : MatchingSupport B) (p : CyclicOrder) : ProperClass B p := by
  intro v
  refine ⟨p, .same (fun _ _ _ => Iff.rfl), ?_⟩
  intro u w huv hvw
  have hs := hB u v
  have hne : B v u ≠ 0 := by omega
  have he := h v u w hne (by omega)
  subst w
  omega

/-- Every cyclic order on two disjoint weighted edges (or any submatching)
is totally proper, for every finite path and every valid mutation output. -/
theorem matchingSupport_totalProper (B : Matrix 4) (hB : SkewSymmetric B)
    (h : MatchingSupport B) (p : CyclicOrder) : TotalProper B p := by
  intro C q ht
  obtain ⟨w,hw⟩ := transport_reachable ht
  rw [hw]
  exact matchingSupport_proper _ (word_preserves_skew B w hB)
    (matchingSupport_applyWord B hB h w) q

end QuiverProofs.MAExistenceAlternative
