import QuiverProofs.ProperObstructionSoundness
import QuiverProofs.ProperMutationClass

/-! Interfaces for the two existence routes. These are proved reductions,
not inhabitants of the still-open acyclic existence proposition. In particular,
the invariant below must be supplied with actual initialization and preservation
proofs before it can establish the requested theorem. -/
namespace QuiverProofs.MAExistenceCoordinator
open ProperOrder ProperWiggle ProperMutation ProperObstructionSoundness

/-- The weaker acyclic starting statement, with no support or weight restrictions. -/
def AcyclicHasTotalProper4 : Prop :=
  ∀ B : Matrix 4, SkewSymmetric B → Acyclic B →
    ∃ p : CyclicOrder, TotalProper B p

/-- Any proved acyclic existence construction can be lifted back along the
reverse of an arbitrary acyclicizing word. -/
theorem existence_of_acyclic_total (hAcyclic : AcyclicHasTotalProper4) :
    MAHasTotalProper4 := by
  intro B hB hMA
  obtain ⟨w, hw⟩ := hMA
  have hC := word_preserves_skew B w hB
  obtain ⟨q, hq⟩ := hAcyclic _ hC hw
  obtain ⟨p, _, hp⟩ := totalProper_lifts_word _ hC q hq w.reverse
  rw [applyWord_undo] at hp
  exact ⟨p, hp⟩

/-- The requested MA theorem and its unrestricted acyclic existence input
are equivalent. This equivalence does not prove either side. -/
theorem ma_existence_iff_acyclic_existence :
    MAHasTotalProper4 ↔ AcyclicHasTotalProper4 := by
  constructor
  · intro h B hB hA
    exact h B hB (acyclic_is_mutationAcyclic B hA)
  · exact existence_of_acyclic_total

/-- In topological coordinates every arrow increases its position. -/
theorem topological_arrows_increase (B : Matrix 4) (hB : SkewSymmetric B)
    (p : CyclicOrder) (hp : Topological B p) :
    ∀ i j, 0 < B i j → p.invFun i < p.invFun j := by
  have upper : ∀ a b : Fin 4, a < b → 0 ≤ B (p.toFun a) (p.toFun b) := by
    intro a b hab
    have ha : a=0 ∨ a=1 ∨ a=2 ∨ a=3 := by omega
    have hb : b=0 ∨ b=1 ∨ b=2 ∨ b=3 := by omega
    rcases ha with rfl | rfl | rfl | rfl <;>
      rcases hb with rfl | rfl | rfl | rfl
    all_goals first | omega | exact hp.1 | exact hp.2.1 | exact hp.2.2.1 |
      exact hp.2.2.2.1 | exact hp.2.2.2.2.1 | exact hp.2.2.2.2.2
  intro i j hij
  by_cases hpos : p.invFun i < p.invFun j
  · exact hpos
  by_cases heq : p.invFun i = p.invFun j
  · have he : i=j := by
      have := congrArg p.toFun heq
      simpa only [p.right_inv] using this
    subst j
    have := hB i i
    omega
  have hrev : p.invFun j < p.invFun i := by omega
  have hnonneg := upper _ _ hrev
  simp only [p.right_inv] at hnonneg
  have := hB i j
  omega

/-- A relation on four vertices with an explicit strict ranking admits a
linear extension. The relation may have absent edges and disconnected parts. -/
theorem ranked_relation_has_linear_extension (R : Fin 4 → Fin 4 → Prop)
    (rank : Fin 4 → Nat) (hRank : ∀ i j, R i j → rank i < rank j) :
    ∃ p : CyclicOrder, ∀ i j, R i j → p.invFun i < p.invFun j := by
  classical
  let B : Matrix 4 := fun i j => if R i j then 1 else if R j i then -1 else 0
  have hB : SkewSymmetric B := by
    intro i j
    by_cases hij : R i j <;> by_cases hji : R j i
    · have := hRank i j hij
      have := hRank j i hji
      omega
    all_goals simp [B, hij, hji]
  have hA : Acyclic B := by
    refine ⟨rank, ?_⟩
    intro i j hij
    by_cases he : R i j
    · exact hRank i j he
    · simp [B, he] at hij
      split at hij <;> omega
  obtain ⟨p, hp⟩ := AcyclicTargets.acyclic_has_topological_coordinates B hB hA
  refine ⟨p, ?_⟩
  intro i j hij
  apply topological_arrows_increase B hB p hp i j
  simp [B, hij]

/-- Apply the linear-extension construction to a relation augmented with
all green-before-red constraints. A ranking of this augmented relation is
the precise remaining input; no ranking is asserted here. -/
theorem ranked_relation_has_color_block_extension
    (R : Fin 4 → Fin 4 → Prop) (green : Fin 4 → Bool)
    (rank : Fin 4 → Nat)
    (hRank : ∀ i j, (R i j ∨ (green i=true ∧ green j=false)) → rank i < rank j) :
    ∃ p : CyclicOrder,
      (∀ i j, R i j → p.invFun i < p.invFun j) ∧
      (∀ i j, green i=true → green j=false → p.invFun i < p.invFun j) := by
  obtain ⟨p, hp⟩ := ranked_relation_has_linear_extension
    (fun i j => R i j ∨ (green i=true ∧ green j=false)) rank hRank
  exact ⟨p, (fun i j h => hp i j (.inl h)),
    (fun i j hi hj => hp i j (.inr ⟨hi, hj⟩))⟩

/-- For a class-invariant certificate, it is enough to construct one certified
proper-mutation target per vertex: representative independence covers every
other admissible representative, cut and output. -/
theorem invariant_preserved_all_choices
    (I : Matrix 4 → CyclicOrder → Prop)
    (hWiggle : ∀ B, SkewSymmetric B → ∀ p q,
      WiggleEquivalent B p q → I B p → I B q)
    (hSelected : ∀ B, SkewSymmetric B → ∀ p, I B p → ∀ k,
      ∃ q, ProperMutation B p k q ∧ I (mutate B k) q)
    {B : Matrix 4} (hB : SkewSymmetric B) {p q : CyclicOrder} {k : Fin 4}
    (hp : I B p) (hm : ProperMutation B p k q) : I (mutate B k) q := by
  obtain ⟨r, hr, hIr⟩ := hSelected B hB p hp k
  have hw := ProperMutationRepresentativeChoice.properMutation_target_unique B hB hr hm
  exact hWiggle _ (mutation_preserves_skew B k hB) r q hw hIr

/-- Induction covers arbitrary-length Transport paths and every allowed
mutation vertex/output choice. No depth or edge-size bound occurs. -/
theorem invariant_transport
    (I : Matrix 4 → CyclicOrder → Prop)
    (hWiggle : ∀ B, SkewSymmetric B → ∀ p q,
      WiggleEquivalent B p q → I B p → I B q)
    (hSelected : ∀ B, SkewSymmetric B → ∀ p, I B p → ∀ k,
      ∃ q, ProperMutation B p k q ∧ I (mutate B k) q)
    {B C : Matrix 4} (hB : SkewSymmetric B) {p q : CyclicOrder}
    (hp : I B p) (ht : Transport B p C q) : I C q := by
  induction ht with
  | refl => exact hp
  | step ht hm ih =>
    exact invariant_preserved_all_choices I hWiggle hSelected
      (transport_skew hB ht) ih hm

/-- A genuinely constructed mutation-closed invariant implies total
properness. All three obligations are explicit hypotheses. -/
theorem totalProper_of_invariant
    (I : Matrix 4 → CyclicOrder → Prop)
    (hWiggle : ∀ B, SkewSymmetric B → ∀ p q,
      WiggleEquivalent B p q → I B p → I B q)
    (hSelected : ∀ B, SkewSymmetric B → ∀ p, I B p → ∀ k,
      ∃ q, ProperMutation B p k q ∧ I (mutate B k) q)
    (hProper : ∀ B, SkewSymmetric B → ∀ p, I B p → ProperClass B p)
    {B : Matrix 4} (hB : SkewSymmetric B) {p : CyclicOrder}
    (hp : I B p) : TotalProper B p := by
  intro C q ht
  exact hProper C (transport_skew hB ht) q
    (invariant_transport I hWiggle hSelected hB hp ht)

end QuiverProofs.MAExistenceCoordinator
