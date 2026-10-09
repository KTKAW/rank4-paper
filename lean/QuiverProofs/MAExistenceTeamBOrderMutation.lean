import QuiverProofs.MAExistenceInitialization
import QuiverProofs.MAExistenceCompanions

/-! Exact order and mutation prerequisites for the joint certificate project.
All matrices in this module retain the original vertex labels. A companion
written in the positions of two different orders cannot be compared entrywise
without undoing those permutations. No all-word or total-properness premise
is assumed here. Only this new module is owned by Team B.+-/
namespace QuiverProofs.MAExistenceTeamBOrderMutation
open ProperOrder ProperWiggle ProperMutation ProperObstructionSoundness
open MAExistenceLiterature MAExistenceCoordinator MAExistenceAlternative
open MAExistenceInitialization MAExistenceCompanions
open ProperMutationRepresentativeChoice Cosquare MutationCongruence

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- The upper unipotent companion in the original vertex labels. -/
def labeledUnipotent (B : Matrix 4) (p : CyclicOrder) : Matrix 4 := fun i j =>
  if i = j then 1 else if p.invFun i < p.invFun j then -B i j else 0

/-- Orient every support edge in the direction of the supplied linear order. -/
def orderOrientation (B : Matrix 4) (p : CyclicOrder) : Matrix 4 := fun i j =>
  if p.invFun i < p.invFun j then (B i j).natAbs else -((B i j).natAbs : Int)

private theorem invFun_ne (p : CyclicOrder) {i j : Fin 4} (hij : i ≠ j) :
    p.invFun i ≠ p.invFun j := by
  intro h
  apply hij
  simpa only [p.right_inv] using congrArg p.toFun h

theorem orderOrientation_skew (B : Matrix 4) (hB : SkewSymmetric B)
    (p : CyclicOrder) : SkewSymmetric (orderOrientation B p) := by
  intro i j
  by_cases hij : i = j
  · subst j
    have hz : B i i = 0 := by have := hB i i; omega
    simp [orderOrientation, hz]
  · have hne := invFun_ne p hij
    by_cases hp : p.invFun i < p.invFun j
    · have hn : ¬ p.invFun j < p.invFun i := by omega
      simp [orderOrientation, hp, hn, hB i j]
    · have hr : p.invFun j < p.invFun i := by omega
      simp [orderOrientation, hp, hr, hB i j]

theorem orderOrientation_zero (B : Matrix 4) (p : CyclicOrder) (i j : Fin 4) :
    orderOrientation B p i j = 0 ↔ B i j = 0 := by
  unfold orderOrientation
  split <;> simp

theorem orderOrientation_arrow (B : Matrix 4) (p : CyclicOrder) (i j : Fin 4)
    (h : 0 < orderOrientation B p i j) :
    p.invFun i < p.invFun j ∧ B i j ≠ 0 := by
  by_cases hp : p.invFun i < p.invFun j
  · refine ⟨hp, ?_⟩
    intro hz
    simp [orderOrientation, hz] at h
  · have hn : 0 ≤ ((B i j).natAbs : Int) := by omega
    simp only [orderOrientation, hp, if_false] at h
    omega

/-- Exact equality determines the relative order of every support edge. -/
theorem labeledUnipotent_eq_orders_support (B : Matrix 4) (p q : CyclicOrder)
    (he : labeledUnipotent B p = labeledUnipotent B q)
    (i j : Fin 4) (hij : i ≠ j) (hne : B i j ≠ 0) :
    p.invFun i < p.invFun j ↔ q.invFun i < q.invFun j := by
  have h := congrFun (congrFun he i) j
  by_cases hp : p.invFun i < p.invFun j <;>
    by_cases hq : q.invFun i < q.invFun j <;>
    simp [labeledUnipotent, hij, hp, hq] at h ⊢
  all_goals omega

private theorem topological_of_increasing (B : Matrix 4) (hB : SkewSymmetric B)
    (p : CyclicOrder)
    (h : ∀ i j, 0 < B i j → p.invFun i < p.invFun j) : Topological B p := by
  have upper : ∀ a b : Fin 4, a < b → 0 ≤ B (p.toFun a) (p.toFun b) := by
    intro a b hab
    by_cases hn : 0 ≤ B (p.toFun a) (p.toFun b)
    · exact hn
    · have hr : 0 < B (p.toFun b) (p.toFun a) := by
        have := hB (p.toFun a) (p.toFun b)
        omega
      have hh := h _ _ hr
      simp only [p.left_inv] at hh
      omega
  exact ⟨upper 0 1 (by decide), upper 0 2 (by decide),
    upper 0 3 (by decide), upper 1 2 (by decide),
    upper 1 3 (by decide), upper 2 3 (by decide)⟩

/-- Equality in vertex labels, stronger than mere integral congruence, identifies
the actual wiggle class. Absent edges and disconnected support are included. -/
theorem labeledUnipotent_eq_wiggle (B : Matrix 4) (hB : SkewSymmetric B)
    (p q : CyclicOrder) (he : labeledUnipotent B p = labeledUnipotent B q) :
    WiggleEquivalent B p q := by
  let D := orderOrientation B p
  have hD : SkewSymmetric D := orderOrientation_skew B hB p
  have hp : Topological D p := by
    apply topological_of_increasing D hD p
    intro i j hij
    exact (orderOrientation_arrow B p i j hij).1
  have hq : Topological D q := by
    apply topological_of_increasing D hD q
    intro i j hij
    obtain ⟨hij', hne⟩ := orderOrientation_arrow B p i j hij
    have hdist : i ≠ j := by intro hh; subst j; omega
    exact (labeledUnipotent_eq_orders_support B p q he i j hdist hne).mp hij'
  exact wiggle_zero_transfer D B
    (fun i j hz => (orderOrientation_zero B p i j).mp hz)
    (topological_orders_wiggle D hD p q hp hq)

/-- The coefficient basis is the transpose of the red exchange basis, or
the transpose of the basis for the opposite exchange matrix when green. -/
theorem coefficientBasis_transpose_basisChange (B : Matrix 4)
    (hB : SkewSymmetric B) (green : Colors) (k : Fin 4) :
    transpose (coefficientBasis B green k) =
      basisChange (if green k then reverse B else B) k := by
  funext i j
  have hs := hB i k
  cases hk : green k <;>
    simp [transpose, coefficientBasis, pivotWeight, basisChange, hk, reverse]
  all_goals split <;> split <;> simp_all <;> omega

/-- Exchange and coefficient-derived companion updates use the same chosen
basis in both pivot colors. There is no sign-coherence premise in this identity. -/
theorem mutation_coefficientBasis_congruence (B : Matrix 4)
    (hB : SkewSymmetric B) (green : Colors) (k : Fin 4) :
    mutate B k = mul (mul (transpose (coefficientBasis B green k)) B)
      (coefficientBasis B green k) := by
  have hE := coefficientBasis_transpose_basisChange B hB green k
  have hE' : coefficientBasis B green k =
      transpose (basisChange (if green k then reverse B else B) k) :=
    congrArg transpose hE
  cases hk : green k
  · simp only [hk, Bool.false_eq_true, if_false] at hE
    simp only [hk, Bool.false_eq_true, if_false] at hE'
    rw [hE, hE']
    exact mutation_congruence B k hB
  · simp only [hk, if_true] at hE
    simp only [hk, if_true] at hE'
    have h := mutation_congruence (reverse B) k (reverse_skew B hB)
    rw [mutate_reverse] at h
    rw [hE, hE']
    funext i j
    have he := congrFun (congrFun h i) j
    simp only [reverse, mul, transpose] at he ⊢
    grind

/-- A compatible order realizes the actual supplied symmetric companion in
vertex labels. The factor two avoids any division or parity assumption. -/
theorem compatible_labeledUnipotent (B A : Matrix 4) (hB : SkewSymmetric B)
    (hA : QuasiCartanCompanion B A) (green : Colors)
    (hs : ArrowSigns B A green) (k : Fin 4) (p : CyclicOrder)
    (hp : Compatible B green k p) (i j : Fin 4) :
    2 * labeledUnipotent B p i j = A i j - B i j := by
  by_cases hij : i = j
  · subst j
    have hz : B i i = 0 := by have := hB i i; omega
    simp [labeledUnipotent, hA.2.1 i, hz]
  · have habs := hA.2.2 i j hij
    by_cases hz : B i j = 0
    · have ha : A i j = 0 := by
        have := Int.natAbs_eq_zero.mp (habs.trans (by simp [hz]))
        exact this
      simp [labeledUnipotent, hij, hz, ha]
    · rcases Int.natAbs_eq_natAbs_iff.mp habs with ha | ha
      · have horder : p.invFun j < p.invFun i := by
          by_cases hpos : 0 < B i j
          · have hc := (hs i j hpos).mp (by omega)
            exact hp j i (Or.inr (Or.inl ⟨hpos, hc.1, hc.2⟩))
          · have hrev : 0 < B j i := by have := hB i j; omega
            have hn : ¬ (green j = false ∧ green i = true) := by
              intro hc
              have hh := (hs j i hrev).mpr hc
              rw [←hA.1 i j] at hh
              omega
            exact hp j i (Or.inl ⟨hrev, hn⟩)
        have hn : ¬ p.invFun i < p.invFun j := by omega
        simp [labeledUnipotent, hij, hn, ha]
      · have horder : p.invFun i < p.invFun j := by
          by_cases hpos : 0 < B i j
          · have hn : ¬ (green i = false ∧ green j = true) := by
              intro hc
              have hh := (hs i j hpos).mpr hc
              omega
            exact hp i j (Or.inl ⟨hpos, hn⟩)
          · have hrev : 0 < B j i := by have := hB i j; omega
            have hapos : 0 < A j i := by rw [←hA.1 i j]; omega
            have hc := (hs j i hrev).mp hapos
            exact hp i j (Or.inr (Or.inl ⟨hrev, hc.1, hc.2⟩))
        simp [labeledUnipotent, hij, horder]
        omega

/-- An actual next compatible order realizes precisely the chosen simultaneous
unipotent update. Current and next quasi-Cartan and arrow-sign data are explicit;
this algebraic identity does not assert any proper mutation or all-word claim. -/
theorem compatible_labeledUnipotent_mutation
    (B A : Matrix 4) (hB : SkewSymmetric B) (green green' : Colors)
    (k l : Fin 4) (p q : CyclicOrder)
    (hA : QuasiCartanCompanion B A) (hs : ArrowSigns B A green)
    (hA' : QuasiCartanCompanion (mutate B k) (localMutation B A green k))
    (hs' : ArrowSigns (mutate B k) (localMutation B A green k) green')
    (hp : Compatible B green k p)
    (hq : Compatible (mutate B k) green' l q) :
    labeledUnipotent (mutate B k) q =
      mul (mul (transpose (coefficientBasis B green k)) (labeledUnipotent B p))
        (coefficientBasis B green k) := by
  have hcur := compatible_labeledUnipotent B A hB hA green hs k p hp
  have hnext := compatible_labeledUnipotent (mutate B k)
    (localMutation B A green k) (mutation_preserves_skew B k hB)
    hA' green' hs' l q hq
  have hmat := localMutation_matrix B A green k
  have hex := mutation_coefficientBasis_congruence B hB green k
  funext i j
  have hn := hnext i j
  have ha := congrFun (congrFun hmat i) j
  have hb := congrFun (congrFun hex i) j
  have h00 := hcur 0 0; have h01 := hcur 0 1
  have h02 := hcur 0 2; have h03 := hcur 0 3
  have h10 := hcur 1 0; have h11 := hcur 1 1
  have h12 := hcur 1 2; have h13 := hcur 1 3
  have h20 := hcur 2 0; have h21 := hcur 2 1
  have h22 := hcur 2 2; have h23 := hcur 2 3
  have h30 := hcur 3 0; have h31 := hcur 3 1
  have h32 := hcur 3 2; have h33 := hcur 3 3
  simp only [mul] at ha hb ⊢
  grind

end QuiverProofs.MAExistenceTeamBOrderMutation
