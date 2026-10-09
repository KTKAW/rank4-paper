import Rank4Formula.PolynomialPullback
import Mathlib.Analysis.Polynomial.Basic

/-!
Every formula in the full polynomial equality-and-order language stabilizes on
the positive integer tail of every polynomially parameterized six-tuple.
-/

open Filter Polynomial

namespace Rank4Formula

private theorem polynomial_le_zero_eventually (P : Polynomial Rat) :
    ∃ b : Bool, ∀ᶠ n : Nat in atTop, decide (P.eval (n : Rat) ≤ 0) = b := by
  by_cases hdeg : P.degree ≤ 0
  · refine ⟨decide (P.coeff 0 ≤ 0), Filter.Eventually.of_forall ?_⟩
    intro n
    rw [P.eq_C_of_degree_le_zero hdeg]
    simp
  · have hpos : 0 < P.degree := lt_of_not_ge hdeg
    rcases le_total 0 P.leadingCoeff with hlc | hlc
    · refine ⟨false, ?_⟩
      have ht : Tendsto (fun x : Rat => P.eval x) atTop atTop :=
        P.tendsto_atTop_of_leadingCoeff_nonneg hpos hlc
      have hnat : Tendsto (fun n : Nat => P.eval (n : Rat)) atTop atTop :=
        ht.comp tendsto_natCast_atTop_atTop
      filter_upwards [hnat.eventually_gt_atTop 0] with n hn
      simp [not_le.mpr hn]
    · refine ⟨true, ?_⟩
      have ht : Tendsto (fun x : Rat => P.eval x) atTop atBot :=
        P.tendsto_atBot_of_leadingCoeff_nonpos hpos hlc
      have hnat : Tendsto (fun n : Nat => P.eval (n : Rat)) atTop atBot :=
        ht.comp tendsto_natCast_atTop_atTop
      filter_upwards [hnat.eventually_lt_atBot 0] with n hn
      simp [hn.le]

private theorem polynomial_eq_zero_eventually (P : Polynomial Rat) :
    ∃ b : Bool, ∀ᶠ n : Nat in atTop, decide (P.eval (n : Rat) = 0) = b := by
  by_cases hP : P = 0
  · refine ⟨true, Filter.Eventually.of_forall ?_⟩
    intro n
    simp [hP]
  · refine ⟨false, ?_⟩
    have hno : ∀ᶠ n : Nat in atTop, ¬ P.IsRoot (n : Rat) :=
      (tendsto_natCast_atTop_atTop (R := Rat)).eventually (P.eventually_no_roots hP)
    filter_upwards [hno] with n hn
    simpa [Polynomial.IsRoot] using hn

private theorem equal_atom_eventually (p r : PolyTerm)
    (q : Fin 6 → Polynomial Int) :
    ∃ b : Bool, ∀ᶠ n : Nat in atTop,
      (Formula.equal p r).eval (polynomialTuple q n) = b := by
  obtain ⟨b, hb⟩ := polynomial_eq_zero_eventually
    (p.onPolynomialFamily (rationalFamily q) -
      r.onPolynomialFamily (rationalFamily q))
  refine ⟨b, hb.mono ?_⟩
  intro n hn
  simpa [Formula.eval, Polynomial.eval_sub, p.eval_polynomialTuple,
    r.eval_polynomialTuple, sub_eq_zero] using hn

private theorem lessEq_atom_eventually (p r : PolyTerm)
    (q : Fin 6 → Polynomial Int) :
    ∃ b : Bool, ∀ᶠ n : Nat in atTop,
      (Formula.lessEq p r).eval (polynomialTuple q n) = b := by
  obtain ⟨b, hb⟩ := polynomial_le_zero_eventually
    (p.onPolynomialFamily (rationalFamily q) -
      r.onPolynomialFamily (rationalFamily q))
  refine ⟨b, hb.mono ?_⟩
  intro n hn
  simpa [Formula.eval, Polynomial.eval_sub, p.eval_polynomialTuple,
    r.eval_polynomialTuple, sub_nonpos] using hn

theorem Formula.eventually_constant_on_polynomialTuple (F : Formula)
    (q : Fin 6 → Polynomial Int) :
    ∃ b : Bool, ∀ᶠ n : Nat in atTop, F.eval (polynomialTuple q n) = b := by
  induction F with
  | equal p r => exact equal_atom_eventually p r q
  | lessEq p r => exact lessEq_atom_eventually p r q
  | not P ih =>
      obtain ⟨b, hb⟩ := ih
      refine ⟨!b, hb.mono ?_⟩
      intro n hn
      simp [Formula.eval, hn]
  | and P Q ihp ihq =>
      obtain ⟨bp, hp⟩ := ihp
      obtain ⟨bq, hq⟩ := ihq
      refine ⟨bp && bq, (hp.and hq).mono ?_⟩
      intro n hn
      simp [Formula.eval, hn.1, hn.2]
  | or P Q ihp ihq =>
      obtain ⟨bp, hp⟩ := ihp
      obtain ⟨bq, hq⟩ := ihq
      refine ⟨bp || bq, (hp.and hq).mono ?_⟩
      intro n hn
      simp [Formula.eval, hn.1, hn.2]

/-- A polynomial six-tuple with both labels recurring arbitrarily far along
the *same positive tail* rules out every finite polynomial-sign formula.
The recurrence hypotheses are not established for mutation-acyclicity here. -/
theorem noAlgebraicMAFormula_of_polynomial_recurrence
    (q : Fin 6 → Polynomial Int)
    (hma : ∀ N : Nat, ∃ n : Nat, N ≤ n ∧
      QuiverProofs.MutationAcyclic (ofTuple (polynomialTuple q n)))
    (hnma : ∀ N : Nat, ∃ n : Nat, N ≤ n ∧
      ¬ QuiverProofs.MutationAcyclic (ofTuple (polynomialTuple q n))) :
    NoAlgebraicMAFormula := by
  intro ⟨F, hrep⟩
  obtain ⟨b, hconst⟩ := F.eventually_constant_on_polynomialTuple q
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hconst
  cases b with
  | false =>
      obtain ⟨n, hn, hma_n⟩ := hma N
      have hf : F.eval (polynomialTuple q n) = true :=
        (hrep (polynomialTuple q n)).2 hma_n
      simp [hN n hn] at hf
  | true =>
      obtain ⟨n, hn, hnma_n⟩ := hnma N
      have hf : F.eval (polynomialTuple q n) = true := hN n hn
      exact hnma_n ((hrep (polynomialTuple q n)).1 hf)

#print axioms Formula.eventually_constant_on_polynomialTuple
#print axioms noAlgebraicMAFormula_of_polynomial_recurrence

end Rank4Formula
