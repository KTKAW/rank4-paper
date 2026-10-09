import Rank4Formula.PolynomialTail
import Rank7Adversarial.PolynomialAlternation

/-!
An affine polynomial six-tuple with MA and NMA recurring arbitrarily far
along the same positive tail. Every finite rational polynomial-sign formula
is eventually constant on this line, so none represents MA on all inputs.
-/

namespace Rank4Round7.Coordinator

open Rank4Formula

noncomputable def alternatingPolynomial : Fin 6 → Polynomial Int := fun i =>
  match i.val with
  | 0 => Polynomial.C (-2)
  | 1 => Polynomial.C 2 + Polynomial.X
  | 2 => Polynomial.X
  | 3 => -Polynomial.X
  | 4 => Polynomial.C 2 - Polynomial.X
  | _ => 0

private theorem alternatingPolynomial_eval_adversarial (n : Nat) :
    polynomialTuple alternatingPolynomial n =
      Rank7Adversarial.alternatingLine n := by
  funext i
  fin_cases i <;>
    simp [polynomialTuple, alternatingPolynomial,
      Rank7Adversarial.alternatingLine]

theorem no_fixed_polynomial_sign_classifier : NoAlgebraicMAFormula := by
  apply noAlgebraicMAFormula_of_polynomial_recurrence alternatingPolynomial
  · intro N
    refine ⟨4 * N, by omega, ?_⟩
    rw [alternatingPolynomial_eval_adversarial]
    exact Rank7Adversarial.line_four_mul_MA N
  · intro N
    refine ⟨4 * N + 1, by omega, ?_⟩
    rw [alternatingPolynomial_eval_adversarial]
    exact Rank7Adversarial.line_four_mul_add_one_NMA N

theorem every_formula_fails (F : Formula) : ¬ RepresentsMA F := by
  intro h
  exact no_fixed_polynomial_sign_classifier ⟨F, h⟩

#print axioms no_fixed_polynomial_sign_classifier
#print axioms every_formula_fails

end Rank4Round7.Coordinator
