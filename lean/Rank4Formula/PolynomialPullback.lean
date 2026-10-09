import Rank4Formula.FormulaLanguage
import Mathlib.Algebra.Polynomial.Roots

/-! Every rational polynomial expression stays polynomial along an integer
polynomially parameterized six-tuple. -/

namespace Rank4Formula

noncomputable def PolyTerm.onPolynomialFamily
    (q : Fin 6 → Polynomial Rat) : PolyTerm → Polynomial Rat
  | .const c => Polynomial.C c
  | .coord i => q i
  | .neg p => -(p.onPolynomialFamily q)
  | .add p r => p.onPolynomialFamily q + r.onPolynomialFamily q
  | .mul p r => p.onPolynomialFamily q * r.onPolynomialFamily q

def polynomialTuple (q : Fin 6 → Polynomial Int) (n : Nat) : SixTuple :=
  fun i => (q i).eval (n : Int)

noncomputable def rationalFamily (q : Fin 6 → Polynomial Int) :
    Fin 6 → Polynomial Rat := fun i => (q i).map (Int.castRingHom Rat)

theorem PolyTerm.eval_polynomialTuple (p : PolyTerm)
    (q : Fin 6 → Polynomial Int) (n : Nat) :
    p.eval (polynomialTuple q n) =
      (p.onPolynomialFamily (rationalFamily q)).eval (n : Rat) := by
  induction p with
  | const c => simp [PolyTerm.eval, PolyTerm.onPolynomialFamily]
  | coord i => simp [PolyTerm.eval, PolyTerm.onPolynomialFamily,
      polynomialTuple, rationalFamily]
  | neg p ih => simp [PolyTerm.eval, PolyTerm.onPolynomialFamily, ih]
  | add p r ihp ihr => simp [PolyTerm.eval, PolyTerm.onPolynomialFamily, ihp, ihr]
  | mul p r ihp ihr => simp [PolyTerm.eval, PolyTerm.onPolynomialFamily, ihp, ihr]

#print axioms PolyTerm.eval_polynomialTuple

end Rank4Formula
