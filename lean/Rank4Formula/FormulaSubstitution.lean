import Rank4Formula.FormulaLanguage

/-!
Syntactic polynomial substitution for the fixed rank-four formula language.
If six polynomial terms evaluate to the coordinates of another integer input,
substitution in a formula agrees exactly with evaluation at that input.
The substitution output remains a finite polynomial-sign `Formula`.
-/

namespace Rank4Formula

def PolyTerm.subst (σ : Fin 6 → PolyTerm) : PolyTerm → PolyTerm
  | .const c => .const c
  | .coord i => σ i
  | .neg p => .neg (p.subst σ)
  | .add p r => .add (p.subst σ) (r.subst σ)
  | .mul p r => .mul (p.subst σ) (r.subst σ)

theorem PolyTerm.subst_eval_of_target
    (σ : Fin 6 → PolyTerm) (p : PolyTerm) (x y : SixTuple)
    (hσ : ∀ i, (σ i).eval x = (y i : Rat)) :
    (p.subst σ).eval x = p.eval y := by
  induction p with
  | const c => rfl
  | coord i => exact hσ i
  | neg p ih => simp [PolyTerm.subst, PolyTerm.eval, ih]
  | add p r ihp ihr => simp [PolyTerm.subst, PolyTerm.eval, ihp, ihr]
  | mul p r ihp ihr => simp [PolyTerm.subst, PolyTerm.eval, ihp, ihr]

def Formula.subst (σ : Fin 6 → PolyTerm) : Formula → Formula
  | .equal p r => .equal (p.subst σ) (r.subst σ)
  | .lessEq p r => .lessEq (p.subst σ) (r.subst σ)
  | .not F => .not (F.subst σ)
  | .and F G => .and (F.subst σ) (G.subst σ)
  | .or F G => .or (F.subst σ) (G.subst σ)

theorem Formula.subst_eval_of_target
    (σ : Fin 6 → PolyTerm) (F : Formula) (x y : SixTuple)
    (hσ : ∀ i, (σ i).eval x = (y i : Rat)) :
    (F.subst σ).eval x = F.eval y := by
  induction F with
  | equal p r =>
      simp [Formula.subst, Formula.eval,
        PolyTerm.subst_eval_of_target σ p x y hσ,
        PolyTerm.subst_eval_of_target σ r x y hσ]
  | lessEq p r =>
      simp [Formula.subst, Formula.eval,
        PolyTerm.subst_eval_of_target σ p x y hσ,
        PolyTerm.subst_eval_of_target σ r x y hσ]
  | not F ih => simp [Formula.subst, Formula.eval, ih]
  | and F G ihF ihG => simp [Formula.subst, Formula.eval, ihF, ihG]
  | or F G ihF ihG => simp [Formula.subst, Formula.eval, ihF, ihG]

#print axioms PolyTerm.subst_eval_of_target
#print axioms Formula.subst_eval_of_target

end Rank4Formula
