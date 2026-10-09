import Rank4Construction.MutationThreePolynomial
import Rank4Construction.ChamberSymmetryOrbitCompletion
import Rank4Formula.FormulaSubstitution

/-!
A fixed polynomial-sign formula for the one-step preimage of the 48 known
chambers under mutation at vertex 3, on a closed sign region.  The matrix
mutation occurs only in the correctness proof, never in the formula AST.
-/

namespace Rank4Construction
open Rank4Formula QuiverProofs

/-- Six polynomial terms for the upper entries after vertex-3 mutation in
the sign chamber. -/
def mutationThreeCoordTerm (k : Fin 6) : PolyTerm :=
  match k.val with
  | 0 => .add (.coord 0) (.mul (.coord 2) (.coord 4))
  | 1 => .add (.coord 1) (.mul (.coord 2) (.coord 5))
  | 2 => .neg (.coord 2)
  | 3 => .coord 3
  | 4 => .neg (.coord 4)
  | _ => .neg (.coord 5)

theorem mutationThreeCoordTerm_eval (k : Fin 6) (q : SixTuple) :
    (mutationThreeCoordTerm k).eval q =
      (mutationThreePolynomialTuple q k : Rat) := by
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [mutationThreeCoordTerm, mutationThreePolynomialTuple,
      PolyTerm.eval]

def mutationThreeSignSyntax : Formula :=
  .and (.lessEq (.coord 2) (.const 0))
    (.and (.lessEq (.const 0) (.coord 4))
      (.lessEq (.const 0) (.coord 5)))

theorem mutationThreeSignSyntax_eval (q : SixTuple) :
    mutationThreeSignSyntax.eval q = true ↔ MutationThreeSignChamber q := by
  simp [mutationThreeSignSyntax, MutationThreeSignChamber,
    Formula.eval, PolyTerm.eval]

/-- The polynomial pullback of the checked 48-chamber MA set. -/
def mutationThreePullbackMASetSyntax : Formula :=
  .and mutationThreeSignSyntax
    (fortyEightChamberMASetSyntax.subst mutationThreeCoordTerm)

def MutationThreePullbackInput (q : SixTuple) : Prop :=
  MutationThreeSignChamber q ∧
    FullSymmetryChamber (mutationThreePolynomialTuple q)

theorem mutationThreePullbackMASetSyntax_correct (q : SixTuple) :
    mutationThreePullbackMASetSyntax.eval q = true ↔
      MutationThreePullbackInput q ∧ MutationAcyclic (ofTuple q) := by
  have hsubst := Formula.subst_eval_of_target
    mutationThreeCoordTerm fortyEightChamberMASetSyntax q
    (mutationThreePolynomialTuple q)
    (fun k => mutationThreeCoordTerm_eval k q)
  change (mutationThreeSignSyntax.eval q &&
    (fortyEightChamberMASetSyntax.subst mutationThreeCoordTerm).eval q) = true ↔ _
  rw [Bool.and_eq_true, mutationThreeSignSyntax_eval, hsubst,
    fortyEightChamberMASetSyntax_correct_unconditional]
  constructor
  · rintro ⟨hsgn, hch, hma⟩
    exact ⟨⟨hsgn, hch⟩,
      (mutationThreePolynomialTuple_MA_iff q hsgn).mp hma⟩
  · rintro ⟨⟨hsgn, hch⟩, hma⟩
    exact ⟨hsgn, hch,
      (mutationThreePolynomialTuple_MA_iff q hsgn).mpr hma⟩

/-- A direct full-support witness reached by the one-step pullback. -/
def oneStepFullSupportWitness : SixTuple := fun i =>
  match i.val with
  | 0 => 1 | 1 => 1 | 2 => -1 | 3 => -1 | 4 => 1 | _ => 2

theorem oneStepFullSupportWitness_edges :
    ∀ i : Fin 6, oneStepFullSupportWitness i ≠ 0 := by decide

theorem oneStepFullSupportWitness_mutation :
    mutationThreePolynomialTuple oneStepFullSupportWitness =
      (fun i => match i.val with
        | 0 => 0 | 1 => -1 | 2 => 1 | 3 => -1 | 4 => -1 | _ => -2) := by
  funext i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

theorem oneStepFullSupportWitness_MA :
    MutationAcyclic (ofTuple oneStepFullSupportWitness) := by
  change MutationAcyclic (ofSix 1 1 (-1) (-1) 1 2)
  refine ⟨[0], ?_⟩
  refine ⟨(fun i => match i.val with
    | 0 => 2 | 1 => 1 | 2 => 0 | _ => 3), ?_⟩
  decide

theorem oneStepFullSupportWitness_in_pullback :
    MutationThreePullbackInput oneStepFullSupportWitness := by
  constructor
  · change (-1 : Int) ≤ 0 ∧ 0 ≤ (1 : Int) ∧ 0 ≤ (2 : Int)
    decide
  · rw [oneStepFullSupportWitness_mutation]
    refine ⟨Relabeling.identity 4, false, ?_⟩
    change (0 : Int) = 0 ∧ 0 < -(-1 : Int) ∧ 0 < (1 : Int) ∧
      0 < -(-1 : Int) ∧ 0 < -(-1 : Int) ∧ 0 < -(-2 : Int)
    decide

theorem oneStepFullSupportWitness_formula_true :
    mutationThreePullbackMASetSyntax.eval oneStepFullSupportWitness = true :=
  (mutationThreePullbackMASetSyntax_correct oneStepFullSupportWitness).mpr
    ⟨oneStepFullSupportWitness_in_pullback,
      oneStepFullSupportWitness_MA⟩

#print axioms mutationThreeCoordTerm_eval
#print axioms mutationThreePullbackMASetSyntax_correct
#print axioms oneStepFullSupportWitness_MA
#print axioms oneStepFullSupportWitness_formula_true

end Rank4Construction
