import QuiverProofs.Mutation

/-!
The fixed finite rational semialgebraic language for the rank-four question.
There are six *integer* inputs, in upper-triangle order 01,02,03,12,13,23.
The only arithmetic leaves are rational constants and those six coordinates;
the only term formers are negation, addition, and multiplication.  Thus every
term denotes a polynomial over ℚ, with no mutation operation or oracle.
Formulae are finite Boolean combinations of polynomial equality and order.
-/

namespace Rank4Formula

abbrev SixTuple := Fin 6 → Int

inductive PolyTerm where
  | const : Rat → PolyTerm
  | coord : Fin 6 → PolyTerm
  | neg : PolyTerm → PolyTerm
  | add : PolyTerm → PolyTerm → PolyTerm
  | mul : PolyTerm → PolyTerm → PolyTerm
  deriving Repr

def PolyTerm.eval : PolyTerm → SixTuple → Rat
  | .const c, _ => c
  | .coord i, x => x i
  | .neg p, x => -(p.eval x)
  | .add p q, x => p.eval x + q.eval x
  | .mul p q, x => p.eval x * q.eval x

inductive Formula where
  | equal : PolyTerm → PolyTerm → Formula
  | lessEq : PolyTerm → PolyTerm → Formula
  | not : Formula → Formula
  | and : Formula → Formula → Formula
  | or : Formula → Formula → Formula
  deriving Repr

def Formula.eval : Formula → SixTuple → Bool
  | .equal p q, x => decide (p.eval x = q.eval x)
  | .lessEq p q, x => decide (p.eval x ≤ q.eval x)
  | .not P, x => !(P.eval x)
  | .and P Q, x => P.eval x && Q.eval x
  | .or P Q, x => P.eval x || Q.eval x

def ofTuple (x : SixTuple) : QuiverProofs.Matrix 4 :=
  QuiverProofs.ofSix (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

/-- The exact all-integer target. `Formula.eval` makes no mutation calls. -/
def RepresentsMA (F : Formula) : Prop :=
  ∀ x : SixTuple,
    F.eval x = true ↔ QuiverProofs.MutationAcyclic (ofTuple x)

/-- Exact positive research target; no inhabitant is asserted here. -/
def ExistsAlgebraicMAFormula : Prop := ∃ F : Formula, RepresentsMA F

/-- Exact negative research target; no proof is asserted here. -/
def NoAlgebraicMAFormula : Prop := ¬ ExistsAlgebraicMAFormula

/-- The unrestricted set-theoretic characteristic function, included to fix
the logical baseline. It is not a member of the finite formula language. -/
noncomputable def maCharacteristic (x : SixTuple) : Bool :=
  by
    classical
    exact if QuiverProofs.MutationAcyclic (ofTuple x) then true else false

theorem maCharacteristic_spec (x : SixTuple) :
    maCharacteristic x = true ↔ QuiverProofs.MutationAcyclic (ofTuple x) := by
  unfold maCharacteristic
  by_cases h : QuiverProofs.MutationAcyclic (ofTuple x) <;> simp [h]

#print axioms maCharacteristic_spec

end Rank4Formula
