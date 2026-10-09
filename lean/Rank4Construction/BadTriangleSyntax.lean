import Rank4Formula.FormulaLanguage
import Rank4Construction.DisconnectedFormula

/-!
# Explicit membership of the disconnected triangle rule in the formula syntax

The formula below is constructed only from rational constants, the six input
coordinates, polynomial operations, order tests, and finite Boolean cases.
The evaluator theorem links it to the independently checked integer predicate
`BadTriangleSix`.
-/

namespace Rank4Construction
open Rank4Formula

private def andFour (A B C D : Formula) : Formula :=
  .and A (.and B (.and C D))

private def andThree (A B C : Formula) : Formula :=
  .and A (.and B C)

private def eqZero (i : Fin 6) : Formula :=
  .equal (.coord i) (.const 0)

/-- An AST term for the seven support cuts. -/
def disconnectedSixSyntax : Formula :=
  .or (andThree (eqZero 0) (eqZero 1) (eqZero 2))
    (.or (andThree (eqZero 0) (eqZero 3) (eqZero 4))
      (.or (andThree (eqZero 1) (eqZero 3) (eqZero 5))
        (.or (andThree (eqZero 2) (eqZero 4) (eqZero 5))
          (.or (andFour (eqZero 1) (eqZero 2) (eqZero 3) (eqZero 4))
            (.or (andFour (eqZero 0) (eqZero 2) (eqZero 3) (eqZero 5))
              (andFour (eqZero 0) (eqZero 1) (eqZero 4) (eqZero 5)))))))

theorem disconnectedSixSyntax_eval (v : SixTuple) :
    disconnectedSixSyntax.eval v = true ↔
      DisconnectedSix (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by
  simp [disconnectedSixSyntax, eqZero, andThree, andFour,
    Formula.eval, PolyTerm.eval, DisconnectedSix,
    Bool.and_eq_true, Bool.or_eq_true,
    Rat.intCast_eq_zero_iff]

private def geTwo (x : PolyTerm) : Formula :=
  .lessEq (.const 2) x

private def markovTerm (x y z : PolyTerm) : PolyTerm :=
  .add (.add (.add (.mul x x) (.mul y y)) (.mul z z))
    (.neg (.mul (.mul x y) z))

private def triangleSyntax (x y z : PolyTerm) : Formula :=
  .or
    (andFour (geTwo x) (geTwo y) (geTwo z)
      (.lessEq (markovTerm x y z) (.const 4)))
    (andFour (geTwo (.neg x)) (geTwo (.neg y)) (geTwo (.neg z))
      (.lessEq (markovTerm (.neg x) (.neg y) (.neg z)) (.const 4)))

/-- The four signed triangle tests as one value of the finite algebraic
formula syntax, with no mutation or classifier operation. -/
def badTriangleSixSyntax : Formula :=
  let a := PolyTerm.coord 0
  let b := PolyTerm.coord 1
  let c := PolyTerm.coord 2
  let d := PolyTerm.coord 3
  let e := PolyTerm.coord 4
  let f := PolyTerm.coord 5
  .or (triangleSyntax a d (.neg b))
    (.or (triangleSyntax a e (.neg c))
      (.or (triangleSyntax b f (.neg c))
        (triangleSyntax d f (.neg e))))

private def BadTriangleRat (x y z : Rat) : Prop :=
  ((2 : Rat) ≤ x ∧ (2 : Rat) ≤ y ∧ (2 : Rat) ≤ z ∧
    x*x + y*y + z*z + -(x*y*z) ≤ 4) ∨
  ((2 : Rat) ≤ -x ∧ (2 : Rat) ≤ -y ∧ (2 : Rat) ≤ -z ∧
    (-x)*(-x) + (-y)*(-y) + (-z)*(-z) + -((-x)*(-y)*(-z)) ≤ 4)

private theorem triangleSyntax_eval (p q r : PolyTerm) (v : SixTuple) :
    (triangleSyntax p q r).eval v = true ↔
      BadTriangleRat (p.eval v) (q.eval v) (r.eval v) := by
  simp [triangleSyntax, andFour, geTwo, markovTerm, BadTriangleRat,
    Formula.eval, PolyTerm.eval, Bool.and_eq_true, Bool.or_eq_true]

private theorem markov_cast_le_four (x y z : Int) :
    (x : Rat)*(x : Rat) + (y : Rat)*(y : Rat) + (z : Rat)*(z : Rat) +
      -((x : Rat)*(y : Rat)*(z : Rat)) ≤ 4 ↔
    x^2 + y^2 + z^2 - x*y*z ≤ 4 := by
  simpa [Int.pow_succ, Rat.pow_succ, Int.sub_eq_add_neg,
    Rat.sub_eq_add_neg] using
    (Rat.intCast_le_intCast :
      (((x^2 + y^2 + z^2 - x*y*z : Int) : Rat) ≤ (4 : Rat)) ↔
        x^2 + y^2 + z^2 - x*y*z ≤ 4)

private theorem two_le_cast_iff (x : Int) :
    (2 : Rat) ≤ (x : Rat) ↔ 2 ≤ x :=
  Rat.intCast_le_intCast

private theorem badTriangleRat_cast_iff (x y z : Int) :
    BadTriangleRat (x : Rat) (y : Rat) (z : Rat) ↔ BadTriangle x y z := by
  unfold BadTriangleRat BadTriangle
  simp only [← Rat.intCast_neg, two_le_cast_iff, markov_cast_le_four]

theorem badTriangleSixSyntax_eval (v : SixTuple) :
    badTriangleSixSyntax.eval v = true ↔
      BadTriangleSix (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by
  simp only [badTriangleSixSyntax, Formula.eval, Bool.or_eq_true,
    triangleSyntax_eval, PolyTerm.eval, ← Rat.intCast_neg,
    badTriangleRat_cast_iff, BadTriangleSix]

/-- A single formula term for the MA half of the disconnected rule. -/
def disconnectedMASyntax : Formula := .not badTriangleSixSyntax

/-- A global formula whose true set is exactly the disconnected MA inputs. -/
def disconnectedMASetSyntax : Formula :=
  .and disconnectedSixSyntax disconnectedMASyntax

theorem disconnectedMASyntax_correct (v : SixTuple)
    (hcut : DisconnectedSix (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) :
    disconnectedMASyntax.eval v = true ↔
      QuiverProofs.MutationAcyclic (ofTuple v) := by
  have hbad := badTriangleSixSyntax_eval v
  have hma := disconnected_MA_formula
    (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) hcut
  change (!badTriangleSixSyntax.eval v) = true ↔
    QuiverProofs.MutationAcyclic
      (QuiverProofs.ofSix (v 0) (v 1) (v 2) (v 3) (v 4) (v 5))
  constructor
  · intro h
    apply hma.mpr
    intro hb
    have ht := hbad.mpr hb
    simp [ht] at h
  · intro h
    have hn := hma.mp h
    have hbf : badTriangleSixSyntax.eval v = false := by
      cases hval : badTriangleSixSyntax.eval v with
      | false => rfl
      | true => exact False.elim (hn (hbad.mp hval))
    simp [hbf]

theorem disconnectedMASetSyntax_correct (v : SixTuple) :
    disconnectedMASetSyntax.eval v = true ↔
      DisconnectedSix (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) ∧
        QuiverProofs.MutationAcyclic (ofTuple v) := by
  change (disconnectedSixSyntax.eval v && disconnectedMASyntax.eval v) = true ↔ _
  rw [Bool.and_eq_true]
  constructor
  · rintro ⟨hcut, hma⟩
    have hc := (disconnectedSixSyntax_eval v).mp hcut
    exact ⟨hc, (disconnectedMASyntax_correct v hc).mp hma⟩
  · rintro ⟨hc, hma⟩
    exact ⟨(disconnectedSixSyntax_eval v).mpr hc,
      (disconnectedMASyntax_correct v hc).mpr hma⟩

#print axioms badTriangleSixSyntax_eval
#print axioms disconnectedMASyntax_correct
#print axioms disconnectedMASetSyntax_correct

end Rank4Construction
