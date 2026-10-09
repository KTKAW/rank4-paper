import Rank4Formula.FormulaLanguage
import QuiverProofs.ChamberProperness

/-!
# Polynomial-sign syntax for the positive five-parameter chamber

Coordinates follow the order `(a,b,c,d,e,f)` in `QuiverProofs.ofSix`.
The formula is the single polynomial inequality `(-b)*c ≤ -f`. Its
correctness is asserted only on the chamber `a=0`, `-b,c,-d,-e,-f>0`,
and retains the archive's explicit `MAHasTotalProper4` premise.
-/

namespace Rank4Construction
open Rank4Formula QuiverProofs

/-- The positive chamber in the six original integer coordinates. -/
def FiveParameterChamber (q : SixTuple) : Prop :=
  q 0 = 0 ∧ 0 < -(q 1) ∧ 0 < q 2 ∧ 0 < -(q 3) ∧
    0 < -(q 4) ∧ 0 < -(q 5)

/-- A finite polynomial comparison in the prescribed formula language. -/
def fiveParameterThresholdSyntax : Formula :=
  .lessEq (.mul (.neg (.coord 1)) (.coord 2)) (.neg (.coord 5))

private def positiveTerm (t : PolyTerm) : Formula :=
  .not (.lessEq t (.const 0))

/-- A syntax-level test for the domain of the five-parameter criterion. -/
def fiveParameterChamberSyntax : Formula :=
  .and (.equal (.coord 0) (.const 0))
    (.and (positiveTerm (.neg (.coord 1)))
      (.and (positiveTerm (.coord 2))
        (.and (positiveTerm (.neg (.coord 3)))
          (.and (positiveTerm (.neg (.coord 4)))
            (positiveTerm (.neg (.coord 5)))))))

private theorem positiveCast_prop (x : Int) :
    (¬ (x : Rat) ≤ 0) ↔ 0 < x := by
  have hcast : ((x : Rat) ≤ (0 : Rat)) ↔ x ≤ 0 :=
    Rat.intCast_le_intCast
  rw [hcast]
  omega

theorem fiveParameterChamberSyntax_eval (q : SixTuple) :
    fiveParameterChamberSyntax.eval q = true ↔
      FiveParameterChamber q := by
  simp only [fiveParameterChamberSyntax, positiveTerm,
    Formula.eval, PolyTerm.eval, Bool.and_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
  simp only [← Rat.intCast_neg, Rat.intCast_eq_zero_iff,
    positiveCast_prop, FiveParameterChamber]

theorem fiveParameterThresholdSyntax_eval (q : SixTuple) :
    fiveParameterThresholdSyntax.eval q = true ↔
      -(q 1) * q 2 ≤ -(q 5) := by
  have hcast := (Rat.intCast_le_intCast :
    (((-(q 1) * q 2 : Int) : Rat) ≤ ((-(q 5) : Int) : Rat)) ↔
      -(q 1) * q 2 ≤ -(q 5))
  simpa [fiveParameterThresholdSyntax, Formula.eval, PolyTerm.eval,
    Rat.intCast_neg, Rat.intCast_mul] using hcast

theorem fiveParameterThresholdSyntax_correct
    (hExist : ProperObstructionSoundness.MAHasTotalProper4)
    (q : SixTuple) (hchamber : FiveParameterChamber q) :
    fiveParameterThresholdSyntax.eval q = true ↔
      MutationAcyclic (ofTuple q) := by
  rcases hchamber with ⟨ha, hb, hc, hd, he, hf⟩
  have hma : MutationAcyclic (ofTuple q) ↔
      -(q 1) * q 2 ≤ -(q 5) := by
    simpa [ofTuple, ha] using
      (ChamberProperness.five_parameter_MA_iff hExist
        (-(q 1)) (q 2) (-(q 3)) (-(q 4)) (-(q 5))
        hb hc hd he hf)
  exact (fiveParameterThresholdSyntax_eval q).trans hma.symm

/-- A global formula whose true set is exactly the MA inputs in this chamber. -/
def fiveParameterMASetSyntax : Formula :=
  .and fiveParameterChamberSyntax fiveParameterThresholdSyntax

theorem fiveParameterMASetSyntax_correct
    (hExist : ProperObstructionSoundness.MAHasTotalProper4)
    (q : SixTuple) :
    fiveParameterMASetSyntax.eval q = true ↔
      FiveParameterChamber q ∧ MutationAcyclic (ofTuple q) := by
  change (fiveParameterChamberSyntax.eval q &&
    fiveParameterThresholdSyntax.eval q) = true ↔ _
  rw [Bool.and_eq_true]
  constructor
  · rintro ⟨hch, hval⟩
    have hc := (fiveParameterChamberSyntax_eval q).mp hch
    exact ⟨hc, (fiveParameterThresholdSyntax_correct hExist q hc).mp hval⟩
  · rintro ⟨hc, hma⟩
    exact ⟨(fiveParameterChamberSyntax_eval q).mpr hc,
      (fiveParameterThresholdSyntax_correct hExist q hc).mpr hma⟩

#print axioms fiveParameterThresholdSyntax_eval
#print axioms fiveParameterThresholdSyntax_correct
#print axioms fiveParameterMASetSyntax_correct

end Rank4Construction
