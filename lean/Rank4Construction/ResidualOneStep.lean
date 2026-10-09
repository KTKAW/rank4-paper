import Rank4Construction.Residual48
import Rank4Construction.MutationThreePullback

/-!
An exact residual reduction after adding one polynomial mutation preimage of
the 48 transported chambers.  The new source still does not assert that the
residual has a finite algebraic classifier.
-/

namespace Rank4Construction
open Rank4Formula QuiverProofs

/-- Fixed syntax for the input region where the one-step theorem applies. -/
def mutationThreePullbackGuardSyntax : Formula :=
  .and mutationThreeSignSyntax
    (fullSymmetryChamberSyntax.subst mutationThreeCoordTerm)

theorem mutationThreePullbackGuardSyntax_eval (q : SixTuple) :
    mutationThreePullbackGuardSyntax.eval q = true ↔
      MutationThreePullbackInput q := by
  have hsubst := Formula.subst_eval_of_target
    mutationThreeCoordTerm fullSymmetryChamberSyntax q
    (mutationThreePolynomialTuple q)
    (fun k => mutationThreeCoordTerm_eval k q)
  change (mutationThreeSignSyntax.eval q &&
    (fullSymmetryChamberSyntax.subst mutationThreeCoordTerm).eval q) = true ↔ _
  rw [Bool.and_eq_true, mutationThreeSignSyntax_eval, hsubst,
    fullSymmetryChamberSyntax_eval]
  rfl

/-- Inputs outside disconnected support, all 48 symmetry chambers, and the
vertex-3 one-step preimage on its closed sign region. -/
def ResidualOneStep (q : SixTuple) : Prop :=
  Residual48 q ∧ ¬ MutationThreePullbackInput q

def RepresentsMAOnResidualOneStep (F : Formula) : Prop :=
  ∀ q : SixTuple, ResidualOneStep q →
    (F.eval q = true ↔ MutationAcyclic (ofTuple q))

def residualOneStepGuardSyntax : Formula :=
  .and residual48GuardSyntax (.not mutationThreePullbackGuardSyntax)

theorem residualOneStepGuardSyntax_eval (q : SixTuple) :
    residualOneStepGuardSyntax.eval q = true ↔ ResidualOneStep q := by
  have hr := residual48GuardSyntax_eval q
  have hm := mutationThreePullbackGuardSyntax_eval q
  cases hrv : residual48GuardSyntax.eval q <;>
    cases hmv : mutationThreePullbackGuardSyntax.eval q <;>
      simp_all [residualOneStepGuardSyntax, Formula.eval, ResidualOneStep]

/-- All presently checked local MA sets as one fixed formula. -/
def patchedOneStepMASyntax : Formula :=
  .or disconnectedMASetSyntax
    (.or fortyEightChamberMASetSyntax mutationThreePullbackMASetSyntax)

theorem patchedOneStepMASyntax_correct (q : SixTuple) :
    patchedOneStepMASyntax.eval q = true ↔
      (DisconnectedSix (q 0) (q 1) (q 2) (q 3) (q 4) (q 5) ∨
        FullSymmetryChamber q ∨ MutationThreePullbackInput q) ∧
        MutationAcyclic (ofTuple q) := by
  have hd := disconnectedMASetSyntax_correct q
  have hc := fortyEightChamberMASetSyntax_correct_unconditional q
  have hm := mutationThreePullbackMASetSyntax_correct q
  change (disconnectedMASetSyntax.eval q ||
    (fortyEightChamberMASetSyntax.eval q ||
      mutationThreePullbackMASetSyntax.eval q)) = true ↔ _
  rw [Bool.or_eq_true, Bool.or_eq_true, hd, hc, hm]
  constructor
  · rintro (⟨hg, hma⟩ | ⟨hg, hma⟩ | ⟨hg, hma⟩)
    · exact ⟨Or.inl hg, hma⟩
    · exact ⟨Or.inr (Or.inl hg), hma⟩
    · exact ⟨Or.inr (Or.inr hg), hma⟩
  · rintro ⟨hguard, hma⟩
    rcases hguard with hg | hg | hg
    · exact Or.inl ⟨hg, hma⟩
    · exact Or.inr (Or.inl ⟨hg, hma⟩)
    · exact Or.inr (Or.inr ⟨hg, hma⟩)

/-- A residual formula joins the three finite local formulas. -/
def assembleWithResidualOneStep (F : Formula) : Formula :=
  .or patchedOneStepMASyntax (.and residualOneStepGuardSyntax F)

theorem assembleWithResidualOneStep_correct
    (F : Formula) (hF : RepresentsMAOnResidualOneStep F) :
    RepresentsMA (assembleWithResidualOneStep F) := by
  intro q
  have hp := patchedOneStepMASyntax_correct q
  have hr := residualOneStepGuardSyntax_eval q
  change (patchedOneStepMASyntax.eval q ||
    (residualOneStepGuardSyntax.eval q && F.eval q)) = true ↔ _
  rw [Bool.or_eq_true, Bool.and_eq_true]
  constructor
  · rintro (h | ⟨hg, hf⟩)
    · exact (hp.mp h).2
    · exact (hF q (hr.mp hg)).mp hf
  · intro hma
    by_cases hd : DisconnectedSix (q 0) (q 1) (q 2) (q 3) (q 4) (q 5)
    · exact Or.inl (hp.mpr ⟨Or.inl hd, hma⟩)
    by_cases hc : FullSymmetryChamber q
    · exact Or.inl (hp.mpr ⟨Or.inr (Or.inl hc), hma⟩)
    by_cases hm : MutationThreePullbackInput q
    · exact Or.inl (hp.mpr ⟨Or.inr (Or.inr hm), hma⟩)
    · have hres : ResidualOneStep q := ⟨⟨hd, hc⟩, hm⟩
      exact Or.inr ⟨hr.mpr hres, (hF q hres).mpr hma⟩

/-- Exact positive target reduction after the one-step expansion. -/
theorem global_formula_iff_residualOneStep_formula :
    ExistsAlgebraicMAFormula ↔
      ∃ F : Formula, RepresentsMAOnResidualOneStep F := by
  constructor
  · rintro ⟨F, hF⟩
    exact ⟨F, fun q _ => hF q⟩
  · rintro ⟨F, hF⟩
    exact ⟨assembleWithResidualOneStep F,
      assembleWithResidualOneStep_correct F hF⟩

#print axioms mutationThreePullbackGuardSyntax_eval
#print axioms patchedOneStepMASyntax_correct
#print axioms global_formula_iff_residualOneStep_formula

end Rank4Construction
