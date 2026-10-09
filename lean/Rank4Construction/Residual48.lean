import Rank4Construction.ChamberSymmetryOrbitCompletion
import Rank4Construction.BadTriangleSyntax

/-!
The 48 transported chambers and disconnected support are exact algebraic
pieces.  The remaining input domain is isolated here without asserting that
it has a finite polynomial-sign classifier.
-/

namespace Rank4Construction
open Rank4Formula QuiverProofs

def orbitChamberUnionSyntax : List (Relabeling 4 × Bool) → Formula
  | [] => .equal (.const 0) (.const 1)
  | (p, flip) :: rest =>
      .or (orbitFiveParameterChamberSyntax p flip)
        (orbitChamberUnionSyntax rest)

theorem orbitChamberUnionSyntax_eval
    (states : List (Relabeling 4 × Bool)) (q : SixTuple) :
    (orbitChamberUnionSyntax states).eval q = true ↔
      ∃ s ∈ states, FiveParameterChamber (orbitTuple s.1 s.2 q) := by
  induction states with
  | nil => simp [orbitChamberUnionSyntax, Formula.eval, PolyTerm.eval]
  | cons s rest ih =>
      rcases s with ⟨p, flip⟩
      simp only [orbitChamberUnionSyntax, Formula.eval, Bool.or_eq_true,
        orbitFiveParameterChamberSyntax_eval, ih, List.mem_cons]
      constructor
      · rintro (hch | ⟨t, ht, hch⟩)
        · exact ⟨(p, flip), Or.inl rfl, hch⟩
        · exact ⟨t, Or.inr ht, hch⟩
      · rintro ⟨t, ht, hch⟩
        rcases ht with rfl | ht
        · exact Or.inl hch
        · exact Or.inr ⟨t, ht, hch⟩

/-- One fixed formula for the union of all 48 chamber guards. -/
def fullSymmetryChamberSyntax : Formula :=
  orbitChamberUnionSyntax chamberOrbitStates

theorem fullSymmetryChamberSyntax_eval (q : SixTuple) :
    fullSymmetryChamberSyntax.eval q = true ↔ FullSymmetryChamber q := by
  change (orbitChamberUnionSyntax chamberOrbitStates).eval q = true ↔ _
  exact (orbitChamberUnionSyntax_eval chamberOrbitStates q).trans
    (fortyEightChamberInput_iff_fullSymmetryChamber q)

/-- The only region not covered by the two unconditional local formulas. -/
def Residual48 (q : SixTuple) : Prop :=
  ¬ DisconnectedSix (q 0) (q 1) (q 2) (q 3) (q 4) (q 5) ∧
    ¬ FullSymmetryChamber q

def RepresentsMAOnResidual48 (F : Formula) : Prop :=
  ∀ q : SixTuple, Residual48 q →
    (F.eval q = true ↔ MutationAcyclic (ofTuple q))

def residual48GuardSyntax : Formula :=
  .and (.not disconnectedSixSyntax) (.not fullSymmetryChamberSyntax)

theorem residual48GuardSyntax_eval (q : SixTuple) :
    residual48GuardSyntax.eval q = true ↔ Residual48 q := by
  have hd := disconnectedSixSyntax_eval q
  have hc := fullSymmetryChamberSyntax_eval q
  cases hdb : disconnectedSixSyntax.eval q <;>
    cases hcb : fullSymmetryChamberSyntax.eval q <;>
      simp_all [residual48GuardSyntax, Formula.eval, Residual48]

/-- A candidate residual formula is joined to the two checked local sets. -/
def assembleWithResidual48 (F : Formula) : Formula :=
  .or disconnectedMASetSyntax
    (.or fortyEightChamberMASetSyntax (.and residual48GuardSyntax F))

theorem assembleWithResidual48_correct
    (F : Formula) (hF : RepresentsMAOnResidual48 F) :
    RepresentsMA (assembleWithResidual48 F) := by
  intro q
  have hd := disconnectedMASetSyntax_correct q
  have hc := fortyEightChamberMASetSyntax_correct_unconditional q
  have hr := residual48GuardSyntax_eval q
  change (disconnectedMASetSyntax.eval q ||
    (fortyEightChamberMASetSyntax.eval q ||
      (residual48GuardSyntax.eval q && F.eval q))) = true ↔ _
  rw [Bool.or_eq_true, Bool.or_eq_true, Bool.and_eq_true]
  constructor
  · intro h
    rcases h with h | h | ⟨hg, hf⟩
    · exact (hd.mp h).2
    · exact (hc.mp h).2
    · exact (hF q (hr.mp hg)).mp hf
  · intro hm
    by_cases hdis : DisconnectedSix (q 0) (q 1) (q 2) (q 3) (q 4) (q 5)
    · exact Or.inl (hd.mpr ⟨hdis, hm⟩)
    by_cases hch : FullSymmetryChamber q
    · exact Or.inr (Or.inl (hc.mpr ⟨hch, hm⟩))
    · have hres : Residual48 q := ⟨hdis, hch⟩
      exact Or.inr (Or.inr ⟨hr.mpr hres, (hF q hres).mpr hm⟩)

/-- Exact equivalence: a global algebraic classifier exists iff one exists
on the residual complement of disconnected inputs and all 48 chambers. -/
theorem global_formula_iff_residual48_formula :
    ExistsAlgebraicMAFormula ↔
      ∃ F : Formula, RepresentsMAOnResidual48 F := by
  constructor
  · rintro ⟨F, hF⟩
    exact ⟨F, fun q _ => hF q⟩
  · rintro ⟨F, hF⟩
    exact ⟨assembleWithResidual48 F,
      assembleWithResidual48_correct F hF⟩

#print axioms fullSymmetryChamberSyntax_eval
#print axioms assembleWithResidual48_correct
#print axioms global_formula_iff_residual48_formula

end Rank4Construction
