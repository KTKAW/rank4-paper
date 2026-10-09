import Rank4Round4.BoundedTwoDepthFormula
import Rank4Adversarial.DepthThreeGlobalGap

/-!
Exact sufficient interfaces for turning the checked decision and partial
formula results into an unrestricted fixed polynomial-sign classifier.  No
inhabitant of either open interface is asserted here.
-/

namespace Rank4Round5.Verification
open Rank4Formula Rank4Invariant Rank4Round4.Formula QuiverProofs

/-- A word-length bound which is one literal number for all integer inputs. -/
def UniformAcyclicDepth (n : Nat) : Prop :=
  ∀ q : SixTuple, MutationAcyclic (ofTuple q) →
    ∃ w : List (Fin 4), w.length ≤ n ∧ Acyclic (applyWord (ofTuple q) w)

theorem uniformDepth_representsMA (n : Nat) (h : UniformAcyclicDepth n) :
    RepresentsMA (depthSyntax n) := by
  intro q
  constructor
  · exact depthSyntax_sound n q
  · intro hm
    obtain ⟨w,hw,ha⟩ := h q hm
    exact depthSyntax_complete_of_short n q w hw ha

theorem some_uniformDepth_implies_fixed_formula
    (h : ∃ n : Nat, UniformAcyclicDepth n) :
    ExistsAlgebraicMAFormula := by
  obtain ⟨n,hn⟩ := h
  exact ⟨depthSyntax n, uniformDepth_representsMA n hn⟩

/-- Depth three is already excluded globally by a certified four-step MA
point; this does not exclude every possible uniform depth. -/
theorem uniformDepth_three_false : ¬ UniformAcyclicDepth 3 := by
  intro h
  exact Rank4Adversarial.depthFourPoint_no_acyclic_word_le_three
    (h Rank4Adversarial.depthFourPoint Rank4Adversarial.depthFourPoint_MA)

/-- Classification needed only on the exact complement of the checked
one-step MA cover. -/
def RepresentsMAOnOneStepResidual (F : Formula) : Prop :=
  ∀ q : SixTuple, Residual q →
    (F.eval q = true ↔ MutationAcyclic (ofTuple q))

theorem fixed_formula_iff_oneStepResidual_formula :
    ExistsAlgebraicMAFormula ↔
      ∃ F : Formula, RepresentsMAOnOneStepResidual F := by
  constructor
  · rintro ⟨F,hF⟩
    exact ⟨F,fun q _ => hF q⟩
  · rintro ⟨F,hF⟩
    refine ⟨.or oneStepCoverSyntax (.and residualSyntax F), ?_⟩
    intro q
    change (oneStepCoverSyntax.eval q ||
      (residualSyntax.eval q && F.eval q)) = true ↔
      MutationAcyclic (ofTuple q)
    rw [Bool.or_eq_true, Bool.and_eq_true]
    constructor
    · rintro (hc | ⟨hr,hval⟩)
      · exact oneStepCoverSyntax_sound q hc
      · exact (hF q ((residualSyntax_eval q).mp hr)).mp hval
    · intro hm
      by_cases hc : OneStepCover q
      · exact Or.inl ((oneStepCoverSyntax_eval q).mpr hc)
      · exact Or.inr ⟨(residualSyntax_eval q).mpr hc,
          (hF q hc).mpr hm⟩

#print axioms uniformDepth_representsMA
#print axioms some_uniformDepth_implies_fixed_formula
#print axioms uniformDepth_three_false
#print axioms fixed_formula_iff_oneStepResidual_formula

end Rank4Round5.Verification
