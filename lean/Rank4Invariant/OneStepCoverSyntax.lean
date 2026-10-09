import Rank4Round3.MutationSignPullback
import Rank4Invariant.OneStepCoverGap
import Rank4AlgebraAudit.ComputableSignPatterns
import Rank4Round2.OrbitWitness
import QuiverProofs.AcyclicTargets

/-!
A finite polynomial-sign Formula for the exact semantic target and all four
one-step mutation preimages. The formula is large by construction: 24
acyclic orientations and 4 × 729 mutation/chamber branches, with all target
sign guards substituted in each branch.
-/

namespace Rank4Invariant
open Rank4Formula Rank4Construction QuiverProofs

private def orSyntax : List Formula → Formula
  | [] => .equal (.const 0) (.const 1)
  | F :: rest => .or F (orSyntax rest)

private theorem orSyntax_map_eval {α : Type} (xs : List α)
    (f : α → Formula) (q : SixTuple) :
    (orSyntax (xs.map f)).eval q = true ↔
      ∃ x ∈ xs, (f x).eval q = true := by
  induction xs with
  | nil => simp [orSyntax, Formula.eval, PolyTerm.eval]
  | cons x xs ih =>
      simp only [List.map_cons, orSyntax, Formula.eval, Bool.or_eq_true,
        ih, List.mem_cons]
      constructor
      · rintro (hx | ⟨y, hy, he⟩)
        · exact ⟨x, Or.inl rfl, hx⟩
        · exact ⟨y, Or.inr hy, he⟩
      · rintro ⟨y, hy, he⟩
        rcases hy with rfl | hy
        · exact Or.inl he
        · exact Or.inr ⟨y, hy, he⟩

private def nonnegativeSixSyntax : Formula :=
  .and (.lessEq (.const 0) (.coord 0))
    (.and (.lessEq (.const 0) (.coord 1))
      (.and (.lessEq (.const 0) (.coord 2))
        (.and (.lessEq (.const 0) (.coord 3))
          (.and (.lessEq (.const 0) (.coord 4))
            (.lessEq (.const 0) (.coord 5))))))

private theorem nonnegativeSixSyntax_eval (q : SixTuple) :
    nonnegativeSixSyntax.eval q = true ↔ ∀ i : Fin 6, 0 ≤ q i := by
  simp only [nonnegativeSixSyntax, Formula.eval, Bool.and_eq_true,
    PolyTerm.eval, decide_eq_true_eq]
  constructor
  · rintro ⟨h0,h1,h2,h3,h4,h5⟩ i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_cast at *
  · intro h
    exact ⟨by exact_mod_cast h 0, by exact_mod_cast h 1,
      by exact_mod_cast h 2, by exact_mod_cast h 3,
      by exact_mod_cast h 4, by exact_mod_cast h 5⟩

private def acyclicSyntax : Formula :=
  orSyntax (permutations4.map
    (fun p => orbitFormula p false nonnegativeSixSyntax))

private theorem nonnegativeSix_acyclic (v : SixTuple)
    (h : ∀ i : Fin 6, 0 ≤ v i) : Acyclic (ofTuple v) := by
  refine ⟨fun i => i.val, ?_⟩
  intro i j hij
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  have h3 := h 3; have h4 := h 4; have h5 := h 5
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases hi with rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl <;>
      simp [ofTuple, ofSix] at hij ⊢ <;> omega

private theorem acyclicSyntax_eval (q : SixTuple) :
    acyclicSyntax.eval q = true ↔ Acyclic (ofTuple q) := by
  rw [acyclicSyntax, orSyntax_map_eval]
  simp only [orbitFormula_eval, nonnegativeSixSyntax_eval]
  constructor
  · rintro ⟨p, _, hnonneg⟩
    have h := nonnegativeSix_acyclic (orbitTuple p false q) hnonneg
    rw [ofTuple_orbitTuple] at h
    exact (acyclic_relabel_iff (ofTuple q) p).mp (by simpa [orbitMatrix] using h)
  · intro hacyclic
    have hs : SkewSymmetric (ofTuple q) := ofSix_skew _ _ _ _ _ _
    obtain ⟨p, h01,h02,h03,h12,h13,h23⟩ :=
      AcyclicTargets.acyclic_has_topological_coordinates (ofTuple q) hs hacyclic
    obtain ⟨s, hs, heq⟩ := permutations4_complete p
    have horbit : orbitTuple s false q = orbitTuple p false q := by
      funext i
      simp [orbitTuple, orbitMatrix, relabel, heq]
    refine ⟨s, hs, ?_⟩
    rw [horbit]
    intro i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | simpa [orbitTuple, orbitMatrix, relabel] using h01
      | simpa [orbitTuple, orbitMatrix, relabel] using h02
      | simpa [orbitTuple, orbitMatrix, relabel] using h03
      | simpa [orbitTuple, orbitMatrix, relabel] using h12
      | simpa [orbitTuple, orbitMatrix, relabel] using h13
      | simpa [orbitTuple, orbitMatrix, relabel] using h23

/-- A finite polynomial-sign syntax for the exact certified target region. -/
def targetSyntax : Formula :=
  .or acyclicSyntax
    (.or disconnectedMASetSyntax fortyEightChamberMASetSyntax)

theorem targetSyntax_eval (q : SixTuple) :
    targetSyntax.eval q = true ↔ Target q := by
  simp only [targetSyntax, Formula.eval, Bool.or_eq_true,
    acyclicSyntax_eval, Target]

private def allSignPatterns : List Rank4Round3.SignPattern :=
  Rank4AlgebraAudit.allSignPatterns

/-- Finite union over every one of the 729 input chambers for one vertex. -/
def vertexPullbackSyntax (F : Formula) (k : Fin 4) : Formula :=
  orSyntax (allSignPatterns.map (fun s => Rank4Round3.pullbackSyntax k s F))

theorem vertexPullbackSyntax_eval (F : Formula) (k : Fin 4) (q : SixTuple) :
    (vertexPullbackSyntax F k).eval q = true ↔
      F.eval (Rank4Round3.mutatedUpper q k) = true := by
  unfold vertexPullbackSyntax
  rw [orSyntax_map_eval]
  simp only [allSignPatterns,
    Rank4AlgebraAudit.allSignPatterns_complete, true_and]
  exact Rank4Round3.all_chamber_pullbacks_iff F k q

/-- All 4 × 729 input vertex/chamber branches as one finite formula. -/
def oneStepPullbackSyntax (F : Formula) : Formula :=
  orSyntax ((List.finRange 4).map (vertexPullbackSyntax F))

theorem oneStepPullbackSyntax_eval (F : Formula) (q : SixTuple) :
    (oneStepPullbackSyntax F).eval q = true ↔
      ∃ k : Fin 4, F.eval (Rank4Round3.mutatedUpper q k) = true := by
  unfold oneStepPullbackSyntax
  rw [orSyntax_map_eval]
  simp only [List.mem_finRange, true_and, vertexPullbackSyntax_eval]

private theorem mutationTuple_eq_mutatedUpper (q : SixTuple) (k : Fin 4) :
    mutationTuple q k = Rank4Round3.mutatedUpper q k := by
  rfl

/-- Finite polynomial-sign AST for target membership immediately or after
one of the four labeled mutations. -/
def oneStepCoverSyntax : Formula :=
  .or targetSyntax (oneStepPullbackSyntax targetSyntax)

theorem oneStepCoverSyntax_eval (q : SixTuple) :
    oneStepCoverSyntax.eval q = true ↔ OneStepCover q := by
  simp only [oneStepCoverSyntax, Formula.eval, Bool.or_eq_true,
    targetSyntax_eval, oneStepPullbackSyntax_eval, OneStepCover]
  constructor
  · rintro (h | ⟨k, h⟩)
    · exact Or.inl h
    · right
      refine ⟨k, ?_⟩
      rw [mutationTuple_eq_mutatedUpper]
      exact h
  · rintro (h | ⟨k, h⟩)
    · exact Or.inl h
    · right
      refine ⟨k, ?_⟩
      rw [mutationTuple_eq_mutatedUpper] at h
      exact h

theorem oneStepCoverSyntax_sound (q : SixTuple)
    (h : oneStepCoverSyntax.eval q = true) :
    MutationAcyclic (ofTuple q) :=
  oneStepCover_sound q ((oneStepCoverSyntax_eval q).mp h)

/-- Exact residual, with no assumption that its elements are NMA. -/
def Residual (q : SixTuple) : Prop := ¬ OneStepCover q

def residualSyntax : Formula := .not oneStepCoverSyntax

theorem residualSyntax_eval (q : SixTuple) :
    residualSyntax.eval q = true ↔ Residual q := by
  change (!oneStepCoverSyntax.eval q) = true ↔ ¬ OneStepCover q
  cases hv : oneStepCoverSyntax.eval q with
  | false =>
      have hn : ¬ OneStepCover q := by
        intro hc
        have ht := (oneStepCoverSyntax_eval q).mpr hc
        rw [hv] at ht
        contradiction
      simp [hn]
  | true =>
      have hc : OneStepCover q := (oneStepCoverSyntax_eval q).mp hv
      simp [hc]

theorem residual_contains_MA :
    ∃ q : SixTuple, Residual q ∧ MutationAcyclic (ofTuple q) :=
  ⟨gap, gap_outside_oneStepCover, gap_MA⟩

/-- A previously known full-support MA witness enters the verified
48-chamber target after mutation at vertex 3. -/
theorem previous_fullSupportMA_in_cover :
    OneStepCover oneStepFullSupportWitness := by
  right
  refine ⟨3, Or.inr (Or.inr ?_)⟩
  have heq : mutationTuple oneStepFullSupportWitness 3 =
      mutationThreePolynomialTuple oneStepFullSupportWitness := by
    funext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hch : FullSymmetryChamber (mutationTuple oneStepFullSupportWitness 3) := by
    rw [heq]
    exact oneStepFullSupportWitness_in_pullback.2
  have hma : MutationAcyclic (ofTuple (mutationTuple oneStepFullSupportWitness 3)) := by
    rw [mutationTuple_correct]
    exact (mutationAcyclic_iff _ 3).mpr oneStepFullSupportWitness_MA
  exact (fortyEightChamberMASetSyntax_correct_unconditional _).mpr ⟨hch, hma⟩

/-- The earlier round-two residual MA witness reaches an acyclic quiver
after mutation at vertex 0. -/
theorem previous_residualMA_in_cover :
    OneStepCover Rank4Round2.Computation.residualMA := by
  right
  refine ⟨0, Or.inl ?_⟩
  refine ⟨fun i => if i = 0 then 2 else if i = 1 then 3 else
    if i = 2 then 1 else 0, ?_⟩
  decide

/-- Soundness alone excludes every NMA input from the cover.  This archived
24-state NMA orbit therefore lies in the exact new residual. -/
theorem previous_residualNMA_in_residual :
    Residual Rank4Round2.Computation.residualNMA := by
  intro hc
  exact Rank4Round2.Computation.residualNMA_NMA
    (oneStepCover_sound _ hc)

theorem residual_contains_NMA :
    ∃ q : SixTuple, Residual q ∧ ¬ MutationAcyclic (ofTuple q) :=
  ⟨Rank4Round2.Computation.residualNMA,
    previous_residualNMA_in_residual,
    Rank4Round2.Computation.residualNMA_NMA⟩

theorem gap_residualSyntax_true : residualSyntax.eval gap = true :=
  (residualSyntax_eval gap).mpr gap_outside_oneStepCover

theorem oneStepCoverSyntax_not_MA_complete :
    ¬ ∀ q : SixTuple, MutationAcyclic (ofTuple q) →
      oneStepCoverSyntax.eval q = true := by
  intro h
  exact gap_outside_oneStepCover ((oneStepCoverSyntax_eval gap).mp (h gap gap_MA))

#print axioms acyclicSyntax_eval
#print axioms targetSyntax_eval
#print axioms vertexPullbackSyntax_eval
#print axioms oneStepPullbackSyntax_eval
#print axioms oneStepCoverSyntax_eval
#print axioms oneStepCoverSyntax_sound
#print axioms residualSyntax_eval
#print axioms residual_contains_MA
#print axioms previous_fullSupportMA_in_cover
#print axioms previous_residualMA_in_cover
#print axioms previous_residualNMA_in_residual
#print axioms residual_contains_NMA
#print axioms gap_residualSyntax_true
#print axioms oneStepCoverSyntax_not_MA_complete

end Rank4Invariant
