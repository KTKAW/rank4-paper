import Rank4Construction.ResidualOneStep
import Rank4Construction.DisconnectedFormula
import QuiverProofs.FiniteOrbit

/-!
A concrete mutation-acyclic input outside both previously certified local
loci. It is the global arrow reversal of the all-unit five-parameter example,
so it lies in the new transported chamber family.
-/

namespace Rank4Round2.Computation

open Rank4Formula Rank4Construction QuiverProofs

/-- Upper entries 01,02,03,12,13,23. Exactly the 01 edge is zero. -/
def reversalWitness : SixTuple := fun i =>
  match i.val with
  | 0 => 0 | 1 => 1 | 2 => -1 | 3 => 1 | 4 => 1 | _ => 1

theorem reversalWitness_not_original_chamber :
    ¬ FiveParameterChamber reversalWitness := by
  simp [FiveParameterChamber, reversalWitness]

theorem reversalWitness_connected :
    ¬ DisconnectedSix
      (reversalWitness 0) (reversalWitness 1) (reversalWitness 2)
      (reversalWitness 3) (reversalWitness 4) (reversalWitness 5) := by
  simp [DisconnectedSix, reversalWitness]

/-- Mutation at 0 gives an acyclic matrix, certified by the displayed rank. -/
theorem reversalWitness_MA : MutationAcyclic (ofTuple reversalWitness) := by
  refine ⟨[0], ?_⟩
  refine ⟨fun i => if i = 0 then 2 else if i = 1 then 0 else
    if i = 2 then 1 else 3, ?_⟩
  decide

theorem reversalWitness_in_fullSymmetryChamber :
    FullSymmetryChamber reversalWitness := by
  refine ⟨Relabeling.identity 4, true, ?_⟩
  simp [FiveParameterChamber, orbitTuple, orbitMatrix,
    Relabeling.identity, reverse, relabel, ofTuple, ofSix,
    reversalWitness]

theorem reversalWitness_new_formula_true :
    fortyEightChamberMASetSyntax.eval reversalWitness = true := by
  exact (fortyEightChamberMASetSyntax_correct_unconditional
    reversalWitness).mpr
      ⟨reversalWitness_in_fullSymmetryChamber, reversalWitness_MA⟩

private theorem offdiag_nonzero_of_fullSupport (q : SixTuple)
    (hq : ∀ k : Fin 6, q k ≠ 0) (i j : Fin 4) (hij : i ≠ j) :
    ofTuple q i j ≠ 0 := by
  have h0 := hq 0
  have h1 := hq 1
  have h2 := hq 2
  have h3 := hq 3
  have h4 := hq 4
  have h5 := hq 5
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases hi with rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl <;>
      simp_all [ofTuple, ofSix]

/-- Every image of the strict five-parameter chamber still has a zero edge. -/
theorem fullSymmetryChamber_has_zero (q : SixTuple)
    (hch : FullSymmetryChamber q) : ∃ k : Fin 6, q k = 0 := by
  by_contra hn
  have hfull : ∀ k : Fin 6, q k ≠ 0 := by
    intro k hk
    exact hn ⟨k, hk⟩
  obtain ⟨p, flip, hpch⟩ := hch
  have hdiff : p.toFun 0 ≠ p.toFun 1 := by
    intro heq
    exact (show (0 : Fin 4) ≠ 1 by decide) (p.injective heq)
  have hentry := offdiag_nonzero_of_fullSupport q hfull
    (p.toFun 0) (p.toFun 1) hdiff
  have hfirst : orbitTuple p flip q 0 ≠ 0 := by
    cases flip <;>
      simpa [orbitTuple, orbitMatrix, relabel, reverse] using hentry
  exact hfirst hpch.1

/-- Same-sign full-support witnesses on opposite sides of MA. -/
def residualMA : SixTuple := fun i =>
  match i.val with
  | 0 => -1 | 1 => 1 | 2 => 1 | _ => -1

def residualNMA : SixTuple := fun i =>
  match i.val with
  | 0 => -2 | 1 => 1 | 2 => 1 | _ => -1

theorem residualMA_fullSupport : ∀ k : Fin 6, residualMA k ≠ 0 := by
  decide

theorem residualNMA_fullSupport : ∀ k : Fin 6, residualNMA k ≠ 0 := by
  decide

theorem residualMA_MA : MutationAcyclic (ofTuple residualMA) := by
  refine ⟨[0], ?_⟩
  refine ⟨fun i => if i = 0 then 2 else if i = 1 then 3 else
    if i = 2 then 1 else 0, ?_⟩
  decide

theorem residualNMA_NMA : ¬ MutationAcyclic (ofTuple residualNMA) := by
  change ¬ MutationAcyclic (ofSix (-2) 1 1 (-1) (-1) (-1))
  exact FiniteOrbit.nma_q617

theorem residualMA_outside_48_chambers :
    ¬ FullSymmetryChamber residualMA := by
  intro hch
  obtain ⟨k, hk⟩ := fullSymmetryChamber_has_zero residualMA hch
  exact residualMA_fullSupport k hk

theorem residualNMA_outside_48_chambers :
    ¬ FullSymmetryChamber residualNMA := by
  intro hch
  obtain ⟨k, hk⟩ := fullSymmetryChamber_has_zero residualNMA hch
  exact residualNMA_fullSupport k hk

theorem residualMA_connected :
    ¬ DisconnectedSix (residualMA 0) (residualMA 1) (residualMA 2)
        (residualMA 3) (residualMA 4) (residualMA 5) := by
  simp [DisconnectedSix, residualMA]

theorem residualNMA_connected :
    ¬ DisconnectedSix (residualNMA 0) (residualNMA 1) (residualNMA 2)
        (residualNMA 3) (residualNMA 4) (residualNMA 5) := by
  simp [DisconnectedSix, residualNMA]

theorem residualMA_in_Residual48 : Residual48 residualMA :=
  ⟨residualMA_connected, residualMA_outside_48_chambers⟩

theorem residualNMA_in_Residual48 : Residual48 residualNMA :=
  ⟨residualNMA_connected, residualNMA_outside_48_chambers⟩

theorem residualMA_outside_one_step_pullback :
    ¬ MutationThreePullbackInput residualMA := by
  simp [MutationThreePullbackInput, MutationThreeSignChamber, residualMA]

theorem residualNMA_outside_one_step_pullback :
    ¬ MutationThreePullbackInput residualNMA := by
  simp [MutationThreePullbackInput, MutationThreeSignChamber, residualNMA]

theorem residualMA_in_ResidualOneStep : ResidualOneStep residualMA :=
  ⟨residualMA_in_Residual48, residualMA_outside_one_step_pullback⟩

theorem residualNMA_in_ResidualOneStep : ResidualOneStep residualNMA :=
  ⟨residualNMA_in_Residual48, residualNMA_outside_one_step_pullback⟩

/-- A full-support input newly covered by the one-step pullback was genuinely
in the old residual. -/
theorem oneStepFullSupportWitness_in_Residual48 :
    Residual48 oneStepFullSupportWitness := by
  constructor
  · simp [DisconnectedSix, oneStepFullSupportWitness]
  · intro hch
    obtain ⟨k, hk⟩ :=
      fullSymmetryChamber_has_zero oneStepFullSupportWitness hch
    exact oneStepFullSupportWitness_edges k hk

theorem oneStepFullSupportWitness_not_ResidualOneStep :
    ¬ ResidualOneStep oneStepFullSupportWitness := by
  intro hres
  exact hres.2 oneStepFullSupportWitness_in_pullback

theorem residualOneStep_strictly_smaller :
    (∀ q : SixTuple, ResidualOneStep q → Residual48 q) ∧
      ∃ q : SixTuple, Residual48 q ∧ ¬ ResidualOneStep q := by
  constructor
  · intro q hq
    exact hq.1
  · exact ⟨oneStepFullSupportWitness,
      oneStepFullSupportWitness_in_Residual48,
      oneStepFullSupportWitness_not_ResidualOneStep⟩

theorem residualMA_new_formula_false :
    fortyEightChamberMASetSyntax.eval residualMA = false := by
  cases h : fortyEightChamberMASetSyntax.eval residualMA with
  | false => rfl
  | true =>
      have hch := (fortyEightChamberMASetSyntax_correct_unconditional
        residualMA).mp h
      exact False.elim (residualMA_outside_48_chambers hch.1)

theorem residualNMA_new_formula_false :
    fortyEightChamberMASetSyntax.eval residualNMA = false := by
  cases h : fortyEightChamberMASetSyntax.eval residualNMA with
  | false => rfl
  | true =>
      have hch := (fortyEightChamberMASetSyntax_correct_unconditional
        residualNMA).mp h
      exact False.elim (residualNMA_outside_48_chambers hch.1)

theorem fortyEightChamberMASetSyntax_not_global :
    ¬ RepresentsMA fortyEightChamberMASetSyntax := by
  intro hF
  have ht := (hF residualMA).mpr residualMA_MA
  rw [residualMA_new_formula_false] at ht
  cases ht

theorem patchedOneStepMASyntax_not_global :
    ¬ RepresentsMA patchedOneStepMASyntax := by
  intro hF
  have htrue := (hF residualMA).mpr residualMA_MA
  have hguard := (patchedOneStepMASyntax_correct residualMA).mp htrue
  have hres := residualMA_in_ResidualOneStep
  rcases hguard.1 with hd | hc | hm
  · exact hres.1.1 hd
  · exact hres.1.2 hc
  · exact hres.2 hm

#check reversalWitness_not_original_chamber
#check reversalWitness_connected
#check reversalWitness_MA
#check reversalWitness_in_fullSymmetryChamber
#check reversalWitness_new_formula_true
#check fullSymmetryChamber_has_zero
#check residualMA_MA
#check residualNMA_NMA
#check residualMA_outside_48_chambers
#check residualNMA_outside_48_chambers
#check residualMA_in_Residual48
#check residualNMA_in_Residual48
#check residualMA_outside_one_step_pullback
#check residualNMA_outside_one_step_pullback
#check residualMA_in_ResidualOneStep
#check residualNMA_in_ResidualOneStep
#check oneStepFullSupportWitness_in_Residual48
#check residualOneStep_strictly_smaller
#check fortyEightChamberMASetSyntax_not_global
#check patchedOneStepMASyntax_not_global

#print axioms reversalWitness_MA
#print axioms reversalWitness_new_formula_true
#print axioms fullSymmetryChamber_has_zero
#print axioms residualMA_MA
#print axioms residualNMA_NMA
#print axioms residualMA_in_Residual48
#print axioms residualNMA_in_Residual48
#print axioms residualMA_outside_one_step_pullback
#print axioms residualNMA_outside_one_step_pullback
#print axioms residualMA_in_ResidualOneStep
#print axioms residualNMA_in_ResidualOneStep
#print axioms residualOneStep_strictly_smaller
#print axioms fortyEightChamberMASetSyntax_not_global
#print axioms patchedOneStepMASyntax_not_global

end Rank4Round2.Computation
