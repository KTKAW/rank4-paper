import Rank4Construction.ResidualOneStep

/-!
A direct finite-cover test for the existing certified local MA regions.
The target is acyclic input, disconnected-MA formula, or the 48 symmetry
chamber-MA formula.  The one-step cover also allows mutation at any vertex.
An explicit MA input lies outside this cover.
-/

namespace Rank4Invariant
open Rank4Formula Rank4Construction QuiverProofs

/-- Upper-triangle coordinates of the actual labeled mutation. -/
def mutationTuple (q : SixTuple) (k : Fin 4) : SixTuple :=
  fun i =>
    let B := mutate (ofTuple q) k
    match i.val with
    | 0 => B 0 1 | 1 => B 0 2 | 2 => B 0 3
    | 3 => B 1 2 | 4 => B 1 3 | _ => B 2 3

theorem mutationTuple_correct (q : SixTuple) (k : Fin 4) :
    ofTuple (mutationTuple q k) = mutate (ofTuple q) k := by
  unfold ofTuple mutationTuple
  exact ofSix_reconstruct _
    (mutation_preserves_skew _ k (ofSix_skew _ _ _ _ _ _))

/-- Concrete target region assembled from previously verified MA formulas. -/
def Target (q : SixTuple) : Prop :=
  Acyclic (ofTuple q) ∨
  disconnectedMASetSyntax.eval q = true ∨
  fortyEightChamberMASetSyntax.eval q = true

theorem target_sound (q : SixTuple) (h : Target q) :
    MutationAcyclic (ofTuple q) := by
  rcases h with h | h | h
  · exact acyclic_is_mutationAcyclic _ h
  · exact (disconnectedMASetSyntax_correct q).mp h |>.2
  · exact (fortyEightChamberMASetSyntax_correct_unconditional q).mp h |>.2

/-- The target itself and all four one-step preimages. -/
def OneStepCover (q : SixTuple) : Prop :=
  Target q ∨ ∃ k : Fin 4, Target (mutationTuple q k)

theorem oneStepCover_sound (q : SixTuple) (h : OneStepCover q) :
    MutationAcyclic (ofTuple q) := by
  rcases h with h | ⟨k, h⟩
  · exact target_sound q h
  · have hm := target_sound (mutationTuple q k) h
    rw [mutationTuple_correct] at hm
    exact (mutationAcyclic_iff _ k).mp hm

/-- A directed triangle certifies failure of `Acyclic` for the exact
natural-valued-ranking definition. -/
theorem cyclicTriangle_not_acyclic (B : Matrix 4) (i j k : Fin 4)
    (hij : 0 < B i j) (hjk : 0 < B j k) (hki : 0 < B k i) :
    ¬ Acyclic B := by
  intro h
  exact acyclic_no_closed_walk B h i
    (DirectedWalk.extend (DirectedWalk.extend (DirectedWalk.edge hij) hjk) hki)

/-- Six coordinates `01,02,03,12,13,23`. -/
def gap : SixTuple := fun i =>
  match i.val with
  | 0 => -2 | 1 => -1 | 2 => 1 | 3 => -1 | 4 => -1 | _ => -2

theorem gap_MA : MutationAcyclic (ofTuple gap) := by
  refine ⟨[0,3], ?_⟩
  refine ⟨(fun i => match i.val with
    | 0 => 0 | 1 => 3 | 2 => 1 | _ => 2), ?_⟩
  decide

theorem gap_not_acyclic : ¬ Acyclic (ofTuple gap) := by
  apply cyclicTriangle_not_acyclic _ 0 3 1 <;> decide

theorem gap_mutations_not_acyclic (k : Fin 4) :
    ¬ Acyclic (ofTuple (mutationTuple gap k)) := by
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hk with rfl | rfl | rfl | rfl
  · apply cyclicTriangle_not_acyclic _ 0 1 3 <;> decide
  · apply cyclicTriangle_not_acyclic _ 0 1 2 <;> decide
  · apply cyclicTriangle_not_acyclic _ 0 2 3 <;> decide
  · apply cyclicTriangle_not_acyclic _ 0 2 1 <;> decide

theorem gap_target_formulae_false :
    disconnectedMASetSyntax.eval gap = false ∧
    fortyEightChamberMASetSyntax.eval gap = false := by decide

theorem gap_mutation_target_formulae_false (k : Fin 4) :
    disconnectedMASetSyntax.eval (mutationTuple gap k) = false ∧
    fortyEightChamberMASetSyntax.eval (mutationTuple gap k) = false := by
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hk with rfl | rfl | rfl | rfl <;> decide

theorem gap_not_target : ¬ Target gap := by
  intro h
  rcases h with h | h | h
  · exact gap_not_acyclic h
  · have hf := gap_target_formulae_false.1
    simp [hf] at h
  · have hf := gap_target_formulae_false.2
    simp [hf] at h

theorem gap_mutations_not_target (k : Fin 4) :
    ¬ Target (mutationTuple gap k) := by
  intro h
  rcases h with h | h | h
  · exact gap_mutations_not_acyclic k h
  · have hf := (gap_mutation_target_formulae_false k).1
    simp [hf] at h
  · have hf := (gap_mutation_target_formulae_false k).2
    simp [hf] at h

/-- Exact failure of universal one-step completeness, even on MA inputs. -/
theorem gap_outside_oneStepCover : ¬ OneStepCover gap := by
  intro h
  rcases h with h | ⟨k, h⟩
  · exact gap_not_target h
  · exact gap_mutations_not_target k h

/-- The witness remains in the exact residual domain from round two. -/
theorem gap_in_ResidualOneStep : ResidualOneStep gap := by
  have hdis : ¬ DisconnectedSix (gap 0) (gap 1) (gap 2)
      (gap 3) (gap 4) (gap 5) := by
    simp [DisconnectedSix, gap]
  have hch : ¬ FullSymmetryChamber gap := by
    intro h
    have he := (fortyEightChamberMASetSyntax_correct_unconditional gap).mpr
      ⟨h, gap_MA⟩
    rw [gap_target_formulae_false.2] at he
    contradiction
  have hpm : mutationThreePullbackMASetSyntax.eval gap = false := by decide
  have hpb : ¬ MutationThreePullbackInput gap := by
    intro h
    have he := (mutationThreePullbackMASetSyntax_correct gap).mpr
      ⟨h, gap_MA⟩
    rw [hpm] at he
    contradiction
  exact ⟨⟨hdis, hch⟩, hpb⟩

theorem oneStepCover_not_all_MA :
    ¬ ∀ q : SixTuple, MutationAcyclic (ofTuple q) → OneStepCover q := by
  intro h
  exact gap_outside_oneStepCover (h gap gap_MA)

#print axioms mutationTuple_correct
#print axioms target_sound
#print axioms oneStepCover_sound
#print axioms gap_MA
#print axioms gap_outside_oneStepCover
#print axioms gap_in_ResidualOneStep
#print axioms oneStepCover_not_all_MA

end Rank4Invariant
