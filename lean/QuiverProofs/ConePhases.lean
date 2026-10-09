import QuiverProofs.ForkDefinition

/-! Every phase of the repeated cone word retains its internal unit edge.
The phase parameter records zero, one, or two mutations into the next block. -/

namespace QuiverProofs.ConePhases
open Cone

def phaseWord (n : Nat) (phase : Fin 3) : List (Fin 4) :=
  repeatedWord n ++ ([0,1,2] : List (Fin 4)).take phase.val

def phaseMatrix (u v w : Int) (s : State) (phase : Fin 3) : Matrix 4 :=
  match phase.val with
  | 0 => quiver u v w s
  | 1 => ofSix u v (-s.A) (-w) (s.H+u*s.A) (v*s.A-s.Z)
  | _ => ofSix (-u) v ((u*u-1)*s.A+u*s.H) w (-(s.H+u*s.A))
      ((v+u*w)*s.A+w*s.H-s.Z)

theorem phase_as_mutations (u v w : Int) (s : State)
    (hu : 1≤u) (hv : 1≤v) (hw : 1≤w)
    (hc : InCone v s.A s.H s.Z) (n : Nat) (phase : Fin 3) :
    applyWord (quiver u v w s) (phaseWord n phase) =
      phaseMatrix u v w (orbit u v w s n) phase := by
  have ho := orbit_in_cone u v w s hu hv hw hc n
  have hp : phase=0 ∨ phase=1 ∨ phase=2 := by omega
  rcases hp with rfl|rfl|rfl
  · simp [phaseWord,phaseMatrix,orbit_as_mutations u v w s hu hv hw hc n]
  · simp only [phaseWord,applyWord_append]
    rw [orbit_as_mutations u v w s hu hv hw hc n]
    simpa [phaseMatrix,applyWord,quiver] using
      mutation_phase_one u v w _ _ _ hu hv ho.1
  · simp only [phaseWord,applyWord_append]
    rw [orbit_as_mutations u v w s hu hv hw hc n]
    simp only [List.take,applyWord,quiver]
    rw [mutation_phase_one u v w _ _ _ hu hv ho.1,
      mutation_phase_two u v w _ _ _ hu hw ho.1 ho.2.1]
    rfl

theorem phase_matrix_unit_edge (u v w : Int) (s : State)
    (hunit : u=1 ∨ v=1 ∨ w=1) (phase : Fin 3) :
    ∃ i j : Fin 4, i≠j ∧ phaseMatrix u v w s phase i j = -1 := by
  have hp : phase=0 ∨ phase=1 ∨ phase=2 := by omega
  rcases hp with rfl|rfl|rfl
  · rcases hunit with rfl|rfl|rfl
    · exact ⟨0,1,by decide,rfl⟩
    · exact ⟨0,2,by decide,rfl⟩
    · exact ⟨1,2,by decide,rfl⟩
  · rcases hunit with rfl|rfl|rfl
    · exact ⟨1,0,by decide,rfl⟩
    · exact ⟨2,0,by decide,rfl⟩
    · exact ⟨1,2,by decide,rfl⟩
  · rcases hunit with rfl|rfl|rfl
    · exact ⟨0,1,by decide,rfl⟩
    · exact ⟨2,0,by decide,rfl⟩
    · exact ⟨2,1,by decide,rfl⟩

theorem mutation_orbit_phase_unit_edge (u v w : Int) (s : State)
    (hu : 1≤u) (hv : 1≤v) (hw : 1≤w)
    (hc : InCone v s.A s.H s.Z) (hunit : u=1 ∨ v=1 ∨ w=1)
    (n : Nat) (phase : Fin 3) :
    ∃ i j : Fin 4, i≠j ∧
      applyWord (quiver u v w s) (phaseWord n phase) i j = -1 := by
  rw [phase_as_mutations u v w s hu hv hw hc n phase]
  exact phase_matrix_unit_edge u v w _ hunit phase

theorem mutation_orbit_phase_not_abundant (u v w : Int) (s : State)
    (hu : 1≤u) (hv : 1≤v) (hw : 1≤w)
    (hc : InCone v s.A s.H s.Z) (hunit : u=1 ∨ v=1 ∨ w=1)
    (n : Nat) (phase : Fin 3) :
    ¬ Abundant (applyWord (quiver u v w s) (phaseWord n phase)) := by
  obtain ⟨i,j,hij,he⟩ := mutation_orbit_phase_unit_edge u v w s hu hv hw hc hunit n phase
  intro h
  have hweight := h i j hij
  rw [he] at hweight
  contradiction

theorem mutation_orbit_phase_not_fork (u v w : Int) (s : State)
    (hu : 1≤u) (hv : 1≤v) (hw : 1≤w)
    (hc : InCone v s.A s.H s.Z) (hunit : u=1 ∨ v=1 ∨ w=1)
    (n : Nat) (phase : Fin 3) (r : Fin 4) :
    ¬ Forks.IsFork (applyWord (quiver u v w s) (phaseWord n phase)) r :=
  FiniteLogic.nonabundant_not_fork
    (mutation_orbit_phase_not_abundant u v w s hu hv hw hc hunit n phase) r

theorem mutation_orbit_phase_not_graphFork (u v w : Int) (s : State)
    (hu : 1≤u) (hv : 1≤v) (hw : 1≤w)
    (hc : InCone v s.A s.H s.Z) (hunit : u=1 ∨ v=1 ∨ w=1)
    (n : Nat) (phase : Fin 3) (r : Fin 4) :
    ¬ ForkDefinition.GraphFork (applyWord (quiver u v w s) (phaseWord n phase)) r := by
  intro hf
  exact mutation_orbit_phase_not_abundant u v w s hu hv hw hc hunit n phase hf.2.2.1

end QuiverProofs.ConePhases
