import QuiverProofs.ForkDefinition

/-!
The exact fork pruning predicate in `prop:finite-forkless` is that the CHILD
is a fork whose return is the just-mutated vertex. The bounded retained-orbit
results below include a starting fork. They do not assert that every mutation
class has finite nonfork part, or that a resource cutoff is an NMA certificate.
-/
namespace QuiverProofs.ForkPruning
open ForkDefinition

def Nonfork (B : Matrix 4) : Prop := ∀ r, ¬ GraphFork B r

def Retained (B : Matrix 4) (k : Fin 4) : Prop := ¬ GraphFork (mutate B k) k

/-- A path explored by precisely the source pruning rule. -/
inductive RetainedWord : Matrix 4 → List (Fin 4) → Prop
  | nil (B) : RetainedWord B []
  | cons {B k word} : Retained B k → RetainedWord (mutate B k) word →
      RetainedWord B (k :: word)

theorem retained_child_nonfork {B : Matrix 4} {k : Fin 4}
    (parent : Nonfork B) (keep : Retained B k) : Nonfork (mutate B k) := by
  intro r fork
  by_cases h : k = r
  · subst r
    exact keep fork
  · have back := graphFork_continuation (mutate B k) r k fork h
    rw [mutation_involutive] at back
    exact parent k back

theorem nonfork_retained_word {B : Matrix 4} {word : List (Fin 4)}
    (parent : Nonfork B) (path : RetainedWord B word) :
    Nonfork (applyWord B word) := by
  induction path with
  | nil => exact parent
  | cons keep _ ih => exact ih (retained_child_nonfork parent keep)

/-- From a fork only its return can be retained. -/
theorem retained_is_return {B : Matrix 4} {r k : Fin 4}
    (fork : GraphFork B r) (keep : Retained B k) : k = r := by
  by_cases h : k = r
  · exact h
  · exact False.elim (keep (graphFork_continuation B r k fork h))

/-- If a retained child is a fork, the retained edge strictly decreases weight.
This handles also the subtle case of a starting fork. -/
theorem retained_fork_child_decreases {B : Matrix 4} {k r : Fin 4}
    (keep : Retained B k) (child : GraphFork (mutate B k) r) :
    Greedy.totalWeight (mutate B k) < Greedy.totalWeight B := by
  have different : k ≠ r := by
    intro h
    subst r
    exact keep child
  have growth := (graphFork_continuation_and_growth (mutate B k) r k child different).2
  simpa only [mutation_involutive] using growth

theorem weight_nonnegative (B : Matrix 4) : 0 ≤ Greedy.totalWeight B := by
  simp only [Greedy.totalWeight, Greedy.magnitude]
  omega

/-- A finite list of nonfork representatives supplies a uniform weight bound.
Relabelings preserve the exact six-edge total weight. -/
def representativeBound : List (Matrix 4) → Int
  | [] => 0
  | B :: rest => max (Greedy.totalWeight B) (representativeBound rest)

theorem weight_le_representativeBound {B : Matrix 4} {representatives : List (Matrix 4)}
    (member : B ∈ representatives) : Greedy.totalWeight B ≤ representativeBound representatives := by
  induction representatives with
  | nil => simp at member
  | cons C rest ih =>
    rcases List.mem_cons.mp member with h | h
    · subst B
      simp only [representativeBound]
      omega
    · have := ih h
      simp only [representativeBound]
      omega

/-- The precise finite-nonfork hypothesis of the source, represented by a
finite list of skew matrices and arbitrary genuine relabelings. -/
def FiniteNonforkOrbit (B : Matrix 4) : Prop :=
  ∃ representatives : List (Matrix 4),
    (∀ C ∈ representatives, SkewSymmetric C) ∧
    ∀ word, Nonfork (applyWord B word) →
      ∃ C ∈ representatives, ∃ p : Relabeling 4, applyWord B word = relabel C p

theorem finite_nonfork_weight_bound {B : Matrix 4} (finite : FiniteNonforkOrbit B) :
    ∃ bound : Int, ∀ word, Nonfork (applyWord B word) →
      Greedy.totalWeight (applyWord B word) ≤ bound := by
  obtain ⟨representatives, skew, covers⟩ := finite
  refine ⟨representativeBound representatives, ?_⟩
  intro word nonfork
  obtain ⟨C, member, p, eq⟩ := covers word nonfork
  rw [eq, totalWeight_relabel C (skew C member) p]
  exact weight_le_representativeBound member

/-- Every retained endpoint has bounded weight, even if the initial input is
itself a fork. A nonfork endpoint uses the finite class bound; every fork child
strictly decreases weight. -/
theorem retained_word_weight_bound (B : Matrix 4) (bound : Int)
    (nonforkBound : ∀ word, Nonfork (applyWord B word) →
      Greedy.totalWeight (applyWord B word) ≤ bound)
    (word : List (Fin 4)) (path : RetainedWord B word) :
    Greedy.totalWeight (applyWord B word) ≤ max (Greedy.totalWeight B) bound := by
  induction path with
  | nil => simp only [applyWord]; omega
  | @cons B k word keep tail ih =>
    have childBound : ∀ rest, Nonfork (applyWord (mutate B k) rest) →
        Greedy.totalWeight (applyWord (mutate B k) rest) ≤ bound := by
      intro rest nonfork
      exact nonforkBound (k :: rest) nonfork
    have endpointBound := ih childBound
    have firstBound : Greedy.totalWeight (mutate B k) ≤ max (Greedy.totalWeight B) bound := by
      by_cases h : Nonfork (mutate B k)
      · have := nonforkBound [k] h
        simp only [applyWord] at this
        omega
      · have hex : ∃ r, GraphFork (mutate B k) r := by
          classical
          exact Classical.byContradiction (fun hn => h (fun r hr => hn ⟨r, hr⟩))
        obtain ⟨r, fork⟩ := hex
        have := retained_fork_child_decreases keep fork
        omega
    change Greedy.totalWeight (applyWord (mutate B k) word) ≤ _
    omega

theorem finite_nonfork_retained_weight_bound (B : Matrix 4) (finite : FiniteNonforkOrbit B) :
    ∃ bound : Int, ∀ word, RetainedWord B word →
      Greedy.totalWeight (applyWord B word) ≤ bound := by
  obtain ⟨bound, hbound⟩ := finite_nonfork_weight_bound finite
  exact ⟨max (Greedy.totalWeight B) bound,
    fun word path => retained_word_weight_bound B bound hbound word path⟩

/-- A concrete finite box of integer coordinates. -/
def coordinateBox (bound : Nat) : List Int :=
  (List.range (2 * bound + 1)).map (fun n : Nat => (n : Int) - (bound : Int))

def matrixBox (bound : Nat) : List (Matrix 4) :=
  let values := coordinateBox bound
  values.flatMap fun a => values.flatMap fun b => values.flatMap fun c =>
    values.flatMap fun d => values.flatMap fun e => values.map fun f => ofSix a b c d e f

theorem coordinateBox_complete (bound : Nat) (x : Int)
    (lower : -(bound : Int) ≤ x) (upper : x ≤ (bound : Int)) :
    x ∈ coordinateBox bound := by
  apply List.mem_map.mpr
  refine ⟨(x + (bound : Int)).toNat, ?_, ?_⟩
  · apply List.mem_range.mpr
    omega
  · omega

theorem matrixBox_complete (bound : Nat) (B : Matrix 4) (skew : SkewSymmetric B)
    (weight : Greedy.totalWeight B ≤ (bound : Int)) : B ∈ matrixBox bound := by
  have h := weight
  simp only [Greedy.totalWeight, Greedy.magnitude] at h
  have h01 := coordinateBox_complete bound (B 0 1) (by omega) (by omega)
  have h02 := coordinateBox_complete bound (B 0 2) (by omega) (by omega)
  have h03 := coordinateBox_complete bound (B 0 3) (by omega) (by omega)
  have h12 := coordinateBox_complete bound (B 1 2) (by omega) (by omega)
  have h13 := coordinateBox_complete bound (B 1 3) (by omega) (by omega)
  have h23 := coordinateBox_complete bound (B 2 3) (by omega) (by omega)
  simp only [matrixBox, List.mem_flatMap, List.mem_map]
  exact ⟨B 0 1, h01, B 0 2, h02, B 0 3, h03, B 1 2, h12,
    B 1 3, h13, B 2 3, h23, ofSix_reconstruct B skew⟩

/-- Under exactly finite nonfork part, the entire retained labeled exploration
is contained in a finite explicit list, including when the seed is a fork. -/
theorem finite_retained_orbit (B : Matrix 4) (skew : SkewSymmetric B)
    (finite : FiniteNonforkOrbit B) :
    ∃ states : List (Matrix 4), ∀ word, RetainedWord B word → applyWord B word ∈ states := by
  obtain ⟨bound, hb⟩ := finite_nonfork_retained_weight_bound B finite
  refine ⟨matrixBox bound.toNat, ?_⟩
  intro word path
  apply matrixBox_complete bound.toNat _ (word_preserves_skew B word skew)
  have := hb word path
  omega

theorem retainedWord_append {B : Matrix 4} {first rest : List (Fin 4)}
    (left : RetainedWord B first) (right : RetainedWord (applyWord B first) rest) :
    RetainedWord B (first ++ rest) := by
  induction left with
  | nil => exact right
  | cons keep _ ih => exact .cons keep (ih right)

/-- The finite mathematical outcome promised by the pruning theorem: either
an actual acyclic word or a finite cyclic set with every outgoing edge checked.
The operational breadth-first queue and its parser are separate obligations. -/
theorem finite_core_or_acyclic (B : Matrix 4) (skew : SkewSymmetric B)
    (finite : FiniteNonforkOrbit B) :
    MutationAcyclic B ∨ ∃ states : List (Matrix 4),
      B ∈ states ∧ (∀ C ∈ states, ¬ Acyclic C) ∧
      ∀ C ∈ states, ∀ k, mutate C k ∈ states ∨ GraphFork (mutate C k) k := by
  classical
  by_cases ma : MutationAcyclic B
  · exact Or.inl ma
  · right
    obtain ⟨boxStates, covers⟩ := finite_retained_orbit B skew finite
    let reaches : Matrix 4 → Prop := fun C =>
      ∃ word, RetainedWord B word ∧ applyWord B word = C
    let states := boxStates.filter (fun C => decide (reaches C))
    have mem_iff (C : Matrix 4) : C ∈ states ↔ reaches C := by
      constructor
      · intro member
        have h := (List.mem_filter.mp member).2
        exact of_decide_eq_true h
      · rintro ⟨word, retained, rfl⟩
        apply List.mem_filter.mpr
        exact ⟨covers word retained, by simp only [decide_eq_true_eq]; exact ⟨word, retained, rfl⟩⟩
    refine ⟨states, (mem_iff B).mpr ⟨[], .nil B, rfl⟩, ?_, ?_⟩
    · intro C member acyclic
      obtain ⟨word, _, eq⟩ := (mem_iff C).mp member
      exact ma ⟨word, eq ▸ acyclic⟩
    · intro C member k
      by_cases fork : GraphFork (mutate C k) k
      · exact Or.inr fork
      · left
        obtain ⟨word, retained, eq⟩ := (mem_iff C).mp member
        apply (mem_iff _).mpr
        refine ⟨word ++ [k], ?_, ?_⟩
        · apply retainedWord_append retained
          rw [eq]
          exact .cons fork (.nil _)
        · simp only [applyWord_append, eq, applyWord]

/-- Exhaustion is sound only after all four outgoing mutations of every stored
state have a stored child or the exact fork return certificate. -/
theorem exhausted_core_NMA (core : Matrix 4 → Prop)
    (cyclic : ∀ B, core B → ¬ Acyclic B)
    (closed : ∀ B, core B → ∀ k, core (mutate B k) ∨ GraphFork (mutate B k) k)
    {B : Matrix 4} (member : core B) : ¬ MutationAcyclic B := by
  apply Forks.fork_shield_NMA core cyclic
  · intro C hc k
    rcases closed C hc k with retained | pruned
    · exact Or.inl retained
    · exact Or.inr (graphFork_to_framed _ _ pruned)
  · exact member

end QuiverProofs.ForkPruning
