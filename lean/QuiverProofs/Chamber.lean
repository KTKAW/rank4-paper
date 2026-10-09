import QuiverProofs.Mutation

namespace QuiverProofs

theorem fin4_cases (i : Fin 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega

/-- Constructive half of thm:five-parameter (including the cancellation boundary).
The opposite implication uses total properness and is not asserted here.
-/
theorem five_parameter_mutation (x y z u v : Int) (hx : 0 < x) (hy : 0 < y) :
    mutate (ofSix 0 (-x) y (-z) (-u) (-v)) 0 =
      ofSix 0 x (-y) (-z) (-u) (x*y-v) := by
  funext i j
  rcases fin4_cases i with rfl | rfl | rfl | rfl <;>
    rcases fin4_cases j with rfl | rfl | rfl | rfl <;>
    simp [mutate, ofSix, correction] <;> grind

theorem five_parameter_MA (x y z u v : Int)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hu : 0 < u)
    (hcancel : x*y ≤ v) :
    MutationAcyclic (ofSix 0 (-x) y (-z) (-u) (-v)) := by
  refine ⟨[0], ?_⟩
  simp only [applyWord, five_parameter_mutation x y z u v hx hy]
  -- The explicit topological order is (3,0,2,1).
  refine ⟨(fun i => match i.val with | 3 => 0 | 0 => 1 | 2 => 2 | _ => 3), ?_⟩
  intro i j
  rcases fin4_cases i with rfl | rfl | rfl | rfl <;>
    rcases fin4_cases j with rfl | rfl | rfl | rfl <;>
    simp [ofSix] <;> omega

end QuiverProofs
