import Rank4Round3.MutationSignPullback

/-! A computable list of all 729 exact sign patterns, for executable formula ASTs. -/

namespace Rank4AlgebraAudit
open Rank4Round3

def sixSigns (a b c d e f : Sign3) : SignPattern := fun i =>
  match i.val with
  | 0 => a | 1 => b | 2 => c | 3 => d | 4 => e | _ => f

def allSignPatterns : List SignPattern :=
  (List.finRange 3).flatMap fun a =>
  (List.finRange 3).flatMap fun b =>
  (List.finRange 3).flatMap fun c =>
  (List.finRange 3).flatMap fun d =>
  (List.finRange 3).flatMap fun e =>
  (List.finRange 3).map fun f => sixSigns a b c d e f

private theorem fin6_cases (i : Fin 6) :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by
  omega

theorem sixSigns_coordinates (s : SignPattern) :
    sixSigns (s 0) (s 1) (s 2) (s 3) (s 4) (s 5) = s := by
  funext i
  rcases fin6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rfl

theorem allSignPatterns_complete (s : SignPattern) : s ∈ allSignPatterns := by
  unfold allSignPatterns
  apply List.mem_flatMap.mpr
  refine ⟨s 0, by simp, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨s 1, by simp, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨s 2, by simp, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨s 3, by simp, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨s 4, by simp, ?_⟩
  apply List.mem_map.mpr
  exact ⟨s 5, by simp, sixSigns_coordinates s⟩

set_option maxRecDepth 8192 in
theorem allSignPatterns_length : allSignPatterns.length = 729 := by
  decide

#print axioms allSignPatterns_complete
#print axioms allSignPatterns_length

end Rank4AlgebraAudit
