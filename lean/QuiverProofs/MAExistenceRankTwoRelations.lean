import QuiverProofs.MAExistenceTeamBRootPositivity

/-! Finite rank-two relations for the actual integral simple reflections.
All other integer entries of the symmetric matrix are unrestricted. There is
no definiteness, nonsingularity, finite-type, or root-coordinate hypothesis.
This module is independent of Team C's group and word constructions.
-/
namespace QuiverProofs.MAExistenceRankTwoRelations
open MAExistenceTeamBRootPositivity

private theorem fin4 (i : Fin 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega

private theorem pairing_simples (A : Matrix 4) (s t : Fin 4) :
    pairing A (simple s) (simple t) = A s t := by
  rcases fin4 s with rfl | rfl | rfl | rfl <;>
    rcases fin4 t with rfl | rfl | rfl | rfl <;>
    simp [pairing, simple]

/-- Conjugating an actual simple reflection is reflection in the actual
reflected simple root. -/
theorem simpleReflection_conjugation (A : Matrix 4)
    (hA : ∀ i j, A i j = A j i) (hd : ∀ i, A i i = 2)
    (s t : Fin 4) (x : Vector4) :
    simpleReflection A s (simpleReflection A t (simpleReflection A s x)) =
      reflection A (simpleReflection A s (simple t)) x := by
  have hs : pairing A (simple s) (simple s) = 2 := by
    rw [pairing_simple_self, hd]
  have hc := reflection_covariant A hA (simple s) (simple t)
    (simpleReflection A s x) hs
  change reflection A (simpleReflection A s (simple t))
    (reflection A (simple s) (reflection A (simple s) x)) =
      simpleReflection A s (simpleReflection A t (simpleReflection A s x)) at hc
  rw [reflection_involutive A (simple s) x hs] at hc
  exact hc.symm

/-- Zero off-diagonal entry gives commuting operators on the full lattice. -/
theorem simpleReflection_commute_of_zero (A : Matrix 4)
    (hA : ∀ i j, A i j = A j i) (hd : ∀ i, A i i = 2)
    (s t : Fin 4) (_hst : s ≠ t) (hentry : A s t = 0) (x : Vector4) :
    simpleReflection A s (simpleReflection A t x) =
      simpleReflection A t (simpleReflection A s x) := by
  have hs : pairing A (simple s) (simple s) = 2 := by
    rw [pairing_simple_self, hd]
  have hfix : simpleReflection A s (simple t) = simple t := by
    funext i
    simp only [simpleReflection, reflection, pairing_simples, hentry,
      Int.zero_mul, Int.sub_zero]
  have hc := reflection_covariant A hA (simple s) (simple t) x hs
  change reflection A (simpleReflection A s (simple t)) (simpleReflection A s x) =
    simpleReflection A s (simpleReflection A t x) at hc
  rw [hfix] at hc
  exact hc.symm

/-- Entry minus one gives the length-three braid relation on the full
integral lattice, even when the full Cartan form is singular or indefinite. -/
theorem simpleReflection_braid_of_neg_one (A : Matrix 4)
    (hA : ∀ i j, A i j = A j i) (hd : ∀ i, A i i = 2)
    (s t : Fin 4) (_hst : s ≠ t) (hentry : A s t = -1) (x : Vector4) :
    simpleReflection A s (simpleReflection A t (simpleReflection A s x)) =
      simpleReflection A t (simpleReflection A s (simpleReflection A t x)) := by
  have hroot : simpleReflection A s (simple t) =
      simpleReflection A t (simple s) := by
    funext i
    have hreverse : A t s = -1 := (hA t s).trans hentry
    simp only [simpleReflection, reflection, pairing_simples, hentry, hreverse]
    omega
  rw [simpleReflection_conjugation A hA hd s t x,
    simpleReflection_conjugation A hA hd t s x, hroot]

end QuiverProofs.MAExistenceRankTwoRelations
