import QuiverProofs.MAExistenceTeamCTrianglePivot
import QuiverProofs.MAExistenceTeamCOrientedOutside

/-! All ordered actual next triangles. Current data settles repeated labels,
missing next edges, pivot triangles, unmixed outside triangles, and directed
outside cycles. The remaining normalized Euler exclusion is supplied only for
supported, mixed, nonoriented outside triangles. Next arrow signs are supplied
independently. Neither supply nor all-word preservation is proved here. -/
namespace QuiverProofs.MAExistenceTeamCTriangleRefinedClosure
open MAExistenceLiterature MAExistenceCompanions MAExistenceAuxiliaryOrders
open MAExistenceCoefficients MAExistenceTeamCTriangleOutside
open MAExistenceTeamCOrientedOutside

open MAExistenceTeamCTrianglePivot MAExistenceTeamDJointSeed
open MAExistenceTeamCCertificateTransport Cosquare

private theorem next_triangle_degenerate (B A : Matrix 4) (hB : SkewSymmetric B)
    (i j l : Fin 4) (h : i = j ∨ j = l ∨ l = i) :
    triangleCompanionAdmissible B A i j l := by
  have hdiag : ∀ t, B t t = 0 := by intro t; have := hB t t; omega
  rcases h with h | h | h
  · subst j; intro hn; exact (hn (hdiag i)).elim
  · subst l; intro _ hn; exact (hn (hdiag j)).elim
  · subst l; intro _ _ hn; exact (hn (hdiag i)).elim

/-- All actual next triangles. Only a supported, mixed, nonoriented outside
triangle consumes the supplied next arrow signs and normalized-root Euler
exclusion. Both supplies remain explicit and unproved; there is no all-word
claim or added future-state field. -/
theorem principalSeed_triangles_of_supported_mixed_nonoriented_noEulerThreeCycle
    (B₀ U₀ : Matrix 4) (hB₀ : SkewSymmetric B₀)
    (hU₀s : add U₀ (transpose U₀) = initialCompanion B₀)
    (hU₀a : add U₀ (scale (-1) (transpose U₀)) = reverse B₀)
    (w : List (Fin 4)) (k : Fin 4) (h : SeedInv B₀ w)
    (hs : ArrowSigns (principalSeed B₀ (w ++ [k])).1
      (coefficientCompanion B₀ (principalSeed B₀ (w ++ [k])).2)
      (columnColor (principalSeed B₀ (w ++ [k])).2))
    (hn : ∀ i j l : Fin 4, i ≠ j → j ≠ l → l ≠ i →
      i ≠ k → j ≠ k → l ≠ k →
      (principalSeed B₀ (w ++ [k])).1 i j ≠ 0 →
      (principalSeed B₀ (w ++ [k])).1 j l ≠ 0 →
      (principalSeed B₀ (w ++ [k])).1 l i ≠ 0 →
      ¬ ((pivotWeight (principalSeed B₀ w).1
          (columnColor (principalSeed B₀ w).2) k i = 0 ↔
        pivotWeight (principalSeed B₀ w).1
          (columnColor (principalSeed B₀ w).2) k j = 0) ∧
        (pivotWeight (principalSeed B₀ w).1
          (columnColor (principalSeed B₀ w).2) k j = 0 ↔
        pivotWeight (principalSeed B₀ w).1
          (columnColor (principalSeed B₀ w).2) k l = 0)) →
      noDirectedTriangle (principalSeed B₀ (w ++ [k])).1 i j l →
      noEulerThreeCycle
        (normalizedEuler (coefficientBilinear U₀ (principalSeed B₀ (w ++ [k])).2)
          (columnColor (principalSeed B₀ (w ++ [k])).2)) i j l) :
    ∀ i j l, triangleCompanionAdmissible (principalSeed B₀ (w ++ [k])).1
      (coefficientCompanion B₀ (principalSeed B₀ (w ++ [k])).2) i j l := by
  have hB := principalSeed_skew B₀ hB₀ w
  have hBn := principalSeed_skew B₀ hB₀ (w ++ [k])
  have hC := seedInv_signCoherent B₀ hB₀ w h
  have he : principalSeed B₀ (w ++ [k]) = mutateSeed (principalSeed B₀ w) k :=
    evolve_append_singleton B₀ identityCoefficients w k
  intro i j l
  by_cases hij : i = j
  · exact next_triangle_degenerate _ _ hBn i j l (Or.inl hij)
  by_cases hjl : j = l
  · exact next_triangle_degenerate _ _ hBn i j l (Or.inr (Or.inl hjl))
  by_cases hli : l = i
  · exact next_triangle_degenerate _ _ hBn i j l (Or.inr (Or.inr hli))
  by_cases h1 : (principalSeed B₀ (w ++ [k])).1 i j = 0
  · intro hb; exact (hb h1).elim
  by_cases h2 : (principalSeed B₀ (w ++ [k])).1 j l = 0
  · intro _ hb; exact (hb h2).elim
  by_cases h3 : (principalSeed B₀ (w ++ [k])).1 l i = 0
  · intro _ _ hb; exact (hb h3).elim
  by_cases hp : k = i ∨ k = j ∨ k = l
  · have ht := coefficientMutation_triangleAdmissible_of_contains_pivot B₀
      (principalSeed B₀ w).1 (principalSeed B₀ w).2 k i j l hB
      h.companion h.arrowSigns h.admissible hC hp
    simpa only [he, mutateSeed] using ht
  have hik : i ≠ k := fun hi => hp (Or.inl hi.symm)
  have hjk : j ≠ k := fun hj => hp (Or.inr (Or.inl hj.symm))
  have hlk : l ≠ k := fun hl => hp (Or.inr (Or.inr hl.symm))
  by_cases hm :
      (pivotWeight (principalSeed B₀ w).1
        (columnColor (principalSeed B₀ w).2) k i = 0 ↔
       pivotWeight (principalSeed B₀ w).1
        (columnColor (principalSeed B₀ w).2) k j = 0) ∧
      (pivotWeight (principalSeed B₀ w).1
        (columnColor (principalSeed B₀ w).2) k j = 0 ↔
       pivotWeight (principalSeed B₀ w).1
        (columnColor (principalSeed B₀ w).2) k l = 0)
  · exact principalSeed_outside_triangle_of_unmixed_weights B₀ hB₀ w k i j l h
      hik hjk hlk hij hjl hli hm.1 hm.2
  by_cases hc :
      (0 < (principalSeed B₀ (w ++ [k])).1 i j ∧
       0 < (principalSeed B₀ (w ++ [k])).1 j l ∧
       0 < (principalSeed B₀ (w ++ [k])).1 l i) ∨
      ((principalSeed B₀ (w ++ [k])).1 i j < 0 ∧
       (principalSeed B₀ (w ++ [k])).1 j l < 0 ∧
       (principalSeed B₀ (w ++ [k])).1 l i < 0)
  · have hc' : (0 < mutate (principalSeed B₀ w).1 k i j ∧
          0 < mutate (principalSeed B₀ w).1 k j l ∧
          0 < mutate (principalSeed B₀ w).1 k l i) ∨
        (mutate (principalSeed B₀ w).1 k i j < 0 ∧
          mutate (principalSeed B₀ w).1 k j l < 0 ∧
          mutate (principalSeed B₀ w).1 k l i < 0) := by
      simpa only [he, mutateSeed] using hc
    have ht := coefficientMutation_oriented_outside_triangleAdmissible B₀
      (principalSeed B₀ w).1 (principalSeed B₀ w).2 k i j l hik hjk hlk hB
      h.companion h.arrowSigns h.admissible hC hc'
    simpa only [he, mutateSeed] using ht
  · exact principalSeed_outside_triangle_of_noEulerThreeCycle B₀ U₀ hB₀ hU₀s hU₀a
      w k i j l h hik hjk hlk hij hjl hli hs
      (hn i j l hij hjl hli hik hjk hlk h1 h2 h3 hm hc)

end QuiverProofs.MAExistenceTeamCTriangleRefinedClosure
