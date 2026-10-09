import MA4RestartEuler20261003.ActualRedChronologicalNoThreeCycle
import MA4RestartArrow20261003.ActualRightSweep

/-! Green chronological Euler and the combined two-color Euler supplier.
Only OLD separate joint-induction realization and original SeedInv are used. -/
namespace QuiverProofs.MA4RestartActualGreenChronologicalNoThreeCycle
open Module CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open MAExistenceLiterature MAExistenceCoefficients MAExistenceTeamBRootPositivity
  MAExistenceTeamCTriangleOutside MAExistenceSupportChronology MAExistenceTeamCCertificateTransport
  MAExistenceTeamDJointSeed MAExistenceTeamBAdjacentHurwitz Cosquare
  MA4RestartWeightedQuiverModel MA4RestartFreePathProjectives MA4RestartModelExt
  MA4RestartMatrixEuler MA4RestartResolvedModelEuler MA4RestartActualSignedNormalization
  MA4RestartArrow20261003.AdjacentExceptionalFrame
  MA4RestartArrow20261003.ActualLeftSweep MA4RestartArrow20261003.ActualFrameChronology
  MA4RestartArrow20261003.ActualRightSweep MA4RestartActualRedChronologicalNoThreeCycle
variable (B : Matrix 4) (K : Type) [Field K]
local instance actualEnoughProjectives : EnoughProjectives (Representation B K) :=
  representation_enoughProjectives B K
local instance actualHasExt : HasExt.{0} (Representation B K) := representation_hasExt B K
local instance actualFiniteBiproducts : HasFiniteBiproducts (Representation B K) :=
  Abelian.hasFiniteBiproducts

/-- The green chronological Euler supplier has only the old actual joint
frame, original current invariant, and original numerical form as premises. -/
theorem principal_seed_green_no_three_cycle (U : Matrix 4) (hB : SkewSymmetric B)
    (hs : add U (transpose U) = initialCompanion B)
    (ha : add U (scale (-1) (transpose U)) = reverse B)
    (w : List (Fin 4)) (hInv : SeedInv B w)
    (hOld : UnorderedActualRealization (vertexFunctor B K) (principalSeed B w).2)
    (k : Fin 4) (hk : columnColor (principalSeed B w).2 k = true)
    (i j l : Fin 4) (hij : i ≠ j) (hjl : j ≠ l) (hli : l ≠ i) :
    noEulerThreeCycle
      (normalizedEuler (coefficientBilinear U (principalSeed B (w ++ [k])).2)
        (columnColor (principalSeed B (w ++ [k])).2)) i j l := by
  have hEuler : ∀ X Y : Representation B K,
      (∀ a, Module.Finite K ((vertexFunctor B K a).obj X)) →
      (∀ a, Module.Finite K ((vertexFunctor B K a).obj Y)) →
      pairing U (vertexDimensions (vertexFunctor B K) X) (vertexDimensions (vertexFunctor B K) Y) =
        (Module.finrank K (X ⟶ Y) : Int) - (Module.finrank K (Abelian.Ext X Y 1) : Int) := by
    intro X Y hX hY
    exact model_euler_pairing B K U hB hs ha X Y hX hY
  have hNext := principalSeed_green_unordered_actual_realization (vertexFunctor B K)
    (vertex_preserves_zero B K) (vertex_preserves_finite_limits B K)
    (vertex_preserves_finite_colimits B K) (fun f hf => vertices_jointly_reflect_epi B K f hf)
    (model_hereditary B K) (model_finite_hom_ext B K) B U hEuler hB hs ha w hInv hOld k hk
  obtain ⟨p,s,ht,hp,hColors,hCurrent,hPrefixes,hTerminal,hExact⟩ :=
    principalSeed_green_fullFrameSweep B U hB hs ha w hInv k hk
  let q := p.trans (rightPermutation (p.invFun k) s ht)
  have hOrdered := current_order_actual_realization (vertexFunctor B K)
    (model_hereditary B K) (model_finite_hom_ext B K) U hEuler
    (principalSeed B (w ++ [k])).2 q hTerminal.2.2 hNext
  exact actual_relabelled_realization_no_three_cycle B K U
    (principalSeed B (w ++ [k])).2 hB hs ha q hTerminal hOrdered i j l hij hjl hli


/-- Both colors: actual next normalized No3 without a next invariant input. -/
theorem principal_seed_next_no_three_cycle (U : Matrix 4) (hB : SkewSymmetric B)
    (hs : add U (transpose U) = initialCompanion B)
    (ha : add U (scale (-1) (transpose U)) = reverse B)
    (w : List (Fin 4)) (hInv : SeedInv B w)
    (hOld : UnorderedActualRealization (vertexFunctor B K) (principalSeed B w).2)
    (k i j l : Fin 4) (hij : i ≠ j) (hjl : j ≠ l) (hli : l ≠ i) :
    noEulerThreeCycle
      (normalizedEuler (coefficientBilinear U (principalSeed B (w ++ [k])).2)
        (columnColor (principalSeed B (w ++ [k])).2)) i j l := by
  cases hk : columnColor (principalSeed B w).2 k with
  | false => exact principal_seed_red_no_three_cycle B K U hB hs ha w hInv hOld k hk i j l hij hjl hli
  | true => exact principal_seed_green_no_three_cycle B K U hB hs ha w hInv hOld k hk i j l hij hjl hli

/-- Actual next objects and their independent numerical Euler exclusion are
both supplied for the private simultaneous induction. -/
theorem principal_seed_next_actual_and_no_three_cycle (U : Matrix 4) (hB : SkewSymmetric B)
    (hs : add U (transpose U) = initialCompanion B)
    (ha : add U (scale (-1) (transpose U)) = reverse B)
    (w : List (Fin 4)) (hInv : SeedInv B w)
    (hOld : UnorderedActualRealization (vertexFunctor B K) (principalSeed B w).2)
    (k : Fin 4) :
    UnorderedActualRealization (vertexFunctor B K) (principalSeed B (w ++ [k])).2 ∧
    (∀ i j l : Fin 4, i ≠ j → j ≠ l → l ≠ i →
      noEulerThreeCycle
        (normalizedEuler (coefficientBilinear U (principalSeed B (w ++ [k])).2)
          (columnColor (principalSeed B (w ++ [k])).2)) i j l) := by
  have hEuler : ∀ X Y : Representation B K,
      (∀ a, Module.Finite K ((vertexFunctor B K a).obj X)) →
      (∀ a, Module.Finite K ((vertexFunctor B K a).obj Y)) →
      pairing U (vertexDimensions (vertexFunctor B K) X) (vertexDimensions (vertexFunctor B K) Y) =
        (Module.finrank K (X ⟶ Y) : Int) - (Module.finrank K (Abelian.Ext X Y 1) : Int) := by
    intro X Y hX hY
    exact model_euler_pairing B K U hB hs ha X Y hX hY
  refine ⟨?_,principal_seed_next_no_three_cycle B K U hB hs ha w hInv hOld k⟩
  cases hk : columnColor (principalSeed B w).2 k with
  | false =>
      exact principalSeed_red_unordered_actual_realization (vertexFunctor B K)
        (vertex_preserves_zero B K) (vertex_preserves_finite_limits B K)
        (vertex_preserves_finite_colimits B K) (fun f hf => vertices_jointly_reflect_epi B K f hf)
        (model_hereditary B K) (model_finite_hom_ext B K) B U hEuler hB hs ha w hInv hOld k hk
  | true =>
      exact principalSeed_green_unordered_actual_realization (vertexFunctor B K)
        (vertex_preserves_zero B K) (vertex_preserves_finite_limits B K)
        (vertex_preserves_finite_colimits B K) (fun f hf => vertices_jointly_reflect_epi B K f hf)
        (model_hereditary B K) (model_finite_hom_ext B K) B U hEuler hB hs ha w hInv hOld k hk


/-- Both colors retain an actual ordered next tuple, all ordinary frame fields,
exact normalized next columns, and every original-label Euler exclusion. -/
theorem principal_seed_next_joint_frame (U : Matrix 4) (hB : SkewSymmetric B)
    (hs : add U (transpose U) = initialCompanion B)
    (ha : add U (scale (-1) (transpose U)) = reverse B)
    (w : List (Fin 4)) (hInv : SeedInv B w)
    (hOld : UnorderedActualRealization (vertexFunctor B K) (principalSeed B w).2)
    (k : Fin 4) :
    ∃ (q : Relabeling 4) (M : Fin 4 → Representation B K),
      OrderedRootFrame B U (columnRelabel (principalSeed B (w ++ [k])).2 q) ∧
      ExceptionalFrame (vertexFunctor B K) M ∧
      (∀ a, dimensionVector B K (M a) = fun b =>
        colorSign (columnColor (columnRelabel (principalSeed B (w ++ [k])).2 q)) a *
          columnRelabel (principalSeed B (w ++ [k])).2 q b a) ∧
      (∀ i j l : Fin 4, i ≠ j → j ≠ l → l ≠ i →
        noEulerThreeCycle
          (normalizedEuler (coefficientBilinear U (principalSeed B (w ++ [k])).2)
            (columnColor (principalSeed B (w ++ [k])).2)) i j l) := by
  obtain ⟨hNext,hNo3⟩ := principal_seed_next_actual_and_no_three_cycle B K U hB hs ha w hInv hOld k
  have hNumeric : ∃ q : Relabeling 4,
      OrderedRootFrame B U (columnRelabel (principalSeed B (w ++ [k])).2 q) := by
    cases hk : columnColor (principalSeed B w).2 k with
    | false =>
        obtain ⟨p,s,ht,hp,hColors,hCurrent,hPrefixes,hTerminal,hExact⟩ :=
          principalSeed_red_fullFrameSweep B U hB hs ha w hInv k hk
        exact ⟨p.trans (leftPermutation (p.invFun k) s ht),hTerminal⟩
    | true =>
        obtain ⟨p,s,ht,hp,hColors,hCurrent,hPrefixes,hTerminal,hExact⟩ :=
          principalSeed_green_fullFrameSweep B U hB hs ha w hInv k hk
        exact ⟨p.trans (rightPermutation (p.invFun k) s ht),hTerminal⟩
  obtain ⟨q,hFrame⟩ := hNumeric
  have hEuler : ∀ X Y : Representation B K,
      (∀ a, Module.Finite K ((vertexFunctor B K a).obj X)) →
      (∀ a, Module.Finite K ((vertexFunctor B K a).obj Y)) →
      pairing U (vertexDimensions (vertexFunctor B K) X) (vertexDimensions (vertexFunctor B K) Y) =
        (Module.finrank K (X ⟶ Y) : Int) - (Module.finrank K (Abelian.Ext X Y 1) : Int) := by
    intro X Y hX hY
    exact model_euler_pairing B K U hB hs ha X Y hX hY
  have hActual := current_order_actual_realization (vertexFunctor B K)
    (model_hereditary B K) (model_finite_hom_ext B K) U hEuler
    (principalSeed B (w ++ [k])).2 q hFrame.2.2 hNext
  obtain ⟨M,hM,hDimensions⟩ := actual_realization_normalized B K U
    (columnRelabel (principalSeed B (w ++ [k])).2 q) hFrame hActual
  exact ⟨q,M,hFrame,hM,hDimensions,hNo3⟩

#print axioms principal_seed_green_no_three_cycle
#print axioms principal_seed_next_actual_and_no_three_cycle
end QuiverProofs.MA4RestartActualGreenChronologicalNoThreeCycle
