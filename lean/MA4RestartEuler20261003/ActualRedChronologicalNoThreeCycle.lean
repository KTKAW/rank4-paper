import MA4RestartEuler20261003.ActualSignedNormalization
import MA4RestartArrow20261003.ActualFrameChronology

/-! Red chronological Euler exclusion from the OLD joint-induction actual
frame and the original six-field SeedInv. All fixed model hypotheses are
derived and the terminal numeric order is reselected on the same objects. -/
namespace QuiverProofs.MA4RestartActualRedChronologicalNoThreeCycle
open Module CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open MAExistenceLiterature MAExistenceCoefficients MAExistenceTeamBRootPositivity
  MAExistenceTeamCTriangleOutside MAExistenceSupportChronology MAExistenceTeamCCertificateTransport
  MAExistenceTeamDJointSeed MAExistenceTeamBAdjacentHurwitz Cosquare
  MA4RestartWeightedQuiverModel MA4RestartFreePathProjectives MA4RestartModelExt
  MA4RestartMatrixEuler MA4RestartResolvedModelEuler MA4RestartActualSignedNormalization
  MA4RestartArrow20261003.AdjacentExceptionalFrame
  MA4RestartArrow20261003.ActualLeftSweep MA4RestartArrow20261003.ActualFrameChronology
variable (B : Matrix 4) (K : Type) [Field K]
local instance actualEnoughProjectives : EnoughProjectives (Representation B K) :=
  representation_enoughProjectives B K
local instance actualHasExt : HasExt.{0} (Representation B K) := representation_hasExt B K
local instance actualFiniteBiproducts : HasFiniteBiproducts (Representation B K) :=
  Abelian.hasFiniteBiproducts

theorem actual_realization_normalized (U D : Matrix 4) (hFrame : OrderedRootFrame B U D)
    (hActual : ActualRealization (vertexFunctor B K) D) :
    ∃ M : Fin 4 → Representation B K, ExceptionalFrame (vertexFunctor B K) M ∧
      ∀ a, dimensionVector B K (M a) = fun b => colorSign (columnColor D) a * D b a := by
  obtain ⟨M,s,hM,hSigned⟩ := hActual
  exact ⟨M,hM,(actual_signed_dimensions_normalized B K U D hFrame.2.2.1 M s
    (fun a => (hSigned a).1) (fun a b => (hSigned a).2 b)).2⟩

theorem actual_realization_no_three_cycle (U D : Matrix 4) (hB : SkewSymmetric B)
    (hs : add U (transpose U) = initialCompanion B)
    (ha : add U (scale (-1) (transpose U)) = reverse B)
    (hFrame : OrderedRootFrame B U D)
    (hActual : ActualRealization (vertexFunctor B K) D)
    (i j l : Fin 4) (hij : i ≠ j) (hjl : j ≠ l) (hli : l ≠ i) :
    noEulerThreeCycle (normalizedEuler (coefficientBilinear U D) (columnColor D)) i j l := by
  obtain ⟨M,s,hM,hSigned⟩ := hActual
  exact signed_actual_ordered_frame_no_three_cycle B K U D hB hs ha hFrame M s
    (fun a => (hSigned a).1) hM.finiteVertices (fun a b => (hSigned a).2 b)
    hM.rigid hM.reverseExt i j l hij hjl hli

theorem actual_relabelled_realization_no_three_cycle (U D : Matrix 4) (hB : SkewSymmetric B)
    (hs : add U (transpose U) = initialCompanion B)
    (ha : add U (scale (-1) (transpose U)) = reverse B)
    (q : Relabeling 4) (hFrame : OrderedRootFrame B U (columnRelabel D q))
    (hActual : ActualRealization (vertexFunctor B K) (columnRelabel D q))
    (i j l : Fin 4) (hij : i ≠ j) (hjl : j ≠ l) (hli : l ≠ i) :
    noEulerThreeCycle (normalizedEuler (coefficientBilinear U D) (columnColor D)) i j l := by
  obtain ⟨M,s,hM,hSigned⟩ := hActual
  exact signed_actual_relabelled_frame_no_three_cycle B K U D hB hs ha q hFrame M s
    (fun a => (hSigned a).1) hM.finiteVertices (fun a b => (hSigned a).2 b)
    hM.rigid hM.reverseExt i j l hij hjl hli

/-- The red chronological Euler supplier has only the old actual joint
frame, original current invariant, and original numerical form as premises. -/
theorem principal_seed_red_no_three_cycle (U : Matrix 4) (hB : SkewSymmetric B)
    (hs : add U (transpose U) = initialCompanion B)
    (ha : add U (scale (-1) (transpose U)) = reverse B)
    (w : List (Fin 4)) (hInv : SeedInv B w)
    (hOld : UnorderedActualRealization (vertexFunctor B K) (principalSeed B w).2)
    (k : Fin 4) (hk : columnColor (principalSeed B w).2 k = false)
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
  have hNext := principalSeed_red_unordered_actual_realization (vertexFunctor B K)
    (vertex_preserves_zero B K) (vertex_preserves_finite_limits B K)
    (vertex_preserves_finite_colimits B K) (fun f hf => vertices_jointly_reflect_epi B K f hf)
    (model_hereditary B K) (model_finite_hom_ext B K) B U hEuler hB hs ha w hInv hOld k hk
  obtain ⟨p,s,ht,hp,hColors,hCurrent,hPrefixes,hTerminal,hExact⟩ :=
    principalSeed_red_fullFrameSweep B U hB hs ha w hInv k hk
  let q := p.trans (leftPermutation (p.invFun k) s ht)
  have hOrdered := current_order_actual_realization (vertexFunctor B K)
    (model_hereditary B K) (model_finite_hom_ext B K) U hEuler
    (principalSeed B (w ++ [k])).2 q hTerminal.2.2 hNext
  exact actual_relabelled_realization_no_three_cycle B K U
    (principalSeed B (w ++ [k])).2 hB hs ha q hTerminal hOrdered i j l hij hjl hli

#print axioms principal_seed_red_no_three_cycle
end QuiverProofs.MA4RestartActualRedChronologicalNoThreeCycle
