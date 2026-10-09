import MA4RestartEuler20261003.ActualFrameNoThreeCycle

/-! Free signed realization metadata is forced to be the literal column
color sign by nonnegative actual dimensions and nonzero unit Euler columns. -/
namespace QuiverProofs.MA4RestartActualSignedNormalization
open Module CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open MAExistenceLiterature MAExistenceCoefficients MAExistenceTeamBRootPositivity
  MAExistenceTeamCTriangleOutside MAExistenceSupportChronology MAExistenceTeamCCertificateTransport
  MA4RestartWeightedQuiverModel MA4RestartModelExt MA4RestartMatrixEuler
  MA4RestartResolvedModelEuler MA4RestartActualFrameNoThreeCycle

theorem signed_nonnegative_column_color (D : Matrix 4) (j : Fin 4) (s : Int)
    (hs : s = 1 ∨ s = -1) (hNonzero : ∃ a, D a j ≠ 0)
    (hNonnegative : ∀ a, 0 ≤ s * D a j) :
    s = colorSign (columnColor D) j := by
  rcases hs with rfl | rfl
  · have hg : columnColor D j = true := by
      simp only [columnColor,decide_eq_true_eq]
      intro a
      simpa only [one_mul] using hNonnegative a
    simp [colorSign,hg]
  · have hg : columnColor D j = false := by
      simp only [columnColor,decide_eq_false_iff_not]
      intro hp
      obtain ⟨a,ha⟩ := hNonzero
      have hn := hNonnegative a
      have hpa := hp a
      simp only [neg_one_mul] at hn
      exact ha (by omega)
    simp [colorSign,hg]

theorem unit_euler_column_nonzero (U D : Matrix 4) (a : Fin 4)
    (hUnit : pairing U (column D a) (column D a) = 1) : ∃ b, D b a ≠ 0 := by
  by_contra hn
  push_neg at hn
  simp [pairing,column,hn] at hUnit

variable (B : Matrix 4) (K : Type) [Field K]
local instance actualHasExt : HasExt.{0} (Representation B K) := representation_hasExt B K

/-- Actual signed vertex dimensions determine the exact normalization;
no separate future color or sign-coherence assertion is an input. -/
theorem actual_signed_dimensions_normalized (U D : Matrix 4)
    (hUnit : ∀ a, pairing U (column D a) (column D a) = 1)
    (M : Fin 4 → Representation B K) (s : Fin 4 → Int)
    (hSigns : ∀ a, s a = 1 ∨ s a = -1)
    (hDimensions : ∀ a b, (Module.finrank K ((vertexFunctor B K b).obj (M a)) : Int) =
      s a * D b a) :
    (∀ a, s a = colorSign (columnColor D) a) ∧
    (∀ a, dimensionVector B K (M a) = fun b => colorSign (columnColor D) a * D b a) := by
  have hForced : ∀ a, s a = colorSign (columnColor D) a := by
    intro a
    apply signed_nonnegative_column_color D a (s a) (hSigns a)
      (unit_euler_column_nonzero U D a (hUnit a))
    intro b
    rw [← hDimensions a b]
    exact Int.natCast_nonneg _
  refine ⟨hForced,?_⟩
  intro a
  funext b
  change (Module.finrank K ((vertexFunctor B K b).obj (M a)) : Int) = _
  rw [hDimensions a b,hForced a]

/-- Exact signed sweep data consume static No3 after normalization is
derived. No next invariant, color transport or normalized dimension is assumed. -/
theorem signed_actual_ordered_frame_no_three_cycle (U D : Matrix 4) (hB : SkewSymmetric B)
    (hs : Cosquare.add U (Cosquare.transpose U) = initialCompanion B)
    (ha : Cosquare.add U (Cosquare.scale (-1) (Cosquare.transpose U)) = reverse B)
    (hFrame : OrderedRootFrame B U D) (M : Fin 4 → Representation B K) (s : Fin 4 → Int)
    (hSigns : ∀ a, s a = 1 ∨ s a = -1)
    (hFinite : ∀ a b, Module.Finite K ((vertexFunctor B K b).obj (M a)))
    (hDimensions : ∀ a b, (Module.finrank K ((vertexFunctor B K b).obj (M a)) : Int) =
      s a * D b a)
    (hRigid : ∀ a, ∀ e : Abelian.Ext (M a) (M a) 1, e = 0)
    (hReverseExt : ∀ a b, a < b → ∀ e : Abelian.Ext (M b) (M a) 1, e = 0)
    (i j l : Fin 4) (hij : i ≠ j) (hjl : j ≠ l) (hli : l ≠ i) :
    noEulerThreeCycle (normalizedEuler (coefficientBilinear U D) (columnColor D)) i j l := by
  have hNormalized := (actual_signed_dimensions_normalized B K U D hFrame.2.2.1
    M s hSigns hDimensions).2
  exact actual_ordered_frame_no_three_cycle B K U D hB hs ha hFrame
    M hFinite hNormalized hRigid hReverseExt i j l hij hjl hli

/-- The signed realization of a terminal relabelled frame directly yields
No3 in the original labels, with literal color normalization derived. -/
theorem signed_actual_relabelled_frame_no_three_cycle (U D : Matrix 4) (hB : SkewSymmetric B)
    (hs : Cosquare.add U (Cosquare.transpose U) = initialCompanion B)
    (ha : Cosquare.add U (Cosquare.scale (-1) (Cosquare.transpose U)) = reverse B)
    (q : Relabeling 4) (hFrame : OrderedRootFrame B U (columnRelabel D q))
    (M : Fin 4 → Representation B K) (s : Fin 4 → Int)
    (hSigns : ∀ a, s a = 1 ∨ s a = -1)
    (hFinite : ∀ a b, Module.Finite K ((vertexFunctor B K b).obj (M a)))
    (hDimensions : ∀ a b, (Module.finrank K ((vertexFunctor B K b).obj (M a)) : Int) =
      s a * (columnRelabel D q) b a)
    (hRigid : ∀ a, ∀ e : Abelian.Ext (M a) (M a) 1, e = 0)
    (hReverseExt : ∀ a b, a < b → ∀ e : Abelian.Ext (M b) (M a) 1, e = 0)
    (i j l : Fin 4) (hij : i ≠ j) (hjl : j ≠ l) (hli : l ≠ i) :
    noEulerThreeCycle (normalizedEuler (coefficientBilinear U D) (columnColor D)) i j l := by
  have hNormalized := (actual_signed_dimensions_normalized B K U (columnRelabel D q)
    hFrame.2.2.1 M s hSigns hDimensions).2
  exact actual_relabelled_frame_no_three_cycle B K U D hB hs ha q hFrame
    M hFinite hNormalized hRigid hReverseExt i j l hij hjl hli

#print axioms actual_signed_dimensions_normalized
#print axioms signed_actual_ordered_frame_no_three_cycle
#print axioms signed_actual_relabelled_frame_no_three_cycle
end QuiverProofs.MA4RestartActualSignedNormalization
