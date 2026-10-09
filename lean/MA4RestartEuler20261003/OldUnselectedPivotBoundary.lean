import MA4RestartEuler20261003.ActualRedChronologicalNoThreeCycle

/-! Old unselected pivot boundaries for both directional sweeps.
Nonpositive exchange gives Hom zero; same old colors additionally give
Ext zero and zero exchange. Opposite old colors may retain Ext. -/
namespace QuiverProofs.MA4RestartOldUnselectedPivotBoundary
open Module CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open MAExistenceLiterature MAExistenceCoefficients MAExistenceCompanions
  MAExistenceTeamBRootPositivity MAExistenceTeamCTriangleOutside
  MAExistenceTeamCCertificateTransport MAExistenceTeamDJointSeed
  MAExistenceTeamBAdjacentHurwitz MAExistenceSupportChronology Cosquare
  MA4RestartWeightedQuiverModel MA4RestartFreePathProjectives MA4RestartModelExt
  MA4RestartMatrixEuler MA4RestartResolvedModelEuler MA4RestartActualFrameNoThreeCycle
  MACompletionPairPurity MACompletionScalarEndomorphisms
  MA4RestartArrow20261003.AdjacentExceptionalFrame

/-- All old color patterns; opposite colors need no Ext-zero assumption. -/
theorem nonpositive_boundary_dimensions (dH dE : Nat) (b : Int) (ci cj : Bool)
    (hB : b ≤ 0)
    (hEuler : (dH : Int) - (dE : Int) = -(if ci = cj then 1 else -1) * b)
    (hPure : dH = 0 ∨ dE = 0)
    (hSame : ci = cj → dH = 0) :
    dH = 0 ∧ (ci = cj → dE = 0 ∧ b = 0) := by
  by_cases hc : ci = cj
  · have hH := hSame hc
    simp only [if_pos hc, neg_one_mul] at hEuler
    have hE : dE = 0 := by omega
    exact ⟨hH,fun _ => ⟨hE,by omega⟩⟩
  · simp only [if_neg hc, neg_neg] at hEuler
    have hH : dH = 0 := by rcases hPure with h | h <;> omega
    exact ⟨hH,fun h => False.elim (hc h)⟩

section Generic
universe w v u z
variable {K : Type w} [Field K] {C : Type u}
  [Category.{v} C] [Abelian C] [Linear K C] [HasExt.{z} C]

/-- Categorical consumer of the exact old dimension law. -/
theorem nonpositive_boundary_hom (X Y : C) (b : Int) (ci cj : Bool)
    (hHered : ∀ T : C, HasProjectiveDimensionLT T 2)
    (hReverseExt : ∀ e : Abelian.Ext Y X 1, e = 0)
    (hRigidX : ∀ e : Abelian.Ext X X 1, e = 0)
    (hRigidY : ∀ e : Abelian.Ext Y Y 1, e = 0)
    (hIdX : 𝟙 X ≠ 0) (hIdY : 𝟙 Y ≠ 0)
    (hEndX : ∀ f : X ⟶ X, ∃ c : K, f = c • 𝟙 X)
    (hEndY : ∀ f : Y ⟶ Y, ∃ c : K, f = c • 𝟙 Y)
    (dH dE : Nat)
    (hHZ : dH = 0 ↔ ∀ f : X ⟶ Y, f = 0)
    (hEZ : dE = 0 ↔ ∀ e : Abelian.Ext X Y 1, e = 0)
    (hB : b ≤ 0)
    (hEuler : (dH : Int) - (dE : Int) = -(if ci = cj then 1 else -1) * b)
    (hSame : ci = cj → ∀ f : X ⟶ Y, f = 0) :
    (∀ f : X ⟶ Y, f = 0) ∧
      (ci = cj → (∀ e : Abelian.Ext X Y 1, e = 0) ∧ b = 0) := by
  letI := local_end_of_scalar_end X hIdX hEndX
  letI := local_end_of_scalar_end Y hIdY hEndY
  have hPure := dimension_purity_of_rigid X Y hHered hReverseExt hRigidX hRigidY dH dE hHZ hEZ
  obtain ⟨hH,hE⟩ := nonpositive_boundary_dimensions dH dE b ci cj hB hEuler hPure
    (fun hc => hHZ.mpr (hSame hc))
  exact ⟨hHZ.mp hH,fun hc => ⟨hEZ.mp (hE hc).1,(hE hc).2⟩⟩
end Generic

variable (B₀ : Matrix 4) (K : Type) [Field K]
local instance actualEnoughProjectives : EnoughProjectives (Representation B₀ K) :=
  representation_enoughProjectives B₀ K
local instance actualHasExt : HasExt.{0} (Representation B₀ K) := representation_hasExt B₀ K

/-- Exact fixed-model old boundary. No finite Hom/Ext, Euler, purity,
heredity, current same-color Hom, or future color law is supplied. -/
theorem current_unselected_boundary_hom_ext (U : Matrix 4) (hB₀ : SkewSymmetric B₀)
    (hs : add U (transpose U) = initialCompanion B₀)
    (ha : add U (scale (-1) (transpose U)) = reverse B₀)
    (w : List (Fin 4)) (hInv : SeedInv B₀ w) (p : Relabeling 4)
    (hNumeric : OrderedRootFrame B₀ U (columnRelabel (principalSeed B₀ w).2 p))
    (M : Fin 4 → Representation B₀ K) (hM : ExceptionalFrame (vertexFunctor B₀ K) M)
    (hDims : ∀ a, dimensionVector B₀ K (M a) = fun b =>
      colorSign (columnColor (columnRelabel (principalSeed B₀ w).2 p)) a *
        columnRelabel (principalSeed B₀ w).2 p b a)
    (a b : Fin 4) (hab : a < b)
    (hNonpos : (principalSeed B₀ w).1 (p.toFun a) (p.toFun b) ≤ 0) :
    (∀ f : M a ⟶ M b, f = 0) ∧
      (columnColor (principalSeed B₀ w).2 (p.toFun a) =
          columnColor (principalSeed B₀ w).2 (p.toFun b) →
        (∀ e : Abelian.Ext (M a) (M b) 1, e = 0) ∧
          (principalSeed B₀ w).1 (p.toFun a) (p.toFun b) = 0) := by
  let D := columnRelabel (principalSeed B₀ w).2 p
  let g := columnColor (principalSeed B₀ w).2
  let B := (principalSeed B₀ w).1
  let A := coefficientCompanion B₀ (principalSeed B₀ w).2
  let E := coefficientBilinear U (principalSeed B₀ w).2
  change B (p.toFun a) (p.toFun b) ≤ 0 at hNonpos
  have hParts := coefficientBilinear_parts B₀ U B (principalSeed B₀ w).2 hs ha hInv.exchangeOrigin
  have hLower : E (p.toFun b) (p.toFun a) = 0 := by
    change coefficientBilinear U D b a = 0
    rw [coefficient_bilinear_pairing]
    exact hNumeric.2.2.2 b a hab
  have hSkew : E (p.toFun a) (p.toFun b) - E (p.toFun b) (p.toFun a) =
      -B (p.toFun a) (p.toFun b) := by
    have h := congrFun (congrFun hParts.2 (p.toFun a)) (p.toFun b)
    change E (p.toFun a) (p.toFun b) + (-1) * E (p.toFun b) (p.toFun a) =
      -B (p.toFun a) (p.toFun b) at h
    omega
  have hForward : E (p.toFun a) (p.toFun b) = -B (p.toFun a) (p.toFun b) := by
    rw [hLower] at hSkew
    omega
  have hCompReverse : A (p.toFun b) (p.toFun a) = -B (p.toFun a) (p.toFun b) := by
    have h := congrFun (congrFun hParts.1 (p.toFun b)) (p.toFun a)
    change E (p.toFun b) (p.toFun a) + E (p.toFun a) (p.toFun b) = A (p.toFun b) (p.toFun a) at h
    rw [hLower,hForward] at h
    omega
  have hEuler :
      (Module.finrank K (M a ⟶ M b) : Int) - (Module.finrank K (Abelian.Ext (M a) (M b) 1) : Int) =
        -(if g (p.toFun a) = g (p.toFun b) then 1 else -1) * B (p.toFun a) (p.toFun b) := by
    have h := normalized_frame_model_euler B₀ K U D hB₀ hs ha M hM.finiteVertices hDims a b
    have hRaw : coefficientBilinear U D a b = -B (p.toFun a) (p.toFun b) := hForward
    rw [normalizedEuler,hRaw] at h
    change colorSign g (p.toFun a) * colorSign g (p.toFun b) *
      -B (p.toFun a) (p.toFun b) = _ at h
    cases hc : g (p.toFun a) <;> cases hd : g (p.toFun b) <;>
      simp only [colorSign,hc,hd,Bool.false_eq_true,Bool.true_eq_false,↓reduceIte,
        neg_mul,one_mul,neg_one_mul,neg_neg] at h ⊢ <;> omega
  have hSameZero : g (p.toFun a) = g (p.toFun b) →
      Module.finrank K (M a ⟶ M b) = 0 := by
    intro hc
    have hBnonneg : 0 ≤ B (p.toFun a) (p.toFun b) := by
      by_contra hn
      have hCurrentSkew := principalSeed_skew B₀ hB₀ w (p.toFun b) (p.toFun a)
      have hPositive : 0 < B (p.toFun b) (p.toFun a) := by change B _ _ = -B _ _ at hCurrentSkew; omega
      have hCompPositive : 0 < A (p.toFun b) (p.toFun a) := by rw [hCompReverse]; omega
      have hColors := (hInv.arrowSigns (p.toFun b) (p.toFun a) hPositive).mp hCompPositive
      change g (p.toFun b) = false ∧ g (p.toFun a) = true at hColors
      rw [hColors.1,hColors.2] at hc
      contradiction
    have hz : B (p.toFun a) (p.toFun b) = 0 := by omega
    have hPair := hEuler
    simp only [if_pos hc,hz,MulZeroClass.mul_zero] at hPair
    letI := local_end_of_scalar_end (M a) (hM.nonzeroId a) (hM.scalarEnd a)
    letI := local_end_of_scalar_end (M b) (hM.nonzeroId b) (hM.scalarEnd b)
    have hPure := dimension_purity_of_rigid (M a) (M b) (model_hereditary B₀ K)
      (hM.reverseExt a b hab) (hM.rigid a) (hM.rigid b)
      (Module.finrank K (M a ⟶ M b)) (Module.finrank K (Abelian.Ext (M a) (M b) 1))
      (model_hom_finrank_zero_iff B₀ K (M a) (M b) (hM.finiteVertices a) (hM.finiteVertices b))
      (model_ext_finrank_zero_iff B₀ K (M a) (M b) (hM.finiteVertices a) (hM.finiteVertices b))
    rcases hPure with h | h <;> omega
  exact nonpositive_boundary_hom (M a) (M b) (B (p.toFun a) (p.toFun b))
    (g (p.toFun a)) (g (p.toFun b)) (model_hereditary B₀ K)
    (hM.reverseExt a b hab) (hM.rigid a) (hM.rigid b)
    (hM.nonzeroId a) (hM.nonzeroId b) (hM.scalarEnd a) (hM.scalarEnd b)
    (Module.finrank K (M a ⟶ M b)) (Module.finrank K (Abelian.Ext (M a) (M b) 1))
    (model_hom_finrank_zero_iff B₀ K (M a) (M b) (hM.finiteVertices a) (hM.finiteVertices b))
    (model_ext_finrank_zero_iff B₀ K (M a) (M b) (hM.finiteVertices a) (hM.finiteVertices b))
    hNonpos hEuler (fun hc => (model_hom_finrank_zero_iff B₀ K (M a) (M b)
      (hM.finiteVertices a) (hM.finiteVertices b)).mp (hSameZero hc))

theorem green_unselected_after_right_endpoint (U : Matrix 4) (hB₀ : SkewSymmetric B₀)
    (hs : add U (transpose U) = initialCompanion B₀)
    (ha : add U (scale (-1) (transpose U)) = reverse B₀)
    (w : List (Fin 4)) (hInv : SeedInv B₀ w) (p : Relabeling 4)
    (hNumeric : OrderedRootFrame B₀ U (columnRelabel (principalSeed B₀ w).2 p))
    (M : Fin 4 → Representation B₀ K) (hM : ExceptionalFrame (vertexFunctor B₀ K) M)
    (hDims : ∀ a, dimensionVector B₀ K (M a) = fun b =>
      colorSign (columnColor (columnRelabel (principalSeed B₀ w).2 p)) a *
        columnRelabel (principalSeed B₀ w).2 p b a)
    (t s j : Fin 4) (hts : t ≤ s) (hsj : s < j)
    (hout : ∀ i, i ≠ t → ¬ (t < i ∧ i ≤ s) →
      (principalSeed B₀ w).1 (p.toFun t) (p.toFun i) ≤ 0) :
    (∀ f : M t ⟶ M j, f = 0) ∧
      (columnColor (principalSeed B₀ w).2 (p.toFun t) =
          columnColor (principalSeed B₀ w).2 (p.toFun j) →
        (∀ e : Abelian.Ext (M t) (M j) 1, e = 0) ∧
          (principalSeed B₀ w).1 (p.toFun t) (p.toFun j) = 0) := by
  exact current_unselected_boundary_hom_ext B₀ K U hB₀ hs ha w hInv p hNumeric M hM hDims
    t j (by omega) (hout j (by omega) (by omega))

theorem red_unselected_before_left_endpoint (U : Matrix 4) (hB₀ : SkewSymmetric B₀)
    (hs : add U (transpose U) = initialCompanion B₀)
    (ha : add U (scale (-1) (transpose U)) = reverse B₀)
    (w : List (Fin 4)) (hInv : SeedInv B₀ w) (p : Relabeling 4)
    (hNumeric : OrderedRootFrame B₀ U (columnRelabel (principalSeed B₀ w).2 p))
    (M : Fin 4 → Representation B₀ K) (hM : ExceptionalFrame (vertexFunctor B₀ K) M)
    (hDims : ∀ a, dimensionVector B₀ K (M a) = fun b =>
      colorSign (columnColor (columnRelabel (principalSeed B₀ w).2 p)) a *
        columnRelabel (principalSeed B₀ w).2 p b a)
    (t s j : Fin 4) (hst : s ≤ t) (hjs : j < s)
    (hout : ∀ i, i ≠ t → ¬ (s ≤ i ∧ i < t) →
      0 ≤ (principalSeed B₀ w).1 (p.toFun t) (p.toFun i)) :
    (∀ f : M j ⟶ M t, f = 0) ∧
      (columnColor (principalSeed B₀ w).2 (p.toFun j) =
          columnColor (principalSeed B₀ w).2 (p.toFun t) →
        (∀ e : Abelian.Ext (M j) (M t) 1, e = 0) ∧
          (principalSeed B₀ w).1 (p.toFun j) (p.toFun t) = 0) := by
  have hNonneg := hout j (by omega) (by omega)
  have hSkew := principalSeed_skew B₀ hB₀ w (p.toFun j) (p.toFun t)
  exact current_unselected_boundary_hom_ext B₀ K U hB₀ hs ha w hInv p hNumeric M hM hDims
    j t (by omega) (by omega)

#print axioms current_unselected_boundary_hom_ext
end QuiverProofs.MA4RestartOldUnselectedPivotBoundary
