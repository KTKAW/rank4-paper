import MA4RestartEuler20261003.ResolvedModelEuler
import MA4EulerRealizedNo301a0fee4
import MA4Coordinator20261003.PairPurity

/-! Actual finite rigid semiorthogonal objects with normalized frame columns
give static normalized No3. Heredity, Euler, dimension zero tests, local End
and forward purity are derived, without ArrowSigns or admissibility inputs. -/
namespace QuiverProofs.MA4RestartActualFrameNoThreeCycle
open Module CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open MAExistenceLiterature MAExistenceTeamBRootPositivity MAExistenceCoefficients
  MAExistenceTeamCTriangleOutside MAExistenceTeamBAdjacentHurwitz MAExistenceSupportChronology
  MAExistenceTeamCCertificateTransport
  MA4RestartWeightedQuiverModel MA4RestartFreePathProjectives MA4RestartModelExt
  MA4RestartMatrixEuler MA4RestartResolvedModelEuler MACompletionScalarEndomorphisms
  MACompletionPairPurity MA4EulerRealizedNo301a0fee4
variable (B : Matrix 4) (K : Type) [Field K]
local instance actualEnoughProjectives : EnoughProjectives (Representation B K) :=
  representation_enoughProjectives B K
local instance actualHasExt : HasExt.{0} (Representation B K) := representation_hasExt B K
local instance actualFiniteBiproducts : HasFiniteBiproducts (Representation B K) :=
  Abelian.hasFiniteBiproducts

theorem model_hom_finrank_zero_iff (M N : Representation B K)
    (hM : ∀ a, Module.Finite K ((vertexFunctor B K a).obj M))
    (hN : ∀ a, Module.Finite K ((vertexFunctor B K a).obj N)) :
    Module.finrank K (M ⟶ N) = 0 ↔ ∀ f : M ⟶ N, f = 0 := by
  letI := (model_finite_hom_ext B K M N hM hN).1
  constructor
  · intro h
    letI := (Module.finrank_zero_iff (R := K)).mp h
    intro f
    exact Subsingleton.elim _ _
  · intro h
    letI : Subsingleton (M ⟶ N) := ⟨fun f g => by rw [h f,h g]⟩
    exact Module.finrank_zero_of_subsingleton

theorem model_ext_finrank_zero_iff (M N : Representation B K)
    (hM : ∀ a, Module.Finite K ((vertexFunctor B K a).obj M))
    (hN : ∀ a, Module.Finite K ((vertexFunctor B K a).obj N)) :
    Module.finrank K (Abelian.Ext M N 1) = 0 ↔ ∀ e : Abelian.Ext M N 1, e = 0 := by
  letI := (model_finite_hom_ext B K M N hM hN).2
  constructor
  · intro h
    letI := (Module.finrank_zero_iff (R := K)).mp h
    intro e
    exact Subsingleton.elim _ _
  · intro h
    letI : Subsingleton (Abelian.Ext M N 1) := ⟨fun e f => by rw [h e,h f]⟩
    exact Module.finrank_zero_of_subsingleton

theorem normalized_frame_model_euler (U D : Matrix 4) (hB : SkewSymmetric B)
    (hs : Cosquare.add U (Cosquare.transpose U) = initialCompanion B)
    (ha : Cosquare.add U (Cosquare.scale (-1) (Cosquare.transpose U)) = reverse B)
    (M : Fin 4 → Representation B K)
    (hFinite : ∀ a b, Module.Finite K ((vertexFunctor B K b).obj (M a)))
    (hDim : ∀ a, dimensionVector B K (M a) =
      fun b => colorSign (columnColor D) a * D b a) (a b : Fin 4) :
    normalizedEuler (coefficientBilinear U D) (columnColor D) a b =
      (Module.finrank K (M a ⟶ M b) : Int) -
        (Module.finrank K (Abelian.Ext (M a) (M b) 1) : Int) := by
  rw [normalizedEuler_eq_pairing,← hDim a,← hDim b]
  exact model_euler_pairing B K U hB hs ha (M a) (M b) (hFinite a) (hFinite b)

theorem coefficient_bilinear_pairing (U D : Matrix 4) (a b : Fin 4) :
    coefficientBilinear U D a b = pairing U (column D a) (column D b) := by
  simp only [coefficientBilinear, pairing, column, Cosquare.mul, Cosquare.transpose]
  ring

/-- Unit frame Euler and actual self-rigidity derive all local End data. -/
theorem actual_frame_end_data (U D : Matrix 4) (hB : SkewSymmetric B)
    (hs : Cosquare.add U (Cosquare.transpose U) = initialCompanion B)
    (ha : Cosquare.add U (Cosquare.scale (-1) (Cosquare.transpose U)) = reverse B)
    (hFrame : OrderedRootFrame B U D) (M : Fin 4 → Representation B K)
    (hFinite : ∀ a b, Module.Finite K ((vertexFunctor B K b).obj (M a)))
    (hDim : ∀ a, dimensionVector B K (M a) =
      fun b => colorSign (columnColor D) a * D b a)
    (hRigid : ∀ a, ∀ e : Abelian.Ext (M a) (M a) 1, e = 0) (a : Fin 4) :
    Module.finrank K (M a ⟶ M a) = 1 ∧
    (𝟙 (M a) : M a ⟶ M a) ≠ 0 ∧
    (∀ f : M a ⟶ M a, ∃ c : K, f = c • 𝟙 (M a)) ∧ IsLocalRing (End (M a)) := by
  letI := (model_finite_hom_ext B K (M a) (M a) (hFinite a) (hFinite a)).1
  have hr : coefficientBilinear U D a a = 1 := by
    rw [coefficient_bilinear_pairing]
    exact hFrame.2.2.1 a
  have hSelf : normalizedEuler (coefficientBilinear U D) (columnColor D) a a = 1 := by
    rw [normalizedEuler,hr]
    unfold colorSign
    split <;> norm_num
  have he := normalized_frame_model_euler B K U D hB hs ha M hFinite hDim a a
  have hExtZero := (model_ext_finrank_zero_iff B K (M a) (M a)
    (hFinite a) (hFinite a)).mpr (hRigid a)
  have hRank : Module.finrank K (M a ⟶ M a) = 1 := by
    rw [hSelf,hExtZero] at he
    omega
  have hId : (𝟙 (M a) : M a ⟶ M a) ≠ 0 := by
    intro h
    have hz : ∀ f : M a ⟶ M a, f = 0 := by
      intro f
      calc f = f ≫ 𝟙 (M a) := by simp
           _ = 0 := by rw [h]; simp
    have hzero := (model_hom_finrank_zero_iff B K (M a) (M a)
      (hFinite a) (hFinite a)).mpr hz
    omega
  have hScalar := scalar_end_of_finrank_one (M a) hId hRank
  exact ⟨hRank,hId,hScalar,local_end_of_scalar_end (M a) hId hScalar⟩

/-- Static No3 in the supplied upper order, deriving every categorical gate
from the actual finite rigid tuple, reverse Ext and its dimension columns. -/
theorem actual_ordered_frame_no_three_cycle (U D : Matrix 4) (hB : SkewSymmetric B)
    (hs : Cosquare.add U (Cosquare.transpose U) = initialCompanion B)
    (ha : Cosquare.add U (Cosquare.scale (-1) (Cosquare.transpose U)) = reverse B)
    (hFrame : OrderedRootFrame B U D) (M : Fin 4 → Representation B K)
    (hFinite : ∀ a b, Module.Finite K ((vertexFunctor B K b).obj (M a)))
    (hDim : ∀ a, dimensionVector B K (M a) =
      fun b => colorSign (columnColor D) a * D b a)
    (hRigid : ∀ a, ∀ e : Abelian.Ext (M a) (M a) 1, e = 0)
    (hReverseExt : ∀ a b, a < b → ∀ e : Abelian.Ext (M b) (M a) 1, e = 0)
    (i j l : Fin 4) (hij : i ≠ j) (hjl : j ≠ l) (hli : l ≠ i) :
    noEulerThreeCycle (normalizedEuler (coefficientBilinear U D) (columnColor D)) i j l := by
  let dH := fun a b => Module.finrank K (M a ⟶ M b)
  let dE := fun a b => Module.finrank K (Abelian.Ext (M a) (M b) 1)
  have hEnd : ∀ a, IsLocalRing (End (M a)) := fun a =>
    (actual_frame_end_data B K U D hB hs ha hFrame M hFinite hDim hRigid a).2.2.2
  have hHZ : ∀ a b, dH a b = 0 ↔ ∀ f : M a ⟶ M b, f = 0 := fun a b =>
    model_hom_finrank_zero_iff B K (M a) (M b) (hFinite a) (hFinite b)
  have hEZ : ∀ a b, dE a b = 0 ↔ ∀ e : Abelian.Ext (M a) (M b) 1, e = 0 := fun a b =>
    model_ext_finrank_zero_iff B K (M a) (M b) (hFinite a) (hFinite b)
  have hUpper : ∀ a b, b < a →
      normalizedEuler (coefficientBilinear U D) (columnColor D) a b = 0 := by
    intro a b hba
    have hz : coefficientBilinear U D a b = 0 := by
      rw [coefficient_bilinear_pairing]
      exact hFrame.2.2.2 a b hba
    simp [normalizedEuler,hz]
  have hPure : ∀ a b, a < b → dH a b = 0 ∨ dE a b = 0 := by
    intro a b hab
    letI := hEnd a
    letI := hEnd b
    exact dimension_purity_of_rigid (M a) (M b) (model_hereditary B K)
      (hReverseExt a b hab) (hRigid a) (hRigid b) (dH a b) (dE a b) (hHZ a b) (hEZ a b)
  exact realized_dimensions_noEulerThreeCycle M _ dH dE hUpper (model_hereditary B K)
    hEnd hReverseExt hHZ hEZ (normalized_frame_model_euler B K U D hB hs ha M hFinite hDim)
    hPure i j l hij hjl hli

/-- Return only the No3 conclusion to original labels, after proving it in
the supplied upper order. No upper property is transported by permutation. -/
theorem actual_relabelled_frame_no_three_cycle (U D : Matrix 4) (hB : SkewSymmetric B)
    (hs : Cosquare.add U (Cosquare.transpose U) = initialCompanion B)
    (ha : Cosquare.add U (Cosquare.scale (-1) (Cosquare.transpose U)) = reverse B)
    (q : Relabeling 4) (hFrame : OrderedRootFrame B U (columnRelabel D q))
    (M : Fin 4 → Representation B K)
    (hFinite : ∀ a b, Module.Finite K ((vertexFunctor B K b).obj (M a)))
    (hDim : ∀ a, dimensionVector B K (M a) =
      fun b => colorSign (columnColor (columnRelabel D q)) a * (columnRelabel D q) b a)
    (hRigid : ∀ a, ∀ e : Abelian.Ext (M a) (M a) 1, e = 0)
    (hReverseExt : ∀ a b, a < b → ∀ e : Abelian.Ext (M b) (M a) 1, e = 0)
    (i j l : Fin 4) (hij : i ≠ j) (hjl : j ≠ l) (hli : l ≠ i) :
    noEulerThreeCycle (normalizedEuler (coefficientBilinear U D) (columnColor D)) i j l := by
  have hinj (a b : Fin 4) (hne : a ≠ b) : q.invFun a ≠ q.invFun b := by
    intro he
    apply hne
    simpa only [q.right_inv] using congrArg q.toFun he
  have hn := actual_ordered_frame_no_three_cycle B K U (columnRelabel D q) hB hs ha hFrame
    M hFinite hDim hRigid hReverseExt (q.invFun i) (q.invFun j) (q.invFun l)
    (hinj i j hij) (hinj j l hjl) (hinj l i hli)
  have hrel (a b : Fin 4) :
      normalizedEuler (coefficientBilinear U (columnRelabel D q))
          (columnColor (columnRelabel D q)) a b =
      normalizedEuler (coefficientBilinear U D) (columnColor D) (q.toFun a) (q.toFun b) := rfl
  simpa only [noEulerThreeCycle, eulerArrow, hrel, q.right_inv] using hn

/-- Direct chronological next-seed conclusion from its realized terminal
upper frame; no invariant at the next seed is a premise. -/
theorem chronological_terminal_frame_no_three_cycle (U : Matrix 4) (hB : SkewSymmetric B)
    (hs : Cosquare.add U (Cosquare.transpose U) = initialCompanion B)
    (ha : Cosquare.add U (Cosquare.scale (-1) (Cosquare.transpose U)) = reverse B)
    (w : List (Fin 4)) (k : Fin 4) (q : Relabeling 4)
    (hFrame : OrderedRootFrame B U (columnRelabel (principalSeed B (w ++ [k])).2 q))
    (M : Fin 4 → Representation B K)
    (hFinite : ∀ a b, Module.Finite K ((vertexFunctor B K b).obj (M a)))
    (hDim : ∀ a, dimensionVector B K (M a) =
      fun b => colorSign (columnColor (columnRelabel (principalSeed B (w ++ [k])).2 q)) a *
        (columnRelabel (principalSeed B (w ++ [k])).2 q) b a)
    (hRigid : ∀ a, ∀ e : Abelian.Ext (M a) (M a) 1, e = 0)
    (hReverseExt : ∀ a b, a < b → ∀ e : Abelian.Ext (M b) (M a) 1, e = 0)
    (i j l : Fin 4) (hij : i ≠ j) (hjl : j ≠ l) (hli : l ≠ i) :
    noEulerThreeCycle
      (normalizedEuler (coefficientBilinear U (principalSeed B (w ++ [k])).2)
        (columnColor (principalSeed B (w ++ [k])).2)) i j l :=
  actual_relabelled_frame_no_three_cycle B K U (principalSeed B (w ++ [k])).2 hB hs ha q hFrame
    M hFinite hDim hRigid hReverseExt i j l hij hjl hli

#print axioms actual_ordered_frame_no_three_cycle
#print axioms chronological_terminal_frame_no_three_cycle
end QuiverProofs.MA4RestartActualFrameNoThreeCycle
