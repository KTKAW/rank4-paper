import MA4RestartArrow20261003.GreenTraceInversions
import MA4RestartArrow20261003.GreenFamilyConstruction
import MA4RestartArrow20261003.TraceColorNormalization

/-! A full actual terminal colored red family on the fixed weighted model.
Every terminal field is constructed. Only OLD colored frame data and OLD
selected/unselected interval gates remain inputs to this bounded supplier. -/
namespace QuiverProofs.MA4RestartArrow20261003.GreenColoredFamily
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open QuiverProofs MAExistenceLiterature MAExistenceCoefficients MAExistenceTeamBRootPositivity
open MAExistenceSupportChronology MA4RestartWeightedQuiverModel MA4RestartFreePathProjectives
open MA4RestartModelExt MA4RestartResolvedModelEuler
open MA4RestartArrow20261003.AdjacentExceptionalFrame MA4RestartArrow20261003.SignedAdjacentLeftHom
open MA4RestartArrow20261003.ActualLeftSweep MA4RestartArrow20261003.RightFamilyFrame
open MA4RestartArrow20261003.LeftFamilyFrame
open MA4RestartArrow20261003.LeftTracedReplacement MA4RestartArrow20261003.GreenFamilyConstruction
open MA4RestartArrow20261003.GreenFamilySameColorHom MA4RestartArrow20261003.GreenTraceInversions
open MA4RestartArrow20261003.TraceColorNormalization
open MACompletionScalarEndomorphisms MACompletionPairPurity
set_option maxHeartbeats 0
local instance actualHasExt (B : Matrix 4) (K : Type) [Field K] :
    HasExt.{0} (Representation B K) := representation_hasExt B K
local instance actualEnoughProjectives (B : Matrix 4) (K : Type) [Field K] :
    EnoughProjectives (Representation B K) := representation_enoughProjectives B K
local instance actualFiniteBiproducts (B : Matrix 4) (K : Type) [Field K] :
    HasFiniteBiproducts (Representation B K) := Abelian.hasFiniteBiproducts

theorem construct_terminal_colored_green_family
    (B U D : Matrix 4) (K : Type) [Field K] (hB : SkewSymmetric B)
    (hs : Cosquare.add U (Cosquare.transpose U) = initialCompanion B)
    (ha : Cosquare.add U (Cosquare.scale (-1) (Cosquare.transpose U)) = reverse B)
    (M : Fin 4 → Representation B K) (hM : ExceptionalFrame (vertexFunctor B K) M)
    (c : Fin 4 → Bool)
    (hDims : ∀ j a, (Module.finrank K ((vertexFunctor B K a).obj (M j)) : Int) =
      branchSign (c j) * D a j)
    (t q : Fin 4) (htq : t ≤ q) (hc : c t = true)
    (hOldBlock : ∀ a b, a < b → c a = false → c b = true → False)
    (hOldSame : ∀ a b, a < b → c a = c b → ∀ f : M a ⟶ M b, f = 0)
    (hSelected : ∀ i, t < i → i ≤ q → pairing U (column D t) (column D i) ≤ 0)
    (hOutsideRed : ∀ b, q < b → c b = false → ∀ f : M t ⟶ M b, f = 0)
    (hOutsideGreen : ∀ b, q < b → c b = true → Orthogonal (M t) (M b)) :
    let E := negateColumn (rightSweep U D t q) q
    ∃ N : Fin 4 → Representation B K,
      ExceptionalFrame (vertexFunctor B K) N ∧
      SignedDimensions (vertexFunctor B K) N E (fun j => branchSign (columnColor E j)) ∧
      (∀ a b, a < b → columnColor E a = columnColor E b → ∀ f : N a ⟶ N b, f = 0) ∧
      (∀ a b, a < b → columnColor E a = false → columnColor E b = true → Orthogonal (N a) (N b)) := by
  let F := vertexFunctor B K
  have hEuler : ∀ X Y : Representation B K,
      (∀ a, Module.Finite K ((F a).obj X)) → (∀ a, Module.Finite K ((F a).obj Y)) →
      pairing U (vertexDimensions F X) (vertexDimensions F Y) =
        (Module.finrank K (X ⟶ Y) : Int) - (Module.finrank K (Ext X Y 1) : Int) :=
    model_euler_pairing B K U hB hs ha
  have hEpi : ∀ {M V : Representation B K} (e : M ⟶ V), (∀ a, Epi ((F a).map e)) → Epi e :=
    fun e h => vertices_jointly_reflect_epi B K e h
  obtain ⟨Q,g,hQ,hTrace,hNext,hNextDims⟩ := construct_traced_green_family F
    (vertex_preserves_zero B K) (vertex_preserves_finite_limits B K)
    (vertex_preserves_finite_colimits B K) hEpi (model_hereditary B K)
    (model_finite_hom_ext B K) U D hEuler M hM c hDims t q htq hc
    (fun i hi h => hOldSame t i hi h.symm) hSelected
  have hRedExt : ∀ i, t < i → i ≤ q → c i = false → ∀ e : Ext (M t) (M i) 1, e = 0 := by
    intro i hti hiq hi
    have hf := model_finite_hom_ext B K (M t) (M i) (hM.finiteVertices t) (hM.finiteVertices i)
    letI := hf.1; letI := hf.2
    have hw := signed_green_pivot_weight F M D U c hDims t i hc
      (hEuler _ _ (hM.finiteVertices t) (hM.finiteVertices i))
    have hsigned := hSelected i hti hiq
    simp only [hi,branchSign,Bool.false_eq_true,↓reduceIte,one_mul,mul_neg,mul_one] at hw
    have hNonneg : 0 ≤ (Module.finrank K (M t ⟶ M i) : Int) -
        (Module.finrank K (Ext (M t) (M i) 1) : Int) := by omega
    letI := local_end_of_scalar_end (M i) (hM.nonzeroId i) (hM.scalarEnd i)
    letI := local_end_of_scalar_end (M t) (hM.nonzeroId t) (hM.scalarEnd t)
    rcases hom_or_extOne_vanishes_of_rigid (M t) (M i) (model_hereditary B K)
      (hM.reverseExt t i hti) (hM.rigid t) (hM.rigid i) with hHom | hExt
    · letI : Subsingleton (M t ⟶ M i) := ⟨fun f g => by rw [hHom f,hHom g]⟩
      have hH0 : Module.finrank K (M t ⟶ M i) = 0 := Module.finrank_zero_of_subsingleton
      have hE0 : Module.finrank K (Ext (M t) (M i) 1) = 0 := by rw [hH0] at hNonneg; omega
      letI : Subsingleton (Ext (M t) (M i) 1) := Module.finrank_zero_iff.mp hE0
      exact fun e => Subsingleton.elim e 0
    · exact hExt
  obtain ⟨hColors,hLiteral⟩ := signed_trace_dimensions_are_literal F hEpi
    (rightFamilyObjects M Q t q) hNext (negateColumn (rightSweep U D t q) q)
    (rightFamilyColors c g t q) hNextDims
  have hSame := terminal_same_color_hom F M Q c g hM t q htq hc hOldBlock hOldSame
    hQ hTrace hOutsideRed
  have hInversions := terminal_red_before_green_orthogonal B U K hB hs ha M Q c g hM t q
    htq hc hOldBlock hOldSame hTrace hRedExt hOutsideGreen
  rw [hColors] at hSame hInversions
  exact ⟨rightFamilyObjects M Q t q,hNext,hLiteral,hSame,hInversions⟩

#print axioms construct_terminal_colored_green_family
end QuiverProofs.MA4RestartArrow20261003.GreenColoredFamily
