import MA4RestartArrow20261003.RedFamilyConstruction

/-! The actual nonzero finite replacement fixes its literal column color.
This uses positive actual vertex dimension and signed trace dimensions;
no future sign coherence or ArrowSigns is assumed. -/
namespace QuiverProofs.MA4RestartArrow20261003.TraceColorNormalization
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open QuiverProofs MAExistenceLiterature MAExistenceCoefficients
open MA4RestartArrow20261003.AdjacentExceptionalFrame
open MA4RestartArrow20261003.SignedAdjacentLeftHom
open MA4RestartArrow20261003.LeftTracedReplacement
open MA4RestartVertexFiniteness
universe w v u z
variable {K : Type w} [Field K] {C : Type u}
  [Category.{v} C] [Abelian C] [Linear K C] [HasExt.{z} C]
set_option maxHeartbeats 0

theorem actual_trace_colors_are_literal
    (F : Fin 4 → C ⥤ ModuleCat.{v} K)
    (hJointEpi : ∀ {M V : C} (e : M ⟶ V), (∀ a, Epi ((F a).map e)) → Epi e)
    (M : Fin 4 → C) (hM : ExceptionalFrame F M) (D : Matrix 4) (g : Fin 4 → Bool)
    (hDims : ∀ j a, (Module.finrank K ((F a).obj (M j)) : Int) = branchSign (g j) * D a j) :
    g = columnColor D := by
  funext j
  cases hj : g j with
  | true =>
    have hg : ∀ a, 0 ≤ D a j := by
      intro a
      have hd := hDims j a
      simp only [hj,branchSign,↓reduceIte,one_mul] at hd
      have hn : (0 : Int) ≤ (Module.finrank K ((F a).obj (M j)) : Int) := by omega
      omega
    simp [hj,columnColor,hg]
  | false =>
    obtain ⟨a,ha⟩ := positive_vertex_dimension_of_nonzero F hJointEpi (M j)
      (hM.finiteVertices j) (hM.nonzeroId j)
    have hd := hDims j a
    simp only [hj,branchSign,Bool.false_eq_true,↓reduceIte,neg_one_mul] at hd
    have hn : ¬ ∀ a, 0 ≤ D a j := by
      intro hg
      have h := hg a
      have hp : (0 : Int) < (Module.finrank K ((F a).obj (M j)) : Int) := by exact_mod_cast ha
      omega
    simp [hj,columnColor,hn]

theorem signed_trace_dimensions_are_literal
    (F : Fin 4 → C ⥤ ModuleCat.{v} K)
    (hJointEpi : ∀ {M V : C} (e : M ⟶ V), (∀ a, Epi ((F a).map e)) → Epi e)
    (M : Fin 4 → C) (hM : ExceptionalFrame F M) (D : Matrix 4) (g : Fin 4 → Bool)
    (hDims : SignedDimensions F M D (fun j => branchSign (g j))) :
    g = columnColor D ∧
      SignedDimensions F M D (fun j => branchSign (columnColor D j)) := by
  have hg := actual_trace_colors_are_literal F hJointEpi M hM D g (fun j => (hDims j).2)
  exact ⟨hg,by simpa only [hg] using hDims⟩

#print axioms actual_trace_colors_are_literal
#print axioms signed_trace_dimensions_are_literal
end QuiverProofs.MA4RestartArrow20261003.TraceColorNormalization
