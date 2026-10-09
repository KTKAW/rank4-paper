import MA4RestartEuler20261003.ResolvedModelEuler
import MA4RestartCoordinator20261003.VertexFiniteness
import MA4RestartArrow20261003.VertexCopies
import MA4RestartArrow20261003.ScalarEndDimension

/-! The actual evaluation replacements in a red-before-green inversion are orthogonal.
All next vertex dimensions and finite Hom/Ext spaces are derived from the
chosen maps. The Euler cancellation uses only old Hom/Ext vanishing. -/
namespace QuiverProofs.MA4RestartMixedEvaluationOrthogonality
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open MAExistenceLiterature MAExistenceTeamBRootPositivity
open MA4RestartWeightedQuiverModel MA4RestartModelExt MA4RestartMatrixEuler
open MA4RestartResolvedModelEuler MA4RestartVertexFiniteness MACompletionExactVertexDimensions
open MA4RestartArrow20261003.VertexCopies MA4RestartArrow20261003.ScalarEndDimension
set_option maxHeartbeats 0

local instance actualHasExt (B : Matrix 4) (K : Type) [Field K] :
    HasExt.{0} (Representation B K) := representation_hasExt B K
local instance actualFiniteBiproducts (B : Matrix 4) (K : Type) [Field K] :
    HasFiniteBiproducts (Representation B K) := Abelian.hasFiniteBiproducts

private theorem hom_finrank_zero (B : Matrix 4) (K : Type) [Field K]
    (X Y : Representation B K) (h : ∀ f : X ⟶ Y, f = 0) :
    Module.finrank K (X ⟶ Y) = 0 := by
  letI : Subsingleton (X ⟶ Y) := ⟨fun f g => by rw [h f,h g]⟩
  exact Module.finrank_zero_of_subsingleton (R := K) (M := X ⟶ Y)

private theorem ext_finrank_zero (B : Matrix 4) (K : Type) [Field K]
    (X Y : Representation B K) (h : ∀ e : Ext X Y 1, e = 0) :
    Module.finrank K (Ext X Y 1) = 0 := by
  letI : Subsingleton (Ext X Y 1) := ⟨fun e f => by rw [h e,h f]⟩
  exact Module.finrank_zero_of_subsingleton (R := K) (M := Ext X Y 1)

private theorem pairing_copy_differences (U : Matrix 4) (x x' y : Vector4) (n m : Int) :
    pairing U (fun a => x a - n * y a) (fun a => m * y a - x' a) =
      m * pairing U x y - pairing U x x' - n * m * pairing U y y + n * pairing U y x' := by
  simp only [pairing]
  ring

/-- Both actual chosen replacements and the old outer pair are orthogonal
in Ext. No next Euler inequality, rank, or finiteness is supplied. -/
theorem mixed_evaluation_orthogonality
    (B U : Matrix 4) (K : Type) [Field K] (hB : SkewSymmetric B)
    (hs : Cosquare.add U (Cosquare.transpose U) = initialCompanion B)
    (ha : Cosquare.add U (Cosquare.scale (-1) (Cosquare.transpose U)) = reverse B)
    (X X' Y : Representation B K) (n m : ℕ)
    (f : Module.Basis (Fin n) K (Y ⟶ X))
    (f' : Module.Basis (Fin m) K (Y ⟶ X'))
    [Mono (biproduct.desc (f := fun _ : Fin n => Y) (fun j => f j))]
    [Epi (biproduct.desc (f := fun _ : Fin m => Y) (fun j => f' j))]
    (hX : ∀ a, Module.Finite K ((vertexFunctor B K a).obj X))
    (hX' : ∀ a, Module.Finite K ((vertexFunctor B K a).obj X'))
    (hY : ∀ a, Module.Finite K ((vertexFunctor B K a).obj Y))
    (hIdY : 𝟙 Y ≠ 0) (hEndY : ∀ g : Y ⟶ Y, ∃ c : K, g = c • 𝟙 Y)
    (hRigidY : ∀ e : Ext Y Y 1, e = 0)
    (hXY : ∀ g : X ⟶ Y, g = 0) (hExtXY : ∀ e : Ext X Y 1, e = 0)
    (hYX' : ∀ e : Ext Y X' 1, e = 0)
    (hXX' : ∀ g : X ⟶ X', g = 0) :
    let e := biproduct.desc (f := fun _ : Fin n => Y) (fun j => f j)
    let e' := biproduct.desc (f := fun _ : Fin m => Y) (fun j => f' j)
    (∀ g : cokernel e ⟶ kernel e', g = 0) ∧
      (∀ z : Ext (cokernel e) (kernel e') 1, z = 0) ∧
      (∀ z : Ext X X' 1, z = 0) := by
  let e := biproduct.desc (f := fun _ : Fin n => Y) (fun j => f j)
  let e' := biproduct.desc (f := fun _ : Fin m => Y) (fun j => f' j)
  let F := vertexFunctor B K
  have hN := vertex_copies_finite F (vertex_preserves_zero B K)
    (vertex_preserves_finite_limits B K) Y n hY
  have hM := vertex_copies_finite F (vertex_preserves_zero B K)
    (vertex_preserves_finite_limits B K) Y m hY
  have hQ := cokernel_vertex_finite F (vertex_preserves_zero B K)
    (vertex_preserves_finite_limits B K) (vertex_preserves_finite_colimits B K) _ X e hX
  have hQ' := kernel_vertex_finite F (vertex_preserves_zero B K)
    (vertex_preserves_finite_limits B K) (vertex_preserves_finite_colimits B K) _ X' e' hM
  have hDimN := vertex_copies_dimension F (vertex_preserves_zero B K)
    (vertex_preserves_finite_limits B K) Y n hY (dimensionVector B K Y) (fun _ => rfl)
  have hDimM := vertex_copies_dimension F (vertex_preserves_zero B K)
    (vertex_preserves_finite_limits B K) Y m hY (dimensionVector B K Y) (fun _ => rfl)
  have hDQ : dimensionVector B K (cokernel e) =
      fun a => dimensionVector B K X a - (n : Int) * dimensionVector B K Y a := by
    funext a
    have hd := mapped_cokernel_dimension_difference F (vertex_preserves_zero B K)
      (vertex_preserves_finite_limits B K) (vertex_preserves_finite_colimits B K) _ X e hN hX a
    rw [hDimN a] at hd
    exact hd
  have hDQ' : dimensionVector B K (kernel e') =
      fun a => (m : Int) * dimensionVector B K Y a - dimensionVector B K X' a := by
    funext a
    have hd := mapped_kernel_dimension_difference F (vertex_preserves_zero B K)
      (vertex_preserves_finite_limits B K) (vertex_preserves_finite_colimits B K) _ X' e' hM hX' a
    rw [hDimM a] at hd
    exact hd
  have hHom : ∀ g : cokernel e ⟶ kernel e', g = 0 := by
    intro g
    let h : X ⟶ (⨁ fun _ : Fin m => Y) := cokernel.π e ≫ g ≫ kernel.ι e'
    have hz : h = 0 := by
      apply biproduct.hom_ext h 0
      intro j
      simpa only [zero_comp] using hXY (h ≫ biproduct.π (fun _ : Fin m => Y) j)
    apply (cancel_mono (kernel.ι e')).mp
    apply (cancel_epi (cokernel.π e)).mp
    simpa only [h,Category.assoc,zero_comp,comp_zero] using hz
  have heXY := model_euler_pairing B K U hB hs ha X Y hX hY
  have heYY := model_euler_pairing B K U hB hs ha Y Y hY hY
  have heYX' := model_euler_pairing B K U hB hs ha Y X' hY hX'
  have heXX' := model_euler_pairing B K U hB hs ha X X' hX hX'
  have heQQ' := model_euler_pairing B K U hB hs ha (cokernel e) (kernel e') hQ hQ'
  have hm : Module.finrank K (Y ⟶ X') = m := by
    simpa using Module.finrank_eq_card_basis f'
  rw [hom_finrank_zero B K X Y hXY,ext_finrank_zero B K X Y hExtXY] at heXY
  rw [end_finrank_one_of_scalar_end Y hIdY hEndY,
    ext_finrank_zero B K Y Y hRigidY] at heYY
  rw [hm, ext_finrank_zero B K Y X' hYX'] at heYX'
  rw [hom_finrank_zero B K X X' hXX'] at heXX'
  rw [hDQ,hDQ',pairing_copy_differences,heYX',heYY,heXX',heXY,
    hom_finrank_zero B K (cokernel e) (kernel e') hHom] at heQQ'
  have hZero : Module.finrank K (Ext (cokernel e) (kernel e') 1) = 0 ∧
      Module.finrank K (Ext X X' 1) = 0 := by
    simp only [Nat.cast_zero,Nat.cast_one,sub_zero,mul_zero,mul_one,zero_sub,sub_neg_eq_add] at heQQ'
    have hsum : (Module.finrank K (Ext X X' 1) : Int) +
        (Module.finrank K (Ext (cokernel e) (kernel e') 1) : Int) = 0 := by
      linear_combination heQQ'
    constructor <;> omega
  have hFin := model_finite_hom_ext B K (cokernel e) (kernel e') hQ hQ'
  have hOldFin := model_finite_hom_ext B K X X' hX hX'
  letI := hFin.2
  letI := hOldFin.2
  letI : Subsingleton (Ext (cokernel e) (kernel e') 1) :=
    (Module.finrank_zero_iff (R := K)).mp hZero.1
  letI : Subsingleton (Ext X X' 1) := (Module.finrank_zero_iff (R := K)).mp hZero.2
  exact ⟨hHom,fun _ => Subsingleton.elim _ _,fun _ => Subsingleton.elim _ _⟩

#check mixed_evaluation_orthogonality
#print axioms mixed_evaluation_orthogonality
end QuiverProofs.MA4RestartMixedEvaluationOrthogonality
