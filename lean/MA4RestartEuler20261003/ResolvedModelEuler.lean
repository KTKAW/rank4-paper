import MA4RestartEuler20261003.MatrixEuler
import MA4RestartEuler20261003.HereditaryBridge
import MA4RestartCoordinator20261003.PathResolution

/-! Fixed-model Euler, hereditary and initial-simple data with the actual
constructed resolution; no caller-supplied short exact sequence remains. -/
namespace QuiverProofs.MA4RestartResolvedModelEuler
open Module CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open MAExistenceLiterature MAExistenceTeamBRootPositivity MA4RestartWeightedQuiverModel
  MA4RestartFreePathProjectives MA4RestartPathResolution MA4RestartModelExt
  MA4RestartInitialSimples MA4RestartMatrixEuler
variable (B : Matrix 4) (K : Type) [Field K]

local instance actualEnoughProjectives : EnoughProjectives (Representation B K) :=
  representation_enoughProjectives B K
local instance actualHasExt : HasExt.{0} (Representation B K) := representation_hasExt B K
local instance actualFiniteBiproducts : HasFiniteBiproducts (Representation B K) :=
  Abelian.hasFiniteBiproducts

/-- The exact class-valued field required by the mutation primitives. -/
theorem model_hereditary : ∀ T : Representation B K, HasProjectiveDimensionLT T 2 := by
  intro T
  letI : Projective (resolutionComplex B K T).X₁ := freeRelations_projective B K T
  letI : Projective (resolutionComplex B K T).X₂ := freeCover_projective B K T
  exact MA4RestartEuler20261003.projective_length_one_dimension_bound (resolution_shortExact B K T)

theorem model_higher_ext_zero (M N : Representation B K) (n : ℕ) (hn : 2 ≤ n)
    (e : Abelian.Ext M N n) : e = 0 :=
  MA4RestartEuler20261003.global_hereditary_ordinary_ext_bound (model_hereditary B K) M N n hn e

/-- The same intrinsic bound consumes the ordinary standard Ext universe too. -/
theorem model_higher_ext_zero_standard :
    letI := HasExt.standard (Representation B K)
    ∀ (M N : Representation B K) (n : ℕ) (_ : 2 ≤ n) (e : Abelian.Ext.{1} M N n), e = 0 := by
  letI := HasExt.standard (Representation B K)
  intro M N n hn e
  exact MA4RestartEuler20261003.global_hereditary_ordinary_ext_bound (model_hereditary B K) M N n hn e

theorem model_finite_hom_ext (M N : Representation B K)
    (hM : ∀ a, Module.Finite K ((vertexFunctor B K a).obj M))
    (hN : ∀ a, Module.Finite K ((vertexFunctor B K a).obj N)) :
    Module.Finite K (M ⟶ N) ∧ Module.Finite K (Abelian.Ext M N 1) := by
  have hM₀ : ∀ i : Vertex B, Module.Finite K (M.obj i) := fun i => hM i.index
  have hM₁ : ∀ a : Arrow B, Module.Finite K (M.obj a.1) := fun a => hM a.1.index
  obtain ⟨hHom,hExt,_,_⟩ := finite_free_path_resolution_euler B K
    (fun i : Vertex B => i) (fun i => M.obj i)
    (fun a : Arrow B => a.2.1) (fun a => M.obj a.1) M N
    (relationMap B K M) (freeCoverTo B K M) (relationMap_augmentation B K M)
    (resolution_shortExact B K M) hM₀ hM₁ hN
  exact ⟨hHom,hExt⟩

theorem model_euler_pairing (U : Matrix 4) (hB : SkewSymmetric B)
    (hs : Cosquare.add U (Cosquare.transpose U) = initialCompanion B)
    (ha : Cosquare.add U (Cosquare.scale (-1) (Cosquare.transpose U)) = reverse B)
    (M N : Representation B K)
    (hM : ∀ a, Module.Finite K ((vertexFunctor B K a).obj M))
    (hN : ∀ a, Module.Finite K ((vertexFunctor B K a).obj N)) :
    pairing U (dimensionVector B K M) (dimensionVector B K N) =
      (Module.finrank K (M ⟶ N) : Int) - (Module.finrank K (Abelian.Ext M N 1) : Int) := by
  obtain ⟨_,_,he,_⟩ := model_euler_pairing_of_actual_resolution B K U hB hs ha M N
    (relationMap B K M) (freeCoverTo B K M) (relationMap_augmentation B K M)
    (resolution_shortExact B K M) hM hN
  exact he

theorem initial_simple_ext_finrank (hB : SkewSymmetric B) (a b : Fin 4) :
    Module.Finite K (Abelian.Ext (simpleRepresentation B K a) (simpleRepresentation B K b) 1) ∧
    Module.finrank K (Abelian.Ext (simpleRepresentation B K a) (simpleRepresentation B K b) 1) =
      (B a b).toNat := by
  have h := original_euler_matrix_parts B hB
  exact initial_simple_ext_finrank_of_actual_resolution B K (originalEulerMatrix B) hB h.1 h.2 a b
    (relationMap B K (simpleRepresentation B K a)) (freeCoverTo B K (simpleRepresentation B K a))
    (relationMap_augmentation B K (simpleRepresentation B K a))
    (resolution_shortExact B K (simpleRepresentation B K a))

theorem initial_simple_rigid (hB : SkewSymmetric B) (a : Fin 4) :
    ∀ e : Abelian.Ext (simpleRepresentation B K a) (simpleRepresentation B K a) 1, e = 0 := by
  have h := original_euler_matrix_parts B hB
  exact initial_simple_rigid_of_actual_resolution B K (originalEulerMatrix B) hB h.1 h.2 a
    (relationMap B K (simpleRepresentation B K a)) (freeCoverTo B K (simpleRepresentation B K a))
    (relationMap_augmentation B K (simpleRepresentation B K a))
    (resolution_shortExact B K (simpleRepresentation B K a))

theorem initial_simple_full_ext_basis (hB : SkewSymmetric B) (a b : Fin 4) :
    Nonempty (Basis (Fin (B a b).toNat) K
      (Abelian.Ext (simpleRepresentation B K a) (simpleRepresentation B K b) 1)) := by
  have h := original_euler_matrix_parts B hB
  exact initial_simple_ext_basis_of_actual_resolution B K (originalEulerMatrix B) hB h.1 h.2 a b
    (relationMap B K (simpleRepresentation B K a)) (freeCoverTo B K (simpleRepresentation B K a))
    (relationMap_augmentation B K (simpleRepresentation B K a))
    (resolution_shortExact B K (simpleRepresentation B K a))

theorem initial_simple_ext_zero_of_nonpositive (hB : SkewSymmetric B)
    (a b : Fin 4) (hab : B a b ≤ 0) :
    ∀ e : Abelian.Ext (simpleRepresentation B K a) (simpleRepresentation B K b) 1, e = 0 := by
  obtain ⟨hExt,hr⟩ := initial_simple_ext_finrank B K hB a b
  letI := hExt
  rw [Int.toNat_eq_zero.mpr hab] at hr
  letI : Subsingleton (Abelian.Ext (simpleRepresentation B K a) (simpleRepresentation B K b) 1) :=
    (Module.finrank_zero_iff (R := K)).mp hr
  intro e
  exact Subsingleton.elim _ _

theorem model_full_ext_basis_from_hom_zero (U : Matrix 4) (hB : SkewSymmetric B)
    (hs : Cosquare.add U (Cosquare.transpose U) = initialCompanion B)
    (ha : Cosquare.add U (Cosquare.scale (-1) (Cosquare.transpose U)) = reverse B)
    (M N : Representation B K)
    (hM : ∀ a, Module.Finite K ((vertexFunctor B K a).obj M))
    (hN : ∀ a, Module.Finite K ((vertexFunctor B K a).obj N))
    (hHom : ∀ f : M ⟶ N, f = 0) :
    Nonempty (Basis (Fin (-pairing U (dimensionVector B K M) (dimensionVector B K N)).toNat)
      K (Abelian.Ext M N 1)) :=
  model_ext_basis_from_hom_zero_of_actual_resolution B K U hB hs ha M N
    (relationMap B K M) (freeCoverTo B K M) (relationMap_augmentation B K M)
    (resolution_shortExact B K M) hM hN hHom

theorem model_full_hom_basis_from_ext_zero (U : Matrix 4) (hB : SkewSymmetric B)
    (hs : Cosquare.add U (Cosquare.transpose U) = initialCompanion B)
    (ha : Cosquare.add U (Cosquare.scale (-1) (Cosquare.transpose U)) = reverse B)
    (M N : Representation B K)
    (hM : ∀ a, Module.Finite K ((vertexFunctor B K a).obj M))
    (hN : ∀ a, Module.Finite K ((vertexFunctor B K a).obj N))
    (hExt : ∀ e : Abelian.Ext M N 1, e = 0) :
    Nonempty (Basis (Fin (pairing U (dimensionVector B K M) (dimensionVector B K N)).toNat)
      K (M ⟶ N)) :=
  model_hom_basis_from_ext_zero_of_actual_resolution B K U hB hs ha M N
    (relationMap B K M) (freeCoverTo B K M) (relationMap_augmentation B K M)
    (resolution_shortExact B K M) hM hN hExt

#print axioms model_hereditary
#print axioms model_higher_ext_zero_standard
#print axioms model_euler_pairing
#print axioms initial_simple_rigid
#print axioms model_full_ext_basis_from_hom_zero
end QuiverProofs.MA4RestartResolvedModelEuler
