import MA4RestartEuler20261003.ProjectiveEuler
import MA4RestartEuler20261003.InitialSimples
import QuiverProofs.MAExistenceTeamBRootOrderClosure

/-! Exact weighted vertex/arrow Euler sums and the unique initial matrix. -/
namespace QuiverProofs.MA4RestartMatrixEuler
open CategoryTheory MA4RestartWeightedQuiverModel
open MAExistenceLiterature MAExistenceTeamBRootPositivity
set_option maxHeartbeats 0

def originalEulerMatrix (B : Matrix 4) : Matrix 4 :=
  fun i j => (if i = j then 1 else 0) - (B i j).toNat

lemma pairing_eq_double_sum (U : Matrix 4) (x y : Vector4) :
    pairing U x y = ∑ i, ∑ j, x i * U i j * y j := by
  simp [pairing,Fin.sum_univ_succ]
  ring

lemma original_euler_entry_from_parts (B U : Matrix 4) (hB : SkewSymmetric B)
    (hs : Cosquare.add U (Cosquare.transpose U) = initialCompanion B)
    (ha : Cosquare.add U (Cosquare.scale (-1) (Cosquare.transpose U)) = reverse B)
    (i j : Fin 4) : U i j = originalEulerMatrix B i j := by
  have hsij := congrFun (congrFun hs i) j
  have haij := congrFun (congrFun ha i) j
  change U i j + U j i = (if i = j then 2 else -((B i j).natAbs : Int)) at hsij
  change U i j + (-1) * U j i = -B i j at haij
  by_cases hij : i = j
  · subst j
    have hb : B i i = 0 := by have := hB i i; omega
    simp only [if_true] at hsij
    simp only [originalEulerMatrix,if_true,hb,Int.toNat_zero,Nat.cast_zero,sub_zero]
    omega
  · simp only [hij,if_false] at hsij
    by_cases hb : 0 ≤ B i j
    · have habs := Int.natAbs_of_nonneg hb
      have hnat := Int.toNat_of_nonneg hb
      simp only [originalEulerMatrix,hij,if_false,zero_sub]
      omega
    · have hn : B i j ≤ 0 := by omega
      have habs := Int.eq_neg_natAbs_of_nonpos hn
      have hnat : (B i j).toNat = 0 := Int.toNat_eq_zero.mpr hn
      simp only [originalEulerMatrix,hij,if_false,hnat,Nat.cast_zero,sub_zero]
      omega

lemma original_euler_unique_from_parts (B U : Matrix 4) (hB : SkewSymmetric B)
    (hs : Cosquare.add U (Cosquare.transpose U) = initialCompanion B)
    (ha : Cosquare.add U (Cosquare.scale (-1) (Cosquare.transpose U)) = reverse B) :
    U = originalEulerMatrix B := by
  funext i j
  exact original_euler_entry_from_parts B U hB hs ha i j

lemma initial_euler_diagonal (B U : Matrix 4) (hB : SkewSymmetric B)
    (hs : Cosquare.add U (Cosquare.transpose U) = initialCompanion B)
    (ha : Cosquare.add U (Cosquare.scale (-1) (Cosquare.transpose U)) = reverse B)
    (i : Fin 4) : U i i = 1 := by
  rw [original_euler_entry_from_parts B U hB hs ha i i]
  have hb : B i i = 0 := by have := hB i i; omega
  simp [originalEulerMatrix,hb]

lemma initial_euler_offdiagonal (B U : Matrix 4) (hB : SkewSymmetric B)
    (hs : Cosquare.add U (Cosquare.transpose U) = initialCompanion B)
    (ha : Cosquare.add U (Cosquare.scale (-1) (Cosquare.transpose U)) = reverse B)
    (i j : Fin 4) (hij : i ≠ j) : U i j = -max (B i j) 0 := by
  rw [original_euler_entry_from_parts B U hB hs ha i j]
  simp [originalEulerMatrix,hij]

lemma original_euler_entry_parts (B : Matrix 4) (hB : SkewSymmetric B)
    (i j : Fin 4) :
    originalEulerMatrix B i j + originalEulerMatrix B j i = initialCompanion B i j ∧
    originalEulerMatrix B i j - originalEulerMatrix B j i = -B i j := by
  have hb := hB i j
  by_cases hij : i = j
  · subst j
    have hz : B i i = 0 := by omega
    simp [originalEulerMatrix,initialCompanion,hz]
  · by_cases hp : 0 ≤ B i j
    · have hn : B j i ≤ 0 := by omega
      have ht : (B j i).toNat = 0 := Int.toNat_eq_zero.mpr hn
      have hcast := Int.toNat_of_nonneg hp
      have habs := Int.natAbs_of_nonneg hp
      simp only [originalEulerMatrix,initialCompanion,hij,Ne.symm hij,if_false,ht,Nat.cast_zero]
      omega
    · have hn : B i j ≤ 0 := by omega
      have hp' : 0 ≤ B j i := by omega
      have ht : (B i j).toNat = 0 := Int.toNat_eq_zero.mpr hn
      have hcast := Int.toNat_of_nonneg hp'
      have habs := Int.eq_neg_natAbs_of_nonpos hn
      simp only [originalEulerMatrix,initialCompanion,hij,Ne.symm hij,if_false,ht,Nat.cast_zero]
      omega

lemma original_euler_matrix_parts (B : Matrix 4) (hB : SkewSymmetric B) :
    Cosquare.add (originalEulerMatrix B) (Cosquare.transpose (originalEulerMatrix B)) =
      initialCompanion B ∧
    Cosquare.add (originalEulerMatrix B)
      (Cosquare.scale (-1) (Cosquare.transpose (originalEulerMatrix B))) = reverse B := by
  constructor
  · funext i j
    exact (original_euler_entry_parts B hB i j).1
  · funext i j
    change originalEulerMatrix B i j + (-1) * originalEulerMatrix B j i = -B i j
    have := (original_euler_entry_parts B hB i j).2
    omega

lemma vertex_sum_reindex (B : Matrix 4) (x y : Vector4) :
    (∑ i : Vertex B, x i.index * y i.index) = ∑ i : Fin 4, x i * y i := by
  exact Fintype.sum_equiv (vertexEquiv B) _ _ (fun _ => rfl)

lemma weighted_arrow_sum_reindex (B : Matrix 4) (x y : Vector4) :
    (∑ a : (Σ i : Vertex B, Σ j : Vertex B, Quiver.Hom i j),
      x a.1.index * y a.2.1.index) =
      ∑ i : Fin 4, ∑ j : Fin 4, (B i j).toNat * (x i * y j) := by
  rw [Fintype.sum_sigma]
  have hi : ∀ i : Vertex B,
      (∑ a : (Σ j : Vertex B, Quiver.Hom i j), x i.index * y a.1.index) =
      ∑ j : Fin 4, (B i.index j).toNat * (x i.index * y j) := by
    intro i
    rw [Fintype.sum_sigma]
    have hj : ∀ j : Vertex B,
        (∑ _ : Quiver.Hom i j, x i.index * y j.index) =
          (B i.index j.index).toNat * (x i.index * y j.index) := by
      intro j
      change (∑ _ : Fin (B i.index j.index).toNat, x i.index * y j.index) = _
      simp
    simp_rw [hj]
    exact Fintype.sum_equiv (vertexEquiv B) _ _ (fun _ => rfl)
  simp_rw [hi]
  exact Fintype.sum_equiv (vertexEquiv B) _ _ (fun _ => rfl)

lemma original_euler_pairing_vertex_arrows (B : Matrix 4) (x y : Vector4) :
    pairing (originalEulerMatrix B) x y =
      (∑ i : Vertex B, x i.index * y i.index) -
      (∑ a : (Σ i : Vertex B, Σ j : Vertex B, Quiver.Hom i j),
        x a.1.index * y a.2.1.index) := by
  rw [pairing_eq_double_sum,vertex_sum_reindex,weighted_arrow_sum_reindex]
  simp [originalEulerMatrix,Fin.sum_univ_succ]
  ring

lemma initial_euler_pairing_vertex_arrows (B U : Matrix 4) (hB : SkewSymmetric B)
    (hs : Cosquare.add U (Cosquare.transpose U) = initialCompanion B)
    (ha : Cosquare.add U (Cosquare.scale (-1) (Cosquare.transpose U)) = reverse B)
    (x y : Vector4) :
    pairing U x y = (∑ i : Vertex B, x i.index * y i.index) -
      (∑ a : (Σ i : Vertex B, Σ j : Vertex B, Quiver.Hom i j),
        x a.1.index * y a.2.1.index) := by
  rw [original_euler_unique_from_parts B U hB hs ha]
  exact original_euler_pairing_vertex_arrows B x y

open Module CategoryTheory.Category CategoryTheory.Limits
open MA4RestartFreePathProjectives MA4RestartModelExt MA4RestartInitialSimples
variable (B : Matrix 4) (K : Type) [Field K]

local instance modelEnoughProjectives : EnoughProjectives (Representation B K) :=
  representation_enoughProjectives B K
local instance modelHasExt : HasExt.{0} (Representation B K) := representation_hasExt B K
local instance modelFiniteBiproducts : HasFiniteBiproducts (Representation B K) :=
  Abelian.hasFiniteBiproducts

abbrev OriginalArrow := Σ i : Vertex B, Σ j : Vertex B, Quiver.Hom i j

noncomputable def dimensionVector (M : Representation B K) : Vector4 :=
  fun a => (Module.finrank K ((vertexFunctor B K a).obj M) : Int)

noncomputable abbrev originalRelations (M : Representation B K) : Representation B K :=
  ⨁ fun a : OriginalArrow B => freePath B K a.2.1 (M.obj a.1)

theorem model_euler_pairing_of_actual_resolution
    (U : Matrix 4) (hB : SkewSymmetric B)
    (hs : Cosquare.add U (Cosquare.transpose U) = initialCompanion B)
    (ha : Cosquare.add U (Cosquare.scale (-1) (Cosquare.transpose U)) = reverse B)
    (M N : Representation B K)
    (d : originalRelations B K M ⟶ freeCover B K M)
    (p : freeCover B K M ⟶ M) (wdp : d ≫ p = 0)
    (hS : (ShortComplex.mk d p wdp).ShortExact)
    (hM : ∀ a, Module.Finite K ((vertexFunctor B K a).obj M))
    (hN : ∀ a, Module.Finite K ((vertexFunctor B K a).obj N)) :
    Module.Finite K (M ⟶ N) ∧ Module.Finite K (Abelian.Ext M N 1) ∧
    pairing U (dimensionVector B K M) (dimensionVector B K N) =
      (Module.finrank K (M ⟶ N) : Int) - (Module.finrank K (Abelian.Ext M N 1) : Int) ∧
    (∀ n, ∀ e : Abelian.Ext M N (n + 2), e = 0) := by
  have hM₀ : ∀ i : Vertex B, Module.Finite K (M.obj i) := fun i => hM i.index
  have hM₁ : ∀ a : OriginalArrow B, Module.Finite K (M.obj a.1) := fun a => hM a.1.index
  obtain ⟨hHom,hExt,hd,hHigher⟩ := finite_free_path_resolution_euler B K
    (fun i : Vertex B => i) (fun i => M.obj i)
    (fun a : OriginalArrow B => a.2.1) (fun a => M.obj a.1)
    M N d p wdp hS hM₀ hM₁ hN
  refine ⟨hHom,hExt,?_,hHigher⟩
  rw [initial_euler_pairing_vertex_arrows B U hB hs ha]
  simpa only [dimensionVector,Nat.cast_sum,Nat.cast_mul] using hd.symm

lemma pairing_simples (U : Matrix 4) (a b : Fin 4) : pairing U (simple a) (simple b) = U a b := by
  fin_cases a <;> fin_cases b <;> simp [pairing,simple]

lemma dimension_vector_simple (a : Fin 4) :
    dimensionVector B K (simpleRepresentation B K a) = simple a :=
  simple_dimension_vector B K a

theorem initial_simple_ext_finrank_of_actual_resolution
    (U : Matrix 4) (hB : SkewSymmetric B)
    (hs : Cosquare.add U (Cosquare.transpose U) = initialCompanion B)
    (ha : Cosquare.add U (Cosquare.scale (-1) (Cosquare.transpose U)) = reverse B)
    (a b : Fin 4)
    (d : originalRelations B K (simpleRepresentation B K a) ⟶
      freeCover B K (simpleRepresentation B K a))
    (p : freeCover B K (simpleRepresentation B K a) ⟶ simpleRepresentation B K a)
    (wdp : d ≫ p = 0) (hS : (ShortComplex.mk d p wdp).ShortExact) :
    Module.Finite K (Abelian.Ext (simpleRepresentation B K a) (simpleRepresentation B K b) 1) ∧
    Module.finrank K (Abelian.Ext (simpleRepresentation B K a) (simpleRepresentation B K b) 1) =
      (B a b).toNat := by
  obtain ⟨_,hExt,he,_⟩ := model_euler_pairing_of_actual_resolution B K U hB hs ha
    (simpleRepresentation B K a) (simpleRepresentation B K b) d p wdp hS
    (simple_finite_vertices B K a) (simple_finite_vertices B K b)
  refine ⟨hExt, ?_⟩
  rw [dimension_vector_simple,dimension_vector_simple,pairing_simples,
    original_euler_entry_from_parts B U hB hs ha a b,simple_hom_finrank] at he
  simp only [originalEulerMatrix] at he
  split at he <;> omega

theorem initial_simple_rigid_of_actual_resolution
    (U : Matrix 4) (hB : SkewSymmetric B)
    (hs : Cosquare.add U (Cosquare.transpose U) = initialCompanion B)
    (ha : Cosquare.add U (Cosquare.scale (-1) (Cosquare.transpose U)) = reverse B)
    (a : Fin 4)
    (d : originalRelations B K (simpleRepresentation B K a) ⟶
      freeCover B K (simpleRepresentation B K a))
    (p : freeCover B K (simpleRepresentation B K a) ⟶ simpleRepresentation B K a)
    (wdp : d ≫ p = 0) (hS : (ShortComplex.mk d p wdp).ShortExact) :
    ∀ e : Abelian.Ext (simpleRepresentation B K a) (simpleRepresentation B K a) 1, e = 0 := by
  obtain ⟨hExt,he⟩ := initial_simple_ext_finrank_of_actual_resolution B K U hB hs ha a a d p wdp hS
  letI := hExt
  have hb : B a a = 0 := by have := hB a a; omega
  rw [hb,Int.toNat_zero] at he
  letI : Subsingleton (Abelian.Ext (simpleRepresentation B K a) (simpleRepresentation B K a) 1) :=
    (Module.finrank_zero_iff (R := K)).mp he
  intro e
  exact Subsingleton.elim _ _

theorem initial_simple_ext_basis_of_actual_resolution
    (U : Matrix 4) (hB : SkewSymmetric B)
    (hs : Cosquare.add U (Cosquare.transpose U) = initialCompanion B)
    (ha : Cosquare.add U (Cosquare.scale (-1) (Cosquare.transpose U)) = reverse B)
    (a b : Fin 4)
    (d : originalRelations B K (simpleRepresentation B K a) ⟶
      freeCover B K (simpleRepresentation B K a))
    (p : freeCover B K (simpleRepresentation B K a) ⟶ simpleRepresentation B K a)
    (wdp : d ≫ p = 0) (hS : (ShortComplex.mk d p wdp).ShortExact) :
    Nonempty (Basis (Fin (B a b).toNat) K
      (Abelian.Ext (simpleRepresentation B K a) (simpleRepresentation B K b) 1)) := by
  obtain ⟨hExt,hr⟩ := initial_simple_ext_finrank_of_actual_resolution B K U hB hs ha a b d p wdp hS
  letI := hExt
  exact ⟨(Module.finBasis K _).reindex (finCongr hr)⟩

theorem model_ext_basis_from_hom_zero_of_actual_resolution
    (U : Matrix 4) (hB : SkewSymmetric B)
    (hs : Cosquare.add U (Cosquare.transpose U) = initialCompanion B)
    (ha : Cosquare.add U (Cosquare.scale (-1) (Cosquare.transpose U)) = reverse B)
    (M N : Representation B K)
    (d : originalRelations B K M ⟶ freeCover B K M)
    (p : freeCover B K M ⟶ M) (wdp : d ≫ p = 0)
    (hS : (ShortComplex.mk d p wdp).ShortExact)
    (hM : ∀ a, Module.Finite K ((vertexFunctor B K a).obj M))
    (hN : ∀ a, Module.Finite K ((vertexFunctor B K a).obj N))
    (hHom : ∀ f : M ⟶ N, f = 0) :
    Nonempty (Basis (Fin (-pairing U (dimensionVector B K M) (dimensionVector B K N)).toNat)
      K (Abelian.Ext M N 1)) := by
  obtain ⟨_,hExt,he,_⟩ := model_euler_pairing_of_actual_resolution B K U hB hs ha M N d p wdp hS hM hN
  letI := hExt
  letI : Subsingleton (M ⟶ N) := ⟨fun f g => by rw [hHom f,hHom g]⟩
  rw [Module.finrank_zero_of_subsingleton] at he
  have hn : (-pairing U (dimensionVector B K M) (dimensionVector B K N)).toNat =
      Module.finrank K (Abelian.Ext M N 1) := by omega
  exact ⟨(Module.finBasis K _).reindex (finCongr hn.symm)⟩

theorem model_hom_basis_from_ext_zero_of_actual_resolution
    (U : Matrix 4) (hB : SkewSymmetric B)
    (hs : Cosquare.add U (Cosquare.transpose U) = initialCompanion B)
    (ha : Cosquare.add U (Cosquare.scale (-1) (Cosquare.transpose U)) = reverse B)
    (M N : Representation B K)
    (d : originalRelations B K M ⟶ freeCover B K M)
    (p : freeCover B K M ⟶ M) (wdp : d ≫ p = 0)
    (hS : (ShortComplex.mk d p wdp).ShortExact)
    (hM : ∀ a, Module.Finite K ((vertexFunctor B K a).obj M))
    (hN : ∀ a, Module.Finite K ((vertexFunctor B K a).obj N))
    (hExt : ∀ e : Abelian.Ext M N 1, e = 0) :
    Nonempty (Basis (Fin (pairing U (dimensionVector B K M) (dimensionVector B K N)).toNat)
      K (M ⟶ N)) := by
  obtain ⟨hHom,hExtFinite,he,_⟩ := model_euler_pairing_of_actual_resolution B K U hB hs ha M N d p wdp hS hM hN
  letI := hHom
  letI : Subsingleton (Abelian.Ext M N 1) := ⟨fun e f => by rw [hExt e,hExt f]⟩
  rw [Module.finrank_zero_of_subsingleton (R := K) (M := Abelian.Ext M N 1)] at he
  have hn : (pairing U (dimensionVector B K M) (dimensionVector B K N)).toNat =
      Module.finrank K (M ⟶ N) := by omega
  exact ⟨(Module.finBasis K _).reindex (finCongr hn.symm)⟩

#print axioms model_euler_pairing_of_actual_resolution
#print axioms initial_simple_ext_finrank_of_actual_resolution
#print axioms initial_simple_rigid_of_actual_resolution
#print axioms initial_simple_ext_basis_of_actual_resolution
#print axioms model_ext_basis_from_hom_zero_of_actual_resolution
#print axioms model_hom_basis_from_ext_zero_of_actual_resolution
#print axioms initial_euler_pairing_vertex_arrows
end QuiverProofs.MA4RestartMatrixEuler
