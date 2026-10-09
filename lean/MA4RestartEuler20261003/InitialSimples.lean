import MA4RestartCoordinator20261003.WeightedQuiverModel
import Mathlib.Algebra.Category.ModuleCat.Simple

/-! Actual arrow-zero initial simples on the fixed weighted-quiver model.
No Ext, projectivity, Euler or root realization conclusion is assumed here. -/
namespace QuiverProofs.MA4RestartInitialSimples
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open MA4RestartWeightedQuiverModel
variable (B : Matrix 4) (K : Type) [Field K]

def simplePrefunctor (a : Fin 4) : Vertex B ⥤q ModuleCat.{0} K where
  obj b := ModuleCat.of K (Fin (if b.index = a then 1 else 0) → K)
  map _ := 0

def simpleRepresentation (a : Fin 4) : Representation B K :=
  Paths.lift (simplePrefunctor B K a)

lemma simple_vertex_object (a b : Fin 4) :
    (vertexFunctor B K b).obj (simpleRepresentation B K a) =
      ModuleCat.of K (Fin (if b = a then 1 else 0) → K) := rfl

lemma simple_arrow_map_zero (a : Fin 4) {i j : Vertex B} (f : Quiver.Hom i j) :
    (simpleRepresentation B K a).map f.toPath = 0 := by
  simp [simpleRepresentation, simplePrefunctor]

lemma simple_finite_vertices (a b : Fin 4) :
    Module.Finite K ((vertexFunctor B K b).obj (simpleRepresentation B K a)) := by
  change Module.Finite K (Fin (if b = a then 1 else 0) → K)
  infer_instance

lemma simple_vertex_finrank (a b : Fin 4) :
    Module.finrank K ((vertexFunctor B K b).obj (simpleRepresentation B K a)) =
      if b = a then 1 else 0 := by
  change Module.finrank K (Fin (if b = a then 1 else 0) → K) = _
  simp

lemma simple_identity_nonzero (a : Fin 4) :
    (𝟙 (simpleRepresentation B K a) : simpleRepresentation B K a ⟶
      simpleRepresentation B K a) ≠ 0 := by
  intro h
  have he := congrArg (fun f : simpleRepresentation B K a ⟶ simpleRepresentation B K a =>
    f.app (⟨a⟩ : Vertex B)) h
  have hv := congrArg (fun f => f (fun _ => (1 : K))) he
  have hi := congrArg (fun v => v (⟨0, by simp⟩ : Fin (if a = a then 1 else 0))) hv
  change (1 : K) = 0 at hi
  exact one_ne_zero hi

lemma simple_pair_hom_orthogonality (a b : Fin 4) (hab : a ≠ b) :
    ∀ f : simpleRepresentation B K a ⟶ simpleRepresentation B K b, f = 0 := by
  intro f
  apply NatTrans.ext
  funext v
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  by_cases ha : v.index = a
  · have hb : v.index ≠ b := by simpa [ha] using hab
    change f.app v x = (0 : Fin (if v.index = b then 1 else 0) → K)
    apply funext
    intro j
    have hj : j.val < 0 := by simpa [hb] using j.isLt
    exact False.elim (Nat.not_lt_zero _ hj)
  · have hx : x = 0 := by
      apply funext
      intro j
      have hj : j.val < 0 := by simpa [ha] using j.isLt
      exact False.elim (Nat.not_lt_zero _ hj)
    simp [hx]

lemma simple_scalar_endomorphisms (a : Fin 4) :
    ∀ f : simpleRepresentation B K a ⟶ simpleRepresentation B K a,
      ∃ c : K, f = c • 𝟙 (simpleRepresentation B K a) := by
  intro f
  let v : Vertex B := ⟨a⟩
  let unit : (simpleRepresentation B K a).obj v := fun _ => 1
  let z : Fin (if a = a then 1 else 0) := ⟨0, by simp⟩
  let c : K := f.app v unit z
  refine ⟨c, ?_⟩
  apply NatTrans.ext
  funext b
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  by_cases hb : b.index = a
  · have hba : b = v := by
      cases b with
      | mk q => change q = a at hb; subst q; rfl
    subst b
    have hx : x = x z • unit := by
      apply funext
      intro j
      have hj : j = z := by
        apply Fin.ext
        change j.val = 0
        have ht : j.val < 1 := by simpa [v] using j.isLt
        omega
      subst j
      change x z = x z * 1
      exact (mul_one _).symm
    rw [hx]
    change (f.app v).hom (x z • unit) = c • (x z • unit)
    rw [map_smul]
    apply funext
    intro j
    have hj : j = z := by
      apply Fin.ext
      change j.val = 0
      have ht : j.val < 1 := by simpa [v] using j.isLt
      omega
    subst j
    change x z * f.app v unit z = c * (x z * 1)
    simp [c,mul_comm]
  · have hx : x = 0 := by
      apply funext
      intro j
      have hj : j.val < 0 := by simpa [hb] using j.isLt
      exact False.elim (Nat.not_lt_zero _ hj)
    simp [hx]

def simpleEndCoordinate (a : Fin 4) :
    (simpleRepresentation B K a ⟶ simpleRepresentation B K a) →ₗ[K] K where
  toFun f := f.app (⟨a⟩ : Vertex B) (fun _ => 1) ⟨0, by simp⟩
  map_add' f g := rfl
  map_smul' c f := rfl

lemma simple_end_coordinate_scalar (a : Fin 4) (c : K) :
    simpleEndCoordinate B K a (c • 𝟙 (simpleRepresentation B K a)) = c := by
  change c * 1 = c
  exact mul_one c

lemma simple_end_coordinate_bijective (a : Fin 4) :
    Function.Bijective (simpleEndCoordinate B K a) := by
  constructor
  · intro f g h
    obtain ⟨c,hc⟩ := simple_scalar_endomorphisms B K a f
    obtain ⟨d,hd⟩ := simple_scalar_endomorphisms B K a g
    rw [hc,hd,simple_end_coordinate_scalar,simple_end_coordinate_scalar] at h
    rw [hc,hd,h]
  · intro c
    exact ⟨c • 𝟙 (simpleRepresentation B K a), simple_end_coordinate_scalar B K a c⟩

noncomputable def simpleEndLinearEquiv (a : Fin 4) :
    (simpleRepresentation B K a ⟶ simpleRepresentation B K a) ≃ₗ[K] K :=
  LinearEquiv.ofBijective (simpleEndCoordinate B K a) (simple_end_coordinate_bijective B K a)

lemma simple_finite_hom (a b : Fin 4) :
    Module.Finite K (simpleRepresentation B K a ⟶ simpleRepresentation B K b) :=
  finite_hom_of_finite_vertices B K (simpleRepresentation B K a) (simpleRepresentation B K b)
    (simple_finite_vertices B K a) (simple_finite_vertices B K b)

lemma simple_hom_finrank (a b : Fin 4) :
    Module.finrank K (simpleRepresentation B K a ⟶ simpleRepresentation B K b) =
      if a = b then 1 else 0 := by
  classical
  by_cases hab : a = b
  · subst b
    rw [(simpleEndLinearEquiv B K a).finrank_eq]
    simp
  · letI : Subsingleton (simpleRepresentation B K a ⟶ simpleRepresentation B K b) :=
      ⟨fun f g => by rw [simple_pair_hom_orthogonality B K a b hab f,
        simple_pair_hom_orthogonality B K a b hab g]⟩
    simpa [hab] using (Module.finrank_zero_of_subsingleton (R := K)
      (M := simpleRepresentation B K a ⟶ simpleRepresentation B K b))

lemma simple_support_detects_nonzero (a : Fin 4) (M : Representation B K)
    (f : M ⟶ simpleRepresentation B K a) (hf : f ≠ 0) :
    f.app (⟨a⟩ : Vertex B) ≠ 0 := by
  intro hz
  apply hf
  apply NatTrans.ext
  funext b
  by_cases hb : b.index = a
  · have hba : b = (⟨a⟩ : Vertex B) := by
      cases b with
      | mk q => change q = a at hb; subst q; rfl
    subst b
    exact hz
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply funext
    intro j
    have hj : j.val < 0 := by simpa [hb] using j.isLt
    exact False.elim (Nat.not_lt_zero _ hj)

lemma simple_nonzero_incoming_epi (a : Fin 4) (M : Representation B K)
    (f : M ⟶ simpleRepresentation B K a) (hf : f ≠ 0) : Epi f := by
  apply vertices_jointly_reflect_epi B K f
  intro b
  by_cases hb : b = a
  · subst b
    apply (ModuleCat.epi_iff_surjective _).mpr
    have hn : (f.app (⟨a⟩ : Vertex B)).hom ≠ 0 := by
      intro hz
      apply simple_support_detects_nonzero B K a M f hf
      exact ModuleCat.hom_ext hz
    exact surjective_of_nonzero_of_finrank_eq_one
      (by simpa using simple_vertex_finrank B K a a) hn
  · apply (ModuleCat.epi_iff_surjective _).mpr
    intro y
    refine ⟨0, ?_⟩
    apply funext
    intro j
    have hj : j.val < 0 := by simpa [hb] using j.isLt
    exact False.elim (Nat.not_lt_zero _ hj)

lemma simple_mono_isIso_iff_nonzero (a : Fin 4) (M : Representation B K)
    (f : M ⟶ simpleRepresentation B K a) [Mono f] : IsIso f ↔ f ≠ 0 := by
  constructor
  · intro h
    letI := h
    intro hz
    apply simple_identity_nonzero B K a
    apply (cancel_epi f).mp
    simp [hz]
  · intro hf
    letI : Epi f := simple_nonzero_incoming_epi B K a M f hf
    exact isIso_of_mono_of_epi f

noncomputable def simpleDimension (a : Fin 4) : Fin 4 → Int :=
  fun b => (Module.finrank K ((vertexFunctor B K b).obj (simpleRepresentation B K a)) : Int)

lemma simple_dimension_vector (a : Fin 4) :
    simpleDimension B K a = fun b => if b = a then 1 else 0 := by
  funext b
  unfold simpleDimension
  rw [simple_vertex_finrank]
  split <;> rfl

noncomputable def simplePivotLinearEquiv (a : Fin 4) :
    ((vertexFunctor B K a).obj (simpleRepresentation B K a)) ≃ₗ[K] K := by
  change (Fin (if a = a then 1 else 0) → K) ≃ₗ[K] K
  rw [if_pos rfl]
  exact LinearEquiv.funUnique (Fin 1) K K

lemma simple_other_vertex_isZero (a b : Fin 4) (hb : b ≠ a) :
    IsZero ((vertexFunctor B K b).obj (simpleRepresentation B K a)) := by
  rw [IsZero.iff_id_eq_zero]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply funext
  intro j
  have hj : j.val < 0 := by simpa [hb] using j.isLt
  exact False.elim (Nat.not_lt_zero _ hj)

lemma simple_is_simple (a : Fin 4) : Simple (simpleRepresentation B K a) :=
  ⟨fun {M} f _ => simple_mono_isIso_iff_nonzero B K a M f⟩

#print axioms simple_is_simple

#print axioms simple_mono_isIso_iff_nonzero

#print axioms simple_hom_finrank
#print axioms simple_identity_nonzero
#print axioms simple_pair_hom_orthogonality
#print axioms simple_scalar_endomorphisms
end QuiverProofs.MA4RestartInitialSimples
