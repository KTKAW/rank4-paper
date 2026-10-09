import MA4Coordinator20261003.ExactVertexDimensions

/-! Export the actual replacement's vertex finiteness and detect nonzero
objects by a positive finite vertex dimension. Vertex exactness and joint
epimorphism reflection are supplied until the fixed representation model is built. -/
namespace QuiverProofs.MA4RestartVertexFiniteness
open CategoryTheory CategoryTheory.Limits
universe w v u
variable {K : Type w} [Field K] {C : Type u} [Category.{v} C] [Abelian C]
set_option maxHeartbeats 0

/-- Mapped surjectivity exports finite-dimensionality of every actual
cokernel component, requiring finiteness only of the old target. -/
theorem cokernel_vertex_finite
    (F : Fin 4 → C ⥤ ModuleCat.{v} K)
    (hZero : ∀ a, (F a).PreservesZeroMorphisms)
    (hLimits : ∀ a, PreservesFiniteLimits (F a))
    (hColimits : ∀ a, PreservesFiniteColimits (F a))
    (M V : C) (e : M ⟶ V) [Mono e]
    (hV : ∀ a, Module.Finite K ((F a).obj V)) :
    ∀ a, Module.Finite K ((F a).obj (cokernel e)) := by
  let S := ShortComplex.mk e (cokernel.π e) (cokernel.condition e)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel e }
  intro a
  letI := hZero a
  letI := hLimits a
  letI := hColimits a
  letI := hV a
  exact Module.Finite.of_surjective ((F a).map (cokernel.π e)).hom
    (hS.map_of_exact (F a)).moduleCat_surjective_g

/-- Mapped injectivity exports finiteness of every actual kernel component,
requiring finiteness only of the old source. -/
theorem kernel_vertex_finite
    (F : Fin 4 → C ⥤ ModuleCat.{v} K)
    (hZero : ∀ a, (F a).PreservesZeroMorphisms)
    (hLimits : ∀ a, PreservesFiniteLimits (F a))
    (hColimits : ∀ a, PreservesFiniteColimits (F a))
    (M V : C) (e : M ⟶ V) [Epi e]
    (hM : ∀ a, Module.Finite K ((F a).obj M)) :
    ∀ a, Module.Finite K ((F a).obj (kernel e)) := by
  let S := ShortComplex.mk (kernel.ι e) e (kernel.condition e)
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel e }
  intro a
  letI := hZero a
  letI := hLimits a
  letI := hColimits a
  letI := hM a
  exact Module.Finite.of_injective ((F a).map (kernel.ι e)).hom
    (hS.map_of_exact (F a)).moduleCat_injective_f

/-- Joint Epi reflection and actual finite components detect every nonzero
object by a positive vertex dimension; this is not a supplied root identity. -/
theorem positive_vertex_dimension_of_nonzero
    (F : Fin 4 → C ⥤ ModuleCat.{v} K)
    (hReflect : ∀ {X Y : C} (f : X ⟶ Y),
      (∀ a, Epi ((F a).map f)) → Epi f)
    (Q : C) (hQ : ∀ a, Module.Finite K ((F a).obj Q))
    (hId : (𝟙 Q : Q ⟶ Q) ≠ 0) :
    ∃ a, 0 < Module.finrank K ((F a).obj Q) := by
  classical
  by_contra h
  have hz : ∀ a, Module.finrank K ((F a).obj Q) = 0 := by
    intro a
    have hh : ¬ 0 < Module.finrank K ((F a).obj Q) := by
      intro hp
      exact h ⟨a, hp⟩
    omega
  have he : Epi (0 : Q ⟶ Q) := by
    apply hReflect
    intro a
    letI := hQ a
    letI : Subsingleton ((F a).obj Q) := Module.finrank_zero_iff.mp (hz a)
    apply (ModuleCat.epi_iff_surjective ((F a).map (0 : Q ⟶ Q))).mpr
    intro x
    exact ⟨0, Subsingleton.elim _ _⟩
  letI := he
  apply hId
  apply (cancel_epi (0 : Q ⟶ Q)).mp
  simp only [zero_comp]

#print axioms cokernel_vertex_finite
#print axioms kernel_vertex_finite
#print axioms positive_vertex_dimension_of_nonzero
end QuiverProofs.MA4RestartVertexFiniteness
