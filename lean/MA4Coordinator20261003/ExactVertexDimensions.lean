import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Pointwise dimensions of actual kernel/cokernel objects under exact vertex
functors. Their exactness and old finite-dimensional objects remain supplied;
no quiver representation model, root frame or numerical Euler theorem is built. -/
namespace QuiverProofs.MACompletionExactVertexDimensions
open CategoryTheory CategoryTheory.Limits
universe w v u
variable {K : Type w} [Field K]
set_option maxHeartbeats 0

/-- Dimension additivity for an actual finite-dimensional short exact sequence. -/
theorem shortExact_finrank_add (S : ShortComplex (ModuleCat.{v} K))
    [Module.Finite K S.X₁] [Module.Finite K S.X₂] [Module.Finite K S.X₃]
    (hS : S.ShortExact) :
    Module.finrank K S.X₂ = Module.finrank K S.X₁ + Module.finrank K S.X₃ := by
  have hd := LinearMap.finrank_range_add_finrank_ker S.g.hom
  rw [LinearMap.range_eq_top.mpr hS.moduleCat_surjective_g, finrank_top,
    ← hS.exact.moduleCat_range_eq_ker,
    LinearMap.finrank_range_of_inj hS.moduleCat_injective_f] at hd
  simpa only [add_comm] using hd.symm

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Exact vertex functors preserve the actual short exact sequence; coordinate
rank additivity follows, with each finite-dimensionality premise explicit. -/
theorem vertex_shortExact_dimension_add
    (F : Fin 4 → C ⥤ ModuleCat.{v} K)
    (hZero : ∀ a, (F a).PreservesZeroMorphisms)
    (hLimits : ∀ a, PreservesFiniteLimits (F a))
    (hColimits : ∀ a, PreservesFiniteColimits (F a))
    (S : ShortComplex C) (hS : S.ShortExact)
    (h₁ : ∀ a, Module.Finite K ((F a).obj S.X₁))
    (h₂ : ∀ a, Module.Finite K ((F a).obj S.X₂))
    (h₃ : ∀ a, Module.Finite K ((F a).obj S.X₃)) :
    ∀ a, (Module.finrank K ((F a).obj S.X₂) : Int) =
      (Module.finrank K ((F a).obj S.X₁) : Int) +
      (Module.finrank K ((F a).obj S.X₃) : Int) := by
  intro a
  letI := hZero a
  letI := hLimits a
  letI := hColimits a
  letI := h₁ a
  letI := h₂ a
  letI := h₃ a
  letI : Module.Finite K (S.map (F a)).X₁ := h₁ a
  letI : Module.Finite K (S.map (F a)).X₂ := h₂ a
  letI : Module.Finite K (S.map (F a)).X₃ := h₃ a
  exact_mod_cast shortExact_finrank_add (S.map (F a)) (hS.map_of_exact (F a))

/-- The actual chosen cokernel has the coordinate difference of target and
source. Its next finite-dimensionality follows from mapped surjectivity. -/
theorem mapped_cokernel_dimension_difference
    (F : Fin 4 → C ⥤ ModuleCat.{v} K)
    (hZero : ∀ a, (F a).PreservesZeroMorphisms)
    (hLimits : ∀ a, PreservesFiniteLimits (F a))
    (hColimits : ∀ a, PreservesFiniteColimits (F a))
    (M V : C) (e : M ⟶ V) [Mono e]
    (hM : ∀ a, Module.Finite K ((F a).obj M))
    (hV : ∀ a, Module.Finite K ((F a).obj V)) :
    ∀ a, (Module.finrank K ((F a).obj (cokernel e)) : Int) =
      (Module.finrank K ((F a).obj V) : Int) -
      (Module.finrank K ((F a).obj M) : Int) := by
  let S := ShortComplex.mk e (cokernel.π e) (cokernel.condition e)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel e }
  intro a
  letI := hZero a
  letI := hLimits a
  letI := hColimits a
  letI := hM a
  letI := hV a
  have hm := hS.map_of_exact (F a)
  letI : Module.Finite K ((F a).obj (cokernel e)) :=
    Module.Finite.of_surjective ((F a).map (cokernel.π e)).hom hm.moduleCat_surjective_g
  letI : Module.Finite K (S.map (F a)).X₁ := by dsimp [ShortComplex.map, S]; infer_instance
  letI : Module.Finite K (S.map (F a)).X₂ := by dsimp [ShortComplex.map, S]; infer_instance
  letI : Module.Finite K (S.map (F a)).X₃ := by dsimp [ShortComplex.map, S]; infer_instance
  have hd := shortExact_finrank_add (S.map (F a)) hm
  change Module.finrank K ((F a).obj V) =
    Module.finrank K ((F a).obj M) + Module.finrank K ((F a).obj (cokernel e)) at hd
  omega

/-- The actual chosen kernel has the opposite difference, with its next
finite-dimensionality derived from mapped injectivity into the old source. -/
theorem mapped_kernel_dimension_difference
    (F : Fin 4 → C ⥤ ModuleCat.{v} K)
    (hZero : ∀ a, (F a).PreservesZeroMorphisms)
    (hLimits : ∀ a, PreservesFiniteLimits (F a))
    (hColimits : ∀ a, PreservesFiniteColimits (F a))
    (M V : C) (e : M ⟶ V) [Epi e]
    (hM : ∀ a, Module.Finite K ((F a).obj M))
    (hV : ∀ a, Module.Finite K ((F a).obj V)) :
    ∀ a, (Module.finrank K ((F a).obj (kernel e)) : Int) =
      (Module.finrank K ((F a).obj M) : Int) -
      (Module.finrank K ((F a).obj V) : Int) := by
  let S := ShortComplex.mk (kernel.ι e) e (kernel.condition e)
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel e }
  intro a
  letI := hZero a
  letI := hLimits a
  letI := hColimits a
  letI := hM a
  letI := hV a
  have hm := hS.map_of_exact (F a)
  letI : Module.Finite K ((F a).obj (kernel e)) :=
    Module.Finite.of_injective ((F a).map (kernel.ι e)).hom hm.moduleCat_injective_f
  letI : Module.Finite K (S.map (F a)).X₁ := by dsimp [ShortComplex.map, S]; infer_instance
  letI : Module.Finite K (S.map (F a)).X₂ := by dsimp [ShortComplex.map, S]; infer_instance
  letI : Module.Finite K (S.map (F a)).X₃ := by dsimp [ShortComplex.map, S]; infer_instance
  have hd := shortExact_finrank_add (S.map (F a)) hm
  change Module.finrank K ((F a).obj M) =
    Module.finrank K ((F a).obj (kernel e)) + Module.finrank K ((F a).obj V) at hd
  omega

#print axioms shortExact_finrank_add
#print axioms vertex_shortExact_dimension_add
#print axioms mapped_cokernel_dimension_difference
#print axioms mapped_kernel_dimension_difference
end QuiverProofs.MACompletionExactVertexDimensions
