import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! Actual finite-copy vertex data from the original finite summand and
vertex limit/zero preservation. No copy finiteness or copy-rank identity is
supplied, and every finite n, including zero, is covered. -/
namespace QuiverProofs.MA4RestartArrow20261003.VertexCopies
open CategoryTheory CategoryTheory.Limits
universe w v u
variable {K : Type w} [Field K] {C : Type u} [Category.{v} C] [Preadditive C]
set_option maxHeartbeats 0

/-- Map the actual chosen finite biproduct to the explicit product of the
old vertex space. This constructs both its finiteness and its dimension. -/
theorem mapped_copies_finite_and_finrank
    (F : C ⥤ ModuleCat.{v} K) [F.PreservesZeroMorphisms]
    [PreservesFiniteLimits F] (Y : C) (n : ℕ)
    [HasBiproduct (fun _ : Fin n => Y)]
    [Module.Finite K (F.obj Y)] :
    Module.Finite K (F.obj (⨁ fun _ : Fin n => Y)) ∧
      Module.finrank K (F.obj (⨁ fun _ : Fin n => Y)) =
        n * Module.finrank K (F.obj Y) := by
  letI : PreservesBiproduct (fun _ : Fin n => Y) F :=
    preservesBiproduct_of_preservesProduct F
  let I := F.mapBiproduct (fun _ : Fin n => Y) ≪≫
    ModuleCat.biproductIsoPi (fun _ : Fin n => F.obj Y)
  constructor
  · exact Module.Finite.of_injective I.toLinearEquiv.toLinearMap I.toLinearEquiv.injective
  · calc
      Module.finrank K (F.obj (⨁ fun _ : Fin n => Y)) =
          Module.finrank K (Fin n → F.obj Y) := I.toLinearEquiv.finrank_eq
      _ = n * Module.finrank K (F.obj Y) := by simp [Module.finrank_pi_fintype]

/-- All four actual vertex copy spaces are finite from the old Y spaces. -/
theorem vertex_copies_finite
    (F : Fin 4 → C ⥤ ModuleCat.{v} K)
    (hZero : ∀ a, (F a).PreservesZeroMorphisms)
    (hLimits : ∀ a, PreservesFiniteLimits (F a))
    (Y : C) (n : ℕ) [HasBiproduct (fun _ : Fin n => Y)]
    (hY : ∀ a, Module.Finite K ((F a).obj Y)) :
    ∀ a, Module.Finite K ((F a).obj (⨁ fun _ : Fin n => Y)) := by
  intro a
  letI := hZero a
  letI := hLimits a
  letI := hY a
  exact (mapped_copies_finite_and_finrank (F a) Y n).1

/-- All four dimension identities are derived from the original Y vector. -/
theorem vertex_copies_dimension
    (F : Fin 4 → C ⥤ ModuleCat.{v} K)
    (hZero : ∀ a, (F a).PreservesZeroMorphisms)
    (hLimits : ∀ a, PreservesFiniteLimits (F a))
    (Y : C) (n : ℕ) [HasBiproduct (fun _ : Fin n => Y)]
    (hY : ∀ a, Module.Finite K ((F a).obj Y))
    (dY : Fin 4 → Int)
    (hDimY : ∀ a, (Module.finrank K ((F a).obj Y) : Int) = dY a) :
    ∀ a, (Module.finrank K ((F a).obj (⨁ fun _ : Fin n => Y)) : Int) =
      (n : Int) * dY a := by
  intro a
  letI := hZero a
  letI := hLimits a
  letI := hY a
  rw [← hDimY a]
  exact_mod_cast (mapped_copies_finite_and_finrank (F a) Y n).2

#print axioms mapped_copies_finite_and_finrank
#print axioms vertex_copies_dimension
end QuiverProofs.MA4RestartArrow20261003.VertexCopies
