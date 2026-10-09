import MA4EulerMonoEpi01a0fee4
import QuiverProofs.MACompletionCategoricalTriangles
import MA4Coordinator20261003.ScalarEndomorphisms

/-! Pair purity from rigidity and actual hereditary map exactness.
Exceptional representation objects, their self-rigidity, endomorphism data
and reverse Ext orthogonality remain explicit; root realization is not supplied. -/
namespace QuiverProofs.MACompletionPairPurity
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open MA4EulerMonoEpi01a0fee4 MACompletionCategoricalTriangles
open QuiverProofs.MA4Arrow20261003.AbsentEvaluationExt MACompletionScalarEndomorphisms
universe w v u z
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
set_option maxHeartbeats 0

/-- A nonzero map between rigid objects forces forward Ext1 vanishing when
reverse Ext1 is zero and both endomorphism rings are local. -/
theorem extOne_vanishes_of_nonzero_hom_rigid (X Y : C)
    [IsLocalRing (End X)] [IsLocalRing (End Y)]
    (hHered : ∀ T : C, HasProjectiveDimensionLT T 2)
    (hReverse : ∀ e : Ext Y X 1, e = 0)
    (hRigidX : ∀ e : Ext X X 1, e = 0)
    (hRigidY : ∀ e : Ext Y Y 1, e = 0)
    (hHom : ∃ f : X ⟶ Y, f ≠ 0) :
    ∀ e : Ext X Y 1, e = 0 := by
  obtain ⟨f, hf⟩ := hHom
  rcases nonzero_map_mono_or_epi hHered hReverse f hf with hm | he
  · letI := hm
    letI := hHered (cokernel f)
    exact extOne_subobject_vanishes Y
      (S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f))
      { exact := ShortComplex.exact_cokernel f } hRigidY
  · letI := he
    letI := hHered X
    exact extOne_quotient_vanishes X
      (S := ShortComplex.mk (kernel.ι f) f (kernel.condition f))
      { exact := ShortComplex.exact_kernel f } hRigidX

/-- Purity is a conclusion, rather than a supplied Hom/Ext alternative. -/
theorem hom_or_extOne_vanishes_of_rigid (X Y : C)
    [IsLocalRing (End X)] [IsLocalRing (End Y)]
    (hHered : ∀ T : C, HasProjectiveDimensionLT T 2)
    (hReverse : ∀ e : Ext Y X 1, e = 0)
    (hRigidX : ∀ e : Ext X X 1, e = 0)
    (hRigidY : ∀ e : Ext Y Y 1, e = 0) :
    (∀ f : X ⟶ Y, f = 0) ∨ (∀ e : Ext X Y 1, e = 0) := by
  classical
  by_cases hHom : ∃ f : X ⟶ Y, f ≠ 0
  · exact Or.inr (extOne_vanishes_of_nonzero_hom_rigid X Y
      hHered hReverse hRigidX hRigidY hHom)
  · left
    intro f
    by_contra hf
    exact hHom ⟨f, hf⟩

/-- Supplied dimension zero tests turn actual categorical purity into the
numerical dimension alternative used by the normalized Euler consumer. -/
theorem dimension_purity_of_rigid (X Y : C)
    [IsLocalRing (End X)] [IsLocalRing (End Y)]
    (hHered : ∀ T : C, HasProjectiveDimensionLT T 2)
    (hReverse : ∀ e : Ext Y X 1, e = 0)
    (hRigidX : ∀ e : Ext X X 1, e = 0)
    (hRigidY : ∀ e : Ext Y Y 1, e = 0)
    (dimHom dimExt : Nat)
    (hHomZero : dimHom = 0 ↔ ∀ f : X ⟶ Y, f = 0)
    (hExtZero : dimExt = 0 ↔ ∀ e : Ext X Y 1, e = 0) :
    dimHom = 0 ∨ dimExt = 0 := by
  rcases hom_or_extOne_vanishes_of_rigid X Y
    hHered hReverse hRigidX hRigidY with hHom | hExt
  · exact Or.inl (hHomZero.mpr hHom)
  · exact Or.inr (hExtZero.mpr hExt)

/-- Explicit one-dimensional endomorphism data supply the local rings in
pair purity. Self-rigidity and reverse Ext remain required representation facts. -/
theorem dimension_purity_of_end_finrank_one
    {K : Type z} [Field K] [Linear K C] (X Y : C)
    [Module.Finite K (X ⟶ X)] [Module.Finite K (Y ⟶ Y)]
    (hIdX : (𝟙 X : X ⟶ X) ≠ 0) (hIdY : (𝟙 Y : Y ⟶ Y) ≠ 0)
    (hEndX : Module.finrank K (X ⟶ X) = 1)
    (hEndY : Module.finrank K (Y ⟶ Y) = 1)
    (hHered : ∀ T : C, HasProjectiveDimensionLT T 2)
    (hReverse : ∀ e : Ext Y X 1, e = 0)
    (hRigidX : ∀ e : Ext X X 1, e = 0)
    (hRigidY : ∀ e : Ext Y Y 1, e = 0)
    (dimHom dimExt : Nat)
    (hHomZero : dimHom = 0 ↔ ∀ f : X ⟶ Y, f = 0)
    (hExtZero : dimExt = 0 ↔ ∀ e : Ext X Y 1, e = 0) :
    dimHom = 0 ∨ dimExt = 0 := by
  letI := local_end_of_scalar_end X hIdX (scalar_end_of_finrank_one X hIdX hEndX)
  letI := local_end_of_scalar_end Y hIdY (scalar_end_of_finrank_one Y hIdY hEndY)
  exact dimension_purity_of_rigid X Y hHered hReverse hRigidX hRigidY
    dimHom dimExt hHomZero hExtZero

#print axioms extOne_vanishes_of_nonzero_hom_rigid
#print axioms hom_or_extOne_vanishes_of_rigid
#print axioms dimension_purity_of_rigid
#print axioms dimension_purity_of_end_finrank_one
end QuiverProofs.MACompletionPairPurity
