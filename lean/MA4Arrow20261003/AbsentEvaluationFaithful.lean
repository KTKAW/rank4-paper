import MA4Arrow20261003.AbsentEvaluationBiproduct
import MA4EulerMonoEpi01a0fee4

/-! A source-endomorphism replacement for the evaluation mono/epi argument.
The source of evaluation is a finite sum and need not have local End. Actual
postcomposition injectivity and target zero-or-iso endomorphisms remain
explicit data. No Hom basis, division End realization, or root-frame
realization is constructed here. -/
namespace QuiverProofs.MA4Arrow20261003.AbsentEvaluationFaithful
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open QuiverProofs.MA4Arrow20261003.AbsentEvaluationBiproduct
universe w v u

section MapArgument
variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- For an epi/mono factorization, the actual image identity gives a map
dichotomy using faithful source postcomposition and target division data. -/
theorem mono_or_epi_of_factorization_identity {M I V : C}
    (π : M ⟶ I) [Epi π] (ι : I ⟶ V) [Mono ι]
    (a : I ⟶ M) (b : V ⟶ I)
    (hidentity : a ≫ π + ι ≫ b = 𝟙 I)
    (hfaith : Function.Injective (fun A : M ⟶ M => A ≫ (π ≫ ι)))
    (hdivision : ∀ d : V ⟶ V, d = 0 ∨ IsIso d) :
    Mono (π ≫ ι) ∨ Epi (π ≫ ι) := by
  rcases hdivision (b ≫ ι) with hz | hi
  · have hb : b = 0 := (cancel_mono ι).mp (by simpa using hz)
    have ha : a ≫ π = 𝟙 I := by simpa only [hb, comp_zero, add_zero] using hidentity
    have hright : π ≫ a = 𝟙 M := hfaith (by
      calc
        (π ≫ a) ≫ (π ≫ ι) = π ≫ (a ≫ π) ≫ ι := by simp only [Category.assoc]
        _ = (𝟙 M) ≫ (π ≫ ι) := by rw [ha]; simp)
    letI : IsSplitMono π := IsSplitMono.mk' { retraction := a, id := hright }
    left
    infer_instance
  · letI := hi
    letI : Epi ι := epi_of_epi b ι
    right
    infer_instance
end MapArgument

section ActualImage
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The same argument at the actual abelian image, with identity witnesses
explicit and no Ext assumptions needed for this map step. -/
theorem mono_or_epi_of_image_identity {M V : C} (f : M ⟶ V)
    (hidentity : ∃ (a : Abelian.image f ⟶ M) (b : V ⟶ Abelian.image f),
      a ≫ Abelian.factorThruImage f + Abelian.image.ι f ≫ b = 𝟙 _)
    (hfaith : Function.Injective (fun A : M ⟶ M => A ≫ f))
    (hdivision : ∀ d : V ⟶ V, d = 0 ∨ IsIso d) : Mono f ∨ Epi f := by
  obtain ⟨a, b, hab⟩ := hidentity
  have hfac := Abelian.image.fac f
  have hfaith' : Function.Injective
      (fun A : M ⟶ M => A ≫ (Abelian.factorThruImage f ≫ Abelian.image.ι f)) := by
    simpa only [hfac] using hfaith
  simpa only [hfac] using mono_or_epi_of_factorization_identity
    (Abelian.factorThruImage f) (Abelian.image.ι f) a b hab hfaith' hdivision

variable [HasExt.{w} C]

/-- Euler's actual Ext-exactness identity supplies the identity premise.
Reverse Ext vanishing and hereditary data remain explicit hypotheses. -/
theorem mono_or_epi_of_reverse_extOne_zero {M V : C} (f : M ⟶ V)
    (hHered : ∀ T : C, HasProjectiveDimensionLT T 2)
    (hReverse : ∀ e : Ext V M 1, e = 0)
    (hfaith : Function.Injective (fun A : M ⟶ M => A ≫ f))
    (hdivision : ∀ d : V ⟶ V, d = 0 ∨ IsIso d) : Mono f ∨ Epi f :=
  mono_or_epi_of_image_identity f
    (MA4EulerMonoEpi01a0fee4.image_identity_of_reverse_extOne_zero f hHered hReverse)
    hfaith hdivision

/-- The finite-family evaluation is mono: reverse Ext vanishing supplies
the image identity; forward Ext data exclude the epi branch. -/
theorem mono_biproduct_evaluation {J : Type*} [Fintype J]
    (U : C) (R : J → C) [HasBiproduct R] (V : C) (f : ∀ j, R j ⟶ V)
    (hHered : ∀ T : C, HasProjectiveDimensionLT T 2)
    (hReverse : ∀ j, ∀ e : Ext V (R j) 1, e = 0)
    (hForward : ∀ j, ∀ e : Ext U (R j) 1, e = 0)
    (hV : ∃ e : Ext U V 1, e ≠ 0)
    (hfaith : Function.Injective (fun A : (⨁ R) ⟶ (⨁ R) => A ≫ biproduct.desc f))
    (hdivision : ∀ d : V ⟶ V, d = 0 ∨ IsIso d) : Mono (biproduct.desc f) := by
  letI := hHered U
  rcases mono_or_epi_of_reverse_extOne_zero (biproduct.desc f) hHered
    (extOne_biproduct_vanishes V R hReverse) hfaith hdivision with hm | he
  · exact hm
  · exact (no_epi_biproduct_evaluation U R V f hForward hV he).elim

/-- Every finite number of copies, including zero, specializes the actual
evaluation mono theorem. No Hom-basis or multiplicity bridge is hidden. -/
theorem mono_copies_evaluation (U R V : C) (n : ℕ)
    [HasBiproduct (fun _ : Fin n => R)] (f : Fin n → (R ⟶ V))
    (hHered : ∀ T : C, HasProjectiveDimensionLT T 2)
    (hReverse : ∀ e : Ext V R 1, e = 0)
    (hForward : ∀ e : Ext U R 1, e = 0)
    (hV : ∃ e : Ext U V 1, e ≠ 0)
    (hfaith : Function.Injective (fun A :
      (⨁ fun _ : Fin n => R) ⟶ (⨁ fun _ : Fin n => R) =>
        A ≫ biproduct.desc (f := fun _ : Fin n => R) f))
    (hdivision : ∀ d : V ⟶ V, d = 0 ∨ IsIso d) :
    Mono (biproduct.desc (f := fun _ : Fin n => R) f) :=
  mono_biproduct_evaluation U (fun _ : Fin n => R) V f hHered
    (fun _ => hReverse) (fun _ => hForward) hV hfaith hdivision
end ActualImage

#print axioms mono_or_epi_of_factorization_identity
#print axioms mono_or_epi_of_image_identity
#print axioms mono_or_epi_of_reverse_extOne_zero
#print axioms mono_biproduct_evaluation
#print axioms mono_copies_evaluation
end QuiverProofs.MA4Arrow20261003.AbsentEvaluationFaithful
