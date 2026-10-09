import MA4Arrow20261003.AbsentEvaluationExt

/-! Finite-sum Ext vanishing and the resulting obstruction to an epimorphic
evaluation map. The family of objects, its actual biproduct, and the maps into
the target are explicit categorical data. No seed realization, Hom-basis
construction, purity, or mono-or-epi dichotomy is asserted. -/
namespace QuiverProofs.MA4Arrow20261003.AbsentEvaluationBiproduct
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open QuiverProofs.MA4Arrow20261003.AbsentEvaluationExt
universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- Vanishing in every summand implies vanishing in any actual finite
biproduct bicone, in every Ext degree. This step needs no hereditary bound. -/
theorem ext_bicone_vanishes {J : Type*} [Fintype J] (U : C)
    {R : J → C} {c : Bicone R} (hc : c.IsBilimit) (n : ℕ)
    (hR : ∀ a, ∀ e : Ext U (R a) n, e = 0) :
    ∀ e : Ext U c.pt n, e = 0 := by
  intro e
  let E := Ext.addEquivBiproduct U hc n
  apply E.injective
  ext a
  simpa only [map_zero, Pi.zero_apply] using hR a (E e a)

/-- The degree-one instance at the chosen finite biproduct. -/
theorem extOne_biproduct_vanishes {J : Type*} [Fintype J] (U : C)
    (R : J → C) [HasBiproduct R]
    (hR : ∀ a, ∀ e : Ext U (R a) 1, e = 0) :
    ∀ e : Ext U (⨁ R) 1, e = 0 :=
  ext_bicone_vanishes U (biproduct.isBilimit R) 1 hR

/-- No map from this biproduct to an Ext1-nonorthogonal target is epi, under
the explicit projective-dimension bound on U. -/
theorem no_epi_from_biproduct {J : Type*} [Fintype J]
    (U : C) [HasProjectiveDimensionLT U 2]
    (R : J → C) [HasBiproduct R] (V : C) (g : (⨁ R) ⟶ V)
    (hR : ∀ a, ∀ e : Ext U (R a) 1, e = 0)
    (hV : ∃ e : Ext U V 1, e ≠ 0) : ¬ Epi g :=
  no_epi_of_nonzero_extOne U (⨁ R) V g
    (extOne_biproduct_vanishes U R hR) hV

/-- The canonical map induced by a supplied finite family of evaluation
maps is not epi. No claim says that these maps form a Hom basis. -/
theorem no_epi_biproduct_evaluation {J : Type*} [Fintype J]
    (U : C) [HasProjectiveDimensionLT U 2]
    (R : J → C) [HasBiproduct R] (V : C) (f : ∀ a, R a ⟶ V)
    (hR : ∀ a, ∀ e : Ext U (R a) 1, e = 0)
    (hV : ∃ e : Ext U V 1, e ≠ 0) : ¬ Epi (biproduct.desc f) :=
  no_epi_from_biproduct U R V (biproduct.desc f) hR hV

/-- The requested R-to-the-n evaluation consumer, allowing every finite n
including zero, with the supplied maps and Ext assumptions explicit. -/
theorem no_epi_copies_evaluation (U : C) [HasProjectiveDimensionLT U 2]
    (R V : C) (n : ℕ) [HasBiproduct (fun _ : Fin n => R)]
    (f : Fin n → (R ⟶ V)) (hR : ∀ e : Ext U R 1, e = 0)
    (hV : ∃ e : Ext U V 1, e ≠ 0) :
    ¬ Epi (biproduct.desc (f := fun _ : Fin n => R) f) :=
  no_epi_biproduct_evaluation U (fun _ : Fin n => R) V f (fun _ => hR) hV

#print axioms ext_bicone_vanishes
#print axioms extOne_biproduct_vanishes
#print axioms no_epi_from_biproduct
#print axioms no_epi_biproduct_evaluation
#print axioms no_epi_copies_evaluation
end QuiverProofs.MA4Arrow20261003.AbsentEvaluationBiproduct
