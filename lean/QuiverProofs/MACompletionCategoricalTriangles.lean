import MA4Arrow20261003.AbsentEvaluationExt

/-! Local categorical triangle obstructions, on explicit categorical data.
No exceptional-module realization, pair purity, map dichotomy, or connection
to the actual numerical SeedInv is constructed by these lemmas. -/
namespace QuiverProofs.MACompletionCategoricalTriangles
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open MA4Arrow20261003.AbsentEvaluationExt
universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
set_option maxHeartbeats 0

/-- Hereditary contravariant exactness: vanishing on the middle object
passes to a subobject when the quotient has projective dimension at most one. -/
theorem extOne_subobject_vanishes (V : C) {S : ShortComplex C}
    [HasProjectiveDimensionLT S.X₃ 2] (hS : S.ShortExact)
    (h₂ : ∀ e : Ext S.X₂ V 1, e = 0) :
    ∀ e : Ext S.X₁ V 1, e = 0 := by
  intro e
  obtain ⟨x, hx⟩ := Ext.contravariant_sequence_exact₁ hS V e
    (show 1 + 1 = 2 from rfl)
    (Ext.eq_zero_of_hasProjectiveDimensionLT _ 2 (by rfl))
  rw [← hx, h₂ x, Ext.comp_zero]

theorem no_shortExact_of_nonzero_subobject_extOne (V : C) {S : ShortComplex C}
    [HasProjectiveDimensionLT S.X₃ 2]
    (h₂ : ∀ e : Ext S.X₂ V 1, e = 0)
    (h₁ : ∃ e : Ext S.X₁ V 1, e ≠ 0) : ¬ S.ShortExact := by
  intro hS
  obtain ⟨e, he⟩ := h₁
  exact he (extOne_subobject_vanishes V hS h₂ e)

theorem no_mono_of_nonzero_extOne (V U M : C) (f : U ⟶ M)
    [HasProjectiveDimensionLT (cokernel f) 2]
    (hM : ∀ e : Ext M V 1, e = 0)
    (hU : ∃ e : Ext U V 1, e ≠ 0) : ¬ Mono f := by
  intro hf
  letI := hf
  exact no_shortExact_of_nonzero_subobject_extOne V
    (S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)) hM hU
    { exact := ShortComplex.exact_cokernel f }

/-- The Hom/Hom/Ext triangle cannot occur with the stated purity data and
the ordinary nonzero-map mono/epi dichotomy. The map property is an input. -/
theorem no_hom_hom_ext_triangle (X Y Z : C)
    [HasProjectiveDimensionLT X 2]
    (hXY : ∃ f : X ⟶ Y, f ≠ 0)
    (hYZ : ∃ g : Y ⟶ Z, g ≠ 0)
    (hXZ : ∀ f : X ⟶ Z, f = 0)
    (hExtXY : ∀ e : Ext X Y 1, e = 0)
    (hExtXZ : ∃ e : Ext X Z 1, e ≠ 0)
    (hMaps : ∀ g : Y ⟶ Z, g ≠ 0 → Mono g ∨ Epi g) : False := by
  obtain ⟨f, hf⟩ := hXY
  obtain ⟨g, hg⟩ := hYZ
  rcases hMaps g hg with hm | he
  · letI := hm
    apply hf
    apply (cancel_mono g).mp
    simpa only [zero_comp] using hXZ (f ≫ g)
  · exact no_epi_of_nonzero_extOne X Y Z g hExtXY hExtXZ he

/-- The Ext/Ext/Hom triangle is excluded by both exactness directions.
The global dimension and nonzero-map conditions remain explicit premises. -/
theorem no_ext_ext_hom_triangle (X Y Z : C)
    (hHered : ∀ T : C, HasProjectiveDimensionLT T 2)
    (hExtXY : ∃ e : Ext X Y 1, e ≠ 0)
    (hExtYZ : ∃ e : Ext Y Z 1, e ≠ 0)
    (hXZ : ∃ f : X ⟶ Z, f ≠ 0)
    (hExtYX : ∀ e : Ext Y X 1, e = 0)
    (hExtZY : ∀ e : Ext Z Y 1, e = 0)
    (hMaps : ∀ f : X ⟶ Z, f ≠ 0 → Mono f ∨ Epi f) : False := by
  obtain ⟨f, hf⟩ := hXZ
  rcases hMaps f hf with hm | he
  · letI := hHered (cokernel f)
    exact no_mono_of_nonzero_extOne Y X Z f hExtZY hExtXY hm
  · letI := hHered Y
    exact no_epi_of_nonzero_extOne Y X Z f hExtYX hExtYZ he

#print axioms no_hom_hom_ext_triangle
#print axioms no_ext_ext_hom_triangle
end QuiverProofs.MACompletionCategoricalTriangles
