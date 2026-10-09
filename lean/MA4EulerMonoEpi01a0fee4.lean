import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.Tactic

/-! Abstract map dichotomy from actual hereditary Ext and local endomorphism rings.
No root realization, pair purity, or numerical Euler interpretation is assumed or produced. -/
namespace MA4EulerMonoEpi01a0fee4
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits CategoryTheory.Preadditive
universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
set_option maxHeartbeats 0

/- Two-object form of the Jacobson identity, proved with explicit inverses. -/
omit [HasExt C] in
theorem isIso_id_sub_comp {Y I : C} (e : Y ⟶ I) (h : I ⟶ Y)
    [IsIso (𝟙 Y - e ≫ h)] : IsIso (𝟙 I - h ≫ e) := by
  let L := 𝟙 Y - e ≫ h
  let b := 𝟙 I + h ≫ inv L ≫ e
  have hleft : inv L - e ≫ h ≫ inv L = 𝟙 Y := by
    simpa only [L, sub_comp, Category.id_comp, Category.assoc] using
      (IsIso.hom_inv_id L)
  have hright : inv L - inv L ≫ e ≫ h = 𝟙 Y := by
    simpa only [L, comp_sub, Category.comp_id, Category.assoc] using
      (IsIso.inv_hom_id L)
  have hl := congrArg (fun t : Y ⟶ Y => h ≫ t ≫ e) hleft
  have hr := congrArg (fun t : Y ⟶ Y => h ≫ t ≫ e) hright
  simp only [comp_sub, sub_comp, Category.assoc, Category.id_comp] at hl hr
  refine ⟨⟨b, ?_, ?_⟩⟩
  · change (𝟙 I - h ≫ e) ≫ (𝟙 I + h ≫ inv L ≫ e) = 𝟙 I
    calc
      _ = 𝟙 I - h ≫ e + (h ≫ inv L ≫ e - h ≫ e ≫ h ≫ inv L ≫ e) := by
        simp only [comp_add, sub_comp, Category.id_comp,
          Category.comp_id, Category.assoc]
      _ = 𝟙 I := by rw [hl]; abel
  · change (𝟙 I + h ≫ inv L ≫ e) ≫ (𝟙 I - h ≫ e) = 𝟙 I
    calc
      _ = 𝟙 I - h ≫ e + (h ≫ inv L ≫ e - h ≫ inv L ≫ e ≫ h ≫ e) := by
        simp only [add_comp, comp_sub, Category.id_comp,
          Category.comp_id, Category.assoc]
        abel
      _ = 𝟙 I := by rw [hr]; abel

/- A nonzero split mono into an object with local endomorphism ring is epic.
The local-ring assumption is structural data, not a map-dichotomy wrapper. -/
omit [HasExt C] in
theorem epi_of_nonzero_retract {I X : C} [IsLocalRing (End X)]
    (m : I ⟶ X) (r : X ⟶ I) (hmr : m ≫ r = 𝟙 I) (hm : m ≠ 0) : Epi m := by
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one (a := End.of (r ≫ m))
    (b := 1 - End.of (r ≫ m)) (by abel) with hu | hu
  · letI : IsIso (r ≫ m) := (isUnit_iff_isIso _).mp hu
    exact epi_of_epi r m
  · letI : IsIso (𝟙 X - r ≫ m) := (isUnit_iff_isIso _).mp hu
    have hz : m ≫ (𝟙 X - r ≫ m) = 0 := by
      rw [comp_sub, Category.comp_id, ← Category.assoc, hmr, Category.id_comp, sub_self]
    have heq : m = 0 := (cancel_mono (𝟙 X - r ≫ m)).mp (by simpa using hz)
    exact (hm heq).elim

/-- Ext exactness directly produces an identity on the image factorization.
This avoids representing arbitrary Ext1 classes by new extension modules. -/
theorem image_identity_of_reverse_extOne_zero {Y X : C} (f : Y ⟶ X)
    (hHered : ∀ T : C, HasProjectiveDimensionLT T 2)
    (hExt : ∀ a : Ext X Y 1, a = 0) :
    ∃ (h : Abelian.image f ⟶ Y) (k : X ⟶ Abelian.image f),
      h ≫ Abelian.factorThruImage f + Abelian.image.ι f ≫ k = 𝟙 _ := by
  let I := Abelian.image f
  let e : Y ⟶ I := Abelian.factorThruImage f
  let m : I ⟶ X := Abelian.image.ι f
  let S₁ := ShortComplex.mk (kernel.ι e) e (kernel.condition e)
  let S₂ := ShortComplex.mk m (cokernel.π m) (cokernel.condition m)
  have hS₁ : S₁.ShortExact := { exact := ShortComplex.exact_kernel e }
  have hS₂ : S₂.ShortExact := { exact := ShortComplex.exact_cokernel m }
  letI := hHered S₂.X₃
  obtain ⟨γ, hγ⟩ := Ext.covariant_sequence_exact₃ S₂.X₃ hS₁ hS₂.extClass
    (show 1 + 1 = 2 from rfl)
    (Ext.eq_zero_of_hasProjectiveDimensionLT _ 2 (by rfl))
  obtain ⟨h₀, hh₀⟩ := Ext.contravariant_sequence_exact₃ hS₂ Y γ
    (hExt _) (show 1 + 0 = 1 from rfl)
  let h := Ext.homEquiv₀ h₀
  have hh : Ext.mk₀ h = h₀ := Ext.mk₀_homEquiv₀_apply h₀
  have hid : hS₂.extClass.comp (Ext.mk₀ (h ≫ e)) (add_zero 1) = hS₂.extClass := by
    rw [← Ext.mk₀_comp_mk₀, ← Ext.comp_assoc (a₁ := 1) (a₂ := 0) (a₃ := 0)]
    rw [hh, hh₀]
    exact hγ
    all_goals rfl
  have hsub : hS₂.extClass.comp (Ext.mk₀ (𝟙 I - h ≫ e)) (add_zero 1) = 0 := by
    have hmksub : Ext.mk₀ (𝟙 I - h ≫ e) =
        Ext.mk₀ (𝟙 I) - Ext.mk₀ (h ≫ e) :=
      (Ext.addEquiv₀ (X := I) (Y := I)).symm.map_sub (𝟙 I) (h ≫ e)
    rw [hmksub]
    have hi : hS₂.extClass.comp (Ext.mk₀ (𝟙 I)) (add_zero 1) = hS₂.extClass :=
      Ext.comp_mk₀_id hS₂.extClass
    simp only [sub_eq_add_neg, Ext.comp_add, Ext.comp_neg, hi, hid, add_neg_cancel]
  obtain ⟨k₀, hk₀⟩ := Ext.contravariant_sequence_exact₁ hS₂ I
    (Ext.mk₀ (𝟙 I - h ≫ e)) (show 1 + 0 = 1 from rfl) hsub
  let k := Ext.homEquiv₀ k₀
  have hk : Ext.mk₀ (m ≫ k) = Ext.mk₀ (𝟙 I - h ≫ e) := by
    rw [← Ext.mk₀_comp_mk₀, Ext.mk₀_homEquiv₀_apply]
    exact hk₀
  have hm : m ≫ k = 𝟙 I - h ≫ e := (Ext.mk₀_bijective I I).injective hk
  refine ⟨h, k, ?_⟩
  change h ≫ e + m ≫ k = 𝟙 I
  rw [hm]
  abel

/-- Ordinary nonzero-map mono/epi dichotomy on explicit hereditary data.
Local endomorphism rings of the two objects remain explicit hypotheses. -/
theorem nonzero_map_mono_or_epi {Y X : C} [IsLocalRing (End Y)] [IsLocalRing (End X)]
    (hHered : ∀ T : C, HasProjectiveDimensionLT T 2)
    (hExt : ∀ a : Ext X Y 1, a = 0) (f : Y ⟶ X) (hf : f ≠ 0) : Mono f ∨ Epi f := by
  obtain ⟨h, k, hk⟩ := image_identity_of_reverse_extOne_zero f hHered hExt
  let I := Abelian.image f
  let e : Y ⟶ I := Abelian.factorThruImage f
  let m : I ⟶ X := Abelian.image.ι f
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one (a := End.of (e ≫ h))
    (b := 1 - End.of (e ≫ h)) (by abel) with hu | hu
  · letI : IsIso (e ≫ h) := (isUnit_iff_isIso _).mp hu
    letI : Mono e := mono_of_mono e h
    left
    rw [← Abelian.image.fac f]
    infer_instance
  · letI : IsIso (𝟙 Y - e ≫ h) := (isUnit_iff_isIso _).mp hu
    have hm : m ≫ k = 𝟙 I - h ≫ e := by
      change h ≫ e + m ≫ k = 𝟙 I at hk
      rw [eq_sub_iff_add_eq]
      simpa only [add_comm] using hk
    letI : IsIso (m ≫ k) := by rw [hm]; exact isIso_id_sub_comp e h
    let r := k ≫ inv (m ≫ k)
    have hmr : m ≫ r = 𝟙 I := by
      change m ≫ (k ≫ inv (m ≫ k)) = 𝟙 I
      rw [← Category.assoc]
      exact IsIso.hom_inv_id (m ≫ k)
    have hm0 : m ≠ 0 := by
      intro hm0
      apply hf
      rw [← Abelian.image.fac f]
      change e ≫ m = 0
      rw [hm0, comp_zero]
    letI : Epi m := epi_of_nonzero_retract m r hmr hm0
    right
    rw [← Abelian.image.fac f]
    infer_instance

#print axioms nonzero_map_mono_or_epi
end MA4EulerMonoEpi01a0fee4
