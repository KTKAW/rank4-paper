import MA4RestartArrow20261003.CoevaluationMap
import MA4Arrow20261003.AbsentEvaluationBiproduct

/-! Actual monic coevaluation replacement Q = coker e, in the tuple (Y,Q).
Internal reverse Hom/Ext, rigidity, scalar End, nonzero and local End are
conclusions from old pair data and the explicit monic branch. -/
namespace QuiverProofs.MA4RestartArrow20261003.CoevaluationCokernel
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open QuiverProofs.MA4RestartArrow20261003.CoevaluationMap
open QuiverProofs.MA4Arrow20261003.AbsentEvaluationExt
open QuiverProofs.MA4Arrow20261003.AbsentEvaluationBiproduct
open QuiverProofs.MACompletionScalarEndomorphisms
universe w v u z
variable {K : Type w} [Field K] {C : Type u}
  [Category.{v} C] [Abelian C] [Linear K C] [HasExt.{z} C]
set_option maxHeartbeats 0

omit [HasExt C] in
/-- Hom(Q,Y)=0 is forced by independent coevaluation maps and scalar End Y. -/
theorem hom_coevaluation_cokernel_summand_zero (X Y : C) (n : ℕ)
    [HasBiproduct (fun _ : Fin n => Y)]
    (f : Module.Basis (Fin n) K (X ⟶ Y))
    (hEndY : ∀ g : Y ⟶ Y, ∃ c : K, g = c • 𝟙 Y) :
    ∀ g : cokernel (biproduct.lift (f := fun _ : Fin n => Y) (fun j => f j)) ⟶ Y,
      g = 0 := by
  let e := biproduct.lift (f := fun _ : Fin n => Y) (fun j => f j)
  intro g
  apply (cancel_epi (cokernel.π e)).mp
  simpa only [comp_zero] using coevaluation_comp_summand_eq_zero X Y (fun j => f j)
    hEndY f.linearIndependent (cokernel.π e ≫ g)
    (by rw [← Category.assoc, cokernel.condition, zero_comp])

/-- Fullness kills the connecting Hom obstruction; old Y-rigidity kills
the remaining Ext term. Thus Ext1(Q,Y)=0 for the actual monic coevaluation. -/
theorem extOne_coevaluation_cokernel_summand_zero (X Y : C) (n : ℕ)
    [HasBiproduct (fun _ : Fin n => Y)]
    (f : Module.Basis (Fin n) K (X ⟶ Y))
    [Mono (biproduct.lift (f := fun _ : Fin n => Y) (fun j => f j))]
    (hRigidY : ∀ x : Ext Y Y 1, x = 0) :
    ∀ x : Ext (cokernel (biproduct.lift (f := fun _ : Fin n => Y) (fun j => f j))) Y 1,
      x = 0 := by
  let e := biproduct.lift (f := fun _ : Fin n => Y) (fun j => f j)
  let S := ShortComplex.mk e (cokernel.π e) (cokernel.condition e)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel e }
  have hMY : ∀ x : Ext (⨁ fun _ : Fin n => Y) Y 1, x = 0 :=
    extOne_biproduct_first_vanishes Y (fun _ : Fin n => Y) (fun _ => hRigidY)
  intro x
  obtain ⟨y, hy⟩ := Ext.contravariant_sequence_exact₃ hS Y x
    (hMY _) (show 1 + 0 = 1 from rfl)
  let g : X ⟶ Y := Ext.homEquiv₀ y
  obtain ⟨a, ha⟩ := hom_basis_coevaluation_factor X Y f g
  rw [← hy, ← Ext.mk₀_homEquiv₀_apply y]
  change hS.extClass.comp (Ext.mk₀ g) (show 1 + 0 = 1 from rfl) = 0
  rw [← ha, ← Ext.mk₀_comp_mk₀]
  exact hS.extClass_comp_assoc (Ext.mk₀ a)

/-- The replacement's rigidity follows from its newly proved Ext(Q,Y)=0
and hereditary covariant exactness, not from any new-root norm identity. -/
theorem coevaluation_cokernel_rigid (X Y : C) (n : ℕ)
    [HasBiproduct (fun _ : Fin n => Y)]
    (f : Module.Basis (Fin n) K (X ⟶ Y))
    [Mono (biproduct.lift (f := fun _ : Fin n => Y) (fun j => f j))]
    [HasProjectiveDimensionLT
      (cokernel (biproduct.lift (f := fun _ : Fin n => Y) (fun j => f j))) 2]
    (hRigidY : ∀ x : Ext Y Y 1, x = 0) :
    ∀ x : Ext (cokernel (biproduct.lift (f := fun _ : Fin n => Y) (fun j => f j)))
      (cokernel (biproduct.lift (f := fun _ : Fin n => Y) (fun j => f j))) 1, x = 0 := by
  let e := biproduct.lift (f := fun _ : Fin n => Y) (fun j => f j)
  let Q := cokernel e
  let S := ShortComplex.mk e (cokernel.π e) (cokernel.condition e)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel e }
  have hQY : ∀ x : Ext Q Y 1, x = 0 :=
    extOne_coevaluation_cokernel_summand_zero X Y n f hRigidY
  have hQM : ∀ x : Ext Q (⨁ fun _ : Fin n => Y) 1, x = 0 :=
    extOne_biproduct_vanishes Q (fun _ : Fin n => Y) (fun _ => hQY)
  exact extOne_quotient_vanishes Q hS hQM

/-- End Q is scalar: lift through q using reverse Ext, then through the
monic e. Old scalar End X and target-End faithfulness determine both lifts. -/
theorem coevaluation_cokernel_scalar_end (X Y : C) (n : ℕ)
    [HasBiproduct (fun _ : Fin n => Y)]
    (f : Module.Basis (Fin n) K (X ⟶ Y))
    [Mono (biproduct.lift (f := fun _ : Fin n => Y) (fun j => f j))]
    (hReverseExt : ∀ x : Ext Y X 1, x = 0)
    (hEndX : ∀ g : X ⟶ X, ∃ c : K, g = c • 𝟙 X)
    (hEndY : ∀ g : Y ⟶ Y, ∃ c : K, g = c • 𝟙 Y) :
    ∀ d : cokernel (biproduct.lift (f := fun _ : Fin n => Y) (fun j => f j)) ⟶
      cokernel (biproduct.lift (f := fun _ : Fin n => Y) (fun j => f j)),
      ∃ c : K, d = c • 𝟙 _ := by
  let e := biproduct.lift (f := fun _ : Fin n => Y) (fun j => f j)
  let M := ⨁ fun _ : Fin n => Y
  let Q := cokernel e
  let q := cokernel.π e
  let S := ShortComplex.mk e q (cokernel.condition e)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel e }
  have hMX : ∀ x : Ext M X 1, x = 0 :=
    extOne_biproduct_first_vanishes X (fun _ : Fin n => Y) (fun _ => hReverseExt)
  intro d
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₃ M hS (Ext.mk₀ (q ≫ d))
    (show 0 + 1 = 1 from rfl) (hMX _)
  let a : M ⟶ M := Ext.homEquiv₀ y
  have ha : a ≫ q = q ≫ d := by
    apply (Ext.mk₀_bijective M Q).injective
    rw [← Ext.mk₀_comp_mk₀, Ext.mk₀_homEquiv₀_apply]
    exact hy
  have hkill : (e ≫ a) ≫ q = 0 := by
    rw [Category.assoc, ha, ← Category.assoc, cokernel.condition, zero_comp]
  obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₂ X hS (Ext.mk₀ (e ≫ a)) (by
    rw [Ext.mk₀_comp_mk₀, hkill, Ext.mk₀_zero])
  let b : X ⟶ X := Ext.homEquiv₀ z
  have hb : b ≫ e = e ≫ a := by
    apply (Ext.mk₀_bijective X M).injective
    rw [← Ext.mk₀_comp_mk₀, Ext.mk₀_homEquiv₀_apply]
    exact hz
  obtain ⟨c, hc⟩ := hEndX b
  have haScalar : a = c • 𝟙 M :=
    (end_precomp_coevaluation_injective X Y (fun j => f j) hEndY f.linearIndependent)
      (by change e ≫ a = e ≫ (c • 𝟙 M)
          rw [← hb, hc]
          simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp]
          change c • e = c • (e ≫ 𝟙 M)
          rw [Category.comp_id])
  refine ⟨c, ?_⟩
  apply (cancel_epi q).mp
  rw [← ha, haScalar]
  simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp]
  change c • q = c • (q ≫ 𝟙 Q)
  rw [Category.comp_id]

omit [HasExt C] in
/-- Non-epicity gives nonzero Q directly through the actual cokernel map. -/
theorem cokernel_id_ne_zero_of_not_epi {X M : C} (e : X ⟶ M) (hNotEpi : ¬ Epi e) :
    𝟙 (cokernel e) ≠ 0 := by
  intro hz
  apply hNotEpi
  apply epi_of_cokernel_π_eq_zero e
  calc
    cokernel.π e = cokernel.π e ≫ 𝟙 _ := (Category.comp_id _).symm
    _ = 0 := by rw [hz, comp_zero]

/-- The strict monic branch has local End from its proved scalar End and
nonzero actual cokernel. -/
theorem coevaluation_cokernel_local_end (X Y : C) (n : ℕ)
    [HasBiproduct (fun _ : Fin n => Y)]
    (f : Module.Basis (Fin n) K (X ⟶ Y))
    [Mono (biproduct.lift (f := fun _ : Fin n => Y) (fun j => f j))]
    (hNotEpi : ¬ Epi (biproduct.lift (f := fun _ : Fin n => Y) (fun j => f j)))
    (hReverseExt : ∀ x : Ext Y X 1, x = 0)
    (hEndX : ∀ g : X ⟶ X, ∃ c : K, g = c • 𝟙 X)
    (hEndY : ∀ g : Y ⟶ Y, ∃ c : K, g = c • 𝟙 Y) :
    IsLocalRing (End (cokernel (biproduct.lift (f := fun _ : Fin n => Y) (fun j => f j)))) :=
  local_end_of_scalar_end _ (cokernel_id_ne_zero_of_not_epi _ hNotEpi)
    (coevaluation_cokernel_scalar_end X Y n f hReverseExt hEndX hEndY)

#print axioms coevaluation_cokernel_rigid
#print axioms coevaluation_cokernel_scalar_end
#print axioms coevaluation_cokernel_local_end
end QuiverProofs.MA4RestartArrow20261003.CoevaluationCokernel
