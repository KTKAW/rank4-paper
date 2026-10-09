import MA4RestartArrow20261003.SignedAdjacentLeftHom
import MA4RestartEuler20261003.UniversalLeft

/-! Actual full adjacent left universal-extension construction with the
signed numerical shear. All next frame fields and dimensions are derived;
the coefficient is the actual old Ext-basis dimension. -/
namespace QuiverProofs.MA4RestartArrow20261003.SignedAdjacentLeftExt
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open QuiverProofs.MA4RestartArrow20261003.AdjacentExceptionalFrame
open QuiverProofs.MA4RestartArrow20261003.SignedAdjacentLeftHom
open QuiverProofs.MA4RestartVertexFiniteness
universe w v u z
variable {K : Type w} [Field K] {C : Type u}
  [Category.{v} C] [Abelian C] [Linear K C] [HasExt.{z} C] [EnoughProjectives C]
set_option maxHeartbeats 0

/-- Construct the entire actual adjacent exceptional frame on the forward
Hom-zero branch, using the full actual Ext basis even when n=0. -/
theorem signed_left_ext_adjacent
    (F : Fin 4 → C ⥤ ModuleCat.{v} K)
    (hZero : ∀ a, (F a).PreservesZeroMorphisms)
    (hLimits : ∀ a, PreservesFiniteLimits (F a))
    (hColimits : ∀ a, PreservesFiniteColimits (F a))
    (hJointEpi : ∀ {M V : C} (e : M ⟶ V), (∀ a, Epi ((F a).map e)) → Epi e)
    (M : Fin 4 → C) (hM : ExceptionalFrame F M)
    (D : Fin 4 → Fin 4 → Int) (s : Fin 4 → Int)
    (hD : SignedDimensions F M D s)
    (t : Fin 4) (ht : t < 3) (n : ℕ)
    [HasBiproduct (fun _ : Fin n => M (t+1))]
    (β : Module.Basis (Fin n) K (Ext (M t) (M (t+1)) 1))
    (hForward : ∀ g : M t ⟶ M (t+1), g = 0) :
    ∃ (Q : C) (i : (⨁ fun _ : Fin n => M (t+1)) ⟶ Q) (p : Q ⟶ M t)
      (wip : i ≫ p = 0) (hS : (ShortComplex.mk i p wip).ShortExact),
      (∀ j, hS.extClass.comp (Ext.mk₀ (biproduct.π (fun _ : Fin n => M (t+1)) j))
        (add_zero 1) = β j) ∧
      ExceptionalFrame F (leftObjects M t Q) ∧
      SignedDimensions F (leftObjects M t Q)
        (leftColumns D (-(s t * s (t+1) * (n : Int))) t) (leftSigns s t (s t)) ∧
      Module.Finite K (Ext (M t) (M (t+1)) 1) ∧
      Module.finrank K (Ext (M t) (M (t+1)) 1) = n ∧
      (∃ a, 0 < Module.finrank K ((F a).obj Q)) := by
  have ht1 : t < t+1 := by fin_cases t <;> simp_all
  obtain ⟨Q, i, p, wip, hS, hβ, hHom, hExt, hRigid, hEnd, hId, hFinite,
    hDim, hOutside, hInside⟩ :=
    MA4RestartEuler20261003.left_universal_extension_finite_frame K F hZero hLimits hColimits
      (M t) (M (t+1)) n β (hM.scalarEnd t) (hM.scalarEnd (t+1)) hForward
      (hM.reverseHom t (t+1) ht1) (hM.rigid t) (hM.rigid (t+1))
      (hM.reverseExt t (t+1) ht1) (hM.nonzeroId t)
      (hM.finiteVertices t) (hM.finiteVertices (t+1))
  have hFrame := frame_leftObjects F M hM t ht Q hRigid hEnd hId hFinite
    ⟨hHom, hExt⟩ (fun T hX hY => hOutside T hY hX) (fun T hX hY => hInside T hY hX)
  have hQ : ∀ a, (Module.finrank K ((F a).obj Q) : Int) =
      s t * (D a t - (-(s t * s (t+1) * (n : Int))) * D a (t+1)) := by
    intro a
    rw [hDim a, (hD (t+1)).2 a, (hD t).2 a]
    rcases (hD t).1 with h | h <;> rw [h] <;> ring
  have hAt : leftObjects M t Q t = M (t+1) := by simp [leftObjects]
  have hNext : leftObjects M t Q (t+1) = Q := by simp [leftObjects, ne_of_gt ht1]
  have hSigned : SignedDimensions F (leftObjects M t Q)
      (leftColumns D (-(s t * s (t+1) * (n : Int))) t) (leftSigns s t (s t)) := by
    intro j
    by_cases hj : j = t
    · subst j
      constructor
      · simpa [leftSigns] using (hD (t+1)).1
      · intro a
        rw [hAt]
        simpa [leftSigns, leftColumns] using (hD (t+1)).2 a
    · by_cases hj1 : j = t+1
      · subst j
        constructor
        · simpa [leftSigns, ne_of_gt ht1] using (hD t).1
        · intro a
          rw [hNext]
          simpa [leftSigns, leftColumns, ne_of_gt ht1] using hQ a
      · have he : leftObjects M t Q j = M j := by simp [leftObjects, hj, hj1]
        constructor
        · simpa [leftSigns, hj, hj1] using (hD j).1
        · intro a
          rw [he]
          simpa [leftSigns, leftColumns, hj, hj1] using (hD j).2 a
  have hRank : Module.finrank K (Ext (M t) (M (t+1)) 1) = n := by
    simpa using Module.finrank_eq_card_basis β
  exact ⟨Q, i, p, wip, hS, hβ, hFrame, hSigned, Module.Finite.of_basis β, hRank,
    positive_vertex_dimension_of_nonzero F hJointEpi Q hFinite hId⟩

#print axioms signed_left_ext_adjacent
end QuiverProofs.MA4RestartArrow20261003.SignedAdjacentLeftExt
