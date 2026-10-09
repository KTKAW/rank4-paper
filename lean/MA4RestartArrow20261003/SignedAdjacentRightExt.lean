import MA4RestartArrow20261003.SignedAdjacentRightHom
import MA4RestartEuler20261003.UniversalClosure

/-! Actual full adjacent right universal-extension construction with the
signed numerical shear. All next frame fields and dimensions are derived;
the coefficient is the actual old Ext-basis dimension. -/
namespace QuiverProofs.MA4RestartArrow20261003.SignedAdjacentRightExt
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open QuiverProofs.MA4RestartArrow20261003.AdjacentExceptionalFrame
open QuiverProofs.MA4RestartArrow20261003.SignedAdjacentLeftHom
open QuiverProofs.MA4RestartArrow20261003.SignedAdjacentRightHom
open QuiverProofs.MA4RestartArrow20261003.AdjacentExceptionalRightFrame
open QuiverProofs.MA4RestartVertexFiniteness
universe w v u z
variable {K : Type w} [Field K] {C : Type u}
  [Category.{v} C] [Abelian C] [Linear K C] [HasExt.{z} C] [EnoughProjectives C]
set_option maxHeartbeats 0

/-- Construct the entire actual adjacent exceptional frame on the forward
Hom-zero branch, using the full actual Ext basis even when n=0. -/
theorem signed_right_ext_adjacent
    (F : Fin 4 → C ⥤ ModuleCat.{v} K)
    (hZero : ∀ a, (F a).PreservesZeroMorphisms)
    (hLimits : ∀ a, PreservesFiniteLimits (F a))
    (hColimits : ∀ a, PreservesFiniteColimits (F a))
    (hJointEpi : ∀ {M V : C} (e : M ⟶ V), (∀ a, Epi ((F a).map e)) → Epi e)
    (M : Fin 4 → C) (hM : ExceptionalFrame F M)
    (D : Fin 4 → Fin 4 → Int) (s : Fin 4 → Int)
    (hD : SignedDimensions F M D s)
    (t : Fin 4) (ht : t < 3) (n : ℕ)
    [HasBiproduct (fun _ : Fin n => M t)]
    (β : Module.Basis (Fin n) K (Ext (M t) (M (t+1)) 1))
    (hForward : ∀ g : M t ⟶ M (t+1), g = 0) :
    ∃ (Q : C) (i : M (t+1) ⟶ Q) (p : Q ⟶ (⨁ fun _ : Fin n => M t))
      (wip : i ≫ p = 0) (hS : (ShortComplex.mk i p wip).ShortExact),
      (∀ j, (Ext.mk₀ (biproduct.ι (fun _ : Fin n => M t) j)).comp hS.extClass
        (zero_add 1) = β j) ∧
      ExceptionalFrame F (rightObjects M t Q) ∧
      SignedDimensions F (rightObjects M t Q)
        (rightColumns D (-(s t * s (t+1) * (n : Int))) t) (rightSigns s t (s (t+1))) ∧
      Module.Finite K (Ext (M t) (M (t+1)) 1) ∧
      Module.finrank K (Ext (M t) (M (t+1)) 1) = n ∧
      (∃ a, 0 < Module.finrank K ((F a).obj Q)) := by
  have ht1 : t < t+1 := by fin_cases t <;> simp_all
  obtain ⟨Q, i, p, wip, hS, hβ, hHom, hExt, hRigid, hEnd, hId, hFinite,
    hDim, hOutside, hInside⟩ :=
    MA4RestartEuler20261003.universal_extension_finite_frame F hZero hLimits hColimits
      (M t) (M (t+1)) n β (hM.scalarEnd t) (hM.scalarEnd (t+1)) hForward
      (hM.reverseHom t (t+1) ht1) (hM.rigid t) (hM.rigid (t+1))
      (hM.reverseExt t (t+1) ht1) (hM.nonzeroId (t+1))
      (hM.finiteVertices t) (hM.finiteVertices (t+1))
  have hFrame := frame_rightObjects F M hM t ht Q hRigid hEnd hId hFinite
    ⟨hHom, hExt⟩ (fun T hX hY => hOutside T hY hX) (fun T hX hY => hInside T hY hX)
  have hQ : ∀ a, (Module.finrank K ((F a).obj Q) : Int) =
      s (t+1) * (D a (t+1) - (-(s t * s (t+1) * (n : Int))) * D a t) := by
    intro a
    rw [hDim a, (hD (t+1)).2 a, (hD t).2 a]
    rcases (hD (t+1)).1 with h | h <;> rw [h] <;> ring
  have hAt : rightObjects M t Q t = Q := by simp [rightObjects]
  have hNext : rightObjects M t Q (t+1) = M t := by simp [rightObjects, ne_of_gt ht1]
  have hSigned : SignedDimensions F (rightObjects M t Q)
      (rightColumns D (-(s t * s (t+1) * (n : Int))) t) (rightSigns s t (s (t+1))) := by
    intro j
    by_cases hj : j = t
    · subst j
      constructor
      · simpa [rightSigns] using (hD (t+1)).1
      · intro a
        rw [hAt]
        simpa [rightSigns, rightColumns] using hQ a
    · by_cases hj1 : j = t+1
      · subst j
        constructor
        · simpa [rightSigns, ne_of_gt ht1] using (hD t).1
        · intro a
          rw [hNext]
          simpa [rightSigns, rightColumns, ne_of_gt ht1] using (hD t).2 a
      · have he : rightObjects M t Q j = M j := by simp [rightObjects, hj, hj1]
        constructor
        · simpa [rightSigns, hj, hj1] using (hD j).1
        · intro a
          rw [he]
          simpa [rightSigns, rightColumns, hj, hj1] using (hD j).2 a
  have hRank : Module.finrank K (Ext (M t) (M (t+1)) 1) = n := by
    simpa using Module.finrank_eq_card_basis β
  exact ⟨Q, i, p, wip, hS, hβ, hFrame, hSigned, Module.Finite.of_basis β, hRank,
    positive_vertex_dimension_of_nonzero F hJointEpi Q hFinite hId⟩

#print axioms signed_right_ext_adjacent
end QuiverProofs.MA4RestartArrow20261003.SignedAdjacentRightExt
