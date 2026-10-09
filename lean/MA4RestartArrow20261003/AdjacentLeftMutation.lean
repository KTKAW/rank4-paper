import MA4RestartArrow20261003.SignedAdjacentLeftExt

/-! One actual left adjacent mutation for the private joint realization
invariant. Old rigidity derives the Hom/Ext choice; old finite dimensions
construct both bases. No branch, basis, or next frame is supplied. -/
namespace QuiverProofs.MA4RestartArrow20261003.AdjacentLeftMutation
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open QuiverProofs.MA4RestartArrow20261003.AdjacentExceptionalFrame
open QuiverProofs.MA4RestartArrow20261003.SignedAdjacentLeftHom
open QuiverProofs.MA4RestartArrow20261003.SignedAdjacentLeftExt
open QuiverProofs.MACompletionPairPurity
open QuiverProofs.MACompletionScalarEndomorphisms
universe w v u z
variable {K : Type w} [Field K] {C : Type u}
  [Category.{v} C] [Abelian C] [Linear K C] [HasExt.{z} C]
  [EnoughProjectives C] [HasFiniteBiproducts C]
set_option maxHeartbeats 0

/-- Construct the full actual ordered exceptional frame and its exact
signed shear, with coefficient equal to the actual old Hom-minus-Ext
Euler dimension. Both finite bases and the branch are chosen internally. -/
theorem adjacent_left_mutation
    (F : Fin 4 → C ⥤ ModuleCat.{v} K)
    (hZero : ∀ a, (F a).PreservesZeroMorphisms)
    (hLimits : ∀ a, PreservesFiniteLimits (F a))
    (hColimits : ∀ a, PreservesFiniteColimits (F a))
    (hJointEpi : ∀ {M V : C} (e : M ⟶ V), (∀ a, Epi ((F a).map e)) → Epi e)
    (M : Fin 4 → C) (hM : ExceptionalFrame F M)
    (D : Fin 4 → Fin 4 → Int) (s : Fin 4 → Int)
    (hD : SignedDimensions F M D s)
    (hHered : ∀ T : C, HasProjectiveDimensionLT T 2)
    (t : Fin 4) (ht : t < 3)
    [Module.Finite K (M t ⟶ M (t+1))]
    [Module.Finite K (Ext (M t) (M (t+1)) 1)] :
    let χ : Int := (Module.finrank K (M t ⟶ M (t+1)) : Int) -
      (Module.finrank K (Ext (M t) (M (t+1)) 1) : Int)
    ∃ (Q : C) (sq : Int),
      ExceptionalFrame F (leftObjects M t Q) ∧
      SignedDimensions F (leftObjects M t Q)
        (leftColumns D (s t * s (t+1) * χ) t) (leftSigns s t sq) ∧
      (∃ a, 0 < Module.finrank K ((F a).obj Q)) := by
  classical
  let χ : Int := (Module.finrank K (M t ⟶ M (t+1)) : Int) -
    (Module.finrank K (Ext (M t) (M (t+1)) 1) : Int)
  have ht1 : t < t+1 := by fin_cases t <;> simp_all
  letI := local_end_of_scalar_end (M t) (hM.nonzeroId t) (hM.scalarEnd t)
  letI := local_end_of_scalar_end (M (t+1)) (hM.nonzeroId (t+1)) (hM.scalarEnd (t+1))
  rcases hom_or_extOne_vanishes_of_rigid (M t) (M (t+1)) hHered
    (hM.reverseExt t (t+1) ht1) (hM.rigid t) (hM.rigid (t+1)) with hHom | hExt
  · letI : Subsingleton (M t ⟶ M (t+1)) := ⟨fun f g => by rw [hHom f, hHom g]⟩
    have hH0 : Module.finrank K (M t ⟶ M (t+1)) = 0 := Module.finrank_zero_of_subsingleton
    obtain ⟨Q, i, p, wip, hS, hBasis, hFrame, hSigned, hFinite, hRank, hPos⟩ :=
      signed_left_ext_adjacent F hZero hLimits hColimits hJointEpi M hM D s hD t ht
        (Module.finrank K (Ext (M t) (M (t+1)) 1))
        (Module.finBasis K (Ext (M t) (M (t+1)) 1)) hHom
    have hCoeff : s t * s (t+1) * χ =
        -(s t * s (t+1) * (Module.finrank K (Ext (M t) (M (t+1)) 1) : Int)) := by
      dsimp [χ]
      rw [hH0]
      simp
    refine ⟨Q, s t, hFrame, ?_, hPos⟩
    change SignedDimensions F (leftObjects M t Q)
      (leftColumns D (s t * s (t+1) * χ) t) (leftSigns s t (s t))
    rw [hCoeff]
    exact hSigned
  · letI : Subsingleton (Ext (M t) (M (t+1)) 1) := ⟨fun f g => by rw [hExt f, hExt g]⟩
    have hE0 : Module.finrank K (Ext (M t) (M (t+1)) 1) = 0 :=
      Module.finrank_zero_of_subsingleton
    obtain ⟨Q, sq, hBranch, hFrame, hSigned, hRank, hPos⟩ :=
      signed_left_hom_adjacent F hZero hLimits hColimits hJointEpi M hM D s hD hHered t ht
        (Module.finrank K (M t ⟶ M (t+1)))
        (Module.finBasis K (M t ⟶ M (t+1))) hExt
    have hCoeff : s t * s (t+1) * χ =
        s t * s (t+1) * (Module.finrank K (M t ⟶ M (t+1)) : Int) := by
      dsimp [χ]
      rw [hE0]
      simp
    refine ⟨Q, sq, hFrame, ?_, hPos⟩
    change SignedDimensions F (leftObjects M t Q)
      (leftColumns D (s t * s (t+1) * χ) t) (leftSigns s t sq)
    rw [hCoeff]
    exact hSigned

#print axioms adjacent_left_mutation
end QuiverProofs.MA4RestartArrow20261003.AdjacentLeftMutation
