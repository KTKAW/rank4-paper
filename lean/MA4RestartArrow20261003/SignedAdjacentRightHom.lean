import MA4RestartArrow20261003.AdjacentExceptionalRightFrame
import MA4RestartArrow20261003.SignedAdjacentLeftHom
import MA4RestartCoordinator20261003.RightHomMutation

/-! Actual whole right Hom frame and exact signed-column shear. The
independently accepted right evaluation primitive constructs Q. All copies,
finite vertices, all four dimensions, sign and outside laws are derived
here from OLD actual objects. No opposite-category Ext transfer is used. -/
namespace QuiverProofs.MA4RestartArrow20261003.SignedAdjacentRightHom
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open QuiverProofs.MA4RestartArrow20261003.AdjacentExceptionalFrame
open QuiverProofs.MA4RestartArrow20261003.AdjacentExceptionalRightFrame
open QuiverProofs.MA4RestartArrow20261003.SignedAdjacentLeftHom
open QuiverProofs.MA4RestartArrow20261003.VertexCopies
open QuiverProofs.MA4RestartRightHomMutation QuiverProofs.MA4RestartVertexFiniteness
open QuiverProofs.MACompletionExactVertexDimensions
open MA4EulerExternalOrthogonality01a0fee4
universe w v u z
variable {K : Type w} [Field K] {C : Type u}
  [Category.{v} C] [Abelian C] [Linear K C] [HasExt.{z} C]
set_option maxHeartbeats 0

def rightColumns (D : Fin 4 → Fin 4 → Int) (m : Int) (t : Fin 4) :
    Fin 4 → Fin 4 → Int := fun a j =>
  if j = t then D a (t+1) - m * D a t else if j = t+1 then D a t else D a j

def rightSigns (s : Fin 4 → Int) (t : Fin 4) (sq : Int) : Fin 4 → Int := fun j =>
  if j = t then sq else if j = t+1 then s t else s j

theorem signed_right_hom_adjacent
    (F : Fin 4 → C ⥤ ModuleCat.{v} K)
    (hZero : ∀ a, (F a).PreservesZeroMorphisms)
    (hLimits : ∀ a, PreservesFiniteLimits (F a))
    (hColimits : ∀ a, PreservesFiniteColimits (F a))
    (hJointEpi : ∀ {M V : C} (e : M ⟶ V), (∀ a, Epi ((F a).map e)) → Epi e)
    (M : Fin 4 → C) (hM : ExceptionalFrame F M)
    (D : Fin 4 → Fin 4 → Int) (s : Fin 4 → Int) (hD : SignedDimensions F M D s)
    (hHered : ∀ T : C, HasProjectiveDimensionLT T 2)
    (t : Fin 4) (ht : t < 3) (n : ℕ) [HasBiproduct (fun _ : Fin n => M t)]
    (f : Module.Basis (Fin n) K (M t ⟶ M (t+1)))
    (hForward : ∀ x : Ext (M t) (M (t+1)) 1, x = 0) :
    let e := biproduct.desc (f := fun _ : Fin n => M t) (fun j => f j)
    ∃ (Q : C) (sq : Int),
      ((Mono e ∧ ¬ Epi e ∧ Q = cokernel e) ∨
       (Epi e ∧ ¬ Mono e ∧ Q = kernel e)) ∧
      ExceptionalFrame F (rightObjects M t Q) ∧
      SignedDimensions F (rightObjects M t Q)
        (rightColumns D (s t * s (t+1) * (n : Int)) t) (rightSigns s t sq) ∧
      Module.finrank K (M t ⟶ M (t+1)) = n ∧
      (∃ a, 0 < Module.finrank K ((F a).obj Q)) := by
  let e := biproduct.desc (f := fun _ : Fin n => M t) (fun j => f j)
  have ht1 : t < t+1 := by fin_cases t <;> simp_all
  obtain ⟨Q, hBranch, hHQ, hEQ, hRigid, hEnd, hId⟩ :=
    right_hom_mutation_exists (M t) (M (t+1)) n f hHered
      (hM.reverseHom t (t+1) ht1) (hM.reverseExt t (t+1) ht1) hForward
      (hM.rigid t) (hM.rigid (t+1)) (hM.nonzeroId (t+1))
      (hM.scalarEnd t) (hM.scalarEnd (t+1))
  have hCopies := vertex_copies_finite F hZero hLimits (M t) n (hM.finiteVertices t)
  have hCopiesDim := vertex_copies_dimension F hZero hLimits (M t) n
    (hM.finiteVertices t) (fun a => s t * D a t) (hD t).2
  have hFinite : ∀ a, Module.Finite K ((F a).obj Q) := by
    rcases hBranch with ⟨hm, hn, hq⟩ | ⟨he, hn, hq⟩
    · letI : Mono e := hm
      rw [hq]
      exact cokernel_vertex_finite F hZero hLimits hColimits _ _ e (hM.finiteVertices (t+1))
    · letI : Epi e := he
      rw [hq]
      exact kernel_vertex_finite F hZero hLimits hColimits _ _ e hCopies
  have hOutside : ∀ T : C,
      ((∀ g : M t ⟶ T, g = 0) ∧ (∀ x : Ext (M t) T 1, x = 0)) →
      ((∀ g : M (t+1) ⟶ T, g = 0) ∧ (∀ x : Ext (M (t+1)) T 1, x = 0)) →
      ((∀ g : Q ⟶ T, g = 0) ∧ (∀ x : Ext Q T 1, x = 0)) := by
    intro T hX hY
    rcases hBranch with ⟨hm, hn, hq⟩ | ⟨he, hn, hq⟩
    · letI : Mono e := hm
      rw [hq]
      exact copies_cokernel_outside_orthogonality (M t) (M (t+1)) T n e hX hY
    · letI : Epi e := he
      letI := hHered (M (t+1))
      rw [hq]
      exact copies_kernel_outside_orthogonality (M t) (M (t+1)) T n e hX hY
  have hInside : ∀ T : C,
      ((∀ g : T ⟶ M t, g = 0) ∧ (∀ x : Ext T (M t) 1, x = 0)) →
      ((∀ g : T ⟶ M (t+1), g = 0) ∧ (∀ x : Ext T (M (t+1)) 1, x = 0)) →
      ((∀ g : T ⟶ Q, g = 0) ∧ (∀ x : Ext T Q 1, x = 0)) := by
    intro T hX hY
    rcases hBranch with ⟨hm, hn, hq⟩ | ⟨he, hn, hq⟩
    · letI : Mono e := hm
      letI := hHered T
      rw [hq]
      exact copies_cokernel_inside_orthogonality T (M t) (M (t+1)) n e hX hY
    · letI : Epi e := he
      rw [hq]
      exact copies_kernel_inside_orthogonality T (M t) (M (t+1)) n e hX hY
  have hFrame := frame_rightObjects F M hM t ht Q hRigid hEnd hId hFinite
    ⟨hHQ, hEQ⟩ hOutside hInside
  have hQSign : ∃ sq : Int, (sq = 1 ∨ sq = -1) ∧ ∀ a,
      (Module.finrank K ((F a).obj Q) : Int) =
        sq * (D a (t+1) - s t * s (t+1) * (n : Int) * D a t) := by
    rcases hBranch with ⟨hm, hn, hq⟩ | ⟨he, hn, hq⟩
    · letI : Mono e := hm
      have hd := mapped_cokernel_dimension_difference F hZero hLimits hColimits
        _ _ e hCopies (hM.finiteVertices (t+1))
      refine ⟨s (t+1), (hD (t+1)).1, ?_⟩
      intro a
      rw [hq, hd a, (hD (t+1)).2 a, hCopiesDim a]
      rcases (hD (t+1)).1 with hs | hs <;> rw [hs] <;> ring
    · letI : Epi e := he
      have hd := mapped_kernel_dimension_difference F hZero hLimits hColimits
        _ _ e hCopies (hM.finiteVertices (t+1))
      refine ⟨-s (t+1), ?_, ?_⟩
      · rcases (hD (t+1)).1 with hs | hs <;> simp [hs]
      · intro a
        rw [hq, hd a, hCopiesDim a, (hD (t+1)).2 a]
        rcases (hD (t+1)).1 with hs | hs <;> rw [hs] <;> ring
  obtain ⟨sq, hSq, hQDim⟩ := hQSign
  have hAt : rightObjects M t Q t = Q := by simp [rightObjects]
  have hNext : rightObjects M t Q (t+1) = M t := by simp [rightObjects, ne_of_gt ht1]
  have hSigned : SignedDimensions F (rightObjects M t Q)
      (rightColumns D (s t * s (t+1) * (n : Int)) t) (rightSigns s t sq) := by
    intro j
    by_cases hj : j = t
    · subst j
      constructor
      · simpa [rightSigns] using hSq
      · intro a; rw [hAt]; simpa [rightSigns, rightColumns] using hQDim a
    · by_cases hj1 : j = t+1
      · subst j
        constructor
        · simpa [rightSigns, ne_of_gt ht1] using (hD t).1
        · intro a; rw [hNext]
          simpa [rightSigns, rightColumns, ne_of_gt ht1] using (hD t).2 a
      · have he : rightObjects M t Q j = M j := by simp [rightObjects, hj, hj1]
        constructor
        · simpa [rightSigns, hj, hj1] using (hD j).1
        · intro a; rw [he]
          simpa [rightSigns, rightColumns, hj, hj1] using (hD j).2 a
  exact ⟨Q, sq, hBranch, hFrame, hSigned, (hom_basis_multiplicity _ _ n f).2,
    positive_vertex_dimension_of_nonzero F hJointEpi Q hFinite hId⟩

#print axioms signed_right_hom_adjacent
end QuiverProofs.MA4RestartArrow20261003.SignedAdjacentRightHom
