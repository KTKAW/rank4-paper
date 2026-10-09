import MA4RestartArrow20261003.RightFamilyFrame
import MA4RestartArrow20261003.AdjacentRightMutation
import MA4RestartArrow20261003.LeftTracedReplacement
import MA4RestartCoordinator20261003.RightColorTraceHom

/-! Actual replacements of original right neighbors through one original
GREEN pivot. OLD samecolorHom/selectedactualEuler gates choose internally
constructed bases/branches. SAME chosen evaluation/SES trace and exact
signed all-coordinate right shear are retained; no opposite transfer. -/
namespace QuiverProofs.MA4RestartArrow20261003.RightTracedReplacement
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open QuiverProofs.MA4RestartArrow20261003.AdjacentExceptionalFrame
open QuiverProofs.MA4RestartArrow20261003.LeftFamilyFrame
open QuiverProofs.MA4RestartArrow20261003.RightFamilyFrame
open QuiverProofs.MA4RestartArrow20261003.LeftTracedReplacement
open QuiverProofs.MA4RestartArrow20261003.VertexCopies
open QuiverProofs.MA4RestartRightColorTraceHom QuiverProofs.MA4RestartRightHomMutation
open QuiverProofs.MA4RestartVertexFiniteness QuiverProofs.MACompletionExactVertexDimensions
open QuiverProofs.MACompletionScalarEndomorphisms QuiverProofs.MACompletionPairPurity
open MA4EulerExternalOrthogonality01a0fee4
universe w v u z
variable {K : Type w} [Field K] {C : Type u}
  [Category.{v} C] [Abelian C] [Linear K C] [HasExt.{z} C]
  [EnoughProjectives C] [HasFiniteBiproducts C]
set_option maxHeartbeats 0

theorem green_pivot_traced_replacement
    (F : Fin 4 → C ⥤ ModuleCat.{v} K)
    (hZero : ∀ a, (F a).PreservesZeroMorphisms)
    (hLimits : ∀ a, PreservesFiniteLimits (F a))
    (hColimits : ∀ a, PreservesFiniteColimits (F a))
    (hJointEpi : ∀ {M V : C} (e : M ⟶ V), (∀ a, Epi ((F a).map e)) → Epi e)
    (hHered : ∀ T : C, HasProjectiveDimensionLT T 2)
    (M : Fin 4 → C) (hM : ExceptionalFrame F M)
    (D : Fin 4 → Fin 4 → Int) (c : Fin 4 → Bool)
    (hD : ∀ j a, (Module.finrank K ((F a).obj (M j)) : Int) = branchSign (c j) * D a j)
    (t i : Fin 4) (hti : t < i) (hc : c t = true)
    [Module.Finite K (M t ⟶ M i)] [Module.Finite K (Ext (M t) (M i) 1)]
    (hOldHom : c i = true → ∀ f : M t ⟶ M i, f = 0)
    (hRedEuler : c i = false → 0 ≤
      (Module.finrank K (M t ⟶ M i) : Int) - (Module.finrank K (Ext (M t) (M i) 1) : Int)) :
    let χ : Int := (Module.finrank K (M t ⟶ M i) : Int) -
      (Module.finrank K (Ext (M t) (M i) 1) : Int)
    ∃ (Q : C) (g : Bool),
      RightReplacement F (M t) (M i) Q ∧
      RightColorTrace (K := K) (M i) (M t) Q (c i) g ∧
      (∀ a, (Module.finrank K ((F a).obj Q) : Int) =
        branchSign g * (D a i - (1 * branchSign (c i) * χ) * D a t)) := by
  classical
  cases hci : c i with
  | true =>
    have hHom := hOldHom hci
    letI : Subsingleton (M t ⟶ M i) := ⟨fun f g => by rw [hHom f,hHom g]⟩
    have hH0 : Module.finrank K (M t ⟶ M i) = 0 := Module.finrank_zero_of_subsingleton
    let n := Module.finrank K (Ext (M t) (M i) 1)
    let β := Module.finBasis K (Ext (M t) (M i) 1)
    obtain ⟨Q,a,p,wap,hS,hβ,hHomQ,hExtQ,hRigid,hEnd,hId,hFinite,hDim,hOutside,hInside⟩ :=
      MA4RestartEuler20261003.universal_extension_finite_frame F hZero hLimits hColimits
        (M t) (M i) n β (hM.scalarEnd t) (hM.scalarEnd i) hHom
        (hM.reverseHom t i hti) (hM.rigid t) (hM.rigid i) (hM.reverseExt t i hti)
        (hM.nonzeroId i) (hM.finiteVertices t) (hM.finiteVertices i)
    have hχ : (Module.finrank K (M t ⟶ M i) : Int) -
        (Module.finrank K (Ext (M t) (M i) 1) : Int) = -(n : Int) := by dsimp [n]; rw [hH0]; ring
    refine ⟨Q,true,⟨hRigid,hEnd,hId,hFinite,⟨hHomQ,hExtQ⟩,
      (fun T hX hY => hOutside T hY hX),(fun T hX hY => hInside T hY hX)⟩,?_,?_⟩
    · exact Or.inr (Or.inr ⟨rfl,rfl,n,a,p,wap,hS⟩)
    · intro b
      rw [hDim b,hD t b,hD i b,hc,hci,hχ]
      simp only [branchSign,↓reduceIte]
      ring
  | false =>
    have hExt : ∀ x : Ext (M t) (M i) 1, x = 0 := by
      letI := local_end_of_scalar_end (M t) (hM.nonzeroId t) (hM.scalarEnd t)
      letI := local_end_of_scalar_end (M i) (hM.nonzeroId i) (hM.scalarEnd i)
      rcases hom_or_extOne_vanishes_of_rigid (M t) (M i) hHered
        (hM.reverseExt t i hti) (hM.rigid t) (hM.rigid i) with hHom | hExt
      · letI : Subsingleton (M t ⟶ M i) := ⟨fun f g => by rw [hHom f,hHom g]⟩
        have hH0 : Module.finrank K (M t ⟶ M i) = 0 := Module.finrank_zero_of_subsingleton
        have hE0 : Module.finrank K (Ext (M t) (M i) 1) = 0 := by
          have hp := hRedEuler hci; rw [hH0] at hp; omega
        letI : Subsingleton (Ext (M t) (M i) 1) := Module.finrank_zero_iff.mp hE0
        exact fun x => Subsingleton.elim x 0
      · exact hExt
    letI : Subsingleton (Ext (M t) (M i) 1) := ⟨fun x y => by rw [hExt x,hExt y]⟩
    have hE0 : Module.finrank K (Ext (M t) (M i) 1) = 0 := Module.finrank_zero_of_subsingleton
    let n := Module.finrank K (M t ⟶ M i)
    let f := Module.finBasis K (M t ⟶ M i)
    let e := biproduct.desc (f := fun _ : Fin n => M t) (fun j => f j)
    obtain ⟨Q,hBranch,hHomQ,hExtQ,hRigid,hEnd,hId⟩ :=
      right_hom_mutation_exists (M t) (M i) n f hHered
        (hM.reverseHom t i hti) (hM.reverseExt t i hti) hExt
        (hM.rigid t) (hM.rigid i) (hM.nonzeroId i) (hM.scalarEnd t) (hM.scalarEnd i)
    have hCopies := vertex_copies_finite F hZero hLimits (M t) n (hM.finiteVertices t)
    have hCopiesDim := vertex_copies_dimension F hZero hLimits (M t) n (hM.finiteVertices t)
      (fun a => (Module.finrank K ((F a).obj (M t)) : Int)) (fun _ => rfl)
    have hFinite : ∀ a, Module.Finite K ((F a).obj Q) := by
      rcases hBranch with ⟨hm,hn,hq⟩ | ⟨he,hn,hq⟩
      · letI : Mono e := hm; rw [hq]
        exact cokernel_vertex_finite F hZero hLimits hColimits _ _ e (hM.finiteVertices i)
      · letI : Epi e := he; rw [hq]
        exact kernel_vertex_finite F hZero hLimits hColimits _ _ e hCopies
    have hOutside : ∀ T : C, Orthogonal (M t) T → Orthogonal (M i) T → Orthogonal Q T := by
      intro T hX hY
      rcases hBranch with ⟨hm,hn,hq⟩ | ⟨he,hn,hq⟩
      · letI : Mono e := hm; rw [hq]
        exact copies_cokernel_outside_orthogonality (M t) (M i) T n e hX hY
      · letI : Epi e := he; letI := hHered (M i); rw [hq]
        exact copies_kernel_outside_orthogonality (M t) (M i) T n e hX hY
    have hInside : ∀ T : C, Orthogonal T (M t) → Orthogonal T (M i) → Orthogonal T Q := by
      intro T hX hY
      rcases hBranch with ⟨hm,hn,hq⟩ | ⟨he,hn,hq⟩
      · letI : Mono e := hm; letI := hHered T; rw [hq]
        exact copies_cokernel_inside_orthogonality T (M t) (M i) n e hX hY
      · letI : Epi e := he; rw [hq]
        exact copies_kernel_inside_orthogonality T (M t) (M i) n e hX hY
    have hFact : RightReplacement F (M t) (M i) Q :=
      ⟨hRigid,hEnd,hId,hFinite,⟨hHomQ,hExtQ⟩,hOutside,hInside⟩
    have hχ : (Module.finrank K (M t ⟶ M i) : Int) -
        (Module.finrank K (Ext (M t) (M i) 1) : Int) = (n : Int) := by dsimp [n]; rw [hE0]; ring
    rcases hBranch with ⟨hm,hn,hq⟩ | ⟨he,hn,hq⟩
    · letI : Mono e := hm
      have hd := mapped_cokernel_dimension_difference F hZero hLimits hColimits
        _ _ e hCopies (hM.finiteVertices i)
      refine ⟨Q,false,hFact,?_,?_⟩
      · exact Or.inr (Or.inl ⟨rfl,rfl,n,f,hm,hq⟩)
      · intro a
        rw [hq,hd a,hCopiesDim a]; dsimp only
        rw [hD i a,hD t a,hci,hc,hχ]
        simp only [branchSign,Bool.false_eq_true,↓reduceIte]
        ring
    · letI : Epi e := he
      have hd := mapped_kernel_dimension_difference F hZero hLimits hColimits
        _ _ e hCopies (hM.finiteVertices i)
      refine ⟨Q,true,hFact,?_,?_⟩
      · exact Or.inl ⟨rfl,rfl,n,f,he,hq⟩
      · intro a
        rw [hq,hd a,hCopiesDim a]; dsimp only
        rw [hD t a,hD i a,hci,hc,hχ]
        simp only [branchSign,Bool.false_eq_true,↓reduceIte]
        ring

#print axioms green_pivot_traced_replacement
end QuiverProofs.MA4RestartArrow20261003.RightTracedReplacement
