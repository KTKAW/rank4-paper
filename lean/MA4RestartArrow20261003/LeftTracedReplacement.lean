import MA4RestartArrow20261003.LeftColorTraceHom
import MA4RestartArrow20261003.AdjacentLeftMutation

/-! Construct actual replacements of arbitrary original selected neighbors
through the fixed red pivot and retain the SAME chosen map/SES color trace.
Only OLD frame, actual OLD dimensions, and OLD color/Euler branch gates
are inputs. Bases, branch, new objects and finite vertices are derived. -/
namespace QuiverProofs.MA4RestartArrow20261003.LeftTracedReplacement
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open QuiverProofs.MA4RestartArrow20261003.AdjacentExceptionalFrame
open QuiverProofs.MA4RestartArrow20261003.LeftFamilyFrame
open QuiverProofs.MA4RestartArrow20261003.LeftColorTraceHom
open QuiverProofs.MA4RestartArrow20261003.LeftHomMutationOldVertices
open QuiverProofs.MA4RestartArrow20261003.VertexCopies
open QuiverProofs.MA4RestartVertexFiniteness
open QuiverProofs.MACompletionExactVertexDimensions
open QuiverProofs.MACompletionScalarEndomorphisms QuiverProofs.MACompletionPairPurity
universe w v u z
variable {K : Type w} [Field K] {C : Type u}
  [Category.{v} C] [Abelian C] [Linear K C] [HasExt.{z} C]
  [EnoughProjectives C] [HasFiniteBiproducts C]
set_option maxHeartbeats 0

def branchSign (c : Bool) : Int := if c then 1 else -1

theorem red_pivot_traced_replacement
    (F : Fin 4 → C ⥤ ModuleCat.{v} K)
    (hZero : ∀ a, (F a).PreservesZeroMorphisms)
    (hLimits : ∀ a, PreservesFiniteLimits (F a))
    (hColimits : ∀ a, PreservesFiniteColimits (F a))
    (hJointEpi : ∀ {M V : C} (e : M ⟶ V), (∀ a, Epi ((F a).map e)) → Epi e)
    (hHered : ∀ T : C, HasProjectiveDimensionLT T 2)
    (M : Fin 4 → C) (hM : ExceptionalFrame F M)
    (D : Fin 4 → Fin 4 → Int) (c : Fin 4 → Bool)
    (hD : ∀ j a, (Module.finrank K ((F a).obj (M j)) : Int) = branchSign (c j) * D a j)
    (i t : Fin 4) (hit : i < t) (hc : c t = false)
    [Module.Finite K (M i ⟶ M t)] [Module.Finite K (Ext (M i) (M t) 1)]
    (hOldHom : c i = false → ∀ f : M i ⟶ M t, f = 0)
    (hGreenEuler : c i = true → 0 ≤
      (Module.finrank K (M i ⟶ M t) : Int) - (Module.finrank K (Ext (M i) (M t) 1) : Int)) :
    let χ : Int := (Module.finrank K (M i ⟶ M t) : Int) -
      (Module.finrank K (Ext (M i) (M t) 1) : Int)
    ∃ (Q : C) (g : Bool),
      LeftReplacement F (M i) (M t) Q ∧
      LeftColorTrace (K := K) (M i) (M t) Q (c i) g ∧
      (∀ a, (Module.finrank K ((F a).obj Q) : Int) =
        branchSign g * (D a i - (branchSign (c i) * (-1) * χ) * D a t)) := by
  classical
  let χ : Int := (Module.finrank K (M i ⟶ M t) : Int) -
    (Module.finrank K (Ext (M i) (M t) 1) : Int)
  cases hci : c i with
  | false =>
    have hHom := hOldHom hci
    letI : Subsingleton (M i ⟶ M t) := ⟨fun f g => by rw [hHom f, hHom g]⟩
    have hH0 : Module.finrank K (M i ⟶ M t) = 0 := Module.finrank_zero_of_subsingleton
    let n := Module.finrank K (Ext (M i) (M t) 1)
    let β := Module.finBasis K (Ext (M i) (M t) 1)
    obtain ⟨Q, a, p, wap, hS, hβ, hHomQ, hExtQ, hRigid, hEnd, hId, hFinite,
      hDim, hOutside, hInside⟩ :=
      MA4RestartEuler20261003.left_universal_extension_finite_frame K F hZero hLimits hColimits
        (M i) (M t) n β (hM.scalarEnd i) (hM.scalarEnd t) hHom
        (hM.reverseHom i t hit) (hM.rigid i) (hM.rigid t)
        (hM.reverseExt i t hit) (hM.nonzeroId i) (hM.finiteVertices i) (hM.finiteVertices t)
    have hχ : (Module.finrank K (M i ⟶ M t) : Int) -
        (Module.finrank K (Ext (M i) (M t) 1) : Int) = -(n : Int) := by dsimp [n]; rw [hH0]; ring
    refine ⟨Q, false, ⟨hRigid, hEnd, hId, hFinite, ⟨hHomQ, hExtQ⟩,
      (fun T hX hY => hOutside T hY hX), (fun T hX hY => hInside T hY hX)⟩, ?_, ?_⟩
    · exact LeftColorTrace.extension n a p wap hS
    · intro b
      rw [hDim b, hD t b, hD i b, hc, hci, hχ]
      simp only [branchSign, Bool.false_eq_true, ↓reduceIte]
      ring
  | true =>
    have hExt : ∀ x : Ext (M i) (M t) 1, x = 0 := by
      letI := local_end_of_scalar_end (M i) (hM.nonzeroId i) (hM.scalarEnd i)
      letI := local_end_of_scalar_end (M t) (hM.nonzeroId t) (hM.scalarEnd t)
      rcases hom_or_extOne_vanishes_of_rigid (M i) (M t) hHered
        (hM.reverseExt i t hit) (hM.rigid i) (hM.rigid t) with hHom | hExt
      · letI : Subsingleton (M i ⟶ M t) := ⟨fun f g => by rw [hHom f, hHom g]⟩
        have hH0 : Module.finrank K (M i ⟶ M t) = 0 := Module.finrank_zero_of_subsingleton
        have hE0 : Module.finrank K (Ext (M i) (M t) 1) = 0 := by
          have hp := hGreenEuler hci
          rw [hH0] at hp
          omega
        letI : Subsingleton (Ext (M i) (M t) 1) := Module.finrank_zero_iff.mp hE0
        exact fun x => Subsingleton.elim x 0
      · exact hExt
    letI : Subsingleton (Ext (M i) (M t) 1) := ⟨fun x y => by rw [hExt x, hExt y]⟩
    have hE0 : Module.finrank K (Ext (M i) (M t) 1) = 0 := Module.finrank_zero_of_subsingleton
    let n := Module.finrank K (M i ⟶ M t)
    let f := Module.finBasis K (M i ⟶ M t)
    let e := biproduct.lift (f := fun _ : Fin n => M t) (fun j => f j)
    obtain ⟨Q, hBranch, hHomQ, hExtQ, hRigid, hEnd, hId, hLocal, hFiniteEnd,
      hRankEnd, hFinite, hDim, hPos, hOutside, hInside⟩ :=
      left_hom_mutation_from_old_vertices (M i) (M t) n f hHered
        (hM.reverseHom i t hit) (hM.reverseExt i t hit) hExt
        (hM.rigid i) (hM.rigid t) (hM.nonzeroId i) (hM.scalarEnd i) (hM.scalarEnd t)
        F hZero hLimits hColimits hJointEpi (hM.finiteVertices i) (hM.finiteVertices t)
        (fun a => (Module.finrank K ((F a).obj (M i)) : Int))
        (fun a => (Module.finrank K ((F a).obj (M t)) : Int)) (fun _ => rfl) (fun _ => rfl)
    have hFact : LeftReplacement F (M i) (M t) Q :=
      ⟨hRigid, hEnd, hId, hFinite, ⟨hHomQ, hExtQ⟩, hOutside, hInside⟩
    have hCopies := vertex_copies_finite F hZero hLimits (M t) n (hM.finiteVertices t)
    have hCopiesDim := vertex_copies_dimension F hZero hLimits (M t) n
      (hM.finiteVertices t) (fun a => (Module.finrank K ((F a).obj (M t)) : Int))
      (fun _ => rfl)
    have hχ : (Module.finrank K (M i ⟶ M t) : Int) -
        (Module.finrank K (Ext (M i) (M t) 1) : Int) = (n : Int) := by dsimp [n]; rw [hE0]; ring
    rcases hBranch with ⟨hm, hn, hq⟩ | ⟨he, hn, hq⟩
    · letI : Mono e := hm
      have hd := mapped_cokernel_dimension_difference F hZero hLimits hColimits
        _ _ e (hM.finiteVertices i) hCopies
      refine ⟨Q, false, hFact, ?_, ?_⟩
      · exact LeftColorTrace.cokernel n f hm hq
      · intro a
        rw [hq, hd a, hCopiesDim a]
        dsimp only
        rw [hD t a, hD i a, hc, hci, hχ]
        simp only [branchSign, Bool.false_eq_true, ↓reduceIte]
        ring
    · letI : Epi e := he
      have hd := mapped_kernel_dimension_difference F hZero hLimits hColimits
        _ _ e (hM.finiteVertices i) hCopies
      refine ⟨Q, true, hFact, ?_, ?_⟩
      · exact LeftColorTrace.kernel n f he hq
      · intro a
        rw [hq, hd a, hCopiesDim a]
        dsimp only
        rw [hD i a, hD t a, hc, hci, hχ]
        simp only [branchSign, Bool.false_eq_true, ↓reduceIte]
        ring

#print axioms red_pivot_traced_replacement
end QuiverProofs.MA4RestartArrow20261003.LeftTracedReplacement
