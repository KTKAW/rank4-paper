import MA4RestartArrow20261003.LeftFamilyFrame
import MA4RestartArrow20261003.ColoredHomTransport

/-! Retain actual chosen left mutation maps/SES and their old/new colors.
Same-color Hom transport is proved for every pair of selected original
neighbors, including changes of branch between the two neighbors. -/
namespace QuiverProofs.MA4RestartArrow20261003.LeftColorTraceHom
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open QuiverProofs.MA4RestartArrow20261003.ColoredHomTransport
open QuiverProofs.MA4RestartArrow20261003.LeftFamilyFrame
universe w v u z
variable {K : Type w} [Field K] {C : Type u}
  [Category.{v} C] [Abelian C] [Linear K C] [HasExt.{z} C] [HasFiniteBiproducts C]
set_option maxHeartbeats 0

/-- The original pivot is red. Old green objects use actual coevaluation;
old red objects use actual universal left-extension SES. The new color is
fixed by the actual branch, and will be matched to signed columns. -/
inductive LeftColorTrace (X Y Q : C) : Bool → Bool → Prop where
  | kernel (n : ℕ) (f : Module.Basis (Fin n) K (X ⟶ Y))
      (he : Epi (biproduct.lift (f := fun _ : Fin n => Y) (fun j => f j)))
      (hQ : Q = kernel (biproduct.lift (f := fun _ : Fin n => Y) (fun j => f j))) :
      LeftColorTrace X Y Q true true
  | cokernel (n : ℕ) (f : Module.Basis (Fin n) K (X ⟶ Y))
      (he : Mono (biproduct.lift (f := fun _ : Fin n => Y) (fun j => f j)))
      (hQ : Q = cokernel (biproduct.lift (f := fun _ : Fin n => Y) (fun j => f j))) :
      LeftColorTrace X Y Q true false
  | extension (n : ℕ) (i : (⨁ fun _ : Fin n => Y) ⟶ Q) (p : Q ⟶ X)
      (wip : i ≫ p = 0) (hS : (ShortComplex.mk i p wip).ShortExact) :
      LeftColorTrace X Y Q false false

/-- This is every selected-selected same-color case. All old Hom/Ext
boundaries come from the original colored exceptional frame; the internal
Q-to-pivot Hom law comes from the actual primitive, not a color oracle. -/
theorem same_color_hom_of_left_traces
    (X X' Y Q Q' : C) (ci cj gi gj : Bool)
    (hI : LeftColorTrace (K := K) X Y Q ci gi) (hJ : LeftColorTrace (K := K) X' Y Q' cj gj)
    (hSame : gi = gj) (hOldBlock : ci = false → cj = true → False)
    (hOldSame : ci = cj → ∀ f : X ⟶ X', f = 0)
    (hYX : ∀ f : Y ⟶ X', f = 0) (hEYX : ∀ x : Ext Y X' 1, x = 0)
    (hEndY : ∀ f : Y ⟶ Y, ∃ c : K, f = c • 𝟙 Y)
    (hQY : ∀ f : Q ⟶ Y, f = 0) :
    ∀ f : Q ⟶ Q', f = 0 := by
  cases hI with
  | kernel n f he hQ =>
    cases hJ with
    | kernel m f' he' hQ' =>
      subst Q; subst Q'
      letI := he; letI := he'
      exact coevaluation_kernels_hom_zero X X' Y n m _ _ (hOldSame rfl) hEYX
    | cokernel m f' he' hQ' => contradiction
    | extension m i' p' wi' hS' => contradiction
  | cokernel n f he hQ =>
    cases hJ with
    | kernel m f' he' hQ' => contradiction
    | cokernel m f' he' hQ' =>
      subst Q; subst Q'
      letI := he; letI := he'
      exact coevaluation_cokernels_hom_zero X X' Y n m f f' hEndY (hOldSame rfl) hEYX
    | extension m i' p' wi' hS' =>
      subst Q
      exact cokernel_to_left_extension_hom_zero X X' Y Q' n m _ i' p' wi' hS' hYX hQY
  | extension n i p wi hS =>
    cases hJ with
    | kernel m f' he' hQ' => exact False.elim (hOldBlock rfl rfl)
    | cokernel m f' he' hQ' => exact False.elim (hOldBlock rfl rfl)
    | extension m i' p' wi' hS' =>
      exact left_extensions_hom_zero X X' Y Q Q' n m i p wi hS i' p' wi' hS'
        (hOldSame rfl) hYX hQY

#print axioms same_color_hom_of_left_traces
end QuiverProofs.MA4RestartArrow20261003.LeftColorTraceHom
