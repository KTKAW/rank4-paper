import MA4RestartCoordinator20261003.EvaluationColorHom

/-! The exhaustive selected-selected same-color case table for a green
right sweep. Actual chosen maps and short exact sequences are retained.
Their metadata must still be matched to literal chronological columns. -/
namespace QuiverProofs.MA4RestartRightColorTraceHom
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open MA4RestartEvaluationColorHom
universe w v u z
variable {K : Type w} [Field K] {C : Type u}
  [Category.{v} C] [Abelian C] [Linear K C] [HasExt.{z} C] [HasFiniteBiproducts C]
set_option maxHeartbeats 0

def RightColorTrace (X Y Q : C) (ci gi : Bool) : Prop :=
  (ci = false ∧ gi = true ∧ ∃ (n : ℕ) (f : Module.Basis (Fin n) K (Y ⟶ X)),
    Epi (biproduct.desc (f := fun _ : Fin n => Y) (fun j => f j)) ∧
      Q = kernel (biproduct.desc (f := fun _ : Fin n => Y) (fun j => f j))) ∨
  (ci = false ∧ gi = false ∧ ∃ (n : ℕ) (f : Module.Basis (Fin n) K (Y ⟶ X)),
    Mono (biproduct.desc (f := fun _ : Fin n => Y) (fun j => f j)) ∧
      Q = cokernel (biproduct.desc (f := fun _ : Fin n => Y) (fun j => f j))) ∨
  (ci = true ∧ gi = true ∧ ∃ (n : ℕ) (i : X ⟶ Q)
    (p : Q ⟶ (⨁ fun _ : Fin n => Y)) (wip : i ≫ p = 0),
      (ShortComplex.mk i p wip).ShortExact)

/-- Every selected-selected same-color branch follows from old categorical
boundaries. The supplied internal Hom law is an output of the actual local
mutation primitive, and is needed only for the extension-extension case. -/
theorem same_color_hom_of_right_traces
    (X X' Y Q Q' : C) (ci cj gi gj : Bool)
    (hI : RightColorTrace (K := K) X Y Q ci gi)
    (hJ : RightColorTrace (K := K) X' Y Q' cj gj)
    (hSame : gi = gj) (hOldBlock : ci = false → cj = true → False)
    (hOldSame : ci = cj → ∀ f : X ⟶ X', f = 0)
    (hXY : ∀ x : Ext X Y 1, x = 0)
    (hGreenHom : ci = true → ∀ f : X ⟶ Y, f = 0)
    (hEndY : ∀ f : Y ⟶ Y, ∃ c : K, f = c • 𝟙 Y)
    (hYQ : ∀ f : Y ⟶ Q', f = 0) : ∀ f : Q ⟶ Q', f = 0 := by
  rcases hI with ⟨hi,hgi,n,f,he,hQ⟩ | ⟨hi,hgi,n,f,he,hQ⟩ | ⟨hi,hgi,n,i,p,wi,hS⟩
  · rcases hJ with ⟨hj,hgj,m,f',he',hQ'⟩ | ⟨hj,hgj,m,f',he',hQ'⟩ |
      ⟨hj,hgj,m,i',p',wi',hS'⟩
    · subst Q; subst Q'
      letI := he; letI := he'
      exact evaluation_kernels_hom_zero X X' Y n m _ f' hEndY
        (hOldSame (by rw [hi,hj])) hXY
    · rw [hgi,hgj] at hSame
      contradiction
    · exact False.elim (hOldBlock hi hj)
  · rcases hJ with ⟨hj,hgj,m,f',he',hQ'⟩ | ⟨hj,hgj,m,f',he',hQ'⟩ |
      ⟨hj,hgj,m,i',p',wi',hS'⟩
    · rw [hgi,hgj] at hSame
      contradiction
    · subst Q; subst Q'
      letI := he'
      exact evaluation_cokernels_hom_zero X X' Y n m _ _
        (hOldSame (by rw [hi,hj])) hXY
    · rw [hgi,hgj] at hSame
      contradiction
  · rcases hJ with ⟨hj,hgj,m,f',he',hQ'⟩ | ⟨hj,hgj,m,f',he',hQ'⟩ |
      ⟨hj,hgj,m,i',p',wi',hS'⟩
    · subst Q'
      exact right_extension_to_kernel_hom_zero X X' Y Q n m i p wi hS f'
        hEndY (hGreenHom hi)
    · rw [hgi,hgj] at hSame
      contradiction
    · exact right_extensions_hom_zero X X' Y Q Q' n m i p wi hS i' p' wi' hS'
        (hOldSame (by rw [hi,hj])) (hGreenHom hi) hYQ

#check same_color_hom_of_right_traces
#print axioms same_color_hom_of_right_traces
end QuiverProofs.MA4RestartRightColorTraceHom
