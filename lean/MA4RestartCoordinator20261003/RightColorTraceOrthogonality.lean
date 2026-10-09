import MA4RestartCoordinator20261003.RightColorTraceHom
import MA4RestartCoordinator20261003.MixedEvaluationOrthogonality

/-! A selected red-before-green right-family inversion is exactly the
chosen cokernel/kernel pair. The old color order excludes the other case.
All new ranks and finiteness are derived inside the actual model. -/
namespace QuiverProofs.MA4RestartRightColorTraceOrthogonality
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open MAExistenceLiterature MAExistenceTeamBRootPositivity
open MA4RestartWeightedQuiverModel MA4RestartModelExt
open MA4RestartRightColorTraceHom MA4RestartMixedEvaluationOrthogonality
set_option maxHeartbeats 0

local instance actualHasExt (B : Matrix 4) (K : Type) [Field K] :
    HasExt.{0} (Representation B K) := representation_hasExt B K
local instance actualFiniteBiproducts (B : Matrix 4) (K : Type) [Field K] :
    HasFiniteBiproducts (Representation B K) := Abelian.hasFiniteBiproducts

/-- Both vanishing conclusions concern the SAME actual chosen replacements
encoded in the traces. No new Euler or colored orthogonality is assumed. -/
theorem inversion_orthogonal_of_right_traces
    (B U : Matrix 4) (K : Type) [Field K] (hB : SkewSymmetric B)
    (hs : Cosquare.add U (Cosquare.transpose U) = initialCompanion B)
    (ha : Cosquare.add U (Cosquare.scale (-1) (Cosquare.transpose U)) = reverse B)
    (X X' Y Q Q' : Representation B K) (ci cj gi gj : Bool)
    (hI : RightColorTrace (K := K) X Y Q ci gi)
    (hJ : RightColorTrace (K := K) X' Y Q' cj gj)
    (hRed : gi = false) (hGreen : gj = true)
    (hOldBlock : ci = false → cj = true → False)
    (hOldSame : ci = cj → ∀ f : X ⟶ X', f = 0)
    (hX : ∀ a, Module.Finite K ((vertexFunctor B K a).obj X))
    (hX' : ∀ a, Module.Finite K ((vertexFunctor B K a).obj X'))
    (hY : ∀ a, Module.Finite K ((vertexFunctor B K a).obj Y))
    (hIdY : 𝟙 Y ≠ 0) (hEndY : ∀ f : Y ⟶ Y, ∃ c : K, f = c • 𝟙 Y)
    (hRigidY : ∀ e : Ext Y Y 1, e = 0)
    (hXY : ∀ f : X ⟶ Y, f = 0) (hExtXY : ∀ e : Ext X Y 1, e = 0)
    (hExtYX' : ∀ e : Ext Y X' 1, e = 0) :
    (∀ f : Q ⟶ Q', f = 0) ∧ (∀ e : Ext Q Q' 1, e = 0) := by
  rcases hI with ⟨hi,hgi,n,f,he,hQ⟩ | ⟨hi,hgi,n,f,he,hQ⟩ | ⟨hi,hgi,n,i,p,wi,hS⟩
  · rw [hgi] at hRed
    contradiction
  · rcases hJ with ⟨hj,hgj,m,f',he',hQ'⟩ | ⟨hj,hgj,m,f',he',hQ'⟩ |
      ⟨hj,hgj,m,i',p',wi',hS'⟩
    · subst Q; subst Q'
      letI := he; letI := he'
      have h := mixed_evaluation_orthogonality B U K hB hs ha X X' Y n m f f'
        hX hX' hY hIdY hEndY hRigidY hXY hExtXY hExtYX'
        (hOldSame (by rw [hi,hj]))
      exact ⟨h.1,h.2.1⟩
    · rw [hgj] at hGreen
      contradiction
    · exact False.elim (hOldBlock hi hj)
  · rw [hgi] at hRed
    contradiction

#check inversion_orthogonal_of_right_traces
#print axioms inversion_orthogonal_of_right_traces
end QuiverProofs.MA4RestartRightColorTraceOrthogonality
