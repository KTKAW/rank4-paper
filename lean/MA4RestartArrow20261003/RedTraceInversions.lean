import MA4RestartArrow20261003.RedFamilySameColorHom
import MA4RestartCoordinator20261003.MixedCoevaluationOrthogonality

/-! Actual red-before-green inversion orthogonality of a fixed red-pivot
terminal family. Mixed selected branches use the independently accepted
SAME chosen coevaluation model lemma. Unselected pivot boundaries concern
OLD objects and are discharged from the numerical interval outside signs. -/
namespace QuiverProofs.MA4RestartArrow20261003.RedTraceInversions
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open QuiverProofs MAExistenceLiterature MAExistenceTeamBRootPositivity
open MA4RestartWeightedQuiverModel MA4RestartModelExt
open MA4RestartMixedCoevaluationOrthogonality
open MA4RestartArrow20261003.AdjacentExceptionalFrame
open MA4RestartArrow20261003.LeftFamilyFrame
open MA4RestartArrow20261003.LeftColorTraceHom
open MA4RestartArrow20261003.LeftTraceBoundaryHom
open MA4RestartArrow20261003.RedFamilySameColorHom
set_option maxHeartbeats 0
local instance actualHasExt (B : Matrix 4) (K : Type) [Field K] :
    HasExt.{0} (Representation B K) := representation_hasExt B K
local instance actualFiniteBiproducts (B : Matrix 4) (K : Type) [Field K] :
    HasFiniteBiproducts (Representation B K) := Abelian.hasFiniteBiproducts

theorem mixed_left_traces_orthogonal
    (B U : Matrix 4) (K : Type) [Field K] (hB : SkewSymmetric B)
    (hs : Cosquare.add U (Cosquare.transpose U) = initialCompanion B)
    (ha : Cosquare.add U (Cosquare.scale (-1) (Cosquare.transpose U)) = reverse B)
    (X X' Y Q Q' : Representation B K) (ci cj : Bool)
    (hI : LeftColorTrace (K := K) X Y Q ci false)
    (hJ : LeftColorTrace (K := K) X' Y Q' cj true)
    (hBlock : ci = false → cj = true → False)
    (hOldSame : ci = cj → ∀ f : X ⟶ X', f = 0)
    (hX : ∀ a, Module.Finite K ((vertexFunctor B K a).obj X))
    (hX' : ∀ a, Module.Finite K ((vertexFunctor B K a).obj X'))
    (hY : ∀ a, Module.Finite K ((vertexFunctor B K a).obj Y))
    (hIdY : 𝟙 Y ≠ 0) (hEndY : ∀ f : Y ⟶ Y, ∃ c : K, f = c • 𝟙 Y)
    (hRigidY : ∀ e : Ext Y Y 1, e = 0)
    (hXY : ci = true → ∀ e : Ext X Y 1, e = 0)
    (hYX' : ∀ f : Y ⟶ X', f = 0) (hEYX' : ∀ e : Ext Y X' 1, e = 0) :
    Orthogonal Q Q' := by
  cases hI with
  | cokernel n f hm hQ =>
    cases hJ with
    | kernel m f' he hQ' =>
      rw [hQ, hQ']
      letI := hm; letI := he
      have h := mixed_coevaluation_orthogonality B U K hB hs ha X X' Y n m f f'
        hX hX' hY hIdY hEndY hRigidY (hXY rfl) hYX' hEYX' (hOldSame rfl)
      exact ⟨h.1, h.2.1⟩
  | extension n i p wi hS =>
    cases hJ with
    | kernel m f' he hQ' => exact False.elim (hBlock rfl rfl)

theorem terminal_red_before_green_orthogonal
    (B U : Matrix 4) (K : Type) [Field K] (hB : SkewSymmetric B)
    (hs : Cosquare.add U (Cosquare.transpose U) = initialCompanion B)
    (ha : Cosquare.add U (Cosquare.scale (-1) (Cosquare.transpose U)) = reverse B)
    (M Q : Fin 4 → Representation B K) (c g : Fin 4 → Bool)
    (hM : ExceptionalFrame (vertexFunctor B K) M)
    (t q : Fin 4) (hqt : q ≤ t) (hc : c t = false)
    (hOldBlock : ∀ a b, a < b → c a = false → c b = true → False)
    (hOldSame : ∀ a b, a < b → c a = c b → ∀ f : M a ⟶ M b, f = 0)
    (hTrace : ∀ i, q ≤ i → i < t → LeftColorTrace (K := K) (M i) (M t) (Q i) (c i) (g i))
    (hGreenExt : ∀ i, q ≤ i → i < t → c i = true → ∀ e : Ext (M i) (M t) 1, e = 0)
    (hOutsideRed : ∀ a, a < q → c a = false → Orthogonal (M a) (M t)) :
    ∀ a b, a < b → familyColors c g t q a = false → familyColors c g t q b = true →
      Orthogonal (familyObjects M Q t q a) (familyObjects M Q t q b) := by
  have hAt : familyObjects M Q t q q = M t := by simp [familyObjects]
  have hIn : ∀ j, q < j ∧ j ≤ t → familyObjects M Q t q j = Q (predecessor j) := by
    intro j hj; simp [familyObjects, ne_of_gt hj.1, hj]
  have hOut : ∀ j, j ≠ q → ¬ (q < j ∧ j ≤ t) → familyObjects M Q t q j = M j := by
    intro j hj hn; simp [familyObjects, hj, hn]
  have hCAt : familyColors c g t q q = true := by simp [familyColors]
  have hCIn : ∀ j, q < j ∧ j ≤ t → familyColors c g t q j = g (predecessor j) := by
    intro j hj; simp [familyColors, ne_of_gt hj.1, hj]
  have hCOut : ∀ j, j ≠ q → ¬ (q < j ∧ j ≤ t) → familyColors c g t q j = c j := by
    intro j hj hn; simp [familyColors, hj, hn]
  have hBounds : ∀ j, q < j ∧ j ≤ t → q ≤ predecessor j ∧ predecessor j < t := by
    intro j hj; change q.val ≤ j.val-1 ∧ j.val-1 < t.val; constructor <;> omega
  intro a b hab hRed hGreen
  by_cases haQ : a = q
  · rw [haQ, hCAt] at hRed; contradiction
  · by_cases hai : q < a ∧ a ≤ t
    · have hbQ : b ≠ q := by omega
      by_cases hbi : q < b ∧ b ≤ t
      · have haB := hBounds a hai; have hbB := hBounds b hbi
        have hij : predecessor a < predecessor b := by change a.val-1 < b.val-1; omega
        rw [hCIn a hai] at hRed; rw [hCIn b hbi] at hGreen
        have hI := hTrace _ haB.1 haB.2; have hJ := hTrace _ hbB.1 hbB.2
        rw [hRed] at hI; rw [hGreen] at hJ
        rw [hIn a hai, hIn b hbi]
        exact mixed_left_traces_orthogonal B U K hB hs ha _ _ _ _ _ _ _ hI hJ
          (hOldBlock _ _ hij) (hOldSame _ _ hij)
          (hM.finiteVertices _) (hM.finiteVertices _) (hM.finiteVertices t)
          (hM.nonzeroId t) (hM.scalarEnd t) (hM.rigid t) (hGreenExt _ haB.1 haB.2)
          (hM.reverseHom _ _ hbB.2) (hM.reverseExt _ _ hbB.2)
      · have htb : t < b := by omega
        rw [hCOut b hbQ hbi] at hGreen
        exact False.elim (hOldBlock t b htb hc hGreen)
    · by_cases hbQ : b = q
      · subst b
        rw [hCOut a haQ hai] at hRed
        rw [hOut a haQ hai, hAt]
        exact hOutsideRed a hab hRed
      · by_cases hbi : q < b ∧ b ≤ t
        · have haq : a < q := by omega
          have hbB := hBounds b hbi
          have haib : a < predecessor b := by change a.val < b.val-1; omega
          rw [hCOut a haQ hai] at hRed; rw [hCIn b hbi] at hGreen
          have hTr := hTrace _ hbB.1 hbB.2
          rw [hGreen] at hTr
          have hci := green_trace_old_green _ _ _ _ hTr
          exact False.elim (hOldBlock _ _ haib hRed hci)
        · rw [hCOut a haQ hai] at hRed; rw [hCOut b hbQ hbi] at hGreen
          exact False.elim (hOldBlock a b hab hRed hGreen)

#print axioms mixed_left_traces_orthogonal
#print axioms terminal_red_before_green_orthogonal
end QuiverProofs.MA4RestartArrow20261003.RedTraceInversions
