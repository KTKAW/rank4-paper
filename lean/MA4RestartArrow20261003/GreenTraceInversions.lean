import MA4RestartArrow20261003.GreenFamilySameColorHom
import MA4RestartCoordinator20261003.RightColorTraceOrthogonality
namespace QuiverProofs.MA4RestartArrow20261003.GreenTraceInversions
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open QuiverProofs MAExistenceLiterature MAExistenceTeamBRootPositivity
open MA4RestartWeightedQuiverModel MA4RestartModelExt
open MA4RestartRightColorTraceOrthogonality MA4RestartRightColorTraceHom
open MA4RestartArrow20261003.AdjacentExceptionalFrame MA4RestartArrow20261003.LeftFamilyFrame
open MA4RestartArrow20261003.RightFamilyFrame MA4RestartArrow20261003.RightTraceBoundaryHom
open MA4RestartArrow20261003.GreenFamilySameColorHom
set_option maxHeartbeats 0
local instance actualHasExt (B : Matrix 4) (K : Type) [Field K] :
    HasExt.{0} (Representation B K) := representation_hasExt B K
local instance actualFiniteBiproducts (B : Matrix 4) (K : Type) [Field K] :
    HasFiniteBiproducts (Representation B K) := Abelian.hasFiniteBiproducts

theorem terminal_red_before_green_orthogonal
    (B U : Matrix 4) (K : Type) [Field K] (hB : SkewSymmetric B)
    (hs : Cosquare.add U (Cosquare.transpose U) = initialCompanion B)
    (ha : Cosquare.add U (Cosquare.scale (-1) (Cosquare.transpose U)) = reverse B)
    (M Q : Fin 4 → Representation B K) (c g : Fin 4 → Bool)
    (hM : ExceptionalFrame (vertexFunctor B K) M)
    (t q : Fin 4) (htq : t ≤ q) (hc : c t = true)
    (hOldBlock : ∀ a b, a < b → c a = false → c b = true → False)
    (hOldSame : ∀ a b, a < b → c a = c b → ∀ f : M a ⟶ M b, f = 0)
    (hTrace : ∀ i, t < i → i ≤ q → RightColorTrace (K := K) (M i) (M t) (Q i) (c i) (g i))
    (hRedExt : ∀ i, t < i → i ≤ q → c i = false → ∀ e : Ext (M t) (M i) 1, e = 0)
    (hOutsideGreen : ∀ b, q < b → c b = true → Orthogonal (M t) (M b)) :
    ∀ a b, a < b → rightFamilyColors c g t q a = false → rightFamilyColors c g t q b = true →
      Orthogonal (rightFamilyObjects M Q t q a) (rightFamilyObjects M Q t q b) := by
  have hAt : rightFamilyObjects M Q t q q = M t := by simp [rightFamilyObjects]
  have hIn : ∀ j, t ≤ j ∧ j < q → rightFamilyObjects M Q t q j = Q (successor j) := by
    intro j hj; simp [rightFamilyObjects, ne_of_lt hj.2, hj]
  have hOut : ∀ j, j ≠ q → ¬ (t ≤ j ∧ j < q) → rightFamilyObjects M Q t q j = M j := by
    intro j hj hn; simp [rightFamilyObjects, hj, hn]
  have hCAt : rightFamilyColors c g t q q = false := by simp [rightFamilyColors]
  have hCIn : ∀ j, t ≤ j ∧ j < q → rightFamilyColors c g t q j = g (successor j) := by
    intro j hj; simp [rightFamilyColors, ne_of_lt hj.2, hj]
  have hCOut : ∀ j, j ≠ q → ¬ (t ≤ j ∧ j < q) → rightFamilyColors c g t q j = c j := by
    intro j hj hn; simp [rightFamilyColors, hj, hn]
  have hSucc : ∀ j, j < 3 → (successor j).val = j.val+1 := by
    intro j hj; fin_cases j <;> simp_all [successor]
  have hBounds : ∀ j, t ≤ j ∧ j < q → t < successor j ∧ successor j ≤ q := by
    intro j hj; change t.val < (successor j).val ∧ (successor j).val ≤ q.val
    rw [hSucc j (by omega)]; constructor <;> omega
  intro a b hab hRed hGreen
  by_cases haQ : a = q
  · subst a
    have hbQ : b ≠ q := by omega
    have hbi : ¬ (t ≤ b ∧ b < q) := by omega
    rw [hCOut b hbQ hbi] at hGreen
    rw [hAt,hOut b hbQ hbi]
    exact hOutsideGreen b hab hGreen
  · by_cases hai : t ≤ a ∧ a < q
    · have haB := hBounds a hai
      by_cases hbQ : b = q
      · rw [hbQ,hCAt] at hGreen; contradiction
      · by_cases hbi : t ≤ b ∧ b < q
        · have hbB := hBounds b hbi
          have hij : successor a < successor b := by
            change (successor a).val < (successor b).val
            rw [hSucc a (by omega),hSucc b (by omega)]; omega
          rw [hCIn a hai] at hRed; rw [hCIn b hbi] at hGreen
          have hI := hTrace _ haB.1 haB.2; have hJ := hTrace _ hbB.1 hbB.2
          rw [hRed] at hI; rw [hGreen] at hJ
          have hci := red_trace_old_red _ _ _ _ hI
          have hcj : c (successor b) = false := by
            cases h : c (successor b) with
            | false => rfl
            | true => exact False.elim (hOldBlock _ _ hij hci h)
          rw [hIn a hai,hIn b hbi]
          exact inversion_orthogonal_of_right_traces B U K hB hs ha _ _ _ _ _ _ _ false true
            hI hJ rfl rfl (hOldBlock _ _ hij) (hOldSame _ _ hij)
            (hM.finiteVertices _) (hM.finiteVertices _) (hM.finiteVertices t)
            (hM.nonzeroId t) (hM.scalarEnd t) (hM.rigid t)
            (hM.reverseHom t _ haB.1) (hM.reverseExt t _ haB.1)
            (hRedExt _ hbB.1 hbB.2 hcj)
        · have hqb : q < b := by omega
          have hib : successor a < b := by
            change (successor a).val < b.val; rw [hSucc a (by omega)]; omega
          rw [hCIn a hai] at hRed; rw [hCOut b hbQ hbi] at hGreen
          have hTr := hTrace _ haB.1 haB.2; rw [hRed] at hTr
          exact False.elim (hOldBlock _ _ hib (red_trace_old_red _ _ _ _ hTr) hGreen)
    · by_cases hbQ : b = q
      · rw [hbQ,hCAt] at hGreen; contradiction
      · by_cases hbi : t ≤ b ∧ b < q
        · have hat : a < t := by omega
          rw [hCOut a haQ hai] at hRed
          exact False.elim (hOldBlock a t hat hRed hc)
        · rw [hCOut a haQ hai] at hRed; rw [hCOut b hbQ hbi] at hGreen
          exact False.elim (hOldBlock a b hab hRed hGreen)
#print axioms terminal_red_before_green_orthogonal
end QuiverProofs.MA4RestartArrow20261003.GreenTraceInversions
