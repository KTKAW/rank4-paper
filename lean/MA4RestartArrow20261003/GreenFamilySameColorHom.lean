import MA4RestartArrow20261003.RightTraceBoundaryHom
namespace QuiverProofs.MA4RestartArrow20261003.GreenFamilySameColorHom
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open QuiverProofs.MA4RestartArrow20261003.AdjacentExceptionalFrame
open QuiverProofs.MA4RestartArrow20261003.RightFamilyFrame
open QuiverProofs.MA4RestartArrow20261003.RightTraceBoundaryHom
open QuiverProofs.MA4RestartRightColorTraceHom
universe w v u z
variable {K : Type w} [Field K] {C : Type u}
  [Category.{v} C] [Abelian C] [Linear K C] [HasExt.{z} C] [HasFiniteBiproducts C]
set_option maxHeartbeats 0

def rightFamilyColors (c g : Fin 4 → Bool) (t q : Fin 4) : Fin 4 → Bool := fun j =>
  if j = q then false else if t ≤ j ∧ j < q then g (successor j) else c j

theorem terminal_same_color_hom
    (F : Fin 4 → C ⥤ ModuleCat.{v} K) (M Q : Fin 4 → C) (c g : Fin 4 → Bool)
    (hM : ExceptionalFrame F M) (t q : Fin 4) (htq : t ≤ q) (hc : c t = true)
    (hOldBlock : ∀ a b, a < b → c a = false → c b = true → False)
    (hOldSame : ∀ a b, a < b → c a = c b → ∀ f : M a ⟶ M b, f = 0)
    (hQ : ∀ i, t < i → i ≤ q → RightReplacement F (M t) (M i) (Q i))
    (hTrace : ∀ i, t < i → i ≤ q → RightColorTrace (K := K) (M i) (M t) (Q i) (c i) (g i))
    (hOutsideRed : ∀ b, q < b → c b = false → ∀ f : M t ⟶ M b, f = 0) :
    ∀ a b, a < b → rightFamilyColors c g t q a = rightFamilyColors c g t q b →
      ∀ f : rightFamilyObjects M Q t q a ⟶ rightFamilyObjects M Q t q b, f = 0 := by
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
  intro a b hab hSame
  by_cases ha : a = q
  · subst a
    have hb : b ≠ q := by omega
    have hbi : ¬ (t ≤ b ∧ b < q) := by omega
    have hcb : c b = false := by rw [hCAt,hCOut b hb hbi] at hSame; exact hSame.symm
    rw [hAt,hOut b hb hbi]
    exact hOutsideRed b hab hcb
  · by_cases hai : t ≤ a ∧ a < q
    · have haB := hBounds a hai
      by_cases hb : b = q
      · subst b
        have hga : g (successor a) = false := by rw [hCIn a hai,hCAt] at hSame; exact hSame
        have hTr := hTrace _ haB.1 haB.2; rw [hga] at hTr
        rw [hIn a hai,hAt]
        exact hom_from_red_trace _ _ _ _ _ hTr (hM.reverseHom t _ haB.1)
      · by_cases hbi : t ≤ b ∧ b < q
        · have hbB := hBounds b hbi
          have hij : successor a < successor b := by
            change (successor a).val < (successor b).val
            rw [hSucc a (by omega),hSucc b (by omega)]; omega
          rw [hCIn a hai,hCIn b hbi] at hSame
          rw [hIn a hai,hIn b hbi]
          exact same_color_hom_of_right_traces _ _ _ _ _ _ _ _ _
            (hTrace _ haB.1 haB.2) (hTrace _ hbB.1 hbB.2) hSame
            (hOldBlock _ _ hij) (hOldSame _ _ hij)
            (hM.reverseExt t _ haB.1) (fun _ => hM.reverseHom t _ haB.1)
            (hM.scalarEnd t) (hQ _ hbB.1 hbB.2).internal.1
        · have hqb : q < b := by omega
          have hib : successor a < b := by
            change (successor a).val < b.val
            rw [hSucc a (by omega)]; omega
          rw [hCIn a hai,hCOut b hb hbi] at hSame
          rw [hIn a hai,hOut b hb hbi]
          cases hcb : c b with
          | false =>
            have hga : g (successor a) = false := by rw [hcb] at hSame; exact hSame
            have hTr := hTrace _ haB.1 haB.2; rw [hga] at hTr
            have hci := red_trace_old_red _ _ _ _ hTr
            exact hom_from_red_trace _ _ _ _ _ hTr (hOldSame _ _ hib (hci.trans hcb.symm))
          | true =>
            have hci : c (successor a) = true := by
              cases h : c (successor a) with
              | true => rfl
              | false => exact False.elim (hOldBlock _ _ hib h hcb)
            have hTr := hTrace _ haB.1 haB.2; rw [hci] at hTr
            exact hom_from_old_green_trace _ _ _ _ _ hTr
              (hOldSame _ _ hib (hci.trans hcb.symm))
              (hOldSame t b (by omega) (hc.trans hcb.symm))
    · by_cases hb : b = q
      · subst b
        have hat : a < t := by omega
        have hca : c a = false := by rw [hCOut a ha hai,hCAt] at hSame; exact hSame
        exact False.elim (hOldBlock a t hat hca hc)
      · by_cases hbi : t ≤ b ∧ b < q
        · have hat : a < t := by omega
          have hbB := hBounds b hbi
          have hca : c a = true := by
            cases h : c a with
            | true => rfl
            | false => exact False.elim (hOldBlock a t hat h hc)
          have hgb : g (successor b) = true := by
            rw [hCOut a ha hai,hCIn b hbi,hca] at hSame; exact hSame.symm
          have hTr := hTrace _ hbB.1 hbB.2; rw [hgb] at hTr
          rw [hOut a ha hai,hIn b hbi]
          exact hom_to_green_trace _ _ _ _ _ hTr
            (hOldSame a t hat (hca.trans hc.symm))
            (fun hi => hOldSame a _ (by omega) (hca.trans hi.symm))
        · rw [hCOut a ha hai,hCOut b hb hbi] at hSame
          rw [hOut a ha hai,hOut b hb hbi]
          exact hOldSame a b hab hSame

#print axioms terminal_same_color_hom
end QuiverProofs.MA4RestartArrow20261003.GreenFamilySameColorHom
