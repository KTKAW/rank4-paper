import MA4RestartArrow20261003.LeftTraceBoundaryHom

/-! Full terminal same-color Hom-zero for a red fixed-pivot family. The
pivot is flipped to green only at the terminal tuple. All selected objects
retain actual chosen map/SES traces; outside inputs concern OLD objects. -/
namespace QuiverProofs.MA4RestartArrow20261003.RedFamilySameColorHom
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open QuiverProofs.MA4RestartArrow20261003.AdjacentExceptionalFrame
open QuiverProofs.MA4RestartArrow20261003.LeftFamilyFrame
open QuiverProofs.MA4RestartArrow20261003.LeftColorTraceHom
open QuiverProofs.MA4RestartArrow20261003.LeftTraceBoundaryHom
universe w v u z
variable {K : Type w} [Field K] {C : Type u}
  [Category.{v} C] [Abelian C] [Linear K C] [HasExt.{z} C] [HasFiniteBiproducts C]
set_option maxHeartbeats 0

def familyColors (c g : Fin 4 → Bool) (t q : Fin 4) : Fin 4 → Bool := fun j =>
  if j = q then true else if q < j ∧ j ≤ t then g (predecessor j) else c j

theorem terminal_same_color_hom
    (F : Fin 4 → C ⥤ ModuleCat.{v} K) (M Q : Fin 4 → C) (c g : Fin 4 → Bool)
    (hM : ExceptionalFrame F M) (t q : Fin 4) (hqt : q ≤ t) (hc : c t = false)
    (hOldBlock : ∀ a b, a < b → c a = false → c b = true → False)
    (hOldSame : ∀ a b, a < b → c a = c b → ∀ f : M a ⟶ M b, f = 0)
    (hQ : ∀ i, q ≤ i → i < t → LeftReplacement F (M i) (M t) (Q i))
    (hTrace : ∀ i, q ≤ i → i < t → LeftColorTrace (K := K) (M i) (M t) (Q i) (c i) (g i))
    (hOutsideGreen : ∀ a, a < q → c a = true → ∀ f : M a ⟶ M t, f = 0) :
    ∀ a b, a < b → familyColors c g t q a = familyColors c g t q b →
      ∀ f : familyObjects M Q t q a ⟶ familyObjects M Q t q b, f = 0 := by
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
  intro a b hab hSame
  by_cases ha : a = q
  · subst a
    have hb : b ≠ q := by omega
    by_cases hbi : q < b ∧ b ≤ t
    · have hbnd := hBounds b hbi
      have hgb : g (predecessor b) = true := by rw [hCAt, hCIn b hbi] at hSame; exact hSame.symm
      have hTr := hTrace _ hbnd.1 hbnd.2
      rw [hgb] at hTr
      rw [hAt, hIn b hbi]
      exact hom_to_green_trace (M t) _ _ _ _ hTr (hM.reverseHom _ _ hbnd.2)
    · have htb : t < b := by omega
      have hcb : c b = true := by rw [hCAt, hCOut b hb hbi] at hSame; exact hSame.symm
      exact False.elim (hOldBlock t b htb hc hcb)
  · by_cases hai : q < a ∧ a ≤ t
    · have hb : b ≠ q := by omega
      by_cases hbi : q < b ∧ b ≤ t
      · have haB := hBounds a hai; have hbB := hBounds b hbi
        have hij : predecessor a < predecessor b := by change a.val-1 < b.val-1; omega
        rw [hCIn a hai, hCIn b hbi] at hSame
        rw [hIn a hai, hIn b hbi]
        exact same_color_hom_of_left_traces _ _ _ _ _ _ _ _ _
          (hTrace _ haB.1 haB.2) (hTrace _ hbB.1 hbB.2) hSame
          (hOldBlock _ _ hij) (hOldSame _ _ hij)
          (hM.reverseHom _ _ hbB.2) (hM.reverseExt _ _ hbB.2) (hM.scalarEnd t)
          (hQ _ haB.1 haB.2).internal.1
      · have htb : t < b := by omega
        have hcb : c b = false := by
          cases h : c b with
          | false => rfl
          | true => exact False.elim (hOldBlock t b htb hc h)
        have haB := hBounds a hai
        have hib : predecessor a < b := by change a.val-1 < b.val; omega
        have hga : g (predecessor a) = false := by rw [hCIn a hai, hCOut b hb hbi, hcb] at hSame; exact hSame
        have hTr := hTrace _ haB.1 haB.2
        rw [hga] at hTr
        rw [hIn a hai, hOut b hb hbi]
        exact hom_from_red_trace _ _ _ _ _ hTr
          (hOldSame t b htb (hc.trans hcb.symm))
          (fun hi => hOldSame _ _ hib (hi.trans hcb.symm))
    · by_cases hb : b = q
      · subst b
        have haq : a < q := hab
        have hca : c a = true := by rw [hCOut a ha hai, hCAt] at hSame; exact hSame
        rw [hOut a ha hai, hAt]
        exact hOutsideGreen a haq hca
      · by_cases hbi : q < b ∧ b ≤ t
        · have haq : a < q := by omega
          have hbB := hBounds b hbi
          have haib : a < predecessor b := by change a.val < b.val-1; omega
          have hat : a < t := by omega
          rw [hCOut a ha hai, hCIn b hbi] at hSame
          rw [hOut a ha hai, hIn b hbi]
          cases hca : c a with
          | true =>
            have hgb : g (predecessor b) = true := by rw [hca] at hSame; exact hSame.symm
            have hTr := hTrace _ hbB.1 hbB.2
            rw [hgb] at hTr
            have hci := green_trace_old_green _ _ _ _ hTr
            exact hom_to_green_trace _ _ _ _ _ hTr
              (hOldSame _ _ haib (hca.trans hci.symm))
          | false =>
            have hci : c (predecessor b) = false := by
              cases h : c (predecessor b) with
              | false => rfl
              | true => exact False.elim (hOldBlock _ _ haib hca h)
            have hTr := hTrace _ hbB.1 hbB.2
            rw [hci] at hTr
            exact hom_to_old_red_trace _ _ _ _ _ hTr
              (hOldSame a t hat (hca.trans hc.symm))
              (hOldSame _ _ haib (hca.trans hci.symm))
        · rw [hCOut a ha hai, hCOut b hb hbi] at hSame
          rw [hOut a ha hai, hOut b hb hbi]
          exact hOldSame a b hab hSame

#print axioms terminal_same_color_hom
end QuiverProofs.MA4RestartArrow20261003.RedFamilySameColorHom
