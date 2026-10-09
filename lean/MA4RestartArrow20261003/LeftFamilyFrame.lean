import MA4RestartArrow20261003.AdjacentExceptionalFrame

/-! Assemble a whole left pivot sweep from actual independent replacements
of the original neighbors through one fixed original pivot. This assembly
helper takes only local categorical replacement facts. Actual map/SES
constructors discharge those facts; no future whole frame is supplied. -/
namespace QuiverProofs.MA4RestartArrow20261003.LeftFamilyFrame
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open QuiverProofs.MA4RestartArrow20261003.AdjacentExceptionalFrame
universe w v u z
variable {K : Type w} [Field K] {C : Type u}
  [Category.{v} C] [Abelian C] [Linear K C] [HasExt.{z} C]
set_option maxHeartbeats 0

abbrev Orthogonal (X Y : C) : Prop :=
  (∀ f : X ⟶ Y, f = 0) ∧ (∀ x : Ext X Y 1, x = 0)

structure LeftReplacement (F : Fin 4 → C ⥤ ModuleCat.{v} K) (X Y Q : C) : Prop where
  rigid : ∀ x : Ext Q Q 1, x = 0
  scalarEnd : ∀ f : Q ⟶ Q, ∃ c : K, f = c • 𝟙 Q
  nonzeroId : 𝟙 Q ≠ 0
  finiteVertices : ∀ a, Module.Finite K ((F a).obj Q)
  internal : Orthogonal Q Y
  outside : ∀ T : C, Orthogonal X T → Orthogonal Y T → Orthogonal Q T
  inside : ∀ T : C, Orthogonal T X → Orthogonal T Y → Orthogonal T Q

def predecessor (j : Fin 4) : Fin 4 := ⟨j.val-1, by omega⟩

def familyObjects (M Q : Fin 4 → C) (t q : Fin 4) : Fin 4 → C := fun j =>
  if j = q then M t else if q < j ∧ j ≤ t then Q (predecessor j) else M j

/-- All reverse laws between two new replacements follow from their
local inside/outside laws and the original frame; no new-pair oracle. -/
theorem family_exceptional_frame
    (F : Fin 4 → C ⥤ ModuleCat.{v} K) (M Q : Fin 4 → C)
    (hM : ExceptionalFrame F M) (t q : Fin 4) (hqt : q ≤ t)
    (hQ : ∀ i, q ≤ i → i < t → LeftReplacement F (M i) (M t) (Q i)) :
    ExceptionalFrame F (familyObjects M Q t q) := by
  have hAt : familyObjects M Q t q q = M t := by simp [familyObjects]
  have hIn : ∀ j, q < j ∧ j ≤ t → familyObjects M Q t q j = Q (predecessor j) := by
    intro j hj; simp [familyObjects, ne_of_gt hj.1, hj]
  have hOut : ∀ j, j ≠ q → ¬ (q < j ∧ j ≤ t) → familyObjects M Q t q j = M j := by
    intro j hj hn; simp [familyObjects, hj, hn]
  have hBounds : ∀ j, q < j ∧ j ≤ t → q ≤ predecessor j ∧ predecessor j < t := by
    intro j hj; change q.val ≤ j.val-1 ∧ j.val-1 < t.val; constructor <;> omega
  have hPairs : ∀ a b, a < b →
      Orthogonal (familyObjects M Q t q b) (familyObjects M Q t q a) := by
    intro a b hab
    by_cases ha : a = q
    · subst a
      have hb : b ≠ q := by omega
      by_cases hbi : q < b ∧ b ≤ t
      · rw [hIn b hbi, hAt]
        exact (hQ _ (hBounds b hbi).1 (hBounds b hbi).2).internal
      · have htb : t < b := by omega
        rw [hOut b hb hbi, hAt]
        exact ⟨hM.reverseHom t b htb, hM.reverseExt t b htb⟩
    · by_cases hai : q < a ∧ a ≤ t
      · have hba : b ≠ q := by omega
        by_cases hbi : q < b ∧ b ≤ t
        · rw [hIn b hbi, hIn a hai]
          have hij : predecessor a < predecessor b := by change a.val-1 < b.val-1; omega
          have hat : predecessor a < t := (hBounds a hai).2
          have hfA := hQ _ (hBounds a hai).1 hat
          have hfB := hQ _ (hBounds b hbi).1 (hBounds b hbi).2
          exact hfA.inside (Q (predecessor b))
            (hfB.outside (M (predecessor a))
              ⟨hM.reverseHom _ _ hij, hM.reverseExt _ _ hij⟩
              ⟨hM.reverseHom _ _ hat, hM.reverseExt _ _ hat⟩)
            hfB.internal
        · have htb : t < b := by omega
          have hpb : predecessor a < b := by change a.val-1 < b.val; omega
          rw [hOut b hba hbi, hIn a hai]
          exact (hQ _ (hBounds a hai).1 (hBounds a hai).2).inside (M b)
            ⟨hM.reverseHom _ _ hpb, hM.reverseExt _ _ hpb⟩
            ⟨hM.reverseHom _ _ htb, hM.reverseExt _ _ htb⟩
      · by_cases hb : b = q
        · subst b
          have hat : a < t := by omega
          rw [hAt, hOut a ha hai]
          exact ⟨hM.reverseHom a t hat, hM.reverseExt a t hat⟩
        · by_cases hbi : q < b ∧ b ≤ t
          · have haq : a < q := by omega
            have hai' : a < predecessor b := by change a.val < b.val-1; omega
            have hat : a < t := by omega
            rw [hIn b hbi, hOut a ha hai]
            exact (hQ _ (hBounds b hbi).1 (hBounds b hbi).2).outside (M a)
              ⟨hM.reverseHom _ _ hai', hM.reverseExt _ _ hai'⟩
              ⟨hM.reverseHom _ _ hat, hM.reverseExt _ _ hat⟩
          · rw [hOut b hb hbi, hOut a ha hai]
            exact ⟨hM.reverseHom a b hab, hM.reverseExt a b hab⟩
  refine ⟨?_, ?_, ?_, ?_, (fun a b hab => (hPairs a b hab).1),
    (fun a b hab => (hPairs a b hab).2)⟩
  · intro a
    by_cases ha : a = q
    · rw [ha, hAt]
      exact hM.rigid t
    · by_cases hai : q < a ∧ a ≤ t
      · rw [hIn a hai]
        exact (hQ _ (hBounds a hai).1 (hBounds a hai).2).rigid
      · rw [hOut a ha hai]
        exact hM.rigid a
  · intro a
    by_cases ha : a = q
    · rw [ha, hAt]
      exact hM.scalarEnd t
    · by_cases hai : q < a ∧ a ≤ t
      · rw [hIn a hai]
        exact (hQ _ (hBounds a hai).1 (hBounds a hai).2).scalarEnd
      · rw [hOut a ha hai]
        exact hM.scalarEnd a
  · intro a
    by_cases ha : a = q
    · rw [ha, hAt]
      exact hM.nonzeroId t
    · by_cases hai : q < a ∧ a ≤ t
      · rw [hIn a hai]
        exact (hQ _ (hBounds a hai).1 (hBounds a hai).2).nonzeroId
      · rw [hOut a ha hai]
        exact hM.nonzeroId a
  · intro a b
    by_cases ha : a = q
    · rw [ha, hAt]
      exact hM.finiteVertices t b
    · by_cases hai : q < a ∧ a ≤ t
      · rw [hIn a hai]
        exact (hQ _ (hBounds a hai).1 (hBounds a hai).2).finiteVertices b
      · rw [hOut a ha hai]
        exact hM.finiteVertices a b

#print axioms family_exceptional_frame
end QuiverProofs.MA4RestartArrow20261003.LeftFamilyFrame
