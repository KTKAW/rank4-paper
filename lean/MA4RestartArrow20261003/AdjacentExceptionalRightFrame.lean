import MA4RestartArrow20261003.AdjacentExceptionalFrame

/-! Whole right adjacent frame assembly. The construction theorem will
derive these actual replacement fields; this helper takes precisely its
internal and outside gates and preserves every old frame object. -/
namespace QuiverProofs.MA4RestartArrow20261003.AdjacentExceptionalRightFrame
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open QuiverProofs.MA4RestartArrow20261003.AdjacentExceptionalFrame
universe w v u z
variable {K : Type w} [Field K] {C : Type u}
  [Category.{v} C] [Abelian C] [Linear K C] [HasExt.{z} C]
set_option maxHeartbeats 0

def rightObjects (M : Fin 4 → C) (t : Fin 4) (Q : C) : Fin 4 → C := fun j =>
  if j = t then Q else if j = t+1 then M t else M j

theorem frame_rightObjects
    (F : Fin 4 → C ⥤ ModuleCat.{v} K) (M : Fin 4 → C)
    (hM : ExceptionalFrame F M) (t : Fin 4) (ht : t < 3) (Q : C)
    (hRigid : ∀ x : Ext Q Q 1, x = 0)
    (hEnd : ∀ g : Q ⟶ Q, ∃ c : K, g = c • 𝟙 Q)
    (hId : 𝟙 Q ≠ 0) (hFinite : ∀ a, Module.Finite K ((F a).obj Q))
    (hInternal : (∀ g : M t ⟶ Q, g = 0) ∧ (∀ x : Ext (M t) Q 1, x = 0))
    (hOutside : ∀ T : C,
      ((∀ g : M t ⟶ T, g = 0) ∧ (∀ x : Ext (M t) T 1, x = 0)) →
      ((∀ g : M (t+1) ⟶ T, g = 0) ∧ (∀ x : Ext (M (t+1)) T 1, x = 0)) →
      ((∀ g : Q ⟶ T, g = 0) ∧ (∀ x : Ext Q T 1, x = 0)))
    (hInside : ∀ T : C,
      ((∀ g : T ⟶ M t, g = 0) ∧ (∀ x : Ext T (M t) 1, x = 0)) →
      ((∀ g : T ⟶ M (t+1), g = 0) ∧ (∀ x : Ext T (M (t+1)) 1, x = 0)) →
      ((∀ g : T ⟶ Q, g = 0) ∧ (∀ x : Ext T Q 1, x = 0))) :
    ExceptionalFrame F (rightObjects M t Q) := by
  have ht1 : t < t+1 := by fin_cases t <;> simp_all
  have hAt : rightObjects M t Q t = Q := by simp [rightObjects]
  have hNext : rightObjects M t Q (t+1) = M t := by simp [rightObjects, ne_of_gt ht1]
  have hElse : ∀ a, a ≠ t → a ≠ t+1 → rightObjects M t Q a = M a := by
    intro a ha hb; simp [rightObjects, ha, hb]
  have hPairs : ∀ a b, a < b →
      (∀ g : rightObjects M t Q b ⟶ rightObjects M t Q a, g = 0) ∧
      (∀ x : Ext (rightObjects M t Q b) (rightObjects M t Q a) 1, x = 0) := by
    intro a b hab
    have htval : (t+1).val = t.val + 1 := by fin_cases t <;> simp_all
    by_cases ha : a = t
    · subst a
      have hb : b ≠ t := by omega
      by_cases hb1 : b = t+1
      · rw [hb1, hNext, hAt]
        exact hInternal
      · have htb : t+1 < b := by omega
        rw [hElse b hb hb1, hAt]
        exact hInside (M b)
          ⟨hM.reverseHom t b (by omega), hM.reverseExt t b (by omega)⟩
          ⟨hM.reverseHom (t+1) b htb, hM.reverseExt (t+1) b htb⟩
    · by_cases ha1 : a = t+1
      · subst a
        have hb : b ≠ t := by omega
        have hb1 : b ≠ t+1 := by omega
        rw [hElse b hb hb1, hNext]
        exact ⟨hM.reverseHom t b (by omega), hM.reverseExt t b (by omega)⟩
      · by_cases hb : b = t
        · subst b
          rw [hAt, hElse a ha ha1]
          exact hOutside (M a)
            ⟨hM.reverseHom a t hab, hM.reverseExt a t hab⟩
            ⟨hM.reverseHom a (t+1) (by omega), hM.reverseExt a (t+1) (by omega)⟩
        · by_cases hb1 : b = t+1
          · subst b
            rw [hNext, hElse a ha ha1]
            exact ⟨hM.reverseHom a t (by omega), hM.reverseExt a t (by omega)⟩
          · rw [hElse b hb hb1, hElse a ha ha1]
            exact ⟨hM.reverseHom a b hab, hM.reverseExt a b hab⟩
  refine ⟨?_, ?_, ?_, ?_, (fun a b hab => (hPairs a b hab).1),
    (fun a b hab => (hPairs a b hab).2)⟩
  · intro a
    by_cases ha : a = t
    · rw [ha, hAt]; exact hRigid
    · by_cases hb : a = t+1
      · rw [hb, hNext]; exact hM.rigid t
      · rw [hElse a ha hb]; exact hM.rigid a
  · intro a
    by_cases ha : a = t
    · rw [ha, hAt]; exact hEnd
    · by_cases hb : a = t+1
      · rw [hb, hNext]; exact hM.scalarEnd t
      · rw [hElse a ha hb]; exact hM.scalarEnd a
  · intro a
    by_cases ha : a = t
    · rw [ha, hAt]; exact hId
    · by_cases hb : a = t+1
      · rw [hb, hNext]; exact hM.nonzeroId t
      · rw [hElse a ha hb]; exact hM.nonzeroId a
  · intro a b
    by_cases ha : a = t
    · rw [ha, hAt]; exact hFinite b
    · by_cases hb : a = t+1
      · rw [hb, hNext]; exact hM.finiteVertices t b
      · rw [hElse a ha hb]; exact hM.finiteVertices a b

#print axioms frame_rightObjects
end QuiverProofs.MA4RestartArrow20261003.AdjacentExceptionalRightFrame
