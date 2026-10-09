import MA4RestartArrow20261003.LeftFamilyFrame

/-! Whole fixed-green-pivot right family from actual local replacements of
original neighbors. All new-new reverse laws are derived from the old
frame and actual primitive inside/outside/internal facts. -/
namespace QuiverProofs.MA4RestartArrow20261003.RightFamilyFrame
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open QuiverProofs.MA4RestartArrow20261003.AdjacentExceptionalFrame
open QuiverProofs.MA4RestartArrow20261003.LeftFamilyFrame
universe w v u z
variable {K : Type w} [Field K] {C : Type u}
  [Category.{v} C] [Abelian C] [Linear K C] [HasExt.{z} C]
set_option maxHeartbeats 0

structure RightReplacement (F : Fin 4 → C ⥤ ModuleCat.{v} K) (X Y Q : C) : Prop where
  rigid : ∀ x : Ext Q Q 1, x = 0
  scalarEnd : ∀ f : Q ⟶ Q, ∃ c : K, f = c • 𝟙 Q
  nonzeroId : 𝟙 Q ≠ 0
  finiteVertices : ∀ a, Module.Finite K ((F a).obj Q)
  internal : Orthogonal X Q
  outside : ∀ T : C, Orthogonal X T → Orthogonal Y T → Orthogonal Q T
  inside : ∀ T : C, Orthogonal T X → Orthogonal T Y → Orthogonal T Q

def successor (j : Fin 4) : Fin 4 := j+1

def rightFamilyObjects (M Q : Fin 4 → C) (t q : Fin 4) : Fin 4 → C := fun j =>
  if j = q then M t else if t ≤ j ∧ j < q then Q (successor j) else M j

theorem right_family_exceptional_frame
    (F : Fin 4 → C ⥤ ModuleCat.{v} K) (M Q : Fin 4 → C)
    (hM : ExceptionalFrame F M) (t q : Fin 4) (htq : t ≤ q)
    (hQ : ∀ i, t < i → i ≤ q → RightReplacement F (M t) (M i) (Q i)) :
    ExceptionalFrame F (rightFamilyObjects M Q t q) := by
  have hAt : rightFamilyObjects M Q t q q = M t := by simp [rightFamilyObjects]
  have hIn : ∀ j, t ≤ j ∧ j < q → rightFamilyObjects M Q t q j = Q (successor j) := by
    intro j hj; simp [rightFamilyObjects, ne_of_lt hj.2, hj]
  have hOut : ∀ j, j ≠ q → ¬ (t ≤ j ∧ j < q) → rightFamilyObjects M Q t q j = M j := by
    intro j hj hn; simp [rightFamilyObjects, hj, hn]
  have hSucc : ∀ j, j < 3 → (successor j).val = j.val+1 := by
    intro j hj; fin_cases j <;> simp_all [successor]
  have hBounds : ∀ j, t ≤ j ∧ j < q → t < successor j ∧ successor j ≤ q := by
    intro j hj; have hv := hSucc j (by omega); constructor <;> omega
  have hPairs : ∀ a b, a < b →
      Orthogonal (rightFamilyObjects M Q t q b) (rightFamilyObjects M Q t q a) := by
    intro a b hab
    by_cases ha : a = q
    · subst a
      have hb : b ≠ q := by omega
      have hbi : ¬ (t ≤ b ∧ b < q) := by omega
      have htb : t < b := by omega
      rw [hOut b hb hbi, hAt]
      exact ⟨hM.reverseHom t b htb,hM.reverseExt t b htb⟩
    · by_cases hai : t ≤ a ∧ a < q
      · by_cases hb : b = q
        · subst b
          rw [hAt,hIn a hai]
          exact (hQ _ (hBounds a hai).1 (hBounds a hai).2).internal
        · by_cases hbi : t ≤ b ∧ b < q
          · have haB := hBounds a hai; have hbB := hBounds b hbi
            have hva := hSucc a (by omega); have hvb := hSucc b (by omega)
            have hij : successor a < successor b := by omega
            rw [hIn b hbi,hIn a hai]
            have hQa := hQ _ haB.1 haB.2; have hQb := hQ _ hbB.1 hbB.2
            exact hQb.outside (Q (successor a)) hQa.internal
              (hQa.inside (M (successor b))
                ⟨hM.reverseHom t _ hbB.1,hM.reverseExt t _ hbB.1⟩
                ⟨hM.reverseHom _ _ hij,hM.reverseExt _ _ hij⟩)
          · have hqb : q < b := by omega
            have htb : t < b := by omega
            have hib : successor a < b := by have hv := hSucc a (by omega); omega
            rw [hOut b hb hbi,hIn a hai]
            exact (hQ _ (hBounds a hai).1 (hBounds a hai).2).inside (M b)
              ⟨hM.reverseHom t b htb,hM.reverseExt t b htb⟩
              ⟨hM.reverseHom _ _ hib,hM.reverseExt _ _ hib⟩
      · by_cases hb : b = q
        · subst b
          have hat : a < t := by omega
          rw [hAt,hOut a ha hai]
          exact ⟨hM.reverseHom a t hat,hM.reverseExt a t hat⟩
        · by_cases hbi : t ≤ b ∧ b < q
          · have hat : a < t := by omega
            have hbB := hBounds b hbi
            have haib : a < successor b := by have hv := hSucc b (by omega); omega
            rw [hIn b hbi,hOut a ha hai]
            exact (hQ _ hbB.1 hbB.2).outside (M a)
              ⟨hM.reverseHom a t hat,hM.reverseExt a t hat⟩
              ⟨hM.reverseHom _ _ haib,hM.reverseExt _ _ haib⟩
          · rw [hOut b hb hbi,hOut a ha hai]
            exact ⟨hM.reverseHom a b hab,hM.reverseExt a b hab⟩
  refine ⟨?_,?_,?_,?_,(fun a b hab => (hPairs a b hab).1),(fun a b hab => (hPairs a b hab).2)⟩
  · intro a
    by_cases ha : a = q
    · rw [ha,hAt]
      exact hM.rigid t
    · by_cases hai : t ≤ a ∧ a < q
      · rw [hIn a hai]
        exact (hQ _ (hBounds a hai).1 (hBounds a hai).2).rigid
      · rw [hOut a ha hai]
        exact hM.rigid a
  · intro a
    by_cases ha : a = q
    · rw [ha,hAt]
      exact hM.scalarEnd t
    · by_cases hai : t ≤ a ∧ a < q
      · rw [hIn a hai]
        exact (hQ _ (hBounds a hai).1 (hBounds a hai).2).scalarEnd
      · rw [hOut a ha hai]
        exact hM.scalarEnd a
  · intro a
    by_cases ha : a = q
    · rw [ha,hAt]
      exact hM.nonzeroId t
    · by_cases hai : t ≤ a ∧ a < q
      · rw [hIn a hai]
        exact (hQ _ (hBounds a hai).1 (hBounds a hai).2).nonzeroId
      · rw [hOut a ha hai]
        exact hM.nonzeroId a
  · intro a b
    by_cases ha : a = q
    · rw [ha,hAt]
      exact hM.finiteVertices t b
    · by_cases hai : t ≤ a ∧ a < q
      · rw [hIn a hai]
        exact (hQ _ (hBounds a hai).1 (hBounds a hai).2).finiteVertices b
      · rw [hOut a ha hai]
        exact hM.finiteVertices a b

#print axioms right_family_exceptional_frame
end QuiverProofs.MA4RestartArrow20261003.RightFamilyFrame
