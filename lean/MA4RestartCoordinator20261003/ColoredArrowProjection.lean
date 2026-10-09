import QuiverProofs.MAExistenceCompanions
import QuiverProofs.MAExistenceLiterature

/-! Project the arrow rule from a colored actual-frame interface. Upper
Euler orthogonality, the color block and same-color nonpositive Euler data
are current facts to be constructed by the separate history induction. -/
namespace QuiverProofs.MA4RestartColoredArrowProjection
open MAExistenceLiterature MAExistenceCompanions ProperOrder
set_option maxHeartbeats 0

/-- This projection uses no arrow rule or cycle admissibility premise. -/
theorem arrowSigns_of_colored_upper_euler
    (B A E : Matrix 4) (g : Colors) (hB : SkewSymmetric B)
    (p : CyclicOrder)
    (hSym : ∀ i j, E i j + E j i = A i j)
    (hSkew : ∀ i j, E i j - E j i = -B i j)
    (hUpper : ∀ a b : Fin 4, a < b → E (p.toFun b) (p.toFun a) = 0)
    (hSame : ∀ a b : Fin 4, a < b → g (p.toFun a) = g (p.toFun b) →
      E (p.toFun a) (p.toFun b) ≤ 0)
    (hBlock : GreenBeforeRed g p) : ArrowSigns B A g := by
  intro i j hBij
  have hij : i ≠ j := by
    intro h
    subst j
    have hd := hB i i
    omega
  have hPosNe : p.invFun i ≠ p.invFun j := by
    intro h
    have he := congrArg p.toFun h
    simp only [p.right_inv] at he
    exact hij he
  have hs := hSym i j
  have hk := hSkew i j
  by_cases hBefore : p.invFun i < p.invFun j
  · have hz : E j i = 0 := by
      simpa only [p.right_inv] using hUpper (p.invFun i) (p.invFun j) hBefore
    have hA : A i j < 0 := by omega
    constructor
    · intro h
      omega
    · rintro ⟨hi,hj⟩
      have hReverse := hBlock j i hj hi
      omega
  · have hReverse : p.invFun j < p.invFun i := by omega
    have hz : E i j = 0 := by
      simpa only [p.right_inv] using hUpper (p.invFun j) (p.invFun i) hReverse
    have hA : 0 < A i j := by omega
    have hDiff : g i ≠ g j := by
      intro he
      have hNonpos := hSame (p.invFun j) (p.invFun i) hReverse
        (by simpa only [p.right_inv] using he.symm)
      simp only [p.right_inv] at hNonpos
      omega
    have hColors : g i = false ∧ g j = true := by
      cases hi : g i <;> cases hj : g j
      · exact False.elim (hDiff (by rw [hi,hj]))
      · exact ⟨rfl,rfl⟩
      · have hBad := hBlock i j hi hj
        omega
      · exact False.elim (hDiff (by rw [hi,hj]))
    exact ⟨fun _ => hColors, fun _ => hA⟩

#check arrowSigns_of_colored_upper_euler
#print axioms arrowSigns_of_colored_upper_euler
end QuiverProofs.MA4RestartColoredArrowProjection
