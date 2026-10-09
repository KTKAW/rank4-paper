import MA4RestartArrow20261003.AdjacentExceptionalFrame
import QuiverProofs.AcyclicTargets
import QuiverProofs.MAExistenceLiterature

/-! Stable color sorting of the same four actual objects. The ordering
key retains each color's original order. Only red-before-green inversions
require the independently constructed orthogonality gate. -/
namespace QuiverProofs.MA4RestartStableColoredFrameSort
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open ProperOrder MAExistenceLiterature
open MA4RestartArrow20261003.AdjacentExceptionalFrame
set_option maxHeartbeats 0

def colorKey (g : Colors) (i : Fin 4) : Nat := if g i then i.val else 4 + i.val

private def orderMatrix (r : Fin 4 → Nat) : Matrix 4 := fun i j =>
  if r i < r j then 1 else if r j < r i then -1 else 0

private theorem ordered_permutation (r : Fin 4 → Nat) :
    ∃ p : CyclicOrder, ∀ a b : Fin 4, a < b → r (p.toFun a) ≤ r (p.toFun b) := by
  have hB : SkewSymmetric (orderMatrix r) := by
    intro i j
    by_cases h₁ : r i < r j <;> by_cases h₂ : r j < r i <;>
      simp [orderMatrix,h₁,h₂] <;> omega
  have hA : Acyclic (orderMatrix r) := by
    refine ⟨r, ?_⟩
    intro i j h
    by_cases hlt : r i < r j
    · exact hlt
    · simp [orderMatrix,hlt] at h
      split at h <;> omega
  obtain ⟨p,h01,h02,h03,h12,h13,h23⟩ :=
    AcyclicTargets.acyclic_has_topological_coordinates (orderMatrix r) hB hA
  have hUpper : ∀ a b : Fin 4, a < b → 0 ≤ orderMatrix r (p.toFun a) (p.toFun b) := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all
  refine ⟨p, ?_⟩
  intro a b hab
  have h := hUpper a b hab
  by_contra hn
  have hRev : r (p.toFun b) < r (p.toFun a) := by omega
  have hNot : ¬ r (p.toFun a) < r (p.toFun b) := by omega
  simp [orderMatrix,hNot,hRev] at h

/-- All sixteen color patterns have a stable green-before-red order. -/
theorem stable_color_permutation (g : Colors) :
    ∃ p : CyclicOrder, GreenBeforeRed g p ∧
      (∀ a b : Fin 4, a < b → g (p.toFun a) = g (p.toFun b) → p.toFun a < p.toFun b) ∧
      (∀ a b : Fin 4, a < b → p.toFun b < p.toFun a →
        g (p.toFun b) = false ∧ g (p.toFun a) = true) := by
  obtain ⟨p,hp⟩ := ordered_permutation (colorKey g)
  have hStable : ∀ a b : Fin 4, a < b →
      g (p.toFun a) = g (p.toFun b) → p.toFun a < p.toFun b := by
    intro a b hab hColor
    have h := hp a b hab
    have hNe : p.toFun a ≠ p.toFun b := fun h => (ne_of_lt hab) (p.injective h)
    cases hca : g (p.toFun a) <;> cases hcb : g (p.toFun b) <;>
      simp only [hca,hcb] at hColor <;> try contradiction
    all_goals simp only [colorKey,hca,hcb,Bool.false_eq_true,↓reduceIte] at h
    all_goals omega
  refine ⟨p, ?_, hStable, ?_⟩
  · intro i j hi hj
    by_contra h
    have hNe : p.invFun i ≠ p.invFun j := by
      intro hEq
      have hSame := congrArg p.toFun hEq
      simp only [p.right_inv] at hSame
      rw [hSame,hj] at hi
      contradiction
    have hRev : p.invFun j < p.invFun i := by omega
    have hk := hp (p.invFun j) (p.invFun i) hRev
    simp only [p.right_inv,colorKey,hi,hj,Bool.false_eq_true,↓reduceIte] at hk
    have hI := i.isLt
    omega
  · intro a b hab hInv
    have hKey := hp a b hab
    cases hca : g (p.toFun a) <;> cases hcb : g (p.toFun b)
    · have hForward := hStable a b hab (by rw [hca,hcb])
      omega
    · simp only [colorKey,hca,hcb,Bool.false_eq_true,↓reduceIte] at hKey
      have hb := (p.toFun b).isLt
      omega
    · exact ⟨rfl,rfl⟩
    · have hForward := hStable a b hab (by rw [hca,hcb])
      omega

universe w v u z
variable {K : Type w} [Field K] {C : Type u}
  [Category.{v} C] [Abelian C] [Linear K C] [HasExt.{z} C]

/-- Sorting constructs the new frame with the same actual objects. All
same-color forward Hom constraints survive because their order is stable. -/
theorem stable_sort_actual_colored_frame
    (F : Fin 4 → C ⥤ ModuleCat.{v} K) (M : Fin 4 → C)
    (hM : ExceptionalFrame F M) (g : Colors)
    (hSame : ∀ a b : Fin 4, a < b → g a = g b → ∀ f : M a ⟶ M b, f = 0)
    (hInversions : ∀ a b : Fin 4, a < b → g a = false → g b = true →
      (∀ f : M a ⟶ M b, f = 0) ∧ (∀ e : Ext (M a) (M b) 1, e = 0)) :
    ∃ p : CyclicOrder, GreenBeforeRed g p ∧
      ExceptionalFrame F (fun a => M (p.toFun a)) ∧
      (∀ a b : Fin 4, a < b → g (p.toFun a) = g (p.toFun b) →
        ∀ f : M (p.toFun a) ⟶ M (p.toFun b), f = 0) := by
  obtain ⟨p,hBlock,hStable,hFlip⟩ := stable_color_permutation g
  have hReverse : ∀ a b : Fin 4, a < b →
      (∀ f : M (p.toFun b) ⟶ M (p.toFun a), f = 0) ∧
      (∀ e : Ext (M (p.toFun b)) (M (p.toFun a)) 1, e = 0) := by
    intro a b hab
    by_cases hOrder : p.toFun a < p.toFun b
    · exact ⟨hM.reverseHom _ _ hOrder,hM.reverseExt _ _ hOrder⟩
    · have hNe : p.toFun a ≠ p.toFun b := fun h => (ne_of_lt hab) (p.injective h)
      have hInv : p.toFun b < p.toFun a := by omega
      have hc := hFlip a b hab hInv
      exact hInversions _ _ hInv hc.1 hc.2
  refine ⟨p,hBlock,?_,?_⟩
  · exact ⟨fun a => hM.rigid (p.toFun a),fun a => hM.scalarEnd (p.toFun a),
      fun a => hM.nonzeroId (p.toFun a),fun a b => hM.finiteVertices (p.toFun a) b,
      fun a b h => (hReverse a b h).1,fun a b h => (hReverse a b h).2⟩
  · intro a b hab hColor
    exact hSame _ _ (hStable a b hab hColor) hColor

#check stable_sort_actual_colored_frame
#print axioms stable_color_permutation
#print axioms stable_sort_actual_colored_frame
end QuiverProofs.MA4RestartStableColoredFrameSort
