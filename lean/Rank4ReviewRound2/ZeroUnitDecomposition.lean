import Rank4CoordinatorR2.ZeroSquareMarkov
import Mathlib.Tactic.Linarith

/-! Exact integer structure of the remaining b=1 square-overflow cone.
This is a reduction of hypotheses and invariants, not an MA/NMA theorem.
-/
namespace Rank4ReviewRound2.ZeroUnitDecomposition
open QuiverProofs Rank4CoordinatorR2

def triangleMarkov (c d e : Int) : Int := c*c+d*d+e*e-c*d*e

theorem zero_unit_overflow_decomposition (c d e f : Int) (H : Nat)
    (hc : 0<c) (hd : 0<d) (he : 0<e)
    (hcH : c≤(H:Int)) (hdH : d≤(H:Int)) (heH : e≤(H:Int))
    (huH : f-c≤(H:Int)) (hvH : d*e-f≤(H:Int))
    (hf : (H:Int)<f) (hover : f+(H:Int)<c+d*e) :
    ∃ u v : Int,
      u=f-c ∧ v=d*e-f ∧ 0<u ∧ 0<v ∧ 2≤d ∧ 2≤e ∧
      u≤(H:Int) ∧ v≤(H:Int) ∧ d*e=c+u+v ∧
      f=c+u ∧ (H:Int)<c+u ∧ (H:Int)<c+v ∧
      zeroMarkov 1 c d e f=triangleMarkov c d e+1-u*v ∧
      triangleMarkov c d e=triangleMarkov (u+v) d e ∧
      Algebra.pfaffian 0 1 (-c) d (-e) f=e-c*d := by
  have hq : f<d*e := by omega
  have hd2 : 2≤d := by
    by_contra h
    have hd1 : d=1 := by omega
    rw [hd1] at hq
    simp only [one_mul] at hq
    omega
  have he2 : 2≤e := by
    by_contra h
    have he1 : e=1 := by omega
    rw [he1] at hq
    simp only [mul_one] at hq
    omega
  refine ⟨f-c,d*e-f,rfl,rfl,by omega,by omega,hd2,he2,huH,hvH,
    by ring,by ring,by omega,by omega,?_,?_,?_⟩
  · unfold zeroMarkov triangleMarkov
    ring
  · unfold triangleMarkov
    ring
  · unfold Algebra.pfaffian
    ring

theorem zero_unit_markov_below_triangle (c d e u v : Int)
    (hu : 0<u) (hv : 0<v) (hde : d*e=c+u+v) :
    zeroMarkov 1 c d e (c+u)≤triangleMarkov c d e := by
  have hid : zeroMarkov 1 c d e (c+u)=triangleMarkov c d e+1-u*v := by
    unfold zeroMarkov triangleMarkov
    nlinarith [hde]
  have huv : 1≤u*v := by
    have h := mul_nonneg (show 0≤u-1 by omega) (show 0≤v-1 by omega)
    nlinarith [h]
  omega

#print axioms zero_unit_overflow_decomposition
#print axioms zero_unit_markov_below_triangle
end Rank4ReviewRound2.ZeroUnitDecomposition
