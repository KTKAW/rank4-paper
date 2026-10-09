import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Ring

/-! The c>0,d>b second-high incident wall in a cyclic selected triangle
has only b=1,d=2 under actual connected scalar/Pfaffian bounds. The
opposite second-high wall is excluded by elementary third-ceiling geometry. -/
namespace QuiverProofs.Rank4StructureRound2.UnitN2PositiveScalar
set_option maxHeartbeats 8000000

def scalar (b m c u F : Int) : Int :=
  1+b^2+b*m+m^2-(b-2)*F^2-m*F*u-c*u
def pf (b m u F : Int) : Int := (m+1)*F-(b+m)*u

theorem incident_wall_shape (b m c u F : Int)
    (hb : 1≤b) (hm : 1≤m) (hc : 1≤c) (hu : 1≤u)
    (hdF : b+m≤F-1) (hWall : c+u=F) (hceil : m*u≤2*F)
    (hM : 3≤scalar b m c u F)
    (hNecessary : 2*abs (pf b m u F)≤scalar b m c u F)
    (hBudget : scalar b m c u F≤F-1) : b=1 ∧ m=1 := by
  have hF : 3≤F := by omega
  have hb2 : b≤2 := by
    by_contra hh
    have hb3 : 3≤b := by omega
    have hscale:=mul_nonneg (show 0≤b-3 by omega) (sq_nonneg F)
    have hmf:=mul_nonneg (show 0≤m by omega) (show 0≤F by omega)
    have hmfU:=mul_nonneg hmf (show 0≤u-1 by omega)
    have hcu : 1≤c*u := by nlinarith [mul_nonneg (show 0≤c-1 by omega) (show 0≤u-1 by omega)]
    have hF2 : (b+m)^2≤F^2 := by nlinarith
    have hmF : m*(b+m)≤m*F := by nlinarith
    unfold scalar at hM
    nlinarith
  have hb1 : b=1 := by
    by_contra hh
    have h2 : b=2 := by omega
    have hprod:=mul_nonneg (show 0≤u-1 by omega)
      (show 0≤(m+1)*F-u-1 by nlinarith [mul_nonneg (show 0≤m by omega) (show 0≤F by omega)])
    have hprod2:=mul_nonneg (show 0≤m+1 by omega) (show 0≤F-m-3 by omega)
    have heq : scalar 2 m c u F=
        6+2*m+m^2-(m+1)*F-(u-1)*((m+1)*F-u-1) := by
      unfold scalar
      rw [←hWall]
      ring
    rw [h2,heq] at hM
    nlinarith
  subst b
  have hpf : pf 1 m u F=(m+1)*c := by unfold pf;nlinarith
  rw [hpf,abs_of_nonneg (by nlinarith)] at hNecessary
  have hSmall : 2*(m+1)*c≤F-1 := by nlinarith
  have huLarge : (2*m+1)*c+1≤u := by nlinarith
  have hm2 : m≤2 := by
    by_contra hh
    have hm3 : 3≤m := by omega
    have hLowU:=mul_nonneg (show 0≤m-3 by omega) (show 0≤u by omega)
    have hLowC:=mul_nonneg (show 0≤2*m-6 by omega) (show 0≤c by omega)
    nlinarith
  have hm1 : m=1 := by
    by_contra hh
    have hmEq : m=2 := by omega
    have hu6 : 6≤u := by rw [hmEq] at huLarge;nlinarith
    have huc : 6≤u*c := by nlinarith [mul_nonneg (show 0≤u-6 by omega) (show 0≤c-1 by omega)]
    have hSquare : c^2≤u^2 := by nlinarith
    have hEq : scalar 1 2 c u F=8+c^2-u*F := by unfold scalar;rw [←hWall];ring
    rw [hmEq,hEq] at hM
    nlinarith
  exact ⟨rfl,hm1⟩

theorem opposite_wall_impossible (m c u F : Int)
    (hm : 1≤m) (hc : 1≤c) (hu : 1≤u) (huF : u≤F-1)
    (hWall : m*u=2*F) (hThird : -(F)≤u-m*F) : False := by
  have hF : 2≤F := by omega
  have hm2 : 2≤m := by
    by_contra hh
    have h1 : m=1 := by omega
    rw [h1] at hWall
    nlinarith
  nlinarith [mul_nonneg (show 0≤m-2 by omega) (show 0≤F by omega)]

#print axioms incident_wall_shape
#print axioms opposite_wall_impossible
end QuiverProofs.Rank4StructureRound2.UnitN2PositiveScalar
