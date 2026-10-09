import Rank4CoordinatorR2.UnitThreeScalar

/-! Geometry for the three-high unit-prefix branch. This module isolates
the opposite-edge escape and its normalized positive column shape. -/
namespace Rank4CoordinatorR2.UnitThreeGeometry
open QuiverProofs Rank4Coordinator Rank4CoordinatorR2 Rank4Round2
set_option maxHeartbeats 4000000
def pos (x : Int) : Int := max x 0
def neg (x : Int) : Int := max (-x) 0
def R (x y d E f : Int) : Matrix 4 := ofSix 1 x y d (-E) f
def g (x d : Int) : Int := x+neg (d-neg x)
def top (x y d E f : Int) : Int :=
  f+correction (-x) y-pos (d-neg x)*(E+neg y)-neg (g x d)*(E+pos y)

theorem pos_neg (x : Int) : pos x=x+neg x := by unfold pos neg;omega

theorem three_column (x y d E f : Int) :
    applyWord (R x y d E f) [0,1,0] 0 2=g x d ∧
    applyWord (R x y d E f) [0,1,0] 1 2= -d+neg x-pos (g x d) := by
  constructor <;> simp [R,applyWord,mutate,ofSix,correction,g,pos,neg] <;> ring

theorem three_other_column (x y d E f : Int) (hE : 1≤E) :
    applyWord (R x y d E f) [0,1,0] 0 3=E+pos y ∧
    applyWord (R x y d E f) [0,1,0] 1 3= -y := by
  have hn := le_max_right (-y) (0:Int)
  have ha : 0≤E+neg y := by unfold neg;omega
  have hb : -E-neg y≤0 := by omega
  constructor <;>
    simp [R,applyWord,mutate,ofSix,correction,pos,neg,
      max_eq_left ha,max_eq_right hb] <;>
    omega

theorem three_top (x y d E f : Int) (hE : 1≤E) :
    applyWord (R x y d E f) [0,1,0] 2 3=top x y d E f := by
  have ha : max (max (-y) 0+E) 0=max (-y) 0+E := by omega
  have hb : max (-max (-y) 0-E) 0=0 := by omega
  have hc : max (-y-(max (-y) 0+E)) 0=0 := by omega
  have hd : max (y+(max (-y) 0+E)) 0=E+max y 0 := by omega
  simp only [R,applyWord,mutate,ofSix]
  simp [correction,top,g,pos,neg,ha,hb,hc,hd]
  simp only [show max (-E+ -max (-y) 0) 0=0 by omega,
    show max (-y+(-E+ -max (-y) 0)) 0=0 by omega,
    show max (max (-y) 0+E+y) 0=E+max y 0 by omega]
  ring

theorem alternate_column_bounded (x d F : Int)
    (hx : -F+1≤x ∧ x≤F-1) (hd : -F+1≤d ∧ d≤F-1)
    (hT : -F≤ -d+neg x-pos (g x d) ∧ -d+neg x-pos (g x d)≤F) :
    -F≤x+pos d ∧ x+pos d≤F := by unfold g pos neg at *;omega

theorem opposite_escape_forces_shape (x y d E f F : Int)
    (hd : 1≤d) (hE : 1≤E) (hOther : f-d*E< -F)
    (hT : -F≤top x y d E f) : x<0 ∧ d< -x ∧ 0<y := by
  have hy0 : 0≤neg y := by unfold neg;omega
  have hxy := pos_neg y
  have hxneg : x<0 := by
    by_contra hn
    have hx : 0≤x := by omega
    have hnx : neg x=0 := by unfold neg;omega
    have hpd : pos (d-neg x)=d := by rw [hnx];unfold pos;omega
    have hnd : neg (d-neg x)=0 := by rw [hnx];unfold neg;omega
    have hng : neg (g x d)=0 := by rw [g,hnd];unfold neg;omega
    have hC : correction (-x) y= -x*neg y := by
      simp [correction,neg,max_eq_right (show -x≤0 by omega),max_eq_left hx]
    rw [top,hC,hpd,hng] at hT
    have hh := mul_nonneg (show 0≤x+d by omega) hy0
    nlinarith
  have hnx : neg x= -x := by unfold neg;omega
  have hC : correction (-x) y= (-x)*pos y := by
    simp [correction,pos,max_eq_left (show 0≤ -x by omega),max_eq_right (show x≤0 by omega)]
  have hdx : d< -x := by
    by_contra hn
    have hd' : 0≤d+x := by omega
    have hpd : pos (d-neg x)=d+x := by rw [hnx];unfold pos;omega
    have hnd : neg (d-neg x)=0 := by rw [hnx];unfold neg;omega
    have hng : neg (g x d)= -x := by rw [g,hnd];unfold neg;omega
    rw [top,hC,hpd,hng] at hT
    have hh := mul_nonneg hd' hy0
    nlinarith
  have hpd : pos (d-neg x)=0 := by rw [hnx];unfold pos;omega
  have hnd : neg (d-neg x)= -d-x := by rw [hnx];unfold neg;omega
  have hng : neg (g x d)=d := by rw [g,hnd];unfold neg;omega
  have hy : 0<y := by
    by_contra hn
    have hpy : pos y=0 := by unfold pos;omega
    rw [top,hC,hpd,hng,hpy] at hT
    nlinarith
  exact ⟨hxneg,hdx,hy⟩

#print axioms three_column
#print axioms three_other_column
#print axioms three_top
#print axioms alternate_column_bounded
#print axioms opposite_escape_forces_shape
end Rank4CoordinatorR2.UnitThreeGeometry
