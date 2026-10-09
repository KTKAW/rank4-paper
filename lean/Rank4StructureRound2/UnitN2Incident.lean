import Rank4StructureRound2.SuperScalarPeak
import Rank4Round2.WordBounds
import Mathlib.Tactic.Ring

/-! Incident-first n2 triangle case. For a cyclic triangle with d>b and
negative entries to vertex3, the third-pivot ceiling and Pfaffian bound
force b=1,d=2. No proper-order scalar normalization is needed. -/
namespace QuiverProofs.Rank4StructureRound2.UnitN2Incident
open Census Rank4Coordinator Rank4Round2
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

def root (b t d u f : Int) : Matrix 4 := ofSix 1 (-b) (-t) d (-u) f
private theorem four (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega

theorem first_two (b t d u f F : Int)
    (hb : 0≤b) (ht : 0≤t) (hu : 0≤u) (hbd : b<d) (hTop : u+t=F) :
    mutate (root b t d u f) 0=ofSix (-1) b t (d-b) (-F) f ∧
    mutate (ofSix (-1) b t (d-b) (-F) f) 1=
      ofSix 1 b (t-F) (b-d) F (f-(d-b)*F) := by
  have hF : 0≤F := by omega
  refine ⟨?_,?_⟩ <;> funext i j <;>
    rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
    simp [root,mutate,ofSix,correction,
      max_eq_left hb,max_eq_left ht,max_eq_left hu,max_eq_left hF,
      max_eq_right (show -b≤0 by omega),max_eq_right (show -t≤0 by omega),
      max_eq_right (show -u≤0 by omega),max_eq_right (show -F≤0 by omega),
      max_eq_left (show 0≤d-b by omega),max_eq_right (show b-d≤0 by omega)] <;> nlinarith

theorem third_edge (b t d u f F : Int)
    (hb : 0≤b) (ht : 0≤t) (hu : 0≤u) (hbd : b<d) (hTop : u+t=F) :
    applyWord (root b t d u f) [0,1,2] 2 3=(d-b)*F-f := by
  obtain ⟨h1,h2⟩:=first_two b t d u f F hb ht hu hbd hTop
  simp only [applyWord,h1,h2]
  simp [mutate,ofSix]

theorem arithmetic_triangle (b t d u f F : Int)
    (hF : 2≤F) (hb : 1≤b) (ht : 1≤t) (hu : 1≤u) (hbd : b<d)
    (hf : f≤F-1) (hTop : u+t=F) (hThird : (d-b)*F-f≤F)
    (hPf : 2*abs (f-b*u-t*d)≤F-1) :
    b=1 ∧ d=2 ∧ 1≤F-f ∧ F-f≤F-1 := by
  have hq : d-b=1 := by
    by_contra h
    have hq2 : 2≤d-b := by omega
    nlinarith [mul_nonneg (show 0≤d-b-2 by omega) (show 0≤F by omega)]
  have hneg : 2*(b*u+t*d-f)≤F-1 := by
    have hn:=neg_le_abs (f-b*u-t*d)
    omega
  have hpf : b*u+t*d-f=(b-1)*F+t+(F-f) := by nlinarith
  have hb1 : b=1 := by
    by_contra h
    have hb2 : 2≤b := by omega
    rw [hpf] at hneg
    nlinarith [mul_nonneg (show 0≤b-2 by omega) (show 0≤F by omega)]
  have hd2 : d=2 := by omega
  refine ⟨hb1,hd2,by omega,?_⟩
  rw [hb1,hd2] at hneg
  nlinarith

theorem incident_first_triangle (b t d u f : Int) (H : Nat)
    (hb : 1≤b) (ht : 1≤t) (hu : 1≤u) (hbd : b<d)
    (hR : HeightLe (root b t d u f) H)
    (hTop : u+t=(H:Int)+1)
    (hThird : HeightLe (applyWord (root b t d u f) [0,1,2]) (H+1))
    (hPf : 2*abs (matrixPfaffian (root b t d u f))≤(H:Int)) :
    b=1 ∧ d=2 ∧ 1≤(H:Int)+1-f ∧ (H:Int)+1-f≤(H:Int) := by
  have hbH:=hR 0 2
  have hfH:=hR 2 3
  simp only [root,ofSix] at hbH hfH
  have hH : 1≤(H:Int) := by omega
  have hT:=hThird 2 3
  rw [third_edge b t d u f ((H:Int)+1) (by omega) (by omega) (by omega) hbd hTop] at hT
  simp only [Nat.cast_add,Nat.cast_one] at hT
  have hP : 2*abs (f-b*u-t*d)≤((H:Int)+1)-1 := by
    simpa [matrixPfaffian,root,ofSix,sub_eq_add_neg] using hPf
  have ha:=arithmetic_triangle b t d u f ((H:Int)+1) (by omega) hb ht hu hbd (by omega) hTop hT.2 hP
  simpa using ha


#print axioms first_two
#print axioms arithmetic_triangle
#print axioms incident_first_triangle
end QuiverProofs.Rank4StructureRound2.UnitN2Incident
