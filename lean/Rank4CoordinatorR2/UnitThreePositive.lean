import Rank4CoordinatorR2.UnitThreeGeometry

/-! The positive orientation of the opposite-edge escape is reduced to
the reviewed normalized scalar/Pf obstruction. Other signs/frames are
handled by a separate consumer. -/
namespace Rank4CoordinatorR2.UnitThreePositive
open QuiverProofs Rank4Coordinator Rank4CoordinatorR2 Rank4Round2
open ProperOrder ProperMutation ProperObstructionSoundness
open UnitThreeGeometry
set_option maxHeartbeats 4000000
def P (b c d E f : Int) : Matrix 4 := ofSix (-1) b (-c) (d-b) (-E) (f+b*c)
def S (b c d E f : Int) : Matrix 4 := ofSix 1 d (-c-E) (b-d) E (f+b*c)
def T (b c d E f : Int) : Matrix 4 :=
  ofSix (-1) (-d) (c+E) (b-d) (-c) (f+b*c-d*(c+E))
private theorem four (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega

theorem matrices (b c d E f : Int)
    (hb : 1≤b) (hc : 1≤c) (hd : 1≤d) (hE : 1≤E) (hbd : d<b) :
    mutate (R (-b) c d E f) 0=P b c d E f ∧
    mutate (P b c d E f) 1=S b c d E f ∧
    mutate (S b c d E f) 0=T b c d E f := by
  refine ⟨?_,?_,?_⟩ <;> funext i j <;>
    rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
    simp [R,P,S,T,mutate,ofSix,correction,
      max_eq_left (show 0≤b by omega),max_eq_left (show 0≤c by omega),
      max_eq_left (show 0≤d by omega),max_eq_left (show 0≤E by omega),
      max_eq_left (show 0≤b-d by omega),max_eq_left (show 0≤c+E by omega),
      max_eq_right (show -b≤0 by omega),max_eq_right (show -c≤0 by omega),
      max_eq_right (show -d≤0 by omega),max_eq_right (show -E≤0 by omega),
      max_eq_right (show d-b≤0 by omega),max_eq_right (show -c-E≤0 by omega)] <;>
      try ring
  all_goals first | omega | (simp only [max_eq_left (show 0≤c+E by omega),
    max_eq_left (show 0≤E+c by omega)];ring)

theorem normalized_wall_conditions (b c d E f : Int) (H : Nat)
    (hb : 1≤b) (hc : 1≤c) (hd : 1≤d) (hE : 1≤E) (hbd : d<b)
    (hR : HeightLe (R (-b) c d E f) H)
    (hPHigh : ¬HeightLe (P b c d E f) H)
    (hP : HeightLe (P b c d E f) (H+1))
    (hS : HeightLe (S b c d E f) (H+1))
    (hT : HeightLe (T b c d E f) (H+1))
    (hTHigh : ¬HeightLe (T b c d E f) H)
    (hOther : f-d*E< -((H:Int)+1)) :
    f=(H:Int)+1-b*c ∧ b*c≤2*((H:Int)+1)-1 ∧
    2*((H:Int)+1)<b*c+d*E ∧ c+E≤(H:Int)+1 ∧
    (c+E=(H:Int)+1 ∨ d*(c+E)=2*((H:Int)+1)) := by
  have hRH := hR 0 1
  have hbH := hR 0 2
  have hcH := hR 0 3
  have hdH := hR 1 2
  have hEH := hR 1 3
  have hfH := hR 2 3
  simp only [R,ofSix] at hRH hbH hcH hdH hEH hfH
  have hPF := hP 2 3
  have hSF := hS 0 3
  have hTF := hT 2 3
  have hTL := hT 0 3
  simp only [P,S,T,ofSix,Nat.cast_add,Nat.cast_one] at hPF hSF hTF hTL
  have hbc0 := mul_pos (show 0<b by omega) (show 0<c by omega)
  have hFirst : f+b*c=(H:Int)+1 := by
    by_contra hn
    have hW : -(H:Int)≤f+b*c ∧ f+b*c≤(H:Int) := by omega
    apply hPHigh
    intro i j
    rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
      simp only [P,ofSix] <;> omega
  have hProd := mul_pos (show 0<d by omega) (show 0<c+E by omega)
  have hTop : c+E=(H:Int)+1 ∨ d*(c+E)=2*((H:Int)+1) := by
    by_contra hn
    have hNot := not_or.mp hn
    have hW : -(H:Int)≤f+b*c-d*(c+E) ∧ f+b*c-d*(c+E)≤(H:Int) := by omega
    have hL : c+E≤(H:Int) := by omega
    apply hTHigh
    intro i j
    rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
      simp only [T,ofSix] <;> omega
  exact ⟨by omega,by omega,by nlinarith,by omega,hTop⟩

theorem positive_escape_MA_impossible (x y d E f : Int) (H : Nat)
    (hd : 1≤d) (hE : 1≤E)
    (hR : HeightLe (R x y d E f) H)
    (hPath : PrefixHeightLe (R x y d E f) [0,1,0] (H+1))
    (hFirst : ¬HeightLe (mutate (R x y d E f) 0) H)
    (hThird : ¬HeightLe (applyWord (R x y d E f) [0,1,0]) H)
    (hOther : f-d*E< -((H:Int)+1))
    (hScalars : ∀ p,TotalProper (R x y d E f) p → orderMarkov (R x y d E f) p≤(H:Int)) :
    ¬MutationAcyclic (R x y d E f) := by
  intro hma
  have hTop := (hPath [0,1,0] [] (by simp) 2 3).1
  rw [three_top x y d E f hE] at hTop
  simp only [Nat.cast_add,Nat.cast_one] at hTop
  obtain ⟨hx,hbd,hy⟩ := opposite_escape_forces_shape x y d E f ((H:Int)+1) hd hE hOther hTop
  let b := -x
  let c := y
  have hb : 1≤b := by dsimp [b];omega
  have hc : 1≤c := by dsimp [c];omega
  have hdx : d<b := hbd
  have hR' : R (-b) c d E f=R x y d E f := by simp [b,c]
  obtain ⟨h1,h2,h3⟩ := matrices b c d E f hb hc hd hE hdx
  have hP : HeightLe (P b c d E f) (H+1) := by
    rw [←h1,hR'];exact hPath [0] [1,0] rfl
  have hS : HeightLe (S b c d E f) (H+1) := by
    rw [←h2,←h1,hR'];exact hPath [0,1] [0] rfl
  have hT : HeightLe (T b c d E f) (H+1) := by
    rw [←h3,←h2,←h1,hR'];exact hPath [0,1,0] [] (by simp)
  have hFirst' : ¬HeightLe (P b c d E f) H := by rwa [←h1,hR']
  have hThird' : ¬HeightLe (T b c d E f) H := by
    rw [←hR',applyWord,h1,applyWord,h2,applyWord,h3,applyWord] at hThird
    exact hThird
  obtain ⟨hf,hbc,hCross,hL,hWall⟩ := normalized_wall_conditions b c d E f H hb hc hd hE hdx
    (by rwa [hR']) hFirst' hP hS hT hThird' hOther
  have hrep : R x y d E f=UnitThreeScalar.root b c d E ((H:Int)+1) := by
    rw [←hR'];simp only [R,UnitThreeScalar.root,hf]
  have hB := hR 0 2
  have hD := hR 1 2
  have hOne := hR 0 1
  simp only [R,ofSix] at hB hD hOne
  obtain ⟨p,hp⟩ := Foundation.ma_existence (R x y d E f) (ofSix_skew _ _ _ _ _ _) hma
  have hm := hScalars p hp
  rw [hrep] at hp hm hma
  exact UnitThreeScalar.normalized_MA_impossible b c d E ((H:Int)+1) (by omega)
    hb hc hd hE (by dsimp [b];omega) (by omega) hL hdx hbc hCross hWall p hp (by omega) hma

#print axioms matrices
#print axioms normalized_wall_conditions
#print axioms positive_escape_MA_impossible
end Rank4CoordinatorR2.UnitThreePositive
