import Rank4CoordinatorR2.LeftAcyclicUnitScalar

/-! The selected entering triangle has x<0 and d<=0. Actual first and
third ceiling bounds split its first crossing into three exact walls;
each wall contradicts the supplied proper scalar/Pf bound. -/
namespace Rank4CoordinatorR2.LeftAcyclicUnitGeometry
open QuiverProofs Rank4Coordinator Rank4CoordinatorR2
open Census ProperOrder ProperWiggle ProperMutation ProperObstructionSoundness
set_option maxHeartbeats 6000000
private theorem four (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
private def pos (x : Int) : Int := max x 0
private def neg (x : Int) : Int := max (-x) 0

def R (b D c e f : Int) : Matrix 4 := ofSix 1 (-b) c (-D) e f
private def h (c e : Int) : Int := e-neg c
private def g (b c f : Int) : Int := f+b*pos c
private def z (b D c e f : Int) : Int := g b c f+(b+D)*pos (h c e)
private def P (b D c e f : Int) : Matrix 4 := ofSix (-1) b (-c) (-D-b) (h c e) (g b c f)
private def S (b D c e f : Int) : Matrix 4 := ofSix 1 (-D) (-c-neg (h c e)) (D+b) (-(h c e)) (z b D c e f)

private theorem first_two (b D c e f : Int) (hb : 0≤b) (hD : 0≤D) :
    mutate (R b D c e f) 0=P b D c e f ∧ mutate (P b D c e f) 1=S b D c e f := by
  refine ⟨?_,?_⟩ <;> funext i j <;>
    rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
    simp [R,P,S,h,g,z,mutate,ofSix,correction,pos,neg,
      max_eq_left hb,max_eq_right (show -b≤0 by omega),
      max_eq_left (show 0≤D+b by omega),max_eq_left (show 0≤b+D by omega),
      max_eq_right (show -D-b≤0 by omega),max_eq_right (show -b-D≤0 by omega)] <;> first | omega | ring

private theorem third_cells (b D c e f : Int) (hb : 0≤b) (hD : 0≤D) :
    applyWord (R b D c e f) [0,1,2] 0 1=1-D*(D+b) ∧
    applyWord (R b D c e f) [0,1,2] 1 3= -(h c e)+(D+b)*pos (z b D c e f) := by
  obtain ⟨hP,hS⟩ := first_two b D c e f hb hD
  simp only [applyWord,hP,hS]
  constructor <;> simp [S,mutate,ofSix,correction,pos,neg,
    max_eq_left hD,max_eq_right (show -D≤0 by omega),
    max_eq_left (show 0≤D+b by omega),max_eq_right (show -(D+b)≤0 by omega)] <;> first | omega | ring

theorem scalar_impossible (b D c e f : Int) (H : Nat) (hb : 1≤b) (hD : 0≤D)
    (hR : HeightLe (R b D c e f) H)
    (hFirst : ¬HeightLe (mutate (R b D c e f) 0) H)
    (hPath : PrefixHeightLe (R b D c e f) [0,1,2] (H+1))
    (p : CyclicOrder) (hp : ProperClass (R b D c e f) p)
    (hPf : 2*abs (matrixPfaffian (R b D c e f))≤orderMarkov (R b D c e f) p)
    (hBudget : orderMarkov (R b D c e f) p≤(H:Int)) : False := by
  obtain ⟨h1,h2⟩ := first_two b D c e f (by omega) hD
  have hP : HeightLe (P b D c e f) (H+1) := by rw [←h1];exact hPath [0] [1,2] rfl
  have hS : HeightLe (S b D c e f) (H+1) := by rw [←h2,←h1];exact hPath [0,1] [2] rfl
  have hT : HeightLe (applyWord (R b D c e f) [0,1,2]) (H+1) := hPath [0,1,2] [] (by simp)
  obtain ⟨ht01,ht13⟩ := third_cells b D c e f (by omega) hD
  have hH := hR 0 1
  have hbH := hR 0 2
  have hcH := hR 0 3
  have hDH := hR 1 2
  have heH := hR 1 3
  have hfH := hR 2 3
  simp only [R,ofSix] at hH hbH hcH hDH heH hfH
  have hH1 : 1≤(H:Int) := by omega
  have hF : 2≤(H:Int)+1 := by omega
  have hK := hP 1 2
  have hh := hP 1 3
  have hg := hP 2 3
  simp only [P,ofSix,Nat.cast_add,Nat.cast_one] at hK hh hg
  have hnC : 0≤neg c := by unfold neg;omega
  have hpC : 0≤pos c := by unfold pos;omega
  have hhUpper : h c e≤(H:Int) := by unfold h;omega
  have hgLower : -(H:Int)≤g b c f := by
    unfold g
    nlinarith [mul_nonneg (show 0≤b by omega) hpC]
  have ht13' := (hT 1 3).2
  rw [ht13] at ht13'
  simp only [Nat.cast_add,Nat.cast_one] at ht13'
  have hpfEq : matrixPfaffian (R b D c e f)=f+b*e-D*c := by
    simp only [matrixPfaffian,R,ofSix,one_mul,neg_mul,mul_neg];ring
  have hPf' := hPf
  rw [hpfEq] at hPf'
  have hWalls : b+D=(H:Int)+1 ∨ h c e= -((H:Int)+1) ∨ g b c f=(H:Int)+1 := by
    by_contra hh'
    push_neg at hh'
    apply hFirst
    rw [h1]
    intro i j
    rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
      simp only [P,ofSix] <;> omega
  rcases hWalls with hPair|hIncident|hOpposite
  · have hD1 : D=1 := by
      have ht := (hT 0 1).1
      rw [ht01] at ht
      simp only [Nat.cast_add,Nat.cast_one] at ht
      have hdPos : 1≤D := by omega
      by_contra hn
      have hd2 : 2≤D := by omega
      nlinarith [mul_nonneg (show 0≤D-2 by omega) (show 0≤(H:Int)+1 by omega)]
    subst D
    have hbEq : b=(H:Int) := by omega
    subst b
    simp only [one_mul] at hPf'
    have hz1 : z (H:Int) 1 c e f≤1 := by
      have hn : z (H:Int) 1 c e f≤pos (z (H:Int) 1 c e f) := by unfold pos;omega
      by_contra hh'
      have hz2 : 2≤pos (z (H:Int) 1 c e f) := by omega
      nlinarith [mul_nonneg (show 0≤pos (z (H:Int) 1 c e f)-2 by omega) (show 0≤(H:Int)+1 by omega)]
    by_cases hc : 0<c
    · have hpc : pos c=c := by unfold pos;omega
      have hnc : neg c=0 := by unfold neg;omega
      have he0 : e≤0 := by
        have hnon : 0≤pos e := by unfold pos;omega
        have hpos0 : pos e=0 := by
          have hmul := mul_nonneg (show 0≤(H:Int) by omega) (show 0≤c-1 by omega)
          by_contra hn
          have hp1 : 1≤pos e := by omega
          have hmulf := mul_nonneg (show 0≤(H:Int)+1 by omega) (show 0≤pos e-1 by omega)
          simp only [z,g,h,hpc,hnc,sub_zero] at hz1
          nlinarith
        unfold pos at hpos0
        omega
      have hpf : f+(H:Int)*e-c≤-(H:Int) := by
        have hpe : pos e=0 := by unfold pos;omega
        simp only [z,g,h,hpc,hnc,sub_zero,hpe,mul_zero,add_zero] at hz1
        nlinarith [mul_nonpos_of_nonneg_of_nonpos (show 0≤(H:Int) by omega) he0,
          mul_nonneg (show 0≤(H:Int)+1 by omega) (show 0≤c-1 by omega)]
      have ha := neg_le_abs (f+(H:Int)*e-c)
      omega
    · have hc0 : c≤0 := by omega
      have hpc : pos c=0 := by unfold pos;omega
      have hnc : neg c= -c := by unfold neg;omega
      by_cases hf : 0<f
      · have hph : 0≤pos (h c e) := by unfold pos;omega
        have hf1 : f=1 := by
          simp only [z,g,hpc,mul_zero,add_zero] at hz1
          nlinarith [mul_nonneg (show 0≤(H:Int)+1 by omega) hph]
        have hh0 : h c e=0 := by
          have hp0 : pos (h c e)=0 := by
            simp only [z,g,hpc,mul_zero,add_zero,hf1] at hz1
            nlinarith
          have hzEq : z (H:Int) 1 c e f=1 := by simp [z,g,hpc,hf1,hp0]
          simp only [hzEq,show pos (1:Int)=1 by decide] at ht13'
          unfold pos at hp0
          omega
        have heq : e= -c := by unfold h at hh0;rw [hnc] at hh0;omega
        have hcEq : c=0 := by
          by_contra hn
          have hcN : c≤-1 := by omega
          have ha := le_abs_self (f+(H:Int)*e-c)
          nlinarith [mul_nonneg (show 0≤(H:Int)+1 by omega) (show 0≤-c-1 by omega)]
        have heEq : e=0 := by omega
        subst c
        subst e
        subst f
        have hm := LeftAcyclicUnitScalar.thin_middle_scalar (H:Int) hH1 p hp
        change orderMarkov (R (H:Int) 1 0 0 1) p=(H:Int)^2+(H:Int)+3 at hm
        nlinarith [hm,sq_nonneg (H:Int)]
      · have hf0 : f≤0 := by omega
        have he1 : e≤1 := by
          by_contra hn
          have he2 : 2≤e := by omega
          have ha := le_abs_self (f+(H:Int)*e-c)
          nlinarith [mul_nonneg (show 0≤(H:Int) by omega) (show 0≤e-2 by omega)]
        have hrep : R (H:Int) 1 c e f=LeftAcyclicUnitScalar.R (H:Int) 1 (-c) e f := by
          simp [R,LeftAcyclicUnitScalar.R]
        have hm := LeftAcyclicUnitScalar.negative_column_proper_scalar (H:Int) 1 (-c) e f
          hH1 (by omega) (by omega) hf0 (Or.inl (by omega)) p (by rwa [←hrep])
        rw [←hrep] at hm
        have hm' : orderMarkov (R (H:Int) 1 c e f) p=(H:Int)^2+(H:Int)+2+(-c)^2+e^2-(-c)*e+f^2+f*(((H:Int)+1)*e-(H:Int)*(-c)) := by nlinarith [hm]
        have hLarge := LeftAcyclicUnitScalar.first_pair_scalar_large (H:Int) (-c) e f
          (orderMarkov (R (H:Int) 1 c e f) p) hH1 (by omega) he1 hf0 hm'
        omega
  · have hc : c<0 := by
      by_contra hn
      have hnc : neg c=0 := by unfold neg;omega
      unfold h at hIncident
      rw [hnc] at hIncident
      omega
    have hpc : pos c=0 := by unfold pos;omega
    have hnc : neg c= -c := by unfold neg;omega
    have hf0 : f≤0 := by
      have hph : pos (h c e)=0 := by rw [hIncident];unfold pos;omega
      have hzEq : z b D c e f=f := by simp [z,g,hpc,hph]
      rw [hIncident,hzEq] at ht13'
      have hpos : 0≤pos f := by unfold pos;omega
      have hp0 : pos f=0 := by
        nlinarith [mul_nonneg (show 0≤D+b-1 by omega) hpos]
      unfold pos at hp0
      omega
    let t:= -c
    let u:= -e
    have ht : 1≤t := by dsimp [t];omega
    have hu : 1≤u := by unfold h at hIncident;rw [hnc] at hIncident;dsimp [u];omega
    have htu : t+u=(H:Int)+1 := by unfold h at hIncident;rw [hnc] at hIncident;dsimp [t,u];omega
    have hrep : R b D c e f=LeftAcyclicUnitScalar.R b D t (-u) f := by simp [R,LeftAcyclicUnitScalar.R,t,u]
    have hm := LeftAcyclicUnitScalar.negative_column_proper_scalar b D t (-u) f hb hD
      (by omega) hf0 (Or.inr (by omega)) p (by rwa [←hrep])
    rw [←hrep] at hm
    have hm' : orderMarkov (R b D c e f) p=1+b^2+D^2+t^2+u^2+f^2+t*u+b*D-f*((b+D)*u+b*t) := by nlinarith [hm]
    have hLarge := LeftAcyclicUnitScalar.incident_scalar_large b D t u f
      (orderMarkov (R b D c e f) p) hb hD ht hu hf0 hm'
    omega
  · have hph : pos (h c e)=0 := by
      have hs := (hS 2 3).2
      simp only [S,ofSix,Nat.cast_add,Nat.cast_one,z,hOpposite] at hs
      have hn : 0≤pos (h c e) := by unfold pos;omega
      nlinarith [mul_nonneg (show 0≤b+D-1 by omega) hn]
    have hh0 : h c e=0 := by
      have hn : h c e≤0 := by unfold pos at hph;omega
      have hzEq : z b D c e f=(H:Int)+1 := by simp [z,hOpposite,hph]
      rw [hzEq,show pos ((H:Int)+1)=(H:Int)+1 by unfold pos;omega] at ht13'
      nlinarith [mul_nonneg (show 0≤b+D-1 by omega) (show 0≤(H:Int)+1 by omega)]
    have hK1 : b+D=1 := by
      have hzEq : z b D c e f=(H:Int)+1 := by simp [z,hOpposite,hph]
      rw [hzEq,hh0,show pos ((H:Int)+1)=(H:Int)+1 by unfold pos;omega] at ht13'
      by_contra hn
      have hk2 : 2≤b+D := by omega
      nlinarith [mul_nonneg (show 0≤b+D-2 by omega) (show 0≤(H:Int)+1 by omega)]
    have hb1 : b=1 := by omega
    have hD0 : D=0 := by omega
    subst b
    subst D
    have hc : 1≤c := by
      unfold g at hOpposite
      unfold pos at hOpposite
      omega
    have hpc : pos c=c := by unfold pos;omega
    have hnc : neg c=0 := by unfold neg;omega
    have he0 : e=0 := by unfold h at hh0;rw [hnc] at hh0;omega
    subst e
    have hcf : c+f=(H:Int)+1 := by unfold g at hOpposite;rw [hpc] at hOpposite;omega
    have hf : 1≤f := by omega
    have hm := LeftAcyclicUnitScalar.thin_positive_scalar c f hc hf p hp
    change orderMarkov (R 1 0 c 0 f) p=2+c^2+f^2+c*f at hm
    have hLarge := EqualUnitScalar.triangle_scalar_large c f 0 hc hf
    nlinarith [hm]

#print axioms scalar_impossible
end Rank4CoordinatorR2.LeftAcyclicUnitGeometry
