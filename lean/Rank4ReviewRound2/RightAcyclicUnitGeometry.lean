import Rank4ReviewRound2.RightAcyclicUnitScalar

/-! Uniform selected-triangle x>=0 barrier for an actual two-letter high
excursion. The second high state is retained; no connectedness is assumed. -/
namespace Rank4ReviewRound2.RightAcyclicUnitGeometry
open QuiverProofs Rank4Coordinator Rank4CoordinatorR2
open Census ProperOrder ProperWiggle ProperMutation ProperObstructionSoundness
open RightAcyclicUnitScalar
set_option maxHeartbeats 12000000
set_option linter.unusedSimpArgs false
private theorem four (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
private def pos (x : Int) : Int := max x 0
private def neg (x : Int) : Int := max (-x) 0
private theorem neg_nonneg (x : Int) : 0≤neg x := by unfold neg;omega
private theorem pos_nonneg (x : Int) : 0≤pos x := by unfold pos;omega

def B (x c d e f : Int) : Matrix 4 := ofSix 1 x c d e f
def R (x t d e f : Int) : Matrix 4 := B x (-t) d e f
private def P (x t d e f : Int) : Matrix 4 := ofSix (-1) (-x) t d (e-t) (f-x*t)
private def z (x t d e f : Int) : Int := f-x*t+correction (-d) (e-t)
private def S (x t d e f : Int) : Matrix 4 :=
  ofSix 1 (-x-neg d) (t-neg (e-t)) (-d) (t-e) (z x t d e f)

private theorem first_two (x t d e f : Int) (hx : 0≤x) (ht : 0≤t) :
    mutate (R x t d e f) 0=P x t d e f ∧ mutate (P x t d e f) 1=S x t d e f := by
  refine ⟨?_,?_⟩ <;> funext i j <;>
    rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
    simp [R,B,P,S,z,mutate,ofSix,correction,pos,neg,
      max_eq_left hx,max_eq_right (show -x≤0 by omega),
      max_eq_left ht,max_eq_right (show -t≤0 by omega)] <;> ring

private theorem third_cells (x t d e f : Int) (hx : 0≤x) (ht : 0≤t) :
    applyWord (R x t d e f) [0,1,2] 0 1=1-(x+neg d)*neg d ∧
    applyWord (R x t d e f) [0,1,2] 0 3=t-neg (e-t)-(x+neg d)*neg (z x t d e f) ∧
    applyWord (R x t d e f) [0,1,2] 1 3=t-e+correction (-d) (z x t d e f) := by
  obtain ⟨hP,hS⟩:=first_two x t d e f hx ht
  simp only [applyWord,hP,hS]
  have hn:=neg_nonneg d
  refine ⟨?_,?_,?_⟩ <;>
    simp [S,mutate,ofSix,correction,pos,neg,
      max_eq_right (show -x-max (-d) 0≤0 by unfold neg at hn;omega),
      max_eq_left (show 0≤x+max (-d) 0 by unfold neg at hn;omega),
      max_eq_left (show 0≤max (-d) 0+x by unfold neg at hn;omega)] <;> ring

private theorem incident_shape (x t d f F : Int)
    (hx : 0≤x) (ht : 1≤t) (htF : t≤F-1) (hfF : f≤F-1)
    (hS : -F≤f-x*t+correction (-d) (-F))
    (h03 : -F≤t-F-(x+neg d)*neg (f-x*t+correction (-d) (-F)))
    (h13 : F+correction (-d) (f-x*t+correction (-d) (-F))≤F)
    (hPf : 2*abs (f-x*(t-F)-t*d)≤F-1) :
    (x=0 ∧ ((d<0 ∧ f≤0) ∨ d=0 ∨ (d=1 ∧ 0≤f))) ∨
      (x=1 ∧ d=0 ∧ 0≤f) := by
  have hF : 2≤F := by omega
  have hxt : 0≤x*t := mul_nonneg hx (by omega)
  by_cases hd : d<0
  · have hc : correction (-d) (-F)=0 := by
      simp [correction,max_eq_left (show 0≤ -d by omega),
        max_eq_right (show d≤0 by omega),max_eq_right (show -F≤0 by omega),
        max_eq_left (show 0≤F by omega)]
    have hnd : neg d= -d := by unfold neg;omega
    simp only [hc,hnd,add_zero] at hS h03 h13
    have h13' : (-d)*pos (f-x*t)≤0 := by
      simpa [correction,pos,max_eq_left (show 0≤ -d by omega),max_eq_right (show d≤0 by omega)] using h13
    have hz : f-x*t≤0 := by
      have hp:=pos_nonneg (f-x*t)
      have hge : f-x*t≤pos (f-x*t) := by unfold pos;omega
      nlinarith [mul_nonneg (show 0≤ -d-1 by omega) hp]
    have hn : neg (f-x*t)=x*t-f := by unfold neg;omega
    rw [hn] at h03
    have hz0 : 0≤x*t-f := by omega
    have hzT : x*t-f≤t := by
      nlinarith [mul_nonneg (show 0≤x-d-1 by omega) hz0]
    have hAbs:=le_abs_self (f-x*(t-F)-t*d)
    have hx0 : x=0 := by
      by_contra hh
      have hh1 : 1≤x := by omega
      nlinarith [mul_nonneg (show 0≤x-1 by omega) (show 0≤F by omega),
        mul_nonneg (show 0≤ -d-1 by omega) (show 0≤t by omega)]
    exact Or.inl ⟨hx0,Or.inl ⟨hd,by subst x;omega⟩⟩
  · have hd0 : 0≤d := by omega
    have hc : correction (-d) (-F)= -(d*F) := by
      simp [correction,max_eq_right (show -d≤0 by omega),max_eq_left hd0,
        max_eq_right (show -F≤0 by omega),max_eq_left (show 0≤F by omega)]
    have hnd : neg d=0 := by unfold neg;omega
    simp only [hc,hnd,add_zero,←sub_eq_add_neg] at hS h03 h13
    by_cases hdz : d=0
    · subst d
      simp only [zero_mul,mul_zero,sub_zero,add_zero] at hS h03 h13 hPf
      by_cases hxz : x=0
      · exact Or.inl ⟨hxz,Or.inr (Or.inl rfl)⟩
      · have hx1 : 1≤x := by omega
        have hn0:=neg_nonneg (f-x*t)
        have hge : x*t-f≤neg (f-x*t) := by unfold neg;omega
        have hnT : neg (f-x*t)≤t := by
          nlinarith [mul_nonneg (show 0≤x-1 by omega) hn0]
        have hAbs:=le_abs_self (f-x*(t-F))
        have hxeq : x=1 := by
          by_contra hh
          have hx2 : 2≤x := by omega
          nlinarith [mul_nonneg (show 0≤x-2 by omega) (show 0≤F by omega)]
        refine Or.inr ⟨hxeq,rfl,?_⟩
        subst x
        norm_num at hge hnT
        omega
    · have hd1 : 1≤d := by omega
      have hdeq : d=1 := by
        by_contra hh
        have hd2 : 2≤d := by omega
        nlinarith [mul_nonneg (show 0≤d-2 by omega) (show 0≤F by omega)]
      subst d
      norm_num at hS h03 h13 hPf
      have hz : f-x*t-F<0 := by nlinarith
      have hn : neg (f-x*t-F)=F+x*t-f := by unfold neg;omega
      rw [hn] at h03
      have hx0 : x=0 := by
        by_contra hh
        have hx1 : 1≤x := by omega
        have hxtT : t≤x*t := by
          nlinarith [mul_nonneg (show 0≤x-1 by omega) (show 0≤t by omega)]
        have hk : 1≤F+x*t-f := by nlinarith
        nlinarith [mul_nonneg (show 0≤x-1 by omega) (show 0≤F+x*t-f by omega)]
      exact Or.inl ⟨hx0,Or.inr (Or.inr ⟨rfl,by subst x;norm_num at hS;omega⟩)⟩

private theorem opposite_shape (x t d e f : Int) (H : Nat)
    (hx : 0≤x) (ht : 1≤t) (htH : t≤(H:Int))
    (hdH : -(H:Int)≤d ∧ d≤(H:Int))
    (heH : -(H:Int)≤e ∧ e≤(H:Int))
    (hfH : -(H:Int)≤f ∧ f≤(H:Int))
    (hTop : f-x*t= -((H:Int)+1))
    (hSecond : ¬HeightLe (S x t d e f) H)
    (h02 : x+neg d≤(H:Int)+1)
    (hZ : -((H:Int)+1)≤z x t d e f ∧ z x t d e f≤(H:Int)+1)
    (h01 : -((H:Int)+1)≤1-(x+neg d)*neg d)
    (h03 : -((H:Int)+1)≤t-neg (e-t)-(x+neg d)*neg (z x t d e f))
    (h13 : -((H:Int)+1)≤t-e+correction (-d) (z x t d e f) ∧
      t-e+correction (-d) (z x t d e f)≤(H:Int)+1)
    (hPf : 2*abs (f-x*e-t*d)≤(H:Int)) : x=1 ∧ d=0 ∧ 0≤e := by
  let F : Int := (H:Int)+1
  have hF : 2≤F := by dsimp [F];omega
  have htF : t≤F-1 := by dsimp [F];omega
  have heF : e≤F-1 := by dsimp [F];omega
  have hfF : -(F-1)≤f ∧ f≤F-1 := by dsimp [F];omega
  have hTop' : f-x*t= -F := hTop
  have hx1 : 1≤x := by
    by_contra hh
    have hx0 : x=0 := by omega
    rw [hx0,zero_mul,sub_zero] at hTop'
    omega
  have hZ' : -F≤z x t d e f ∧ z x t d e f≤F := hZ
  have h01' : -F≤1-(x+neg d)*neg d := h01
  have h03' : -F≤t-neg (e-t)-(x+neg d)*neg (z x t d e f) := h03
  have h13' : -F≤t-e+correction (-d) (z x t d e f) ∧
      t-e+correction (-d) (z x t d e f)≤F := h13
  by_cases hd : d<0
  · have hnd : neg d= -d := by unfold neg;omega
    have hc : correction (-d) (e-t)=(-d)*pos (e-t) := by
      simp [correction,pos,max_eq_left (show 0≤ -d by omega),max_eq_right (show d≤0 by omega)]
    have hz : z x t d e f= -F+(-d)*pos (e-t) := by unfold z;rw [hTop',hc]
    have hev : 0≤e-t := by
      by_contra hh
      have hv : e-t<0 := by omega
      have hp : pos (e-t)=0 := by unfold pos;omega
      have hnF : neg (-F)=F := by unfold neg;omega
      rw [hz,hp,mul_zero,add_zero,hnF,hnd] at h03'
      have hn0:=neg_nonneg (e-t)
      nlinarith [mul_nonneg (show 0≤x-d-2 by omega) (show 0≤F by omega)]
    have hnv : neg (e-t)=0 := by unfold neg;omega
    have hpv : pos (e-t)=e-t := by unfold pos;omega
    rw [hpv] at hz
    have hWalls : x-d=F ∨ z x t d e f= -F ∨ z x t d e f=F := by
      by_contra hh
      push_neg at hh
      apply hSecond
      intro i j
      rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
        simp only [S,ofSix,hnd,hnv,sub_zero] <;> dsimp [F] at * <;> omega
    rcases hWalls with hK|hn|hp
    · have hD1 : d= -1 := by
        rw [hnd] at h01'
        have hKd : x+ -d=F := by omega
        rw [hKd] at h01'
        by_contra hh
        have hD2 : 2≤ -d := by omega
        nlinarith [mul_nonneg (show 0≤ -d-2 by omega) (show 0≤F by omega)]
      have hzN : neg (z x t d e f)=F-(e-t) := by
        rw [hz,hD1]
        norm_num
        unfold neg
        omega
      rw [hnv,hnd,hzN,sub_zero] at h03'
      rw [hD1] at hK h03'
      have hxF : x+1=F := by omega
      have h03a : F*(F-(e-t))≤F+t := by nlinarith [h03']
      have hgap : t+1≤F-(e-t) := by omega
      nlinarith [mul_nonneg (show 0≤F by omega) (show 0≤F-(e-t)-(t+1) by omega),
        mul_nonneg (show 0≤F-2 by omega) (show 0≤t by omega)]
    · have hv0 : e-t=0 := by
        rw [hn] at hz
        nlinarith [mul_nonneg (show 0≤ -d-1 by omega) hev]
      have hnF : neg (-F)=F := by unfold neg;omega
      rw [hn,hnF,hnv,hnd,sub_zero] at h03'
      nlinarith [mul_nonneg (show 0≤x-d-2 by omega) (show 0≤F by omega)]
    · have hpF : pos F=F := by unfold pos;omega
      have hcF : correction (-d) F=(-d)*F := by
        simp [correction,max_eq_left (show 0≤ -d by omega),max_eq_right (show d≤0 by omega),
          max_eq_left (show 0≤F by omega),max_eq_right (show -F≤0 by omega)]
      rw [hp,hcF] at h13'
      have hD1 : d= -1 := by
        by_contra hh
        have hD2 : 2≤ -d := by omega
        nlinarith [mul_nonneg (show 0≤ -d-2 by omega) (show 0≤F by omega)]
      rw [hD1] at hz hp
      norm_num at hz
      rw [hp] at hz
      omega
  · have hd0 : 0≤d := by omega
    have hnd : neg d=0 := by unfold neg;omega
    have hc : correction (-d) (e-t)= -d*neg (e-t) := by
      simp [correction,neg,max_eq_right (show -d≤0 by omega),max_eq_left hd0]
    have hz : z x t d e f= -F-d*neg (e-t) := by unfold z;rw [hTop',hc];ring
    have hn0:=neg_nonneg (e-t)
    have hprod : 0≤d*neg (e-t) := mul_nonneg hd0 hn0
    have hnZ : neg (z x t d e f)=F+d*neg (e-t) := by rw [hz];unfold neg at hprod ⊢;omega
    rw [hnZ,hnd,add_zero] at h03'
    have hxeq : x=1 := by
      by_contra hh
      have hx2 : 2≤x := by omega
      nlinarith [mul_nonneg (show 0≤x-2 by omega) (show 0≤F+d*neg (e-t) by omega)]
    subst x
    have he0 : 0≤e := by
      have hnGe : t-e≤neg (e-t) := by unfold neg;omega
      nlinarith [h03']
    have hdz : d=0 := by
      by_contra hh
      have hd1 : 1≤d := by omega
      have hnZero : neg (e-t)=0 := by
        have hzL:=hZ'.1
        rw [hz] at hzL
        nlinarith [mul_nonneg (show 0≤d-1 by omega) hn0]
      have he0' : t≤e := by unfold neg at hnZero;omega
      have hzF : z 1 t d e f= -F := by rw [hz,hnZero,mul_zero,sub_zero]
      have hcF : correction (-d) (-F)= -(d*F) := by
        simp [correction,max_eq_right (show -d≤0 by omega),max_eq_left hd0,
          max_eq_right (show -F≤0 by omega),max_eq_left (show 0≤F by omega)]
      rw [hzF,hcF] at h13'
      have hdEq : d=1 := by
        by_contra hh'
        have hd2 : 2≤d := by omega
        nlinarith [mul_nonneg (show 0≤d-2 by omega) (show 0≤F by omega)]
      have het : e=t := by rw [hdEq] at h13';nlinarith [h13'.1]
      have hAbs:=neg_le_abs (f-1*e-t*d)
      rw [hdEq,het] at hAbs hPf
      dsimp [F] at hTop'
      nlinarith
    exact ⟨rfl,hdz,he0⟩

theorem scalar_impossible (x c d e f : Int) (H : Nat) (hx : 0≤x)
    (hR : HeightLe (B x c d e f) H)
    (hFirst : ¬HeightLe (mutate (B x c d e f) 0) H)
    (hSecond : ¬HeightLe (applyWord (B x c d e f) [0,1]) H)
    (hPath : PrefixHeightLe (B x c d e f) [0,1,2] (H+1))
    (p : CyclicOrder) (hp : ProperClass (B x c d e f) p)
    (hPf : 2*abs (matrixPfaffian (B x c d e f))≤orderMarkov (B x c d e f) p)
    (hBudget : orderMarkov (B x c d e f) p≤(H:Int)) : False := by
  have hH:=hR 0 1
  have hxH:=hR 0 2
  have hcH:=hR 0 3
  have hdH:=hR 1 2
  have heH:=hR 1 3
  have hfH:=hR 2 3
  simp only [B,ofSix] at hH hxH hcH hdH heH hfH
  have hc : c<0 := by
    by_contra hh
    have hc0 : 0≤c := by omega
    apply hFirst
    intro i j
    rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
      simp [mutate,B,ofSix,correction,max_eq_left hx,max_eq_right (show -x≤0 by omega),
        max_eq_left hc0,max_eq_right (show -c≤0 by omega)] <;> omega
  let t := -c
  have ht : 1≤t := by dsimp [t];omega
  have htH : t≤(H:Int) := by dsimp [t];omega
  have hcEq : c= -t := by dsimp [t];omega
  rw [hcEq] at hR hFirst hSecond hPath hp hPf hBudget
  change HeightLe (R x t d e f) H at hR
  change ¬HeightLe (mutate (R x t d e f) 0) H at hFirst
  change ¬HeightLe (applyWord (R x t d e f) [0,1]) H at hSecond
  change PrefixHeightLe (R x t d e f) [0,1,2] (H+1) at hPath
  change ProperClass (R x t d e f) p at hp
  change orderMarkov (R x t d e f) p≤(H:Int) at hBudget
  change 2*abs (matrixPfaffian (R x t d e f))≤orderMarkov (R x t d e f) p at hPf
  have hpfeq : matrixPfaffian (R x t d e f)=f-x*e-t*d := by
    simp only [matrixPfaffian,R,B,ofSix,one_mul]
    ring
  have hPf0 : 2*abs (f-x*e-t*d)≤(H:Int) := by rw [hpfeq] at hPf;omega
  obtain ⟨h1,h2⟩:=first_two x t d e f hx (by omega)
  have hP := hPath [0] [1,2] rfl
  rw [show applyWord (R x t d e f) [0]=mutate (R x t d e f) 0 from rfl,h1] at hP
  have hS := hPath [0,1] [2] rfl
  simp only [applyWord,h1,h2] at hS hSecond
  have hT := hPath [0,1,2] [] (by simp)
  obtain ⟨h01,h03,h13⟩ := third_cells x t d e f hx (by omega)
  have hT01 := (hT 0 1).1
  have hT03 := (hT 0 3).1
  have hT13 := hT 1 3
  rw [h01] at hT01
  rw [h03] at hT03
  rw [h13] at hT13
  simp only [Nat.cast_add,Nat.cast_one] at hT01 hT03 hT13
  have hPe := hP 1 3
  have hPf' := hP 2 3
  have hS02 := (hS 0 2).1
  have hSz := hS 2 3
  simp only [P,S,ofSix,Nat.cast_add,Nat.cast_one] at hPe hPf' hS02 hSz
  have hxt : 0≤x*t := mul_nonneg hx (by omega)
  have hWalls : e-t= -((H:Int)+1) ∨ f-x*t= -((H:Int)+1) := by
    by_contra hh
    push_neg at hh
    apply hFirst
    rw [h1]
    intro i j
    rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
      simp only [P,ofSix] <;> omega
  rcases hWalls with hInc|hOpp
  · let F : Int := (H:Int)+1
    let u := F-t
    have hu : 1≤u := by dsimp [u,F];omega
    have hsum : t+u=F := by dsimp [u];ring
    have heq : e=t-F := by dsimp [F];omega
    have heU : e= -u := by dsimp [u];omega
    have hnF : neg (-F)=F := by unfold neg;dsimp [F];omega
    have hEt : e-t= -F := hInc
    have hTe : t-e=F := by omega
    have h03i : -F≤t-F-(x+neg d)*neg (f-x*t+correction (-d) (-F)) := by
      simpa only [z,hEt,hnF] using hT03
    have h13i : F+correction (-d) (f-x*t+correction (-d) (-F))≤F := by
      simpa only [z,hEt,hTe] using hT13.2
    have hZi : -F≤f-x*t+correction (-d) (-F) := by
      simpa only [z,hEt] using hSz.1
    have hPfi : 2*abs (f-x*(t-F)-t*d)≤F-1 := by
      rw [heq] at hPf0
      dsimp [F] at hPf0 ⊢
      simpa only [add_sub_cancel_right] using hPf0
    obtain hZero|hUnit := incident_shape x t d f F hx ht (by dsimp [F];omega)
      (by dsimp [F];omega) hZi h03i h13i hPfi
    · obtain ⟨hx0,hdCases⟩:=hZero
      subst x
      rcases hdCases with hNeg|hd0|hOne
      · obtain ⟨hdNeg,hfNeg⟩:=hNeg
        have hpX : ProperClass (X t u (-(-d)) f) p := by simpa [R,B,X,heU] using hp
        have hm:=negative_d_scalar t u (-d) f ht hu (by omega) hfNeg p hpX
        have hm' : orderMarkov (R 0 t d e f) p=1+(-d)^2+t^2+u^2+f^2+t*u-u*(-d)*f := by
          simpa [R,B,X,heU] using hm
        have hlarge:=negative_d_large t u (-d) f F ht hu (by omega) hfNeg hsum
        dsimp [F] at hlarge
        nlinarith [hm']
      · subst d
        have hpX : ProperClass (X t u 0 f) p := by simpa [R,B,X,heU] using hp
        have hm:=zero_d_scalar t u f ht hu p hpX
        have hm' : orderMarkov (R 0 t 0 e f) p=1+t^2+u^2+f^2+t*u := by simpa [R,B,X,heU] using hm
        have hlarge:=zero_d_large t u f F ht hu hsum
        dsimp [F] at hlarge
        nlinarith [hm']
      · obtain ⟨hd1,hf0⟩:=hOne
        subst d
        have hpX : ProperClass (X t u 1 f) p := by simpa [R,B,X,heU] using hp
        have hm:=one_d_scalar t u f ht hu hf0 p hpX
        have hm' : orderMarkov (R 0 t 1 e f) p=2+t^2+u^2+f^2+t*u-(t+u)*f := by simpa [R,B,X,heU] using hm
        have hlarge:=one_d_large t u f F ht hu hsum
        dsimp [F] at hlarge
        nlinarith [hm']
    · obtain ⟨hx1,hd0,hf0⟩:=hUnit
      subst x
      subst d
      have hpU : ProperClass (U t (-u) f) p := by simpa [R,B,U,heU] using hp
      have hm:=unit_x_scalar t (-u) f ht p hpU
      have hm' : orderMarkov (R 1 t 0 e f) p=2+t^2+u^2+f^2+t*u-t*f := by
        simpa [R,B,U,heU] using hm
      have hlarge:=unit_x_large t u f F ht hu hsum
      dsimp [F] at hlarge
      nlinarith [hm']
  · obtain ⟨hx1,hd0,he0⟩ := opposite_shape x t d e f H hx ht htH hdH heH hfH hOpp hSecond
      (by omega) hSz hT01 hT03 hT13 hPf0
    subst x
    subst d
    let F : Int := (H:Int)+1
    let u := F-t
    have hu : 1≤u := by dsimp [u,F];omega
    have hsum : t+u=F := by dsimp [u];ring
    have hfU : f= -u := by dsimp [u,F];norm_num at hOpp;omega
    have hpU : ProperClass (U t e (-u)) p := by simpa [R,B,U,hfU] using hp
    have hm:=unit_x_scalar t e (-u) ht p hpU
    have hm' : orderMarkov (R 1 t 0 e f) p=2+t^2+u^2+e^2+t*u-t*e := by
      have hRep : R 1 t 0 e f=U t e (-u) := by rw [hfU];rfl
      rw [hRep,hm]
      ring
    have hlarge:=unit_x_large t u e F ht hu hsum
    dsimp [F] at hlarge
    nlinarith [hm']

theorem actual_MA_impossible (x c d e f : Int) (H : Nat) (hx : 0≤x)
    (hR : HeightLe (B x c d e f) H)
    (hFirst : ¬HeightLe (mutate (B x c d e f) 0) H)
    (hSecond : ¬HeightLe (applyWord (B x c d e f) [0,1]) H)
    (hPath : PrefixHeightLe (B x c d e f) [0,1,2] (H+1))
    (hma : MutationAcyclic (B x c d e f))
    (hAll : ∀ p,TotalProper (B x c d e f) p → orderMarkov (B x c d e f) p≤(H:Int)) : False := by
  have hs : SkewSymmetric (B x c d e f) := ofSix_skew _ _ _ _ _ _
  obtain ⟨p,hp⟩:=Foundation.ma_existence _ hs hma
  have hPf:=QuiverProofs.Rank4StructureRound2.SuperScalarPeak.MA_totalProper_pfaffian_bound
    EndpointFoundation.endpoint_bridge _ hs hma p hp
  exact scalar_impossible x c d e f H hx hR hFirst hSecond hPath p
    (totalProper_proper _ p hp) hPf (hAll p hp)

#print axioms scalar_impossible
#print axioms actual_MA_impossible
end Rank4ReviewRound2.RightAcyclicUnitGeometry
