import Rank4CoordinatorR2.EqualUnitScalar

/-! Equal connectors in the cyclic entering triangle cannot occur in an
actual MA first-switch ceiling path above its supplied proper scalar.
The equality case is separate from the two strict connector orientations. -/
namespace Rank4CoordinatorR2.EqualUnitTriangle
open QuiverProofs Rank4Coordinator Rank4CoordinatorR2
open Census ProperOrder ProperWiggle ProperMutation ProperObstructionSoundness
set_option maxHeartbeats 4000000
private theorem four (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
private def pos (x : Int) : Int := max x 0
private def neg (x : Int) : Int := max (-x) 0

def B (b c e f : Int) : Matrix 4 := ofSix 1 (-b) c b e f
private def P (b c e f : Int) : Matrix 4 :=
  ofSix (-1) b (-c) 0 (e-neg c) (f+b*pos c)
private def S (b c e f : Int) : Matrix 4 :=
  ofSix 1 b (-c-neg (e-neg c)) 0 (-(e-neg c)) (f+b*pos c)

private theorem first_two (b c e f : Int) (hb : 0≤b) :
    mutate (B b c e f) 0=P b c e f ∧ mutate (P b c e f) 1=S b c e f := by
  refine ⟨?_,?_⟩ <;> funext i j <;>
    rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
    simp [B,P,S,mutate,ofSix,correction,pos,neg,
      max_eq_left hb,max_eq_right (show -b≤0 by omega)] <;> ring

private theorem third_cell (b c e f : Int) (hb : 0≤b) :
    applyWord (B b c e f) [0,1,2] 0 3=
      -c-neg (e-neg c)+b*pos (f+b*pos c) := by
  obtain ⟨hP,hS⟩ := first_two b c e f hb
  simp only [applyWord,hP,hS]
  simp [S,mutate,ofSix,correction,pos,neg,
    max_eq_left hb,max_eq_right (show -b≤0 by omega)]

theorem scalar_triangle_impossible (b c e f : Int) (H : Nat) (hb : 1≤b)
    (hR : HeightLe (B b c e f) H)
    (hFirst : ¬HeightLe (mutate (B b c e f) 0) H)
    (hCeil : HeightLe (mutate (B b c e f) 0) (H+1))
    (hThird : HeightLe (applyWord (B b c e f) [0,1,2]) (H+1))
    (p : CyclicOrder) (hp : ProperClass (B b c e f) p)
    (hLower : 3≤orderMarkov (B b c e f) p)
    (hPf : 2*abs (matrixPfaffian (B b c e f))≤orderMarkov (B b c e f) p)
    (hBudget : orderMarkov (B b c e f) p≤(H:Int)) : False := by
  obtain ⟨hP,hS⟩ := first_two b c e f (by omega)
  have hH := hR 0 1
  have hbH := hR 0 2
  have hcH := hR 0 3
  have heH := hR 1 3
  have hfH := hR 2 3
  simp only [B,ofSix] at hH hbH hcH heH hfH
  have hF : 2≤(H:Int)+1 := by omega
  by_cases hc : 0<c
  · have hpc : pos c=c := by unfold pos;omega
    have hnc : neg c=0 := by unfold neg;omega
    have hbc : 1≤b*c := by
      nlinarith [mul_nonneg (show 0≤b-1 by omega) (show 0≤c-1 by omega)]
    have hTop : f+b*c=(H:Int)+1 := by
      have hedge := hCeil 2 3
      rw [hP] at hedge
      simp only [P,ofSix,hpc,Nat.cast_add,Nat.cast_one] at hedge
      by_contra hh
      apply hFirst
      rw [hP]
      intro i j
      rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
        simp only [P,ofSix,hpc,hnc,sub_zero] <;> omega
    have he : e<0 := by
      by_contra hh
      have he0 : 0≤e := by omega
      have hpfEq : matrixPfaffian (B b c e f)=(H:Int)+1+b*e := by
        simp only [matrixPfaffian,B,ofSix,one_mul,neg_mul]
        nlinarith
      have hAbs := le_abs_self (matrixPfaffian (B b c e f))
      rw [hpfEq] at hAbs hPf
      nlinarith [mul_nonneg (show 0≤b by omega) he0]
    have hnE : neg e= -e := by unfold neg;omega
    have ht := (hThird 0 3).2
    rw [third_cell b c e f (by omega)] at ht
    simp only [hpc,hnc,sub_zero,hnE,hTop,
      show pos ((H:Int)+1)=(H:Int)+1 by unfold pos;omega,
      Nat.cast_add,Nat.cast_one] at ht
    have hrep : B b c e f=EqualUnitScalar.root b c (-e) f := by simp [B,EqualUnitScalar.root]
    have hm := EqualUnitScalar.positive_proper_scalar b c (-e) f hb (by omega) (by omega)
      p (by rwa [←hrep])
    rw [←hrep] at hm
    exact EqualUnitScalar.positive_arithmetic_impossible b c (-e) f ((H:Int)+1)
      (orderMarkov (B b c e f) p) hF hb (by omega) (by omega) (by omega) (by omega)
      hTop (by omega) hm hLower (by omega)
  · have hc0 : c≤0 := by omega
    have hpc : pos c=0 := by unfold pos;omega
    have hnc : neg c= -c := by unfold neg;omega
    have hTop : e+c= -((H:Int)+1) := by
      have hedge := hCeil 1 3
      rw [hP] at hedge
      simp only [P,ofSix,hnc,Nat.cast_add,Nat.cast_one] at hedge
      by_contra hh
      apply hFirst
      rw [hP]
      intro i j
      rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
        simp only [P,ofSix,hpc,hnc,mul_zero,add_zero] <;> omega
    have hcNeg : c<0 := by omega
    have heNeg : e<0 := by omega
    have hrep : B b c e f=EqualUnitScalar.root b (-(-c)) (-e) f := by
      simp [B,EqualUnitScalar.root]
    have hpfEq : matrixPfaffian (B b c e f)=f-b*((H:Int)+1) := by
      calc matrixPfaffian (B b c e f)=f+b*(e+c) := by
             simp only [matrixPfaffian,B,ofSix,one_mul,neg_mul];ring
           _=f-b*((H:Int)+1) := by rw [hTop];ring
    have hPf' := hPf
    rw [hpfEq] at hPf'
    apply EqualUnitScalar.negative_arithmetic_impossible b (-c) (-e) f ((H:Int)+1)
      (orderMarkov (B b c e f) p) hF hb (by omega) (by omega) (by omega) (by omega)
      hPf' (by omega)
    intro hf
    have hm := EqualUnitScalar.negative_proper_scalar b (-c) (-e) f hb (by omega) (by omega)
      hf p (by rwa [←hrep])
    rwa [←hrep] at hm

theorem actual_MA_impossible (b c e f : Int) (H : Nat) (hb : 1≤b)
    (hR : HeightLe (B b c e f) H)
    (hFirst : ¬HeightLe (mutate (B b c e f) 0) H)
    (hCeil : HeightLe (mutate (B b c e f) 0) (H+1))
    (hThird : HeightLe (applyWord (B b c e f) [0,1,2]) (H+1))
    (hma : MutationAcyclic (B b c e f))
    (hAll : ∀ p,TotalProper (B b c e f) p → orderMarkov (B b c e f) p≤(H:Int)) : False := by
  have hs : SkewSymmetric (B b c e f) := ofSix_skew _ _ _ _ _ _
  have hc : c≠0 := by
    intro heq
    subst c
    obtain ⟨hP,_⟩ := first_two b 0 e f (by omega)
    apply hFirst
    rw [hP]
    have hbH := hR 0 2
    have heH := hR 1 3
    have hfH := hR 2 3
    have hH := hR 0 1
    simp only [B,ofSix] at hbH heH hfH hH
    intro i j
    rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
      simp [P,pos,neg,ofSix] <;> omega
  have hconn : ConnectedSupport (B b c e f) := by
    intro aa bb cc dd hEdges
    have h01 : aa=bb := hEdges 0 1 (by change (1:Int)≠0;omega)
    have h02 : aa=cc := hEdges 0 2 (by change -b≠0;omega)
    have h03 : aa=dd := hEdges 0 3 (by change c≠0;exact hc)
    exact ⟨h01,h01.symm.trans h02,h02.symm.trans h03⟩
  obtain ⟨p,hp⟩ := Foundation.ma_existence _ hs hma
  have hM := hAll p hp
  have hLower := connected_MA_totalProper_markov EndpointFoundation.endpoint_bridge
    _ hs hconn hma p hp
  have hPf := QuiverProofs.Rank4StructureRound2.SuperScalarPeak.MA_totalProper_pfaffian_bound
    EndpointFoundation.endpoint_bridge _ hs hma p hp
  exact scalar_triangle_impossible b c e f H hb hR hFirst hCeil hThird p
    (totalProper_proper _ p hp) hLower hPf hM

#print axioms scalar_triangle_impossible
#print axioms actual_MA_impossible
end Rank4CoordinatorR2.EqualUnitTriangle
