import Rank4StructureRound2.SuperScalarPeak
import Rank4Round2.WordBounds
import QuiverProofs.ChamberProperness
import Mathlib.Tactic.Ring

/-! A structural n2 first-switch case. The opposite edge first reaches F;
the selected outside pivot lies on the smaller side of the cyclic triangle.
Proper scalar and Pfaffian bounds force the triangle (1,-2,1), with zero
connector. This is a conditional local case, not universal sign coverage. -/
namespace QuiverProofs.Rank4StructureRound2.UnitN2Opposite
open Census ProperOrder ProperWiggle ProperObstructionSoundness
open Rank4Coordinator
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

def root (b c d E f : Int) : Matrix 4 := ofSix 1 (-b) c d (-E) f

private theorem four (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega

private theorem seed_classes : ∀ s : Fin 3, ∀ i : Fin 6,
    ProperClassTable (ofSix 1 (-1) 1 1 0 ((s.val:Int)-1)) i →
    component (supportMask (ofSix 1 (-1) 1 1 0 ((s.val:Int)-1))) i=
      component (supportMask (ofSix 1 (-1) 1 1 0 ((s.val:Int)-1))) 4 := by decide

theorem proper_scalar (b c d f : Int) (hb : 1≤b) (hc : 1≤c) (hd : 1≤d)
    (p : CyclicOrder) (hp : ProperClass (root b c d 0 f) p) :
    orderMarkov (root b c d 0 f) p=
      1+b^2+c^2+d^2+f^2-b*d+b*c*f := by
  let s : Fin 3 := if f<0 then 0 else if f=0 then 1 else 2
  let seed := ofSix 1 (-1) 1 1 0 ((s.val:Int)-1)
  let Q := root b c d 0 f
  have hmask : supportMask Q=supportMask seed := by
    by_cases hn : f<0 <;> by_cases hz : f=0 <;>
      simp [Q,root,seed,s,supportMask,supportBit,ofSix,hn,hz,
        show b≠0 by omega,show c≠0 by omega,show d≠0 by omega]
  have hsign : ∀ i j,0<Q i j ↔ 0<seed i j := by
    intro i j
    by_cases hn : f<0 <;> by_cases hz : f=0 <;>
      rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
      simp [Q,root,seed,s,ofSix,hn,hz] <;> omega
  obtain ⟨i,hi⟩ := cyclic_order_exhaustive p
  have ht := (properClass_iff_table Q (ofSix_skew _ _ _ _ _ _) p i hi).mp hp
  have hs := (ChamberProperness.properClassTable_sign_iff Q seed hmask hsign i).mp ht
  have hcomp := seed_classes s i hs
  have hw : WiggleEquivalent Q p (order 4) := by
    apply (wiggle_iff_component Q (ofSix_skew _ _ _ _ _ _) p (order 4) i 4
      hi (fun _ _ _ => Iff.rfl)).mpr
    rwa [hmask]
  have hm := ProperWiggleInvariants.markov_wiggle_invariant Q (ofSix_skew _ _ _ _ _ _) hw
  rw [hm]
  change Algebra.markov c 1 (-b) 0 (-f) d=_
  unfold Algebra.markov Algebra.squareSum Algebra.cycleTerms
  ring

theorem first_two (b c d E f F : Int)
    (hb : 0≤b) (hc : 0≤c) (hE : 0≤E) (hbd : d<b) (hTop : f+b*c=F) :
    mutate (root b c d E f) 0=ofSix (-1) b (-c) (d-b) (-E) F ∧
    mutate (ofSix (-1) b (-c) (d-b) (-E) F) 1=
      ofSix 1 d (-c-E) (b-d) E F := by
  refine ⟨?_,?_⟩ <;> funext i j <;>
    rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
    simp [root,mutate,ofSix,correction,max_eq_left hb,max_eq_left hc,max_eq_left hE,
      max_eq_right (show -b≤0 by omega),max_eq_right (show -c≤0 by omega),
      max_eq_right (show -E≤0 by omega),
      max_eq_left (show 0≤b-d by omega),max_eq_right (show d-b≤0 by omega)] <;> nlinarith


theorem third_edge (b c d E f F : Int)
    (hb : 0≤b) (hc : 0≤c) (hE : 0≤E) (hbd : d<b) (hF : 0≤F) (hTop : f+b*c=F) :
    applyWord (root b c d E f) [0,1,2] 1 3=E+(b-d)*F := by
  obtain ⟨h1,h2⟩ := first_two b c d E f F hb hc hE hbd hTop
  simp only [applyWord,h1,h2]
  simp [mutate,ofSix,correction,max_eq_left hF,
    max_eq_right (show -F≤0 by omega),
    max_eq_left (show 0≤b-d by omega),max_eq_right (show d-b≤0 by omega)]


theorem arithmetic_triangle (b c d E f F M : Int)
    (hF : 2≤F) (hb : 1≤b) (hc : 1≤c) (hd : 1≤d) (hbd : d<b)
    (hE : 0≤E) (hcF : c≤F-1) (hf : 1-F≤f)
    (hTop : f+b*c=F) (hThird : E+(b-d)*F≤F)
    (hScalar : E=0 → M=1+b^2+c^2+d^2+f^2-b*d+b*c*f)
    (hNecessary : 2*abs (f-b*E+c*d)≤M) (hBudget : M≤F-1) :
    b=2 ∧ d=1 ∧ E=0 := by
  have hq : b-d=1 := by
    by_contra h
    have hq2 : 2≤b-d := by omega
    nlinarith [mul_nonneg (show 0≤b-d-2 by omega) (show 0≤F by omega)]
  have hE0 : E=0 := by nlinarith
  have hM := hScalar hE0
  have hpf : f-b*E+c*d=F-c := by rw [hE0];nlinarith
  rw [hpf] at hNecessary
  have ht0 : 1≤F-c := by omega
  rw [abs_of_nonneg (by omega)] at hNecessary
  have htwo : 2*(F-c)≤F-1 := by omega
  have hbc : b*c≤2*F-1 := by omega
  have hb4 : b≤3 := by
    by_contra h
    have h4 : 4≤b := by omega
    nlinarith [mul_nonneg (show 0≤b-4 by omega) (show 0≤c by omega)]
  have hb2 : 2≤b := by omega
  by_cases h3 : b=3
  · have hd2 : d=2 := by omega
    let t:=F-c
    have ht : 2≤t := by dsimp [t];nlinarith
    have hct : t+1≤c := by dsimp [t];omega
    have hFt : 2*t+1≤F := by dsimp [t];omega
    have hcf : (t+1)*(2*t+1)≤c*F := by
      nlinarith [mul_nonneg (show 0≤c-(t+1) by omega) (show 0≤F by omega),
        mul_nonneg (show 0≤F-(2*t+1) by omega) (show 0≤t+1 by omega)]
    have hm3 : M=8+t^2-c*F := by
      rw [h3,hd2] at hM
      dsimp [t]
      nlinarith [hM]
    have ht2 : 4≤t^2 := by nlinarith
    have hneg : M<0 := by nlinarith
    have hnonneg : 0≤M := by have hh:=abs_nonneg (F-c);omega
    omega
  · exact ⟨by omega,by omega,hE0⟩

theorem opposite_first_triangle (b c d E f : Int) (H : Nat)
    (hb : 1≤b) (hc : 1≤c) (hd : 1≤d) (hbd : d<b) (hE : 0≤E)
    (hR : HeightLe (root b c d E f) H)
    (hTop : f+b*c=(H:Int)+1)
    (hThird : HeightLe (applyWord (root b c d E f) [0,1,2]) (H+1))
    (p : CyclicOrder) (hp : ProperClass (root b c d E f) p)
    (hNecessary : 2*abs (matrixPfaffian (root b c d E f))≤orderMarkov (root b c d E f) p)
    (hBudget : orderMarkov (root b c d E f) p≤(H:Int)) :
    b=2 ∧ d=1 ∧ E=0 := by
  have hbH:=hR 0 2
  have hcH:=hR 0 3
  have hfH:=hR 2 3
  simp only [root,ofSix] at hbH hcH hfH
  have hH : 1≤(H:Int) := by omega
  have hT:=hThird 1 3
  rw [third_edge b c d E f ((H:Int)+1) (by omega) (by omega) hE hbd (by omega) hTop] at hT
  simp only [Nat.cast_add,Nat.cast_one] at hT
  apply arithmetic_triangle b c d E f ((H:Int)+1) (orderMarkov (root b c d E f) p)
    (by omega) hb hc hd hbd hE (by omega) (by omega) hTop hT.2
  · intro h0
    subst E
    exact proper_scalar b c d f hb hc hd p hp
  · simpa only [matrixPfaffian,root,ofSix,neg_mul,neg_neg,mul_neg,one_mul] using hNecessary
  · omega

#print axioms proper_scalar
#print axioms arithmetic_triangle
#print axioms opposite_first_triangle
end QuiverProofs.Rank4StructureRound2.UnitN2Opposite
