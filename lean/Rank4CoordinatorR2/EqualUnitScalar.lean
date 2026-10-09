import Rank4CoordinatorR2.Foundation
import Rank4CoordinatorR2.ScalarTransport
import QuiverProofs.ChamberProperness
import Mathlib.Tactic.Ring

/-! The cyclic unit triangle with equal connectors. Proper scalars in its
positive/negative fourth-column cones are explicit. The positive cone
requires the genuine connected-MA lower scalar three; a nonnegative-only
shortcut fails at an exact scalar-one example. No all-sign entry is assumed. -/
namespace Rank4CoordinatorR2.EqualUnitScalar
open QuiverProofs Rank4Coordinator Rank4CoordinatorR2
open Census ProperOrder ProperWiggle ProperMutation ProperObstructionSoundness
set_option maxHeartbeats 3000000
private theorem four (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega

def root (b c E f : Int) : Matrix 4 := ofSix 1 (-b) c b (-E) f

private theorem positive_seed_classes : ∀ s : Fin 3, ∀ i : Fin 6,
    ProperClassTable (ofSix 1 (-1) 1 1 (-1) ((s.val:Int)-1)) i →
    component (supportMask (ofSix 1 (-1) 1 1 (-1) ((s.val:Int)-1))) i=
      component (supportMask (ofSix 1 (-1) 1 1 (-1) ((s.val:Int)-1))) 4 := by decide

private theorem negative_seed_classes : ∀ i : Fin 6,
    ProperClassTable (ofSix 1 (-1) (-1) 1 (-1) 1) i →
    component (supportMask (ofSix 1 (-1) (-1) 1 (-1) 1)) i=
      component (supportMask (ofSix 1 (-1) (-1) 1 (-1) 1)) 0 := by decide

theorem positive_proper_scalar (b c E f : Int) (hb : 1≤b) (hc : 1≤c) (hE : 1≤E)
    (p : CyclicOrder) (hp : ProperClass (root b c E f) p) :
    orderMarkov (root b c E f) p=
      1+b^2+c^2+E^2+f^2+b*c*f-b*E*f+(1-b^2)*c*E := by
  let s : Fin 3 := if f<0 then 0 else if f=0 then 1 else 2
  let seed := ofSix 1 (-1) 1 1 (-1) ((s.val:Int)-1)
  let Q := root b c E f
  have hmask : supportMask Q=supportMask seed := by
    by_cases hn : f<0 <;> by_cases hz : f=0 <;>
      simp [Q,root,seed,s,supportMask,supportBit,ofSix,hn,hz,
        show b≠0 by omega,show c≠0 by omega,show E≠0 by omega]
  have hsign : ∀ i j,0<Q i j ↔ 0<seed i j := by
    intro i j
    by_cases hn : f<0 <;> by_cases hz : f=0 <;>
      rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
      simp [Q,root,seed,s,ofSix,hn,hz] <;> omega
  obtain ⟨i,hi⟩ := cyclic_order_exhaustive p
  have ht := (properClass_iff_table Q (ofSix_skew _ _ _ _ _ _) p i hi).mp hp
  have hs := (ChamberProperness.properClassTable_sign_iff Q seed hmask hsign i).mp ht
  have hcomp := positive_seed_classes s i hs
  have hw : WiggleEquivalent Q p (order 4) := by
    apply (wiggle_iff_component Q (ofSix_skew _ _ _ _ _ _) p (order 4) i 4
      hi (fun _ _ _ => Iff.rfl)).mpr
    rwa [hmask]
  have hm := ProperWiggleInvariants.markov_wiggle_invariant Q (ofSix_skew _ _ _ _ _ _) hw
  rw [hm]
  change Algebra.markov c 1 (-b) (- -E) (-f) b=_
  unfold Algebra.markov Algebra.squareSum Algebra.cycleTerms
  ring

theorem negative_proper_scalar (b t u f : Int) (hb : 1≤b) (ht : 1≤t)
    (hu : 1≤u) (hf : 1≤f) (p : CyclicOrder) (hp : ProperClass (root b (-t) u f) p) :
    orderMarkov (root b (-t) u f) p=1+b^2+t^2+u^2+f^2+t*u-b*u*f := by
  let seed := ofSix 1 (-1) (-1) 1 (-1) 1
  let Q := root b (-t) u f
  have hmask : supportMask Q=supportMask seed := by
    simp [Q,root,seed,supportMask,supportBit,ofSix,
      show b≠0 by omega,show t≠0 by omega,show u≠0 by omega,show f≠0 by omega]
  have hsign : ∀ i j,0<Q i j ↔ 0<seed i j := by
    intro i j
    rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
      simp [Q,root,seed,ofSix] <;> omega
  obtain ⟨i,hi⟩ := cyclic_order_exhaustive p
  have ht' := (properClass_iff_table Q (ofSix_skew _ _ _ _ _ _) p i hi).mp hp
  have hs := (ChamberProperness.properClassTable_sign_iff Q seed hmask hsign i).mp ht'
  have hcomp := negative_seed_classes i hs
  have hw : WiggleEquivalent Q p (order 0) := by
    apply (wiggle_iff_component Q (ofSix_skew _ _ _ _ _ _) p (order 0) i 0
      hi (fun _ _ _ => Iff.rfl)).mpr
    rwa [hmask]
  have hm := ProperWiggleInvariants.markov_wiggle_invariant Q (ofSix_skew _ _ _ _ _ _) hw
  rw [hm]
  change Algebra.markov 1 (-b) (-t) b (-u) f=_
  unfold Algebra.markov Algebra.squareSum Algebra.cycleTerms
  ring

theorem triangle_scalar_large (a b z : Int) (ha : 1≤a) (hb : 1≤b) :
    a+b<2+a^2+b^2+a*b+z^2-b*z := by
  nlinarith [sq_nonneg (2*z-b),sq_nonneg b,
    mul_nonneg (show 0≤a by omega) (show 0≤a-1 by omega),
    mul_nonneg (show 0≤b by omega) (show 0≤a-1 by omega)]

theorem positive_arithmetic_impossible (b c E f F M : Int)
    (hF : 2≤F) (hb : 1≤b) (hc : 1≤c) (hE : 1≤E)
    (hcF : c≤F-1) (hEF : E≤F-1) (hTop : f+b*c=F)
    (hThird : b*F-c-E≤F)
    (hM : M=1+b^2+c^2+E^2+f^2+b*c*f-b*E*f+(1-b^2)*c*E)
    (hLower : 3≤M) (hBudget : M≤F-1) : False := by
  have hb2 : b≤2 := by
    by_contra h
    have hh : 3≤b := by omega
    nlinarith [mul_nonneg (show 0≤b-3 by omega) (show 0≤F by omega)]
  rcases (show b=1 ∨ b=2 by omega) with h1|h2
  · subst b
    have hf : 1≤f := by omega
    have hlarge := triangle_scalar_large c f E hc hf
    nlinarith [hM]
  · subst b
    have hF4 : 4≤F := by omega
    let u:=F-c
    let v:=F-E
    have hu : 1≤u := by dsimp [u];omega
    have hv : 1≤v := by dsimp [v];omega
    have hs : u+v≤F := by dsimp [u,v];nlinarith
    have hm : M=5+u^2+v^2+u*v-F*(u+v) := by dsimp [u,v];nlinarith [hM]
    have hprod : 1≤u*v := by
      nlinarith [mul_nonneg (show 0≤u-1 by omega) (show 0≤v-1 by omega)]
    have hprod2 : u*v≤2 := by
      nlinarith [mul_nonneg (show 0≤F-(u+v) by omega) (show 0≤u+v by omega)]
    have hsum : u+v≤3 := by
      nlinarith [mul_nonneg (show 0≤u-1 by omega) (show 0≤v-1 by omega)]
    have hs2 : 2≤u+v := by omega
    nlinarith [mul_nonneg (show 0≤3-(u+v) by omega) (show 0≤u+v by omega),
      mul_nonneg (show 0≤F-4 by omega) (show 0≤u+v by omega)]

theorem negative_arithmetic_impossible (b t u f F M : Int)
    (hF : 2≤F) (hb : 1≤b) (ht : 1≤t) (hu : 1≤u)
    (hTop : t+u=F) (hfF : f≤F-1)
    (hPf : 2*abs (f-b*F)≤M) (hBudget : M≤F-1)
    (hM : 1≤f → M=1+b^2+t^2+u^2+f^2+t*u-b*u*f) : False := by
  have hpfneg : f-b*F≤0 := by
    nlinarith [mul_nonneg (show 0≤b-1 by omega) (show 0≤F by omega)]
  rw [abs_of_nonpos hpfneg] at hPf
  have hb1 : b=1 := by
    by_contra h
    have hh : 2≤b := by omega
    nlinarith [mul_nonneg (show 0≤b-2 by omega) (show 0≤F by omega)]
  subst b
  have hf : 1≤f := by omega
  have hm := hM hf
  have hlarge := triangle_scalar_large t u f ht hu
  nlinarith [hm]

#print axioms positive_proper_scalar
#print axioms negative_proper_scalar
#print axioms triangle_scalar_large
#print axioms positive_arithmetic_impossible
#print axioms negative_arithmetic_impossible
end Rank4CoordinatorR2.EqualUnitScalar
