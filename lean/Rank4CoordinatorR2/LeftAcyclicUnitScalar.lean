import Rank4CoordinatorR2.EqualUnitScalar

/-! Proper scalar formulas for the remaining x<0,d<=0 entering triangle.
These are sign-chamber identities and arithmetic barriers, not a claim of
universal triangle membership. Zero columns and absent connectors retained. -/
namespace Rank4CoordinatorR2.LeftAcyclicUnitScalar
open QuiverProofs Rank4Coordinator Rank4CoordinatorR2
open Census ProperOrder ProperWiggle ProperMutation ProperObstructionSoundness
set_option maxHeartbeats 6000000
private theorem four (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega

def R (b D t e f : Int) : Matrix 4 := ofSix 1 (-b) (-t) (-D) e f

private theorem negative_seed_classes : ∀ D t z : Fin 2, ∀ s : Fin 3, ∀ i : Fin 6,
    (0<D.val ∨ 0<t.val) →
    ProperClassTable (R 1 D.val t.val ((s.val:Int)-1) (-(z.val:Int))) i →
    component (supportMask (R 1 D.val t.val ((s.val:Int)-1) (-(z.val:Int)))) i=
      component (supportMask (R 1 D.val t.val ((s.val:Int)-1) (-(z.val:Int)))) 1 := by decide

theorem negative_column_proper_scalar (b D t e f : Int)
    (hb : 1≤b) (hD : 0≤D) (ht : 0≤t) (hf : f≤0) (hNZ : 0<D ∨ 0<t)
    (p : CyclicOrder) (hp : ProperClass (R b D t e f) p) :
    orderMarkov (R b D t e f) p=
      1+b^2+D^2+t^2+e^2+f^2-t*e+b*D+f*((b+D)*e-b*t) := by
  let dd : Fin 2 := if D=0 then 0 else 1
  let tt : Fin 2 := if t=0 then 0 else 1
  let zz : Fin 2 := if f=0 then 0 else 1
  let ss : Fin 3 := if e<0 then 0 else if e=0 then 1 else 2
  let seed := R 1 dd.val tt.val ((ss.val:Int)-1) (-(zz.val:Int))
  let Q := R b D t e f
  have hmask : supportMask Q=supportMask seed := by
    by_cases hD0 : D=0 <;> by_cases ht0 : t=0 <;> by_cases hf0 : f=0 <;>
      by_cases heN : e<0 <;> by_cases he0 : e=0 <;>
      simp [Q,R,seed,dd,tt,zz,ss,supportMask,supportBit,ofSix,hD0,ht0,hf0,heN,he0,
        show b≠0 by omega]
  have hsign : ∀ i j,0<Q i j ↔ 0<seed i j := by
    intro i j
    by_cases hD0 : D=0 <;> by_cases ht0 : t=0 <;> by_cases hf0 : f=0 <;>
      by_cases heN : e<0 <;> by_cases he0 : e=0 <;>
      rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
      simp [Q,R,seed,dd,tt,zz,ss,ofSix,hD0,ht0,hf0,heN,he0] <;> omega
  obtain ⟨i,hi⟩ := cyclic_order_exhaustive p
  have ht' := (properClass_iff_table Q (ofSix_skew _ _ _ _ _ _) p i hi).mp hp
  have hs := (ChamberProperness.properClassTable_sign_iff Q seed hmask hsign i).mp ht'
  have hNZseed : 0<dd.val ∨ 0<tt.val := by
    rcases hNZ with hd|ht
    · simp [dd,show D≠0 by omega]
    · simp [tt,show t≠0 by omega]
  have hcomp := negative_seed_classes dd tt zz ss i hNZseed hs
  have hw : WiggleEquivalent Q p (order 1) := by
    apply (wiggle_iff_component Q (ofSix_skew _ _ _ _ _ _) p (order 1) i 1
      hi (fun _ _ _ => Iff.rfl)).mpr
    rwa [hmask]
  rw [ProperWiggleInvariants.markov_wiggle_invariant Q (ofSix_skew _ _ _ _ _ _) hw]
  change Algebra.markov 1 (-t) (-b) e (-D) (-f)=_
  unfold Algebra.markov Algebra.squareSum Algebra.cycleTerms
  ring

theorem incident_scalar_large (b D t u f M : Int)
    (hb : 1≤b) (hD : 0≤D) (ht : 1≤t) (hu : 1≤u) (hf : f≤0)
    (hM : M=1+b^2+D^2+t^2+u^2+f^2+t*u+b*D-f*((b+D)*u+b*t)) :
    t+u<M := by
  have hcoef : 0≤(b+D)*u+b*t := by
    nlinarith [mul_nonneg (show 0≤b+D by omega) (show 0≤u by omega),
      mul_nonneg (show 0≤b by omega) (show 0≤t by omega)]
  nlinarith [mul_nonneg (show 0≤-f by omega) hcoef,
    mul_nonneg (show 0≤b by omega) hD,mul_nonneg (show 0≤t by omega) (show 0≤t-1 by omega),
    mul_nonneg (show 0≤u by omega) (show 0≤u-1 by omega),sq_nonneg D,sq_nonneg f,
    mul_nonneg (show 0≤t by omega) (show 0≤u by omega)]

theorem first_pair_scalar_large (H t e f M : Int)
    (hH : 1≤H) (ht : 0≤t) (he : e≤1) (hf : f≤0)
    (hM : M=H^2+H+2+t^2+e^2-t*e+f^2+f*((H+1)*e-H*t)) : H<M := by
  have hcoef : (H+1)*e-H*t≤H+1 := by
    nlinarith [mul_nonneg (show 0≤H+1 by omega) (show 0≤1-e by omega),mul_nonneg (show 0≤H by omega) ht]
  have hmul : f*(H+1)≤f*((H+1)*e-H*t) := by
    nlinarith [mul_nonneg (show 0≤-f by omega) (show 0≤H+1-((H+1)*e-H*t) by omega)]
  have hquad : 0≤t^2+e^2-t*e := by
    nlinarith [sq_nonneg (t-e),sq_nonneg t,sq_nonneg e]
  nlinarith [sq_nonneg (2*f+H+1),sq_nonneg (H-1)]

private theorem thin_positive_seed : ∀ i : Fin 6,
    ProperClassTable (ofSix 1 (-1) 1 0 0 1) i →
    component (supportMask (ofSix 1 (-1) 1 0 0 1)) i=
      component (supportMask (ofSix 1 (-1) 1 0 0 1)) 1 := by decide

theorem thin_positive_scalar (c f : Int) (hc : 1≤c) (hf : 1≤f)
    (p : CyclicOrder) (hp : ProperClass (ofSix 1 (-1) c 0 0 f) p) :
    orderMarkov (ofSix 1 (-1) c 0 0 f) p=2+c^2+f^2+c*f := by
  let seed:=ofSix 1 (-1) 1 0 0 1
  let Q:=ofSix 1 (-1) c 0 0 f
  have hmask : supportMask Q=supportMask seed := by
    simp [Q,seed,supportMask,supportBit,ofSix,show c≠0 by omega,show f≠0 by omega]
  have hsign : ∀ i j,0<Q i j ↔ 0<seed i j := by
    intro i j
    rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
      simp [Q,seed,ofSix] <;> omega
  obtain ⟨i,hi⟩ := cyclic_order_exhaustive p
  have ht' := (properClass_iff_table Q (ofSix_skew _ _ _ _ _ _) p i hi).mp hp
  have hs := (ChamberProperness.properClassTable_sign_iff Q seed hmask hsign i).mp ht'
  have hcomp := thin_positive_seed i hs
  have hw : WiggleEquivalent Q p (order 1) := by
    apply (wiggle_iff_component Q (ofSix_skew _ _ _ _ _ _) p (order 1) i 1
      hi (fun _ _ _ => Iff.rfl)).mpr
    rwa [hmask]
  rw [ProperWiggleInvariants.markov_wiggle_invariant Q (ofSix_skew _ _ _ _ _ _) hw]
  change Algebra.markov 1 c (-1) 0 0 (-f)=_
  unfold Algebra.markov Algebra.squareSum Algebra.cycleTerms
  ring

private theorem thin_middle_seed : ∀ i : Fin 6,
    ProperClassTable (ofSix 1 (-1) 0 (-1) 0 1) i →
    component (supportMask (ofSix 1 (-1) 0 (-1) 0 1)) i=
      component (supportMask (ofSix 1 (-1) 0 (-1) 0 1)) 0 := by decide

theorem thin_middle_scalar (b : Int) (hb : 1≤b)
    (p : CyclicOrder) (hp : ProperClass (ofSix 1 (-b) 0 (-1) 0 1) p) :
    orderMarkov (ofSix 1 (-b) 0 (-1) 0 1) p=b^2+b+3 := by
  let seed:=ofSix 1 (-1) 0 (-1) 0 1
  let Q:=ofSix 1 (-b) 0 (-1) 0 1
  have hmask : supportMask Q=supportMask seed := by
    simp [Q,seed,supportMask,supportBit,ofSix,show b≠0 by omega]
  have hsign : ∀ i j,0<Q i j ↔ 0<seed i j := by
    intro i j
    rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
      simp [Q,seed,ofSix] <;> omega
  obtain ⟨i,hi⟩ := cyclic_order_exhaustive p
  have ht' := (properClass_iff_table Q (ofSix_skew _ _ _ _ _ _) p i hi).mp hp
  have hs := (ChamberProperness.properClassTable_sign_iff Q seed hmask hsign i).mp ht'
  have hcomp := thin_middle_seed i hs
  have hw : WiggleEquivalent Q p (order 0) := by
    apply (wiggle_iff_component Q (ofSix_skew _ _ _ _ _ _) p (order 0) i 0
      hi (fun _ _ _ => Iff.rfl)).mpr
    rwa [hmask]
  rw [ProperWiggleInvariants.markov_wiggle_invariant Q (ofSix_skew _ _ _ _ _ _) hw]
  change Algebra.markov 1 (-b) 0 (-1) 0 1=_
  unfold Algebra.markov Algebra.squareSum Algebra.cycleTerms
  ring

#print axioms negative_column_proper_scalar
#print axioms incident_scalar_large
#print axioms first_pair_scalar_large
#print axioms thin_positive_scalar
#print axioms thin_middle_scalar
end Rank4CoordinatorR2.LeftAcyclicUnitScalar
