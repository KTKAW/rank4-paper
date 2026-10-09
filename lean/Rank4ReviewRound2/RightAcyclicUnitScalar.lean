import Rank4CoordinatorR2.EqualUnitScalar

/-! Proper scalar formulas and uniform budget barriers for the right
acyclic unit triangle. Sign/support chambers are exhaustive, including zeros.
No finite entry-size bound or MA absence inference is used. -/
namespace Rank4ReviewRound2.RightAcyclicUnitScalar
open QuiverProofs Rank4Coordinator Rank4CoordinatorR2
open Census ProperOrder ProperWiggle ProperMutation ProperObstructionSoundness
open Algebra
set_option maxHeartbeats 8000000
private theorem four (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
private theorem order_zero (i : Fin 4) : (order 0).toFun i=i := by revert i;decide

def U (t e f : Int) : Matrix 4 := ofSix 1 1 (-t) 0 e f
def X (t u d f : Int) : Matrix 4 := ofSix 1 0 (-t) d (-u) f

private theorem unit_x_seed : ∀ s v : Fin 3, ∀ i : Fin 6,
    ProperClassTable (ofSix 1 1 (-1) 0 ((s.val:Int)-1) ((v.val:Int)-1)) i →
    component (supportMask (ofSix 1 1 (-1) 0 ((s.val:Int)-1) ((v.val:Int)-1))) i=component (supportMask (ofSix 1 1 (-1) 0 ((s.val:Int)-1) ((v.val:Int)-1))) 0 := by decide

theorem unit_x_scalar (t e f : Int) (ht : 1≤t)
    (p : CyclicOrder) (hp : ProperClass (U t e f) p) :
    orderMarkov (U t e f) p=2+t^2+e^2+f^2-t*e-t*f := by
  let s : Fin 3 := if e<0 then 0 else if e=0 then 1 else 2
  let v : Fin 3 := if f<0 then 0 else if f=0 then 1 else 2
  let seed := ofSix 1 1 (-1) 0 ((s.val:Int)-1) ((v.val:Int)-1)
  let Q := U t e f
  have hmask : supportMask Q=supportMask seed := by
    by_cases h0n : e<0 <;> by_cases h0z : e=0 <;> by_cases h1n : f<0 <;> by_cases h1z : f=0 <;>
      simp [Q,U,X,seed,s,v,ofSix,h0n,h0z,h1n,h1z,supportMask,supportBit,show t≠0 by omega]
  have hsign : ∀ i j,0<Q i j ↔ 0<seed i j := by
    intro i j
    by_cases h0n : e<0 <;> by_cases h0z : e=0 <;> by_cases h1n : f<0 <;> by_cases h1z : f=0 <;>
      rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
      simp [Q,U,X,seed,s,v,ofSix,h0n,h0z,h1n,h1z] <;> omega
  obtain ⟨i,hi⟩ := cyclic_order_exhaustive p
  have ht' := (properClass_iff_table Q (ofSix_skew _ _ _ _ _ _) p i hi).mp hp
  have hs := (ChamberProperness.properClassTable_sign_iff Q seed hmask hsign i).mp ht'
  have hc := unit_x_seed s v i hs
  have hw : WiggleEquivalent Q p (order 0) := by
    apply (wiggle_iff_component Q (ofSix_skew _ _ _ _ _ _) p (order 0) i 0
      hi (fun _ _ _ => Iff.rfl)).mpr
    rwa [hmask]
  rw [ProperWiggleInvariants.markov_wiggle_invariant Q (ofSix_skew _ _ _ _ _ _) hw]
  change markov 1 1 (-t) 0 e f=_
  unfold markov squareSum cycleTerms
  ring

private theorem zero_d_seed : ∀ s : Fin 3, ∀ i : Fin 6,
    ProperClassTable (ofSix 1 0 (-1) 0 (-1) ((s.val:Int)-1)) i →
    component (supportMask (ofSix 1 0 (-1) 0 (-1) ((s.val:Int)-1))) i=component (supportMask (ofSix 1 0 (-1) 0 (-1) ((s.val:Int)-1))) 0 := by decide

theorem zero_d_scalar (t u f : Int) (ht : 1≤t) (hu : 1≤u)
    (p : CyclicOrder) (hp : ProperClass (X t u 0 f) p) :
    orderMarkov (X t u 0 f) p=1+t^2+u^2+f^2+t*u := by
  let s : Fin 3 := if f<0 then 0 else if f=0 then 1 else 2
  let seed := ofSix 1 0 (-1) 0 (-1) ((s.val:Int)-1)
  let Q := X t u 0 f
  have hmask : supportMask Q=supportMask seed := by
    by_cases h0n : f<0 <;> by_cases h0z : f=0 <;>
      simp [Q,U,X,seed,s,ofSix,h0n,h0z,supportMask,supportBit,show t≠0 by omega,show u≠0 by omega]
  have hsign : ∀ i j,0<Q i j ↔ 0<seed i j := by
    intro i j
    by_cases h0n : f<0 <;> by_cases h0z : f=0 <;>
      rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
      simp [Q,U,X,seed,s,ofSix,h0n,h0z] <;> omega
  obtain ⟨i,hi⟩ := cyclic_order_exhaustive p
  have ht' := (properClass_iff_table Q (ofSix_skew _ _ _ _ _ _) p i hi).mp hp
  have hs := (ChamberProperness.properClassTable_sign_iff Q seed hmask hsign i).mp ht'
  have hc := zero_d_seed s i hs
  have hw : WiggleEquivalent Q p (order 0) := by
    apply (wiggle_iff_component Q (ofSix_skew _ _ _ _ _ _) p (order 0) i 0
      hi (fun _ _ _ => Iff.rfl)).mpr
    rwa [hmask]
  rw [ProperWiggleInvariants.markov_wiggle_invariant Q (ofSix_skew _ _ _ _ _ _) hw]
  change markov 1 0 (-t) 0 (-u) f=_
  unfold markov squareSum cycleTerms
  ring

private theorem one_d_seed : ∀ s : Fin 2, ∀ i : Fin 6,
    ProperClassTable (ofSix 1 0 (-1) 1 (-1) (s.val:Int)) i →
    component (supportMask (ofSix 1 0 (-1) 1 (-1) (s.val:Int))) i=component (supportMask (ofSix 1 0 (-1) 1 (-1) (s.val:Int))) 0 := by decide

theorem one_d_scalar (t u f : Int) (ht : 1≤t) (hu : 1≤u) (hf : 0≤f)
    (p : CyclicOrder) (hp : ProperClass (X t u 1 f) p) :
    orderMarkov (X t u 1 f) p=2+t^2+u^2+f^2+t*u-(t+u)*f := by
  let s : Fin 2 := if f=0 then 0 else 1
  let seed := ofSix 1 0 (-1) 1 (-1) (s.val:Int)
  let Q := X t u 1 f
  have hmask : supportMask Q=supportMask seed := by
    by_cases h0 : f=0 <;>
      simp [Q,U,X,seed,s,ofSix,h0,supportMask,supportBit,show t≠0 by omega,show u≠0 by omega]
  have hsign : ∀ i j,0<Q i j ↔ 0<seed i j := by
    intro i j
    by_cases h0 : f=0 <;>
      rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
      simp [Q,U,X,seed,s,ofSix,h0] <;> omega
  obtain ⟨i,hi⟩ := cyclic_order_exhaustive p
  have ht' := (properClass_iff_table Q (ofSix_skew _ _ _ _ _ _) p i hi).mp hp
  have hs := (ChamberProperness.properClassTable_sign_iff Q seed hmask hsign i).mp ht'
  have hc := one_d_seed s i hs
  have hw : WiggleEquivalent Q p (order 0) := by
    apply (wiggle_iff_component Q (ofSix_skew _ _ _ _ _ _) p (order 0) i 0
      hi (fun _ _ _ => Iff.rfl)).mpr
    rwa [hmask]
  rw [ProperWiggleInvariants.markov_wiggle_invariant Q (ofSix_skew _ _ _ _ _ _) hw]
  change markov 1 0 (-t) 1 (-u) f=_
  unfold markov squareSum cycleTerms
  ring

private theorem negative_d_seed : ∀ s : Fin 2, ∀ i : Fin 6,
    ProperClassTable (ofSix 1 0 (-1) (-1) (-1) (-(s.val:Int))) i →
    component (supportMask (ofSix 1 0 (-1) (-1) (-1) (-(s.val:Int)))) i=component (supportMask (ofSix 1 0 (-1) (-1) (-1) (-(s.val:Int)))) 1 := by decide

theorem negative_d_scalar (t u D f : Int) (ht : 1≤t) (hu : 1≤u) (hD : 1≤D) (hf : f≤0)
    (p : CyclicOrder) (hp : ProperClass (X t u (-D) f) p) :
    orderMarkov (X t u (-D) f) p=1+D^2+t^2+u^2+f^2+t*u-u*D*f := by
  let s : Fin 2 := if f=0 then 0 else 1
  let seed := ofSix 1 0 (-1) (-1) (-1) (-(s.val:Int))
  let Q := X t u (-D) f
  have hmask : supportMask Q=supportMask seed := by
    by_cases h0 : f=0 <;>
      simp [Q,U,X,seed,s,ofSix,h0,supportMask,supportBit,show t≠0 by omega,show u≠0 by omega,show D≠0 by omega]
  have hsign : ∀ i j,0<Q i j ↔ 0<seed i j := by
    intro i j
    by_cases h0 : f=0 <;>
      rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
      simp [Q,U,X,seed,s,ofSix,h0] <;> omega
  obtain ⟨i,hi⟩ := cyclic_order_exhaustive p
  have ht' := (properClass_iff_table Q (ofSix_skew _ _ _ _ _ _) p i hi).mp hp
  have hs := (ChamberProperness.properClassTable_sign_iff Q seed hmask hsign i).mp ht'
  have hc := negative_d_seed s i hs
  have hw : WiggleEquivalent Q p (order 1) := by
    apply (wiggle_iff_component Q (ofSix_skew _ _ _ _ _ _) p (order 1) i 1
      hi (fun _ _ _ => Iff.rfl)).mpr
    rwa [hmask]
  rw [ProperWiggleInvariants.markov_wiggle_invariant Q (ofSix_skew _ _ _ _ _ _) hw]
  change markov 1 (-t) 0 (-u) (-D) (-f)=_
  unfold markov squareSum cycleTerms
  ring

theorem unit_x_large (t u z F : Int) (ht : 1≤t) (hu : 1≤u) (hF : t+u=F) :
    F<2+t^2+u^2+z^2+t*u-t*z := by
  have h:=EqualUnitScalar.triangle_scalar_large u t z hu ht
  nlinarith

theorem zero_d_large (t u f F : Int) (ht : 1≤t) (hu : 1≤u) (hF : t+u=F) :
    F<1+t^2+u^2+f^2+t*u := by
  nlinarith [mul_nonneg (show 0≤t by omega) (show 0≤t-1 by omega),
    mul_nonneg (show 0≤u by omega) (show 0≤u-1 by omega),
    mul_nonneg (show 0≤t by omega) (show 0≤u by omega),sq_nonneg f]

theorem one_d_large (t u f F : Int) (ht : 1≤t) (hu : 1≤u) (hF : t+u=F) :
    F<2+t^2+u^2+f^2+t*u-(t+u)*f := by
  nlinarith [sq_nonneg (2*f-(t+u)),sq_nonneg (t-u),
    mul_nonneg (show 0≤F-2 by omega) (show 0≤F by omega)]

theorem negative_d_large (t u D f F : Int) (ht : 1≤t) (hu : 1≤u)
    (hD : 1≤D) (hf : f≤0) (hF : t+u=F) :
    F<1+D^2+t^2+u^2+f^2+t*u-u*D*f := by
  have h:=zero_d_large t u f F ht hu hF
  have hpos : 0≤u*D := mul_nonneg (by omega) (by omega)
  nlinarith [sq_nonneg D,mul_nonpos_of_nonneg_of_nonpos hpos hf]

#print axioms unit_x_scalar
#print axioms zero_d_scalar
#print axioms one_d_scalar
#print axioms negative_d_scalar
#print axioms unit_x_large
#print axioms zero_d_large
#print axioms one_d_large
#print axioms negative_d_large
end Rank4ReviewRound2.RightAcyclicUnitScalar
