import Rank4StructureRound2.FlatMixedScalar
import QuiverProofs.ChamberProperness
import QuiverProofs.ProperObstructionSoundness

/-! Actual proper-order formula for the mixed flat-block orientation, including
both zero walls. All proper classes lie in the canonical class's wiggle
component. MA proper-order existence and scalar admissibility are separate.+-/
namespace QuiverProofs.Rank4StructureRound2.FlatMixedOrder
open Census ProperOrder ProperWiggle ProperMutation ProperObstructionSoundness
open FlatMixedScalar

private theorem four (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
def peak (a b c d E f : Int) : Matrix 4 := ofSix a b (-c) d E f

theorem proper_markov (a b c d E f : Int)
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0≤d) (hE : 0≤E) (hf : 0<f)
    (p : CyclicOrder) (hp : ProperClass (peak a b c d E f) p) :
    orderMarkov (peak a b c d E f) p=scalar a b c d E f := by
  let Q := peak a b c d E f
  let seed := ofSix 1 1 (-1) (if d=0 then 0 else 1) (if E=0 then 0 else 1) 1
  have hmask : supportMask Q=supportMask seed := by
    by_cases hd0 : d=0 <;> by_cases hE0 : E=0 <;>
      simp [Q,peak,seed,supportMask,supportBit,ofSix,hd0,hE0,
        show a≠0 by omega,show b≠0 by omega,show c≠0 by omega,show f≠0 by omega]
  have hsign : ∀ i j,0<Q i j ↔ 0<seed i j := by
    intro i j
    by_cases hd0 : d=0 <;> by_cases hE0 : E=0 <;>
      rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
      simp [Q,peak,seed,ofSix,hd0,hE0] <;> omega
  obtain ⟨i,hi⟩ := cyclic_order_exhaustive p
  have ht := (properClass_iff_table Q (ofSix_skew _ _ _ _ _ _) p i hi).mp hp
  have hs := (ChamberProperness.properClassTable_sign_iff Q seed hmask hsign i).mp ht
  have hcomp : ∀ i : Fin 6, ProperClassTable seed i→
      component (supportMask seed) i=component (supportMask seed) 0 := by
    by_cases hd0 : d=0 <;> by_cases hE0 : E=0 <;>
      simp only [seed,hd0,hE0,ite_true,ite_false] <;> decide
  have hwiggle : WiggleEquivalent Q p (order 0) := by
    apply (wiggle_iff_component Q (ofSix_skew _ _ _ _ _ _) p (order 0) i 0
      hi (fun _ _ _ => Iff.rfl)).mpr
    rw [hmask]
    exact hcomp i hs
  have hM := ProperWiggleInvariants.markov_wiggle_invariant Q (ofSix_skew _ _ _ _ _ _) hwiggle
  rw [hM]
  change Algebra.markov a b (-c) d E f=scalar a b c d E f
  unfold Algebra.markov Algebra.squareSum Algebra.cycleTerms scalar
  ring

theorem matrix_pfaffian (a b c d E f : Int) :
    matrixPfaffian (peak a b c d E f)=pfaffian a b c d E f := by
  unfold matrixPfaffian peak pfaffian
  simp only [ofSix]
  ring

theorem admissible_proper_scalar_exceeds_height (a b c d E f : Int)
    (ha : 2≤a) (hb : 1≤b) (hd : 0≤d) (hE : 0≤E) (hc : a*E<c)
    (hleft : a*c-E<f) (hright : a*b+(a^2-1)*d<f)
    (p : CyclicOrder) (hp : ProperClass (peak a b c d E f) p)
    (hnecessary : 2*abs (matrixPfaffian (peak a b c d E f))<
      orderMarkov (peak a b c d E f) p) :
    f<orderMarkov (peak a b c d E f) p := by
  have ha0 : 0≤a := by omega
  have ha2 : 4≤a^2 := by nlinarith
  have hde := mul_nonneg (show 0≤a^2-1 by omega) hd
  have hab := mul_nonneg ha0 (show 0≤b-1 by omega)
  have hc0 : 0<c := by have h := mul_nonneg ha0 hE; omega
  have hf : 0<f := by nlinarith
  rw [proper_markov a b c d E f (by omega) (by omega) hc0 hd hE hf p hp] at *
  rw [matrix_pfaffian] at hnecessary
  exact scalar_exceeds_height a b c d E f ha hb hd hE hc hleft hright hnecessary

#print axioms proper_markov
#print axioms admissible_proper_scalar_exceeds_height
end QuiverProofs.Rank4StructureRound2.FlatMixedOrder
