import Rank4StructureRound2.PositivePeakScalar
import QuiverProofs.ChamberProperness
import QuiverProofs.ProperObstructionSoundness

/-! The arithmetic peak scalar is the scalar of every actual proper class
in the complete positive orientation. The scalar admissibility hypothesis is
explicit: neither MA proper-order existence nor endpoint transport is asserted.
-/
namespace QuiverProofs.Rank4StructureRound2.PositivePeakOrder
open Census ProperOrder ProperWiggle ProperMutation ProperObstructionSoundness
open PositivePeakScalar

private theorem four (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega

def peak (a b c d e f : Int) : Matrix 4 := ofSix a b (-c) d (-e) f

theorem proper_markov (a b c d e f : Int)
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e) (hf : 0<f)
    (p : CyclicOrder) (hp : ProperClass (peak a b c d e f) p) :
    orderMarkov (peak a b c d e f) p=scalar a b c d e f := by
  let Q := peak a b c d e f
  let seed := ofSix 1 1 (-1) 1 (-1) 1
  have hmask : supportMask Q=supportMask seed := by
    simp [Q,peak,seed,supportMask,supportBit,ofSix,
      show a≠0 by omega,show b≠0 by omega,show c≠0 by omega,
      show d≠0 by omega,show e≠0 by omega,show f≠0 by omega]
  have hsign : ∀ i j,0<Q i j ↔ 0<seed i j := by
    intro i j
    rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
      simp [Q,peak,seed,ofSix] <;> omega
  obtain ⟨i,hi⟩ := cyclic_order_exhaustive p
  have ht := (properClass_iff_table Q (ofSix_skew _ _ _ _ _ _) p i hi).mp hp
  have hs := (ChamberProperness.properClassTable_sign_iff Q seed hmask hsign i).mp ht
  have hi0 : i=0 := (show ∀ i : Fin 6,ProperClassTable seed i→i=0 by decide) i hs
  subst i
  have hM := ProperWiggleInvariants.markov_cyclic Q (ofSix_skew _ _ _ _ _ _) p (order 0) hi
  rw [hM]
  change Algebra.markov a b (-c) d (-e) f=scalar a b c d e f
  unfold Algebra.markov Algebra.squareSum Algebra.cycleTerms scalar
  ring

theorem matrix_pfaffian (a b c d e f : Int) :
    matrixPfaffian (peak a b c d e f)=pfaffian a b c d e f := by
  unfold matrixPfaffian peak pfaffian
  simp only [ofSix]
  ring

theorem admissible_proper_scalar_exceeds_height (a b c d e f : Int)
    (ha : 2≤a) (hb : 1≤b) (hc : 1≤c) (hd : 1≤d) (he : 1≤e)
    (hE : e+a*c<f) (hB : b+a*d<f)
    (p : CyclicOrder) (hp : ProperClass (peak a b c d e f) p)
    (hnecessary : 2*abs (matrixPfaffian (peak a b c d e f))<
      orderMarkov (peak a b c d e f) p) :
    f<orderMarkov (peak a b c d e f) p := by
  have hac := mul_nonneg (show 0≤a by omega) (show 0≤c-1 by omega)
  have hf : 0<f := by nlinarith
  rw [proper_markov a b c d e f (by omega) (by omega) (by omega) (by omega)
    (by omega) hf p hp] at *
  rw [matrix_pfaffian] at hnecessary
  exact scalar_exceeds_height a b c d e f ha hb hc hd he hE hB hnecessary

#print axioms proper_markov
#print axioms admissible_proper_scalar_exceeds_height
end QuiverProofs.Rank4StructureRound2.PositivePeakOrder
