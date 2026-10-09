import Rank4CoordinatorR2.ScalarTransport
import Rank4CoordinatorR2.ZeroSquareMarkov
import QuiverProofs.ChamberProperness

/-! Canonical proper scalar for a positive zero-pivot peak and its
conditional MA lower bound. The two structural bridges remain explicit. -/
namespace Rank4CoordinatorR2
open QuiverProofs QuiverProofs.Census QuiverProofs.ProperOrder
  QuiverProofs.ProperWiggle QuiverProofs.ProperMutation
  QuiverProofs.ProperObstructionSoundness

private theorem four (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega

theorem zeroPeak_connected (b c d e f : Int) (hb : 0<b) (hd : 0<d) (hf : 0<f) :
    ConnectedSupport (ofSix 0 b (-c) d (-e) f) := by
  intro aa bb cc dd hs
  have h02 : aa=cc := hs 0 2 (by change b≠0; omega)
  have h12 : bb=cc := hs 1 2 (by change d≠0; omega)
  have h23 : cc=dd := hs 2 3 (by change f≠0; omega)
  exact ⟨h02.trans h12.symm,h12,h23⟩

theorem zeroPeak_proper_markov (b c d e f : Int)
    (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e) (hf : 0<f)
    (p : CyclicOrder) (hp : ProperClass (ofSix 0 b (-c) d (-e) f) p) :
    orderMarkov (ofSix 0 b (-c) d (-e) f) p = zeroMarkov b c d e f := by
  let Q := ofSix 0 b (-c) d (-e) f
  let seed := ofSix 0 1 (-1) 1 (-1) 1
  have hmask : supportMask Q = supportMask seed := by
    simp [Q,seed,supportMask,supportBit,ofSix,
      show b≠0 by omega,show c≠0 by omega,show d≠0 by omega,
      show e≠0 by omega,show f≠0 by omega]
  have hsign : ∀ i j, 0<Q i j ↔ 0<seed i j := by
    intro i j
    rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
      simp [Q,seed,ofSix] <;> omega
  obtain ⟨i,hi⟩ := cyclic_order_exhaustive p
  have ht := (properClass_iff_table Q (ofSix_skew _ _ _ _ _ _) p i hi).mp hp
  have hs := (ChamberProperness.properClassTable_sign_iff Q seed hmask hsign i).mp ht
  have hi03 : i=0 ∨ i=3 :=
    (show ∀ i : Fin 6, ProperClassTable seed i → i=0 ∨ i=3 by decide) i hs
  have hwiggle : WiggleEquivalent Q p (order 0) := by
    apply (wiggle_iff_component Q (ofSix_skew _ _ _ _ _ _) p (order 0) i 0
      hi (fun _ _ _ => Iff.rfl)).mpr
    rw [hmask]
    rcases hi03 with rfl|rfl <;> decide
  have hM := ProperWiggleInvariants.markov_wiggle_invariant Q
    (ofSix_skew _ _ _ _ _ _) hwiggle
  rw [zeroMarkov_eq]
  exact hM

/-- An actual MA parent has the required lower scalar provided the named
existence and endpoint bridges are supplied. No such supplier is asserted. -/
theorem zeroPeak_MA_markov (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4)
    (b c d e f : Int)
    (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e) (hf : 0<f)
    (hma : MutationAcyclic (ofSix 0 b (-c) d (-e) f)) :
    3 ≤ zeroMarkov b c d e f := by
  let B := ofSix 0 b (-c) d (-e) f
  have hsk : SkewSymmetric B := ofSix_skew _ _ _ _ _ _
  obtain ⟨p,hp⟩ := hExist B hsk hma
  have hm := connected_MA_totalProper_markov hEnd B hsk
    (zeroPeak_connected b c d e f hb hd hf) hma p hp
  rw [zeroPeak_proper_markov b c d e f hb hc hd he hf p
    (totalProper_proper B p hp)] at hm
  exact hm

theorem zeroPeak_MA_square_guard (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4)
    (b c d e f : Int) (H : Nat)
    (hb : 2≤b) (hc : 2≤c) (hd : 2≤d) (he : 2≤e)
    (hf : (H:Int)<f)
    (h0lo : -(H:Int)≤f-b*c) (h0hi : f-b*c≤(H:Int))
    (h1lo : -(H:Int)≤f-d*e) (h1hi : f-d*e≤(H:Int))
    (hma : MutationAcyclic (ofSix 0 b (-c) d (-e) f)) :
    -(H:Int)≤f-b*c-d*e ∧ f-b*c-d*e≤(H:Int) := by
  exact zero_square_guard_of_markov b c d e f H hb hc hd he hf h0lo h0hi h1lo h1hi
    (zeroPeak_MA_markov hExist hEnd b c d e f (by omega) (by omega) (by omega)
      (by omega) (by omega) hma)

#print axioms zeroPeak_connected
#print axioms zeroPeak_proper_markov
#print axioms zeroPeak_MA_markov
#print axioms zeroPeak_MA_square_guard
end Rank4CoordinatorR2
