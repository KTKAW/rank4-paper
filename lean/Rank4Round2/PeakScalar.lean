import Rank4Round2.UnitMarkov
import QuiverProofs.ChamberProperness
import QuiverProofs.ProperObstructionSoundness
import QuiverProofs.ProperWiggleInvariants

/-! The scalar of every proper cyclic class in the normalized positive peak
cone. The MA-to-scalar consumer retains exactly the two existing structural
bridges as explicit arguments; no inhabitant of either is asserted here.
-/
namespace Rank4Round2
open QuiverProofs Rank4Coordinator ProperOrder ProperWiggle ProperMutation
open ProperObstructionSoundness

private theorem four (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega

theorem positivePeak_proper_markov (a b c d e f : Int)
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e) (hf : 0<f)
    (p : CyclicOrder) (hp : ProperClass (positivePeak a b c d e f) p) :
    orderMarkov (positivePeak a b c d e f) p = Algebra.markov a b (-c) d (-e) f := by
  let Q := positivePeak a b c d e f
  let seed := ofSix 1 1 (-1) 1 (-1) 1
  have hmask : supportMask Q = supportMask seed := by
    simp [Q,seed,positivePeak,supportMask,supportBit,ofSix,
      show a≠0 by omega,show b≠0 by omega,show c≠0 by omega,
      show d≠0 by omega,show e≠0 by omega,show f≠0 by omega]
  have hsign : ∀ i j, 0<Q i j ↔ 0<seed i j := by
    intro i j
    rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
      simp [Q,seed,positivePeak,ofSix] <;> omega
  obtain ⟨i,hi⟩ := cyclic_order_exhaustive p
  have ht := (properClass_iff_table Q (ofSix_skew _ _ _ _ _ _) p i hi).mp hp
  have hs := (ChamberProperness.properClassTable_sign_iff Q seed hmask hsign i).mp ht
  have hi0 : i=0 := (show ∀ i : Fin 6, ProperClassTable seed i → i=0 by decide) i hs
  rw [ProperWiggleInvariants.markov_cyclic Q (ofSix_skew _ _ _ _ _ _) p (order i) hi]
  subst i
  rfl

/-- Conditional on precisely the existing MA properness and endpoint bridges,
the canonical scalar in this sign cone is nonnegative. -/
theorem positivePeak_ma_markov_nonnegative
    (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4)
    (a b c d e f : Int)
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e) (hf : 0<f)
    (hma : MutationAcyclic (positivePeak a b c d e f)) :
    0≤Algebra.markov a b (-c) d (-e) f := by
  let B := positivePeak a b c d e f
  have hsk : SkewSymmetric B := ofSix_skew _ _ _ _ _ _
  obtain ⟨p,hp⟩ := hExist B hsk hma
  obtain ⟨w,hw⟩ := hma
  have hC := word_preserves_skew B w hsk
  obtain ⟨r,htr,hpr⟩ := totalProper_lifts_word B hsk p hp w
  obtain ⟨q,hq,hrq⟩ := hEnd _ hC hw r hpr
  have htrans := transport_markov hsk htr
  have hwiggle := ProperWiggleInvariants.markov_wiggle_invariant _ hC hrq
  have hsource := positivePeak_proper_markov a b c d e f ha hb hc hd he hf p
    (totalProper_proper B p hp)
  have hscalar : orderMarkov (applyWord B w) q = Algebra.markov a b (-c) d (-e) f :=
    hwiggle.symm.trans (htrans.trans hsource)
  have hnonneg : 0≤orderMarkov (applyWord B w) q := by
    unfold orderMarkov
    have h := Algebra.squareSum_le_markov _ _ _ _ _ _
      hq.1 hq.2.1 hq.2.2.1 hq.2.2.2.1 hq.2.2.2.2.1 hq.2.2.2.2.2
    have h0 := Algebra.square_nonnegative ((applyWord B w) (q.toFun 0) (q.toFun 1))
    have h1 := Algebra.square_nonnegative ((applyWord B w) (q.toFun 0) (q.toFun 2))
    have h2 := Algebra.square_nonnegative ((applyWord B w) (q.toFun 0) (q.toFun 3))
    have h3 := Algebra.square_nonnegative ((applyWord B w) (q.toFun 1) (q.toFun 2))
    have h4 := Algebra.square_nonnegative ((applyWord B w) (q.toFun 1) (q.toFun 3))
    have h5 := Algebra.square_nonnegative ((applyWord B w) (q.toFun 2) (q.toFun 3))
    unfold Algebra.squareSum at h
    omega
  rw [hscalar] at hnonneg
  exact hnonneg

/-- A genuine MA-specific local guard, conditional on the two named bridges.
All incident parameters are at least two; flat plateaus are not covered. -/
theorem unit_ma_guard_of_bridges (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4)
    (b c d e f : Int) (H : Nat)
    (hb : 2≤b) (hc : 2≤c) (hd : 2≤d) (he : 2≤e)
    (h0 : HeightLe (mutate (unitPeak b c d e f) 0) H)
    (h1 : HeightLe (mutate (unitPeak b c d e f) 1) H)
    (hf : (H:Int)<f) (hma : MutationAcyclic (unitPeak b c d e f)) :
    PrefixHeightLe (mutate (unitPeak b c d e f) 0) [1,0,1] H := by
  have hm := positivePeak_ma_markov_nonnegative hExist hEnd 1 b c d e f
    (by decide) (by omega) (by omega) (by omega) (by omega) (by omega) hma
  rw [← unitMarkov_eq] at hm
  exact unit_guard_of_markov b c d e f H hb hc hd he h0 h1 hf (by omega)

#print axioms positivePeak_proper_markov
#print axioms positivePeak_ma_markov_nonnegative
#print axioms unit_ma_guard_of_bridges
end Rank4Round2
