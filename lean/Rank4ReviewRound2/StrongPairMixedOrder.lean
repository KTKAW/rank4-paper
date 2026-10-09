import Rank4ReviewRound2.StrongPairMixedScalar
import Rank4StructureRound2.SuperScalarPeak

/-! Proper scalar exclusion for the full mixed range c>(a-1)E.
The endpoint bridge is explicit in this frozen layer. -/
namespace Rank4ReviewRound2.StrongPairMixedOrder
open QuiverProofs
open ProperOrder ProperMutation ProperObstructionSoundness
open QuiverProofs.Rank4StructureRound2
open StrongPairMixedScalar

theorem mixed_totalProper_scalar_bound (hEnd : EndpointTopological4)
    (a b c d E f : Int) (ha : 2≤a) (hb : 1≤b) (hc : 0<c)
    (hd : 0≤d) (hE : 0≤E) (hf : a<f)
    (hturn : (a-1)*E<c) (hFirst : b+a*d<f) (hcBound : c<f)
    (hleft : a*c-E<f) (hright : a*b+(a^2-1)*d<f)
    (hma : MutationAcyclic (FlatMixedOrder.peak a b c d E f))
    (p : CyclicOrder) (hp : TotalProper (FlatMixedOrder.peak a b c d E f) p) :
    f<orderMarkov (FlatMixedOrder.peak a b c d E f) p := by
  by_cases hcBig : a*E<c
  · exact SuperScalarPeak.mixed_totalProper_scalar_bound hEnd a b c d E f
      ha hb hd hE hcBig hleft hright hma p hp
  · have hPf := SuperScalarPeak.MA_totalProper_pfaffian_bound hEnd _
      (ofSix_skew _ _ _ _ _ _) hma p hp
    have hM := FlatMixedOrder.proper_markov a b c d E f (by omega) (by omega)
      hc hd hE (by omega) p (totalProper_proper _ _ hp)
    change 2*abs (matrixPfaffian (FlatMixedOrder.peak a b c d E f))≤
      orderMarkov (FlatMixedOrder.peak a b c d E f) p at hPf
    rw [FlatMixedOrder.matrix_pfaffian,hM] at hPf
    rw [hM]
    by_contra hnot
    have hNeg := adjacent_mixed_low_pfaffian_negative a b c d E f ha hb hd hE hf
      hturn (by omega) (by nlinarith) (by have he:=mul_nonneg (show 0≤a-1 by omega) hE; nlinarith)
      (by have habs:=le_abs_self (FlatMixedScalar.pfaffian a b c d E f); omega)
    have hnon := abs_nonneg (FlatMixedScalar.pfaffian a b c d E f)
    omega

#print axioms mixed_totalProper_scalar_bound
end Rank4ReviewRound2.StrongPairMixedOrder
