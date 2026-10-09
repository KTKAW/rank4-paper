import Rank4Round2.PeakScalar
import Rank4ReviewRound2.UnitUniformGuard
import Rank4CoordinatorR2.ScalarTransport

/-! The normalized all-positive strict unit peak has an actual bounded
reroute when the two existing properness bridges are supplied. These named
premises remain explicit. No global plateau or height coverage follows here.
-/
namespace Rank4Round2
open QuiverProofs Rank4Coordinator Census ProperOrder ProperWiggle
open ProperMutation ProperObstructionSoundness

theorem positivePeak_connected (a b c d e f : Int)
    (hb : 0<b) (hd : 0<d) (hf : 0<f) :
    ConnectedSupport (positivePeak a b c d e f) := by
  intro aa bb cc dd hs
  have h02 : aa=cc := hs 0 2 (by change b≠0; omega)
  have h12 : bb=cc := hs 1 2 (by change d≠0; omega)
  have h23 : cc=dd := hs 2 3 (by change f≠0; omega)
  exact ⟨h02.trans h12.symm,h12,h23⟩

theorem unit_ma_scalar_bound (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4)
    (b c d e f : Int) (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e) (hf : 0<f)
    (hma : MutationAcyclic (unitPeak b c d e f)) :
    2*|unitPfaffian b c d e f|<unitMarkov b c d e f := by
  let B := unitPeak b c d e f
  have hsk : SkewSymmetric B := ofSix_skew _ _ _ _ _ _
  obtain ⟨p,hp⟩ := hExist B hsk hma
  have h := Rank4CoordinatorR2.connected_MA_totalProper_strict_pfaffian hEnd B hsk
    (positivePeak_connected 1 b c d e f hb hd hf) hma p hp
  have hscalar : orderMarkov B p=unitMarkov b c d e f := by
    change orderMarkov (positivePeak 1 b c d e f) p=unitMarkov b c d e f
    rw [positivePeak_proper_markov 1 b c d e f (by decide) hb hc hd he hf p
      (totalProper_proper B p hp)]
    exact (unitMarkov_eq b c d e f).symm
  have hpf : matrixPfaffian B=unitPfaffian b c d e f := by
    change Algebra.pfaffian 1 b (-c) d (-e) f=unitPfaffian b c d e f
    exact (unitPfaffian_eq b c d e f).symm
  rw [hscalar,hpf,Int.natCast_natAbs] at h
  exact h

theorem unit_ma_uniform_guard (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4)
    (b c d e f : Int) (H : Nat)
    (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e)
    (h0 : HeightLe (mutate (unitPeak b c d e f) 0) H)
    (h1 : HeightLe (mutate (unitPeak b c d e f) 1) H)
    (hf : (H:Int)<f) (hma : MutationAcyclic (unitPeak b c d e f)) :
    PrefixHeightLe (mutate (unitPeak b c d e f) 0) [1,0,1] H := by
  have hs := unit_ma_scalar_bound hExist hEnd b c d e f hb hc hd he (by omega) hma
  exact Rank4ReviewRound2.UnitUniformGuard.unit_uniform_guard b c d e f H
    hb hc hd he h0 h1 hf (by omega)

theorem unit_ma_uniform_count_decrease
    (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4)
    (b c d e f : Int) (H : Nat)
    (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e)
    (h0 : HeightLe (mutate (unitPeak b c d e f) 0) H)
    (h1 : HeightLe (mutate (unitPeak b c d e f) 1) H)
    (hf : (H:Int)<f) (hma : MutationAcyclic (unitPeak b c d e f))
    (tail : List (Fin 4)) :
    overCount (mutate (unitPeak b c d e f) 0)
        ([1,0,1]++tail.map Forks.swap01.invFun) H + 1 =
      overCount (mutate (unitPeak b c d e f) 0) ([0,1]++tail) H := by
  have hs := unit_ma_scalar_bound hExist hEnd b c d e f hb hc hd he (by omega) hma
  exact Rank4ReviewRound2.UnitUniformGuard.unit_uniform_count_decrease b c d e f H
    hb hc hd he h0 h1 hf (by omega) tail

theorem unit_ma_uniform_acyclic_reroute
    (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4)
    (b c d e f : Int) (H : Nat)
    (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e)
    (h0 : HeightLe (mutate (unitPeak b c d e f) 0) H)
    (h1 : HeightLe (mutate (unitPeak b c d e f) 1) H)
    (hf : (H:Int)<f) (tail : List (Fin 4))
    (ha : Acyclic (applyWord (mutate (unitPeak b c d e f) 0) ([0,1]++tail))) :
    Acyclic (applyWord (mutate (unitPeak b c d e f) 0)
      ([1,0,1]++tail.map Forks.swap01.invFun)) ∧
      overCount (mutate (unitPeak b c d e f) 0)
        ([1,0,1]++tail.map Forks.swap01.invFun) H <
      overCount (mutate (unitPeak b c d e f) 0) ([0,1]++tail) H := by
  have hmaL : MutationAcyclic (mutate (unitPeak b c d e f) 0) := ⟨[0,1]++tail,ha⟩
  have hma := (mutationAcyclic_iff _ 0).mp hmaL
  apply strict_peak_reroute _ 0 1 [1,0,1] tail Forks.swap01 H _ h1
    (unitPeak_detour_endpoint b c d e f hb hc hd he)
    (unit_ma_uniform_guard hExist hEnd b c d e f H hb hc hd he h0 h1 hf hma) ha
  intro hP
  have h := (hP 2 3).2
  simp only [unitPeak,positivePeak,ofSix] at h
  omega

#print axioms unit_ma_scalar_bound
#print axioms unit_ma_uniform_guard
#print axioms unit_ma_uniform_acyclic_reroute
end Rank4Round2
