import Rank4ReviewRound2.ZeroUnitDecomposition
import Rank4Round2.ZeroMAGuard

/-! The two incident unit edges b=c=1 in a zero square-overflow peak.
Overflow forces a balanced factorization and a scalar below three. The
semantic consumer retains the properness and endpoint bridges explicitly.
-/
namespace Rank4ReviewRound2.ZeroDoubleUnitOverflow
open QuiverProofs Rank4Coordinator Rank4Round2 Rank4CoordinatorR2 ZeroUnitDecomposition

theorem double_unit_zero_overflow_markov (d e f : Int) (H : Nat)
    (hd : 0<d) (he : 0<e) (hdH : d≤(H:Int)) (heH : e≤(H:Int))
    (huH : f-1≤(H:Int)) (hvH : d*e-f≤(H:Int))
    (hf : (H:Int)<f) (hover : f+(H:Int)<1+d*e) :
    zeroMarkov 1 1 d e f≤1 := by
  obtain ⟨u,v,hu,hv,hup,hvp,hd2,he2,huH',hvH',hde,hf',hfu,hfv,hM,hK,hpf⟩ :=
    zero_unit_overflow_decomposition 1 d e f H (by decide) hd he (by omega)
      hdH heH huH hvH hf hover
  have huv : u=v := by omega
  have hq : d*e=1+2*u := by omega
  have hd3 : 3≤d := by
    by_contra h
    have hd' : d=2 := by omega
    rw [hd'] at hq
    omega
  have he3 : 3≤e := by
    by_contra h
    have he' : e=2 := by omega
    rw [he'] at hq
    omega
  have hq9 : 9≤d*e := by
    have h := mul_nonneg (show 0≤d-3 by omega) (show 0≤e-3 by omega)
    nlinarith [h]
  have hpair := mul_nonneg (show 0≤d*d-4 by nlinarith) (show 0≤e*e-4 by nlinarith)
  have hmid : zeroMarkov 1 1 d e f=2+d*d+e*e-(u+1)*(u+1) := by
    rw [hM]
    unfold triangleMarkov
    rw [←huv]
    nlinarith [hq]
  nlinarith [hmid,hpair,hq,hq9]

theorem double_unit_zero_overflow_NMA
    (hExist : ProperObstructionSoundness.MAHasTotalProper4)
    (hEnd : ProperObstructionSoundness.EndpointTopological4)
    (d e f : Int) (H : Nat) (hd : 0<d) (he : 0<e)
    (h0 : HeightLe (mutate (zeroPeak 1 1 d e f) 0) H)
    (h1 : HeightLe (mutate (zeroPeak 1 1 d e f) 1) H)
    (hf : (H:Int)<f) (hover : f+(H:Int)<1+d*e) :
    ¬MutationAcyclic (zeroPeak 1 1 d e f) := by
  have hb := h0 1 2
  have hc := h0 1 3
  have hu := h0 2 3
  have hv := h1 2 3
  rw [zeroPeak_zero 1 1 d e f (by decide) (by decide)] at hb hc hu
  rw [zeroPeak_one 1 1 d e f hd he] at hv
  simp only [ofSix] at hb hc hu hv
  have hm := double_unit_zero_overflow_markov d e f H hd he hb.2 (by omega)
    hu.2 (by omega) hf hover
  intro hma
  have hlow := zeroPeak_MA_markov hExist hEnd 1 1 d e f
    (by decide) (by decide) hd he (by omega) hma
  omega

#print axioms double_unit_zero_overflow_markov
#print axioms double_unit_zero_overflow_NMA
end Rank4ReviewRound2.ZeroDoubleUnitOverflow
