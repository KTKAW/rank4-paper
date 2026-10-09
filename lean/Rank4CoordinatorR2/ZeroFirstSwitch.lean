import Rank4CoordinatorR2.Foundation
import QuiverProofs.ChamberProperness

/-! Work on zero-pair first-entry switching. This module is not yet a
whole arbitrary-word or height-coverage theorem. -/
namespace Rank4CoordinatorR2.ZeroFirstSwitch
open QuiverProofs Rank4Coordinator Rank4CoordinatorR2
open ProperOrder ProperWiggle ProperMutation ProperObstructionSoundness
set_option maxHeartbeats 2000000

def peak (b c d E f : Int) : Matrix 4 := ofSix 0 b (-c) d E f

def scalar (b c d E f : Int) : Int :=
  b^2+c^2+d^2+E^2+f^2-b*c*f+d*E*f

private theorem four (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega

private theorem sign_chamber_components :
    ∀ d E : Fin 3, ¬(d.val=0 ∧ E.val=2) → ∀ i : Fin 6,
      ProperClassTable (ofSix 0 1 (-1) ((d.val:Int)-1) ((E.val:Int)-1) 1) i →
      component (supportMask (ofSix 0 1 (-1) ((d.val:Int)-1) ((E.val:Int)-1) 1)) i=
      component (supportMask (ofSix 0 1 (-1) ((d.val:Int)-1) ((E.val:Int)-1) 1)) 0 := by
  decide


def signIndex (x : Int) : Fin 3 := if x<0 then 0 else if x=0 then 1 else 2

theorem proper_markov (b c d E f : Int) (hb : 0<b) (hc : 0<c) (hf : 0<f)
    (hforbid : ¬(d<0 ∧ 0<E)) (p : CyclicOrder)
    (hp : ProperClass (peak b c d E f) p) :
    orderMarkov (peak b c d E f) p=scalar b c d E f := by
  let Q := peak b c d E f
  let seed := ofSix 0 1 (-1) ((signIndex d).val-1) ((signIndex E).val-1) 1
  have hmask : supportMask Q=supportMask seed := by
    by_cases hd : d<0 <;> by_cases hd0 : d=0 <;>
      by_cases he : E<0 <;> by_cases he0 : E=0 <;>
      simp [Q,peak,seed,signIndex,supportMask,supportBit,ofSix,hd,hd0,he,he0,
        show b≠0 by omega,show c≠0 by omega,show f≠0 by omega]
  have hsign : ∀ i j,0<Q i j ↔ 0<seed i j := by
    intro i j
    by_cases hd : d<0 <;> by_cases hd0 : d=0 <;>
      by_cases he : E<0 <;> by_cases he0 : E=0 <;>
      rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
      simp [Q,peak,seed,signIndex,ofSix,hd,hd0,he,he0] <;> omega
  have hnot : ¬((signIndex d).val=0 ∧ (signIndex E).val=2) := by
    by_cases hd : d<0 <;> by_cases hd0 : d=0 <;>
      by_cases he : E<0 <;> by_cases he0 : E=0 <;>
      simp [signIndex,hd,hd0,he,he0] <;> omega
  obtain ⟨i,hi⟩ := cyclic_order_exhaustive p
  have ht := (properClass_iff_table Q (ofSix_skew _ _ _ _ _ _) p i hi).mp hp
  have hs := (ChamberProperness.properClassTable_sign_iff Q seed hmask hsign i).mp ht
  have hw : WiggleEquivalent Q p (order 0) := by
    apply (wiggle_iff_component Q (ofSix_skew _ _ _ _ _ _) p (order 0) i 0
      hi (fun _ _ _ => Iff.rfl)).mpr
    rw [hmask]
    exact sign_chamber_components (signIndex d) (signIndex E) hnot i hs
  have hm := ProperWiggleInvariants.markov_wiggle_invariant Q (ofSix_skew _ _ _ _ _ _) hw
  rw [hm]
  change Algebra.markov 0 b (-c) d E f=scalar b c d E f
  unfold Algebra.markov Algebra.squareSum Algebra.cycleTerms scalar
  ring

theorem unit_scalar_exceeds (c d E f : Int) (hf : 0<f)
    (hforbid : ¬(d<0 ∧ 0<E)) (hd : d≤1) (hd1 : d=1 → E≤0) :
    f<scalar 1 c d E f := by
  by_cases hpos : 0<d
  · have hdEq : d=1 := by omega
    have he := hd1 hdEq
    subst d
    unfold scalar
    nlinarith [sq_nonneg (2*c-f),sq_nonneg (2*E+f),sq_nonneg (f-1)]
  · have hde : 0≤d*E := by
      by_cases hz : d=0
      · simp [hz]
      · have hdN : d<0 := by omega
        have heN : E≤0 := by by_contra h;exact hforbid ⟨hdN,by omega⟩
        exact mul_nonneg_of_nonpos_of_nonpos (by omega) heN
    have hprod := mul_nonneg hde hf.le
    unfold scalar
    nlinarith [sq_nonneg (2*c-f),sq_nonneg d,sq_nonneg E,sq_nonneg (f-1)]

private theorem corr_positive (x y : Int) (hx : 0≤x) (hy : 0≤y) : correction x y=x*y := by
  simp only [correction,max_eq_left hx,max_eq_left hy,
    max_eq_right (show -x≤0 by omega),max_eq_right (show -y≤0 by omega)]
  ring

theorem normalized_first_no_two (b c d E : Int) (H : Nat)
    (hb : 0<b) (hc : 0<c) (hP : Rank4ReviewRound2.StrongPairIncident.IncidentLe
      (peak b c d E ((H:Int)+1)) 0 1 H)
    (h1 : HeightLe (mutate (peak b c d E ((H:Int)+1)) 1) (H+1))
    (p : CyclicOrder) (hp : ProperClass (peak b c d E ((H:Int)+1)) p)
    (hM : orderMarkov (peak b c d E ((H:Int)+1)) p≤(H:Int)) :
    ¬HeightLe (mutate (peak b c d E ((H:Int)+1)) 2) (H+1) := by
  intro h2
  have hforbid : ¬(d<0 ∧ 0<E) := by
    rintro ⟨hd,he⟩
    have h := (h1 2 3).2
    change (H:Int)+1+correction (-d) E≤((H+1:Nat):Int) at h
    rw [corr_positive (-d) E (by omega) (by omega)] at h
    have hprod := mul_pos (show 0< -d by omega) he
    simp only [Nat.cast_add,Nat.cast_one] at h
    omega
  have hcH := (hP 3).1.1
  change -(H:Int)≤ -c at hcH
  have heH := (hP 3).2.1
  change -(H:Int)≤E at heH
  have hb1 : b=1 := by
    have h := (h2 0 3).2
    change -c+correction b ((H:Int)+1)≤((H+1:Nat):Int) at h
    rw [corr_positive b ((H:Int)+1) (by omega) (by omega)] at h
    simp only [Nat.cast_add,Nat.cast_one] at h
    by_contra hn
    have hb2 : 2≤b := by omega
    have hp := mul_nonneg (show 0≤b-2 by omega) (show 0≤(H:Int)+1 by omega)
    nlinarith
  have hd : d≤1 := by
    by_contra hn
    have hd2 : 2≤d := by omega
    have h := (h2 1 3).2
    change E+correction d ((H:Int)+1)≤((H+1:Nat):Int) at h
    rw [corr_positive d ((H:Int)+1) (by omega) (by omega)] at h
    simp only [Nat.cast_add,Nat.cast_one] at h
    have hp := mul_nonneg (show 0≤d-2 by omega) (show 0≤(H:Int)+1 by omega)
    nlinarith
  have hd1 : d=1 → E≤0 := by
    intro he
    have h := (h2 1 3).2
    change E+correction d ((H:Int)+1)≤((H+1:Nat):Int) at h
    rw [he,corr_positive 1 ((H:Int)+1) (by decide) (by omega)] at h
    simp only [Nat.cast_add,Nat.cast_one] at h
    omega
  have hm := proper_markov b c d E ((H:Int)+1) hb hc (by omega) hforbid p hp
  have hgt := unit_scalar_exceeds c d E ((H:Int)+1) (by omega) hforbid hd hd1
  rw [hb1] at hm hM
  rw [hm] at hM
  omega

#print axioms proper_markov
#print axioms unit_scalar_exceeds
#print axioms normalized_first_no_two
end Rank4CoordinatorR2.ZeroFirstSwitch
