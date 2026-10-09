import Rank4StructureRound2.HalfEntryStable
import Rank4Round2.NegativeUnitScalar

/-! The first stable forward state cannot switch to either frozen pivot
above the supplied proper scalar. Mutation at 2 exceeds the ceiling by
integer geometry. Mutation at 3 can only reach it at the exact d=0,E=c=1
wall, whose original proper scalar exceeds f without an MA premise. -/
namespace QuiverProofs.Rank4StructureRound2.StableFirstSwitch
open Census ProperOrder ProperWiggle ProperMutation TwoStateScalar
open Rank4Coordinator
set_option maxHeartbeats 4000000

private theorem corr_positive (x y : Int) (hx : 0≤x) (hy : 0≤y) : correction x y=x*y := by
  simp only [correction,max_eq_left hx,max_eq_left hy,
    max_eq_right (show -x≤0 by omega),max_eq_right (show -y≤0 by omega)]
  ring
private theorem corr_negative (x y : Int) (hx : x≤0) (hy : y≤0) : correction x y= -x*y := by
  simp only [correction,max_eq_right hx,max_eq_right hy,
    max_eq_left (show 0≤ -x by omega),max_eq_left (show 0≤ -y by omega)]
  ring

private theorem mutate_one_mixed (a b c d E f : Int)
    (ha : 0≤a) (hd : 0≤d) (hE : 0≤E) :
    mutate (Q a b c d E f) 1=ofSix (-a) (b+a*d) (-c+a*E) (-d) (-E) f := by
  have hrec := (ofSix_reconstruct (mutate (Q a b c d E f) 1)
    (mutation_preserves_skew _ _ (ofSix_skew _ _ _ _ _ _))).symm
  change mutate (Q a b c d E f) 1=ofSix (-a) (b+correction a d)
    (-c+correction a E) (-d) (-E) (f+correction (-d) E) at hrec
  have hzero : correction (-d) E=0 := by
    simp only [correction,max_eq_right (show -d≤0 by omega),max_eq_left hE,
      max_eq_right (show -E≤0 by omega)]
    ring
  rwa [corr_positive a d ha hd,corr_positive a E ha hE,hzero,Int.add_zero] at hrec

theorem stable_second_pivot_exceeds (a b c d E f : Int) (H : Nat)
    (ha : 2≤a) (hb : 0<b) (hc : 0<c) (hd : 0≤d) (hcE : c≤E)
    (hf : f=(H:Int)+1) :
    ¬HeightLe (mutate (mutate (Q a b c d E f) 1) 2) (H+1) := by
  intro h2
  have h := (h2 0 3).2
  have hE : 0≤E := by omega
  rw [mutate_one_mixed a b c d E f (by omega) hd hE] at h
  change -c+a*E+correction (b+a*d) f≤((H+1:Nat):Int) at h
  have had := mul_nonneg (show 0≤a by omega) hd
  rw [corr_positive (b+a*d) f (by nlinarith) (by omega)] at h
  have hsum := mul_nonneg (show 0≤a-2 by omega) hE
  have hprod := mul_nonneg (show 0≤b+a*d-1 by nlinarith) (show 0≤f by omega)
  simp only [Nat.cast_add,Nat.cast_one] at h
  nlinarith

theorem stable_third_pivot_forces_wall (a b c d E f : Int) (H : Nat)
    (ha : 2≤a) (hc : 0<c) (hd : 0≤d) (hcE : c≤E)
    (hf : f=(H:Int)+1)
    (h3 : HeightLe (mutate (mutate (Q a b c d E f) 1) 3) (H+1)) :
    d=0 ∧ E=1 ∧ c=1 := by
  have h := (h3 1 2).1
  have hE : 1≤E := by omega
  rw [mutate_one_mixed a b c d E f (by omega) hd (by omega)] at h
  change -((H+1:Nat):Int)≤ -d+correction (-E) (-f) at h
  rw [corr_negative (-E) (-f) (by omega) (by omega)] at h
  have hprod := mul_nonneg (show 0≤E-1 by omega) (show 0<f by omega).le
  simp only [Nat.cast_add,Nat.cast_one] at h
  have hd0 : d=0 := by nlinarith
  have hE1 : E=1 := by nlinarith
  exact ⟨hd0,hE1,by omega⟩

theorem wall_proper_scalar_exceeds (a b f : Int) (ha : 2≤a) (hb : 0<b) (hf : 0<f)
    (p : CyclicOrder) (hp : ProperClass (Q a b 1 0 1 f) p) :
    f<orderMarkov (Q a b 1 0 1 f) p := by
  have hm := FlatMixedOrder.proper_markov a b 1 0 1 f (by omega) hb (by decide)
    (by decide) (by decide) hf p hp
  change orderMarkov (Q a b 1 0 1 f) p=FlatMixedScalar.scalar a b 1 0 1 f at hm
  rw [hm]
  have hl := Rank4Round2.NegativeUnitScalar.base_exceeds a b 1 f ha
  have heq : FlatMixedScalar.scalar a b 1 0 1 f=Rank4Round2.NegativeUnitScalar.base a b 1 f := by
    unfold FlatMixedScalar.scalar Rank4Round2.NegativeUnitScalar.base
    ring
  rwa [heq]

theorem stable_first_no_third (a b c d E f : Int) (H : Nat)
    (ha : 2≤a) (hb : 0<b) (hc : 0<c) (hd : 0≤d) (hcE : c≤E)
    (hf : f=(H:Int)+1) (p : CyclicOrder) (hp : ProperClass (Q a b c d E f) p)
    (hM : orderMarkov (Q a b c d E f) p≤(H:Int))
    (k : Fin 4) (hk : k=2 ∨ k=3) :
    ¬HeightLe (mutate (mutate (Q a b c d E f) 1) k) (H+1) := by
  rcases hk with rfl | rfl
  · exact stable_second_pivot_exceeds a b c d E f H ha hb hc hd hcE hf
  · intro h3
    obtain ⟨hd0,hE1,hc1⟩ := stable_third_pivot_forces_wall a b c d E f H ha hc hd hcE hf h3
    subst d
    subst E
    subst c
    have hl := wall_proper_scalar_exceeds a b f ha hb (by omega) p hp
    omega

#print axioms stable_first_no_third
end QuiverProofs.Rank4StructureRound2.StableFirstSwitch
