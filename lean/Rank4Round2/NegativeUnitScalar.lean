import Rank4Round2.FlatUnitBridge

/-! A negative high pair with a positively directed unit connection has
an explicit proper scalar. Both signs and both zero walls of the other
entries are included. The arithmetic conclusion uses the nonstrict MA
Pfaffian bound only in the negative E chamber.+-/
namespace Rank4Round2.NegativeUnitScalar
open QuiverProofs Census ProperOrder ProperWiggle ProperMutation ProperObstructionSoundness

def base (a c v F : Int) : Int := 1+a^2+c^2+v^2+F^2-a*v-c*F
def scalarPlus (a c v e F : Int) : Int := base a c v F+e^2+e*(a*c+v*(F-c))
def scalarMinus (a c v e F : Int) : Int := base a c v F+e^2+e*(a*c+F*v-a*F)
def pfMinus (a c v e F : Int) : Int := -a*F+e+c*v
def Q (a c v e F : Int) (s : Bool) : Matrix 4 :=
  ofSix (-a) 1 (-c) (-v) (if s then -e else e) F

theorem base_exceeds (a c v F : Int) (ha : 2≤a) : F<base a c v F := by
  unfold base
  have ha2 : 4≤a^2 := by nlinarith
  nlinarith [sq_nonneg (a-v),sq_nonneg v,sq_nonneg (F-c),sq_nonneg (F-1),sq_nonneg c]

theorem plus_exceeds (a c v e F : Int) (ha : 2≤a)
    (hc : 0≤c) (hv : 0≤v) (he : 0≤e) (hcF : c≤F) : F<scalarPlus a c v e F := by
  have hb := base_exceeds a c v F ha
  have hac := mul_nonneg (show 0≤a by omega) hc
  have hvc := mul_nonneg hv (show 0≤F-c by omega)
  have hprod := mul_nonneg he (show 0≤a*c+v*(F-c) by omega)
  unfold scalarPlus
  nlinarith [sq_nonneg e]

theorem minus_exceeds (a c v e F : Int) (ha : 2≤a) (hc : 0≤c)
    (hv : 1≤v) (he : 0≤e) (hcF : c≤F) (heF : e≤F) (hF : 0<F)
    (hn : 2*abs (pfMinus a c v e F)≤scalarMinus a c v e F) :
    F<scalarMinus a c v e F := by
  have hb := base_exceeds a c v F ha
  have habs := neg_le_abs (pfMinus a c v e F)
  by_cases hk : 0≤a*c+F*v-a*F
  · have hprod := mul_nonneg he hk
    unfold scalarMinus
    nlinarith [sq_nonneg e]
  · have hvA : v≤a-1 := by
      by_contra hbad
      have hp := mul_nonneg (show 0≤v-a by omega) (show 0≤F by omega)
      have hac := mul_nonneg (show 0≤a by omega) hc
      nlinarith
    by_cases hsmall : v≤a-2
    · have hvc := mul_nonneg (show 0≤v by omega) (show 0≤F-c by omega)
      have hvf := mul_nonneg (show 0≤a-2-v by omega) (show 0≤F by omega)
      have hp : pfMinus a c v e F≤ -F := by unfold pfMinus; nlinarith
      omega
    · have heq : v=a-1 := by omega
      have hacF : a*c<F := by rw [heq] at hk; nlinarith
      by_cases ha2 : a=2
      · subst a
        have hv1 : v=1 := by omega
        have hp : 2*pfMinus 2 c v e F< -F := by unfold pfMinus; nlinarith
        omega
      · have ha3 : 3≤a := by omega
        have hvc := mul_nonneg hc (show 0≤a-v by omega)
        have haf := mul_nonneg (show 0≤a-3 by omega) (show 0≤F by omega)
        have hp : pfMinus a c v e F≤ -F := by unfold pfMinus; nlinarith
        omega

private theorem four (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega

theorem proper_markov (a c v e F : Int) (s : Bool)
    (ha : 0<a) (hc : 0≤c) (hv : 0<v) (he : 0≤e) (hF : 0<F)
    (p : CyclicOrder) (hp : ProperClass (Q a c v e F s) p) :
    orderMarkov (Q a c v e F s) p=
      if s then scalarMinus a c v e F else scalarPlus a c v e F := by
  let B := Q a c v e F s
  let seed := ofSix (-1) 1 (if c=0 then 0 else -1) (-1)
    (if e=0 then 0 else if s then -1 else 1) 1
  let target : Fin 6 := if s then 3 else 2
  have hmask : supportMask B=supportMask seed := by
    cases s <;> by_cases hc0 : c=0 <;> by_cases he0 : e=0 <;>
      simp [B,Q,seed,supportMask,supportBit,ofSix,hc0,he0,
        show a≠0 by omega,show v≠0 by omega,show F≠0 by omega]
  have hsign : ∀ i j, 0<B i j ↔ 0<seed i j := by
    intro i j
    cases s <;> by_cases hc0 : c=0 <;> by_cases he0 : e=0 <;>
      rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
      simp [B,Q,seed,ofSix,hc0,he0] <;> omega
  obtain ⟨i,hi⟩ := cyclic_order_exhaustive p
  have ht := (properClass_iff_table B (ofSix_skew _ _ _ _ _ _) p i hi).mp hp
  have hs := (ChamberProperness.properClassTable_sign_iff B seed hmask hsign i).mp ht
  have hcomp : ∀ i : Fin 6, ProperClassTable seed i→
      component (supportMask seed) i=component (supportMask seed) target := by
    cases s <;> by_cases hc0 : c=0 <;> by_cases he0 : e=0 <;>
      simp only [seed,target,hc0,he0,ite_true,ite_false] <;> decide
  have hwiggle : WiggleEquivalent B p (order target) := by
    apply (wiggle_iff_component B (ofSix_skew _ _ _ _ _ _) p (order target) i target
      hi (fun _ _ _ => Iff.rfl)).mpr
    rw [hmask]
    exact hcomp i hs
  have hM := ProperWiggleInvariants.markov_wiggle_invariant B (ofSix_skew _ _ _ _ _ _) hwiggle
  rw [hM]
  cases s <;> norm_num [B,Q,target,orderMarkov,order,Census.permutation,Census.permFun,
    Census.digit4,Census.permutationCodes,Census.Table.get,ofSix]
  · change Algebra.markov 1 (-a) (-c) v F e=scalarPlus a c v e F
    unfold Algebra.markov Algebra.squareSum Algebra.cycleTerms scalarPlus base
    ring
  · change Algebra.markov 1 (-c) (-a) F v e=scalarMinus a c v e F
    unfold Algebra.markov Algebra.squareSum Algebra.cycleTerms scalarMinus base
    ring

theorem negative_totalProper_scalar_exceeds_height (hEnd : EndpointTopological4)
    (a c v e F : Int) (s : Bool) (ha : 2≤a) (hc : 0≤c) (hv : 1≤v)
    (he : 0≤e) (hcF : c≤F) (heF : e≤F) (hF : 0<F)
    (hma : MutationAcyclic (Q a c v e F s))
    (p : CyclicOrder) (hp : TotalProper (Q a c v e F s) p) :
    F<orderMarkov (Q a c v e F s) p := by
  have hM := proper_markov a c v e F s (by omega) hc (by omega) he hF p
    (totalProper_proper _ p hp)
  rw [hM]
  cases s
  · exact plus_exceeds a c v e F ha hc (by omega) he hcF
  · have hn := QuiverProofs.Rank4StructureRound2.SuperScalarPeak.MA_totalProper_pfaffian_bound
      hEnd (Q a c v e F true) (ofSix_skew _ _ _ _ _ _) hma p hp
    have hpf : matrixPfaffian (Q a c v e F true)=pfMinus a c v e F := by
      simp [matrixPfaffian,Q,ofSix,pfMinus]
    rw [hpf,hM] at hn
    exact minus_exceeds a c v e F ha hc hv he hcF heF hF hn

#print axioms minus_exceeds
#print axioms proper_markov
#print axioms negative_totalProper_scalar_exceeds_height
end Rank4Round2.NegativeUnitScalar
