import Rank4CoordinatorR2.Foundation
import QuiverProofs.ChamberProperness

/-! A barrier for the incident-top alternative in the fixed (1,2,1)
three-pivot core. Negative final edge has no proper cyclic class; at the
zero wall every proper scalar exceeds the opposite ceiling. This does not
supply the universal mixed-switch triangle normalization. -/
namespace Rank4CoordinatorR2.MixedUnitIncident
open QuiverProofs Rank4Coordinator Rank4CoordinatorR2
open ProperOrder ProperWiggle
set_option maxHeartbeats 2000000

def peak (t f F : Int) : Matrix 4 := ofSix 1 (-2) (-t) 1 (t-F) f

private theorem four (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega

private theorem seed_classes : ∀ s : Fin 2, ∀ i : Fin 6,
    ProperClassTable (ofSix 1 (-1) (-1) 1 (-1) (-(s.val:Int))) i →
    s.val=0 ∧ component (supportMask (ofSix 1 (-1) (-1) 1 (-1) (-(s.val:Int)))) i=
      component (supportMask (ofSix 1 (-1) (-1) 1 (-1) (-(s.val:Int)))) 0 := by decide

theorem proper_scalar_exceeds (t f F : Int) (hF : 2≤F)
    (ht : 1≤t) (htF : t≤F-1) (hf : f≤0)
    (p : CyclicOrder) (hp : ProperClass (peak t f F) p) :
    F<orderMarkov (peak t f F) p := by
  let s : Fin 2 := if f=0 then 0 else 1
  let seed := ofSix 1 (-1) (-1) 1 (-1) (-(s.val:Int))
  let Q := peak t f F
  have hmask : supportMask Q=supportMask seed := by
    by_cases hz : f=0 <;>
      simp [Q,peak,seed,s,supportMask,supportBit,ofSix,hz,
        show t≠0 by omega,show t-F≠0 by omega]
  have hsign : ∀ i j,0<Q i j ↔ 0<seed i j := by
    intro i j
    by_cases hz : f=0 <;>
      rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
      simp [Q,peak,seed,s,ofSix,hz] <;> omega
  obtain ⟨i,hi⟩ := cyclic_order_exhaustive p
  have ht' := (properClass_iff_table Q (ofSix_skew _ _ _ _ _ _) p i hi).mp hp
  have hs := (ChamberProperness.properClassTable_sign_iff Q seed hmask hsign i).mp ht'
  obtain ⟨hs0,hcomp⟩ := seed_classes s i hs
  have hf0 : f=0 := by
    by_contra hz
    simp [s,hz] at hs0
  have hw : WiggleEquivalent Q p (order 0) := by
    apply (wiggle_iff_component Q (ofSix_skew _ _ _ _ _ _) p (order 0) i 0
      hi (fun _ _ _ => Iff.rfl)).mpr
    rwa [hmask]
  have hm := ProperWiggleInvariants.markov_wiggle_invariant Q (ofSix_skew _ _ _ _ _ _) hw
  rw [hm]
  change F<Algebra.markov 1 (-2) (-t) 1 (t-F) f
  rw [hf0]
  unfold Algebra.markov Algebra.squareSum Algebra.cycleTerms
  nlinarith [sq_nonneg (2*t-F),sq_nonneg (F-1)]

#print axioms proper_scalar_exceeds
end Rank4CoordinatorR2.MixedUnitIncident
