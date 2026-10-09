import Rank4StructureRound2.MixedIncidentEqualCore
import Rank4StructureRound2.MixedIncidentFamilyHeight
import Rank4StructureRound2.ScalarFivePfTwo
import QuiverProofs.ChamberProperness

/-! The equal slope wall of the other unit triangle phase is impossible
for an actual MA matrix with supplied proper scalar <=H. For t>=2 a
closed two-node/root grammar proves NMA; t=1 uses the accepted scalar-five
finite mutation core. Consequently one of the two guarded routes is legal. -/
namespace QuiverProofs.Rank4StructureRound2.MixedIncidentEqual
open Census ProperOrder ProperWiggle ProperMutation ProperObstructionSoundness
open Rank4Coordinator Rank4Round2 MixedIncidentFamilyHeight
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
private theorem four (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega

private theorem seed_classes : ∀ i : Fin 6,
    ProperClassTable (ofSix 1 (-1) (-1) 2 (-1) 1) i →
    component (supportMask (ofSix 1 (-1) (-1) 2 (-1) 1)) i=
      component (supportMask (ofSix 1 (-1) (-1) 2 (-1) 1)) 0 := by decide

theorem proper_scalar (t w F : Int) (ht : 1≤t) (hw : 1≤w)
    (htF : t≤F-1) (hwF : w≤F-1) (p : CyclicOrder) (hp : ProperClass (R t w F) p) :
    orderMarkov (R t w F) p=4+t^2-t*w+w^2 := by
  let seed:=ofSix 1 (-1) (-1) 2 (-1) 1
  let Q:=R t w F
  have hmask : supportMask Q=supportMask seed := by
    simp [Q,R,seed,supportMask,supportBit,ofSix,show t≠0 by omega,
      show t-F≠0 by omega,show F-w≠0 by omega]
  have hsign : ∀ i j,0<Q i j ↔ 0<seed i j := by
    intro i j
    rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
      simp [Q,R,seed,ofSix] <;> omega
  obtain ⟨i,hi⟩:=cyclic_order_exhaustive p
  have ht':=(properClass_iff_table Q (ofSix_skew _ _ _ _ _ _) p i hi).mp hp
  have hs:=(ChamberProperness.properClassTable_sign_iff Q seed hmask hsign i).mp ht'
  have hcomp:=seed_classes i hs
  have hW : WiggleEquivalent Q p (order 0) := by
    apply (wiggle_iff_component Q (ofSix_skew _ _ _ _ _ _) p (order 0) i 0 hi
      (fun _ _ _ => Iff.rfl)).mpr
    rwa [hmask]
  rw [ProperWiggleInvariants.markov_wiggle_invariant Q (ofSix_skew _ _ _ _ _ _) hW]
  change Algebra.markov 1 (-1) (-t) 2 (t-F) (F-w)=_
  unfold Algebra.markov Algebra.squareSum Algebra.cycleTerms
  ring

theorem actual_equal_slope_impossible (hEnd : EndpointTopological4)
    (t : Int) (H : Nat) (ht : 1≤t) (htH : t≤(H:Int))
    (hma : MutationAcyclic (R t t ((H:Int)+1)))
    (p : CyclicOrder) (hp : TotalProper (R t t ((H:Int)+1)) p)
    (hBudget : orderMarkov (R t t ((H:Int)+1)) p≤(H:Int)) : False := by
  have hM:=proper_scalar t t ((H:Int)+1) ht ht (by omega) (by omega) p (totalProper_proper _ p hp)
  have hM' : orderMarkov (R t t ((H:Int)+1)) p=4+t^2 := by nlinarith [hM]
  have hF : t^2+5≤(H:Int)+1 := by nlinarith [hM']
  by_cases h1 : t=1
  · subst t
    have hm : orderMarkov (R 1 1 ((H:Int)+1)) p=5 := by norm_num at hM';exact hM'
    have hpf : (matrixPfaffian (R 1 1 ((H:Int)+1)))^2=4 := by
      simp [matrixPfaffian,R,ofSix]
    have hLow:=ScalarFivePfTwo.actual_MA_scalar_five_pf_two_below hEnd _
      (ofSix_skew _ _ _ _ _ _) hma p hp hm hpf
    have h:=hLow 1 3
    simp only [R,ofSix] at h
    omega
  · have ht2 : 2≤t := by omega
    have hN:=MixedIncidentEqualCore.EqualSlopeModule.family_NMA t ((H:Int)+1) ht2 hF
    exact hN hma

theorem actual_slopes_unequal (hEnd : EndpointTopological4)
    (t w : Int) (H : Nat) (ht : 1≤t) (hw : 1≤w) (htH : t≤(H:Int)) (hwH : w≤(H:Int))
    (hma : MutationAcyclic (R t w ((H:Int)+1)))
    (p : CyclicOrder) (hp : TotalProper (R t w ((H:Int)+1)) p)
    (hBudget : orderMarkov (R t w ((H:Int)+1)) p≤(H:Int)) : t≠w := by
  intro hEq
  subst w
  exact actual_equal_slope_impossible hEnd t H ht htH hma p hp hBudget

theorem actual_one_route_below (hEnd : EndpointTopological4)
    (t w : Int) (H : Nat) (hH : 2≤H)
    (ht : 1≤t) (hw : 1≤w) (htH : t≤(H:Int)) (hwH : w≤(H:Int))
    (hma : MutationAcyclic (R t w ((H:Int)+1)))
    (p : CyclicOrder) (hp : TotalProper (R t w ((H:Int)+1)) p)
    (hBudget : orderMarkov (R t w ((H:Int)+1)) p≤(H:Int)) :
    PrefixHeightLe (R t w ((H:Int)+1)) [1,0,2,1,2] H ∨
      PrefixHeightLe (R t w ((H:Int)+1)) [2,0,2,1,0] H := by
  have hn:=actual_slopes_unequal hEnd t w H ht hw htH hwH hma p hp hBudget
  by_cases hl : w<t
  · exact .inl (first_slope_below t w H hH ht hw htH hwH hl)
  · exact .inr (second_slope_below t w H hH ht hw htH hwH (by omega))

#print axioms proper_scalar
#print axioms actual_equal_slope_impossible
#print axioms actual_one_route_below
end QuiverProofs.Rank4StructureRound2.MixedIncidentEqual
