import QuiverProofs.ProperExclusionCertificates
import QuiverProofs.FirstGap
import QuiverProofs.ChamberProperness

namespace QuiverProofs.DependentProperConsequences
open ProperOrder ProperWiggle ProperMutation ProperObstructionSoundness Census

theorem E1_NMA_of_bridges (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4) :
    ¬ MutationAcyclic (ClassSeparation.printed 0) :=
  ProperExclusionCertificates.q196.NMA_of_structural_bridges hExist hEnd

theorem E2_NMA_of_bridges (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4) :
    ¬ MutationAcyclic (ClassSeparation.printed 1) :=
  ProperExclusionCertificates.q446.NMA_of_structural_bridges hExist hEnd

theorem E3_NMA_of_bridges (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4) :
    ¬ MutationAcyclic (ClassSeparation.printed 2) :=
  ProperExclusionCertificates.q476.NMA_of_structural_bridges hExist hEnd

theorem E4_NMA_of_bridges (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4) :
    ¬ MutationAcyclic (ClassSeparation.printed 3) :=
  ProperExclusionCertificates.q498.NMA_of_structural_bridges hExist hEnd

private theorem fin4 (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega

/-- Semantic Boolean-cut connectedness supplies the seven support cuts. -/
theorem connectedSupport_firstGap (a b c d e f : Int)
    (hconn : ConnectedSupport (ofSix a b c d e f)) :
    FirstGap.Connected a b c d e f := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · apply Classical.byContradiction
    intro hn
    have hc := hconn false true true true (by
      intro i j hij
      rcases fin4 i with rfl|rfl|rfl|rfl <;>
        rcases fin4 j with rfl|rfl|rfl|rfl <;>
        simp_all [ofSix,side])
    simp at hc
  · apply Classical.byContradiction
    intro hn
    have hc := hconn true false true true (by
      intro i j hij
      rcases fin4 i with rfl|rfl|rfl|rfl <;>
        rcases fin4 j with rfl|rfl|rfl|rfl <;>
        simp_all [ofSix,side])
    simp at hc
  · apply Classical.byContradiction
    intro hn
    have hc := hconn true true false true (by
      intro i j hij
      rcases fin4 i with rfl|rfl|rfl|rfl <;>
        rcases fin4 j with rfl|rfl|rfl|rfl <;>
        simp_all [ofSix,side])
    simp at hc
  · apply Classical.byContradiction
    intro hn
    have hc := hconn true true true false (by
      intro i j hij
      rcases fin4 i with rfl|rfl|rfl|rfl <;>
        rcases fin4 j with rfl|rfl|rfl|rfl <;>
        simp_all [ofSix,side])
    simp at hc
  · apply Classical.byContradiction
    intro hn
    have hc := hconn false false true true (by
      intro i j hij
      rcases fin4 i with rfl|rfl|rfl|rfl <;>
        rcases fin4 j with rfl|rfl|rfl|rfl <;>
        simp_all [ofSix,side])
    simp at hc
  · apply Classical.byContradiction
    intro hn
    have hc := hconn false true false true (by
      intro i j hij
      rcases fin4 i with rfl|rfl|rfl|rfl <;>
        rcases fin4 j with rfl|rfl|rfl|rfl <;>
        simp_all [ofSix,side])
    simp at hc
  · apply Classical.byContradiction
    intro hn
    have hc := hconn false true true false (by
      intro i j hij
      rcases fin4 i with rfl|rfl|rfl|rfl <;>
        rcases fin4 j with rfl|rfl|rfl|rfl <;>
        simp_all [ofSix,side])
    simp at hc

/-- All canonical representatives of the family's proper class carry the
scalar invariant in the manuscript, for every integer s>=1. -/
theorem family_proper_markov (s : Int) (hs : 1≤s)
    (p : CyclicOrder)
    (hp : ProperClass (ofSix 0 0 (Algebra.familyC s) (Algebra.familyD s) (-1) 1) p) :
    orderMarkov (ofSix 0 0 (Algebra.familyC s) (Algebra.familyD s) (-1) 1) p =
      Algebra.markov 0 0 (Algebra.familyC s) (Algebra.familyD s) (-1) 1 := by
  let Q := ofSix 0 0 (Algebra.familyC s) (Algebra.familyD s) (-1) 1
  let seed := ofSix 0 0 3 2 (-1) 1
  have hC : 0<Algebra.familyC s := by
    have hsq := Algebra.square_nonnegative s
    unfold Algebra.familyC; omega
  have hD : 0<Algebra.familyD s := by
    have hsq := Algebra.square_nonnegative s
    unfold Algebra.familyD; omega
  have hm : supportMask Q=supportMask seed := by
    simp [Q,seed,supportMask,supportBit,ofSix,show Algebra.familyC s ≠ 0 by omega,
      show Algebra.familyD s ≠ 0 by omega]
  have hsign : ∀ i j, 0<Q i j ↔ 0<seed i j := by
    intro i j
    rcases fin4 i with rfl|rfl|rfl|rfl <;>
      rcases fin4 j with rfl|rfl|rfl|rfl <;> simp [Q,seed,ofSix] <;> omega
  obtain ⟨i,hi⟩ := cyclic_order_exhaustive p
  have ht := (properClass_iff_table Q (ofSix_skew _ _ _ _ _ _) p i hi).mp hp
  have hseed := (ChamberProperness.properClassTable_sign_iff Q seed hm hsign i).mp ht
  have hcases : i=0 ∨ i=3 ∨ i=4 :=
    (show ∀ i : Fin 6, ProperClassTable seed i → i=0 ∨ i=3 ∨ i=4 by decide) i hseed
  rw [ProperWiggleInvariants.markov_cyclic Q (ofSix_skew _ _ _ _ _ _) p (order i) hi]
  rcases hcases with rfl|rfl|rfl
  · rfl
  · change Algebra.markov 0 (Algebra.familyC s) 0 1 (-(Algebra.familyD s)) 1 = _
    unfold Algebra.markov Algebra.squareSum Algebra.cycleTerms
    grind
  · change Algebra.markov (Algebra.familyC s) 0 0 1 (-1) (Algebra.familyD s) = _
    unfold Algebra.markov Algebra.squareSum Algebra.cycleTerms
    grind

private theorem family_connected (s : Int) (hs : 1≤s) :
    ConnectedSupport (ofSix 0 0 (Algebra.familyC s) (Algebra.familyD s) (-1) 1) := by
  have hC : Algebra.familyC s ≠ 0 := by
    have hsq := Algebra.square_nonnegative s
    unfold Algebra.familyC; omega
  have hD : Algebra.familyD s ≠ 0 := by
    have hsq := Algebra.square_nonnegative s
    unfold Algebra.familyD; omega
  apply (connected_iff_all_colorings _).mpr
  intro color hc i j
  have h03 := hc 0 3 (by simp [ofSix,hC])
  have h12 := hc 1 2 (by simp [ofSix,hD])
  have h13 := hc 1 3 (by simp [ofSix])
  rcases fin4 i with rfl|rfl|rfl|rfl <;>
    rcases fin4 j with rfl|rfl|rfl|rfl <;> simp_all

/-- Complete unbounded first-gap family NMA, conditional on precisely the
MA-to-total-properness and acyclic endpoint identification bridges. -/
theorem first_gap_family_NMA_of_bridges (hExist : MAHasTotalProper4)
    (hEnd : EndpointTopological4) (s : Int) (hs : 1≤s) :
    ¬ MutationAcyclic (ofSix 0 0 (Algebra.familyC s) (Algebra.familyD s) (-1) 1) := by
  let Q := ofSix 0 0 (Algebra.familyC s) (Algebra.familyD s) (-1) 1
  apply NMA_of_scalar_exclusion hExist hEnd Q (ofSix_skew _ _ _ _ _ _) (family_connected s hs)
  intro p hp C hC hconn q hq hm hD
  have hM := family_proper_markov s hs p hp
  have hMtuple : Algebra.markov (C (q.toFun 0) (q.toFun 1))
      (C (q.toFun 0) (q.toFun 2)) (C (q.toFun 0) (q.toFun 3))
      (C (q.toFun 1) (q.toFun 2)) (C (q.toFun 1) (q.toFun 3))
      (C (q.toFun 2) (q.toFun 3)) =
      Algebra.markov 0 0 (Algebra.familyC s) (Algebra.familyD s) (-1) 1 := hm.trans hM
  have hconnq := connected_relabel C q hconn
  rw [← ofSix_reconstruct (relabel C q) (relabel_skew C q hC)] at hconnq
  have hcuts := connectedSupport_firstGap _ _ _ _ _ _ hconnq
  have hDq := ClassSeparation.pfaffian_square_relabel C hC q
  have hDtuple : matrixPfaffian (relabel C q)^2 = (Algebra.familyP s)^2 := by
    rw [hDq,hD]
    simp [Q,matrixPfaffian,ofSix,Algebra.familyP]
  have hPpos := Algebra.family_pfaffian_at_least_six s hs
  have hPabs : ((matrixPfaffian (relabel C q)).natAbs : Int) = Algebra.familyP s := by
    rcases ClassSeparation.square_eq_cases _ _ hDtuple with hh|hh
    · rw [hh,Int.natAbs_of_nonneg (show 0≤Algebra.familyP s by omega)]
    · rw [hh,Int.natAbs_neg,Int.natAbs_of_nonneg (show 0≤Algebra.familyP s by omega)]
  exact FirstGap.family_no_acyclic_invariant_representative s _ _ _ _ _ _ hs
    hq.1 hq.2.1 hq.2.2.1 hq.2.2.2.1 hq.2.2.2.2.1 hq.2.2.2.2.2
    hcuts hMtuple hPabs

end QuiverProofs.DependentProperConsequences
