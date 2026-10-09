import Rank4CoordinatorR2.ConnectedScalar

/-! Scalar transport to actual acyclic endpoints. EndpointTopological4 is
explicit here; the source does not assert MAHasTotalProper4. -/
namespace Rank4CoordinatorR2
open QuiverProofs QuiverProofs.Census QuiverProofs.ProperOrder
  QuiverProofs.ProperWiggle QuiverProofs.ProperMutation
  QuiverProofs.ProperObstructionSoundness

private theorem cases4 (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega

theorem connected_not_matching (a b c d e f : Int)
    (hconn : ConnectedSupport (ofSix a b c d e f)) :
    ¬ Algebra.MatchingSupport a b c d e f := by
  intro hm
  rcases hm with ⟨hb,hc,hd,he⟩ | ⟨ha,hc,hd,hf⟩ | ⟨ha,hb,he,hf⟩
  · have hres : RespectsEdges (ofSix a b c d e f) (side false false true true) := by
      intro i j hij
      rcases cases4 i with rfl | rfl | rfl | rfl <;>
        rcases cases4 j with rfl | rfl | rfl | rfl <;>
        simp_all [ofSix, side]
    have hh := hconn false false true true hres
    exact Bool.noConfusion hh.2.1
  · have hres : RespectsEdges (ofSix a b c d e f) (side false true false true) := by
      intro i j hij
      rcases cases4 i with rfl | rfl | rfl | rfl <;>
        rcases cases4 j with rfl | rfl | rfl | rfl <;>
        simp_all [ofSix, side]
    have hh := hconn false true false true hres
    exact Bool.noConfusion hh.1
  · have hres : RespectsEdges (ofSix a b c d e f) (side false true true false) := by
      intro i j hij
      rcases cases4 i with rfl | rfl | rfl | rfl <;>
        rcases cases4 j with rfl | rfl | rfl | rfl <;>
        simp_all [ofSix, side]
    have hh := hconn false true true false hres
    exact Bool.noConfusion hh.1

theorem connected_topological_strict_pfaffian (C : Matrix 4) (hC : SkewSymmetric C)
    (hconn : ConnectedSupport C) (q : CyclicOrder) (hq : Topological C q) :
    2 * (Algebra.pfaffian (C (q.toFun 0) (q.toFun 1))
      (C (q.toFun 0) (q.toFun 2)) (C (q.toFun 0) (q.toFun 3))
      (C (q.toFun 1) (q.toFun 2)) (C (q.toFun 1) (q.toFun 3))
      (C (q.toFun 2) (q.toFun 3))).natAbs < orderMarkov C q := by
  have hrec := ofSix_reconstruct (relabel C q) (relabel_skew C q hC)
  have hconnq := connected_relabel C q hconn
  rw [← hrec] at hconnq
  exact Algebra.strict_pfaffian_bound_of_not_matching _ _ _ _ _ _
    hq.1 hq.2.1 hq.2.2.1 hq.2.2.2.1 hq.2.2.2.2.1 hq.2.2.2.2.2
    (connected_not_matching _ _ _ _ _ _ hconnq)

/-- The total-proper order supplied by a future existence proof has
scalar at least three if this connected matrix is actually MA. -/
theorem connected_MA_totalProper_markov (hEndpoint : EndpointTopological4)
    (B : Matrix 4) (hB : SkewSymmetric B) (hconn : ConnectedSupport B)
    (hMA : MutationAcyclic B) (p : CyclicOrder) (hp : TotalProper B p) :
    3 ≤ orderMarkov B p := by
  obtain ⟨w,hw⟩ := hMA
  obtain ⟨r,htr,hpr⟩ := totalProper_lifts_word B hB p hp w
  have hC := word_preserves_skew B w hB
  obtain ⟨q,hq,hrq⟩ := hEndpoint _ hC hw r hpr
  have hM := transport_markov hB htr
  have hMq := ProperWiggleInvariants.markov_wiggle_invariant _ hC hrq
  have hm := connected_topological_markov _ hC (connected_applyWord B w hconn) q hq
  omega

/-- The Pfaffian bound is transported as an absolute value using its
proved square invariance. It concerns the supplied total-proper order,
not an arbitrarily chosen fixed order during ordinary mutation. -/
theorem connected_MA_totalProper_strict_pfaffian (hEndpoint : EndpointTopological4)
    (B : Matrix 4) (hB : SkewSymmetric B) (hconn : ConnectedSupport B)
    (hMA : MutationAcyclic B) (p : CyclicOrder) (hp : TotalProper B p) :
    2 * (matrixPfaffian B).natAbs < orderMarkov B p := by
  obtain ⟨w,hw⟩ := hMA
  obtain ⟨r,htr,hpr⟩ := totalProper_lifts_word B hB p hp w
  have hC := word_preserves_skew B w hB
  obtain ⟨q,hq,hrq⟩ := hEndpoint _ hC hw r hpr
  have hM := transport_markov hB htr
  have hMq := ProperWiggleInvariants.markov_wiggle_invariant _ hC hrq
  have hm := connected_topological_strict_pfaffian _ hC
    (connected_applyWord B w hconn) q hq
  change (2:Int) * ((matrixPfaffian (relabel (applyWord B w) q)).natAbs : Int) < _ at hm
  have hsq := (ClassSeparation.pfaffian_square_relabel _ hC q).trans
    (pfaffian_square_word B w hB)
  have hxa : ((matrixPfaffian (relabel (applyWord B w) q)).natAbs : Int)^2 =
      (matrixPfaffian (relabel (applyWord B w) q))^2 := by
    simpa only [pow_two] using Int.natAbs_mul_self' (matrixPfaffian (relabel (applyWord B w) q))
  have hya : ((matrixPfaffian B).natAbs : Int)^2 = (matrixPfaffian B)^2 := by
    simpa only [pow_two] using Int.natAbs_mul_self' (matrixPfaffian B)
  have hxn : 0 ≤ ((matrixPfaffian (relabel (applyWord B w) q)).natAbs : Int) := by omega
  have hyn : 0 ≤ ((matrixPfaffian B).natAbs : Int) := by omega
  have habs : ((matrixPfaffian (relabel (applyWord B w) q)).natAbs : Int) =
      ((matrixPfaffian B).natAbs : Int) := by nlinarith [hsq,hxa,hya]
  rw [habs] at hm
  omega

#print axioms connected_not_matching
#print axioms connected_topological_strict_pfaffian
#print axioms connected_MA_totalProper_markov
#print axioms connected_MA_totalProper_strict_pfaffian
end Rank4CoordinatorR2
