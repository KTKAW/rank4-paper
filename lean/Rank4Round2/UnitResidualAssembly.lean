import Rank4Round2.CyclicUnitResidual
import Rank4Round2.LeftAcyclicUnitResidual
import Rank4ReviewRound2.RightAcyclicUnitGeometry

/-! Assembly of the exhaustive actual selected-triangle sign split.
Every actual selected triangle is covered by the independently reviewed
cyclic, negative02/nonpositive12, and nonnegative02 barriers. -/
namespace Rank4Round2.UnitResidualAssembly
open QuiverProofs Rank4Coordinator Rank4CoordinatorR2 Rank4Round2
open ProperOrder ProperMutation ResidualUnitExcursion
open Rank4ReviewRound2.PeakNormalization

def NonnegativeTriangleBarrier : Prop :=
  ∀ (C : Matrix 4) (H : Nat),SkewSymmetric C → MutationAcyclic C → HeightLe C H →
    ¬HeightLe (mutate C 0) H → PrefixHeightLe C [0,1,2] (H+1) →
    ¬HeightLe (applyWord C [0,1]) H →
    C 0 1=1 → 0≤C 0 2 →
    (∀ o,TotalProper C o → orderMarkov C o≤(H:Int)) → False

theorem packet_impossible_of_nonnegative_triangle_barrier
    (hRight : NonnegativeTriangleBarrier) (Q : Rank4Input) (H : Nat)
    (w lead : List (Fin 4)) (i j : Fin 4) (mid tail : List (Fin 4))
    (hp : Packet Q H w lead i j mid tail) : False := by
  obtain ⟨k,rest,he,hki,hkj,hNot⟩ := CyclicUnitResidual.packet_first_switch_not_cyclic
    Q H w lead i j mid tail hp
  let p := MixedUnitThreeFrame.tripleFrame i j k
  let r := MixedUnitThreeFrame.flip (applyWord Q.val lead) i j
  let C := signedFrame (applyWord Q.val lead) p r
  change ¬(C 0 2<0 ∧ 0<C 1 2) at hNot
  obtain ⟨h0,h1,h2⟩ := MixedUnitThreeFrame.triple_slots i j k hp.distinct hki hkj
  have hu : abs (applyWord Q.val lead i j)=1 := by simpa [mutate] using hp.unit
  have h01 : C 0 1=1 := MixedUnitThreeFrame.unit_positive _ i j k hp.distinct hki hkj hu
  obtain ⟨hs,hm,hl,hFirst,hPath,hSecond,hAll⟩ := UnitPacketFrame.facts Q H w lead i j k mid rest tail
    hp he p r h0 h1 h2
  by_cases hx : 0≤C 0 2
  · exact hRight C H hs hm hl hFirst hPath hSecond h01 hx hAll
  · have hxNeg : C 0 2<0 := by omega
    have hy : C 1 2≤0 := by
      by_contra hn
      apply hNot
      exact ⟨hxNeg,by omega⟩
    exact LeftAcyclicUnitResidual.signed_triangle_impossible Q H w lead i j k mid rest tail
      hp he p r h0 h1 h2 h01 hxNeg hy

theorem nonnegative_triangle_barrier : NonnegativeTriangleBarrier := by
  intro C H hs hm hl hFirst hPath hSecond h01 hx hAll
  have hrep : C=Rank4ReviewRound2.RightAcyclicUnitGeometry.B
      (C 0 2) (C 0 3) (C 1 2) (C 1 3) (C 2 3) := by
    simpa only [Rank4ReviewRound2.RightAcyclicUnitGeometry.B,h01]
      using (ofSix_reconstruct C hs).symm
  exact Rank4ReviewRound2.RightAcyclicUnitGeometry.actual_MA_impossible
    (C 0 2) (C 0 3) (C 1 2) (C 1 3) (C 2 3) H hx
    (by rw [←hrep];exact hl)
    (by rw [←hrep];exact hFirst)
    (by rw [←hrep];exact hSecond)
    (by rw [←hrep];exact hPath)
    (by rw [←hrep];exact hm)
    (by rw [←hrep];exact hAll)

/-- Every corrected actual residual Packet is impossible, with no additional
geometric, properness, endpoint or coverage premise. -/
theorem packet_impossible (Q : Rank4Input) (H : Nat)
    (w lead : List (Fin 4)) (i j : Fin 4) (mid tail : List (Fin 4))
    (hp : Packet Q H w lead i j mid tail) : False :=
  packet_impossible_of_nonnegative_triangle_barrier nonnegative_triangle_barrier
    Q H w lead i j mid tail hp

#print axioms packet_impossible_of_nonnegative_triangle_barrier
#print axioms nonnegative_triangle_barrier
#print axioms packet_impossible
end Rank4Round2.UnitResidualAssembly
