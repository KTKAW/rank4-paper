import Rank4CoordinatorR2.LeftAcyclicUnitGeometry
import Rank4Round2.UnitPacketFrame

/-! Original-budget actual Packet consumer for normalized02<0/12<=0.
The pure geometry barrier receives an actual TP scalar and its endpoint
Pf bound, with no additional user-supplied foundation hypotheses. -/
namespace Rank4Round2.LeftAcyclicUnitResidual
open QuiverProofs Rank4Coordinator Rank4CoordinatorR2 Rank4Round2
open ProperOrder ProperMutation ResidualUnitExcursion
open Rank4ReviewRound2.PeakNormalization

theorem triangle_impossible (Q : Rank4Input) (H : Nat)
    (w lead : List (Fin 4)) (i j k : Fin 4) (mid rest tail : List (Fin 4))
    (hp : Packet Q H w lead i j mid tail)
    (he : (i::j::mid)=[i,j]++k::rest)
    (p : Relabeling 4) (r : Bool) (b D c e f : Int)
    (h0 : p.toFun 0=i) (h1 : p.toFun 1=j) (h2 : p.toFun 2=k)
    (hb : 1≤b) (hD : 0≤D)
    (hrep : signedFrame (applyWord Q.val lead) p r=LeftAcyclicUnitGeometry.R b D c e f) : False := by
  obtain ⟨hs,hm,hl,hFirst,hPath,_,hAll⟩ := UnitPacketFrame.facts Q H w lead i j k mid rest tail
    hp he p r h0 h1 h2
  obtain ⟨o,ho⟩ := Foundation.ma_existence _ hs hm
  have hScalar := hAll o ho
  have hPf := EndpointFoundation.MA_totalProper_pfaffian_bound _ hs hm o ho
  have hProper := totalProper_proper _ o ho
  rw [hrep] at hl hFirst hPath hScalar hPf hProper
  exact LeftAcyclicUnitGeometry.scalar_impossible b D c e f H hb hD
    hl hFirst hPath o hProper hPf hScalar

theorem signed_triangle_impossible (Q : Rank4Input) (H : Nat)
    (w lead : List (Fin 4)) (i j k : Fin 4) (mid rest tail : List (Fin 4))
    (hp : Packet Q H w lead i j mid tail)
    (he : (i::j::mid)=[i,j]++k::rest)
    (p : Relabeling 4) (r : Bool)
    (h0 : p.toFun 0=i) (h1 : p.toFun 1=j) (h2 : p.toFun 2=k)
    (h01 : signedFrame (applyWord Q.val lead) p r 0 1=1)
    (hx : signedFrame (applyWord Q.val lead) p r 0 2<0)
    (hy : signedFrame (applyWord Q.val lead) p r 1 2≤0) : False := by
  let C := signedFrame (applyWord Q.val lead) p r
  have hC01 : C 0 1=1 := h01
  have hs := signedFrame_skew _ (word_preserves_skew Q.val lead Q.property) p r
  have hrep : C=LeftAcyclicUnitGeometry.R (-C 0 2) (-C 1 2) (C 0 3) (C 1 3) (C 2 3) := by
    simpa only [LeftAcyclicUnitGeometry.R,hC01,neg_neg] using (ofSix_reconstruct C hs).symm
  exact triangle_impossible Q H w lead i j k mid rest tail hp he p r
    (-C 0 2) (-C 1 2) (C 0 3) (C 1 3) (C 2 3) h0 h1 h2
    (by change C 0 2<0 at hx;omega) (by change C 1 2≤0 at hy;omega) hrep

#print axioms triangle_impossible
#print axioms signed_triangle_impossible
end Rank4Round2.LeftAcyclicUnitResidual
