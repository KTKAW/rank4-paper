import Rank4StructureRound2.UnitN2CyclicStrict
import Rank4CoordinatorR2.EqualUnitTriangle
import Rank4Round2.FixedTriangleResidual
import Rank4Round2.MixedIncidentResidual

/-! Actual all-label/sign cyclic selected triangles are impossible in a
corrected minimal Packet. The original scalar budget supplies every TP
order at the actual signed lead; no frame covariance is assumed. -/
namespace Rank4Round2.CyclicUnitResidual
open QuiverProofs Rank4Coordinator Rank4CoordinatorR2 Rank4Round2
open ProperOrder ProperMutation ProperWiggle ResidualUnitExcursion
open Rank4ReviewRound2.PeakNormalization
open QuiverProofs.Rank4StructureRound2

theorem cyclic_triangle_impossible (Q : Rank4Input) (H : Nat)
    (w lead : List (Fin 4)) (i j k : Fin 4) (mid rest tail : List (Fin 4))
    (hp : Packet Q H w lead i j mid tail)
    (he : (i::j::mid)=[i,j]++k::rest)
    (p : Relabeling 4) (r : Bool) (b c d e f : Int)
    (h0 : p.toFun 0=i) (h1 : p.toFun 1=j) (h2 : p.toFun 2=k)
    (hb : 1≤b) (hd : 1≤d)
    (hrep : signedFrame (applyWord Q.val lead) p r=UnitN2CyclicStrict.R b c d e f) : False := by
  let B := applyWord Q.val lead
  let C := signedFrame B p r
  have hmid : mid=k::rest := (List.cons.inj (List.cons.inj he).2).2
  have hw : w=lead++([i,j,k]++(rest++tail)) := by
    simpa only [hmid,List.cons_append,List.nil_append] using hp.split
  have hWhole : PrefixHeightLe Q.val (lead++([i,j,k]++(rest++tail))) (H+1) := by
    rw [←hw];exact hp.ceiling
  have hPath : PrefixHeightLe B [i,j,k] (H+1) :=
    ((prefixHeight_append_iff B [i,j,k] (rest++tail) (H+1)).mp
      ((prefixHeight_append_iff Q.val lead _ (H+1)).mp hWhole).2).1
  have hPathC : PrefixHeightLe C [0,1,2] (H+1) := by
    apply (signedFrame_forward_prefix B p r [0,1,2] (H+1)).mpr
    simpa only [List.map_cons,List.map_nil,h0,h1,h2] using hPath
  have hStart : HeightLe C H := (signedFrame_height B p r H).mpr hp.lowLeft
  have hFirst : ¬HeightLe (mutate C 0) H := by
    rw [show C=signedFrame B p r from rfl,signedFrame_mutate,h0,signedFrame_height]
    exact hp.highFirst
  have hSecond : ¬HeightLe (applyWord C [0,1]) H := by
    rw [show C=signedFrame B p r from rfl,signedFrame_word,signedFrame_height]
    simp only [List.map_cons,List.map_nil,h0,h1]
    exact hp.properHigh [j] (k::rest)
      (by simp only [hmid,List.cons_append,List.nil_append]) (by simp)
  have hCeil1 : HeightLe (mutate C 0) (H+1) := hPathC [0] [1,2] rfl
  have hCeil2 : HeightLe (applyWord C [0,1]) (H+1) := hPathC [0,1] [2] rfl
  have hCeil3 : HeightLe (applyWord C [0,1,2]) (H+1) := hPathC [0,1,2] [] (by simp)
  have hsB := word_preserves_skew Q.val lead Q.property
  have hsC := signedFrame_skew B hsB p r
  have hmaC : MutationAcyclic C := (signedFrame_MA B hsB p r).mpr
    ((mutationAcyclic_word_iff Q.val lead).mpr ⟨w,hp.acyclic⟩)
  have hBudget : scalarBudget Q.val≤H := by
    have hh := hp.budget;unfold endpointHeightBudget at hh;omega
  have hAll : ∀ o,TotalProper C o → orderMarkov C o≤(H:Int) := by
    intro o ho
    have hM := ScalarPathBudget.lead_totalProper_scalar_budget Q.val Q.property lead p r o ho
    have hAbs := Int.le_natAbs (a:=orderMarkov C o)
    change (orderMarkov C o).natAbs≤scalarBudget Q.val at hM
    omega
  change C=UnitN2CyclicStrict.R b c d e f at hrep
  by_cases hEq : b=d
  · have hEqual : C=EqualUnitTriangle.B b c e f := by rw [hrep,←hEq];rfl
    rw [hEqual] at hStart hFirst hCeil1 hCeil3 hmaC hAll
    exact EqualUnitTriangle.actual_MA_impossible b c e f H hb hStart hFirst hCeil1 hCeil3 hmaC hAll
  · obtain ⟨o,ho⟩ := Foundation.ma_existence C hsC hmaC
    have hScalar := hAll o ho
    have hStartR := hStart
    rw [hrep] at hStart hFirst hCeil1 hCeil2 hSecond hCeil3 hmaC ho hScalar
    obtain hFixed|hIncident := UnitN2CyclicStrict.actual_phases EndpointFoundation.endpoint_bridge
      b c d e f H hb hd hEq hStart hFirst hCeil1 hCeil2 hSecond hCeil3 hmaC o ho hScalar
    · obtain ⟨hb2,hd1,he0⟩ := hFixed
      have hFixedRep : signedFrame (applyWord Q.val lead) p r=MixedUnitRelation.R c 0 f := by
        change C=MixedUnitRelation.R c 0 f
        rw [hrep,hb2,hd1,he0]
        rfl
      exact FixedTriangleResidual.first_switch_triangle_impossible Q H w lead i j k mid rest tail
        hp he p r c 0 f h0 h1 h2 hFixedRep
    · obtain ⟨hb1,hd2,hcNeg,heNeg,hTop,hu1,huH⟩ := hIncident
      have hcH : -c≤(H:Int) := by
        have hh := (hStartR 0 3).1
        rw [hrep] at hh
        change -(H:Int)≤c at hh
        omega
      have heq : e= -c-((H:Int)+1) := by omega
      have hIncidentRep : signedFrame (applyWord Q.val lead) p r=
          MixedIncidentFamilyHeight.R (-c) ((H:Int)+1-f) ((H:Int)+1) := by
        change C=MixedIncidentFamilyHeight.R (-c) ((H:Int)+1-f) ((H:Int)+1)
        rw [hrep,hb1,hd2]
        change ofSix 1 (-1) c 2 e f=ofSix 1 (-1) (- -c) 2
          (-c-((H:Int)+1)) ((H:Int)+1-((H:Int)+1-f))
        rw [heq,neg_neg]
        congr 1 <;> ring
      exact MixedIncidentResidual.pattern_impossible Q H w lead i j k mid rest tail hp hmid
        p r (-c) ((H:Int)+1-f) h0 h1 h2 (by omega) hu1 hcH huH hIncidentRep

theorem packet_first_switch_not_cyclic (Q : Rank4Input) (H : Nat)
    (w lead : List (Fin 4)) (i j : Fin 4) (mid tail : List (Fin 4))
    (hp : Packet Q H w lead i j mid tail) :
    ∃ k rest,(i::j::mid)=[i,j]++k::rest ∧ k≠i ∧ k≠j ∧
      ¬(signedFrame (applyWord Q.val lead) (MixedUnitThreeFrame.tripleFrame i j k)
          (MixedUnitThreeFrame.flip (applyWord Q.val lead) i j) 0 2<0 ∧
        0<signedFrame (applyWord Q.val lead) (MixedUnitThreeFrame.tripleFrame i j k)
          (MixedUnitThreeFrame.flip (applyWord Q.val lead) i j) 1 2) := by
  obtain ⟨k,rest,he,hki,hkj⟩ := UnitFirstSwitchTwo.packet_first_switch_two_only
    Q H w lead i j mid tail hp
  refine ⟨k,rest,he,hki,hkj,?_⟩
  rintro ⟨hx,hy⟩
  let p := MixedUnitThreeFrame.tripleFrame i j k
  let r := MixedUnitThreeFrame.flip (applyWord Q.val lead) i j
  let C := signedFrame (applyWord Q.val lead) p r
  obtain ⟨h0,h1,h2⟩ := MixedUnitThreeFrame.triple_slots i j k hp.distinct hki hkj
  have hu : abs (applyWord Q.val lead i j)=1 := by simpa [mutate] using hp.unit
  have h01 : C 0 1=1 := MixedUnitThreeFrame.unit_positive _ i j k hp.distinct hki hkj hu
  have hs := signedFrame_skew _ (word_preserves_skew Q.val lead Q.property) p r
  have hrep : C=UnitN2CyclicStrict.R (-C 0 2) (C 0 3) (C 1 2) (C 1 3) (C 2 3) := by
    simpa only [UnitN2CyclicStrict.R,h01,neg_neg] using (ofSix_reconstruct C hs).symm
  exact cyclic_triangle_impossible Q H w lead i j k mid rest tail hp he p r
    (-C 0 2) (C 0 3) (C 1 2) (C 1 3) (C 2 3) h0 h1 h2
    (by change C 0 2<0 at hx;omega) (by change 0<C 1 2 at hy;omega) hrep

#print axioms cyclic_triangle_impossible
#print axioms packet_first_switch_not_cyclic
end Rank4Round2.CyclicUnitResidual
