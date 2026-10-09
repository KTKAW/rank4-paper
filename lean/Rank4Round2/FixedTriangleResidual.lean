import Rank4CoordinatorR2.FixedUnitTriangle
import Rank4Round2.UnitForcedReturn
import Rank4Round2.MixedUnitResidual
import Rank4Round2.MixedUnitThreeFrame
import Rank4Round2.UnitFirstSwitchTwo

/-! The actual first-return consumer for the fixed (1,-2,1) triangle.
The original input supplies the proper scalar budget. The actual signed
triangle frame is explicit; its first return is proved to be [j,k,i,k]. -/
namespace Rank4Round2.FixedTriangleResidual
open QuiverProofs Rank4Coordinator Rank4CoordinatorR2 Rank4Round2
open ProperOrder ProperMutation ProperWiggle ResidualUnitExcursion
open Rank4ReviewRound2.PeakNormalization

theorem return_shape (Q : Rank4Input) (H : Nat)
    (w lead : List (Fin 4)) (i j k : Fin 4) (mid rest tail : List (Fin 4))
    (hp : Packet Q H w lead i j mid tail) (hmid : mid=k::rest)
    (p : Relabeling 4) (r : Bool) (c e f : Int)
    (h0 : p.toFun 0=i) (h1 : p.toFun 1=j) (h2 : p.toFun 2=k)
    (hrep : signedFrame (applyWord Q.val lead) p r=MixedUnitRelation.R c e f) :
    rest=[i,k] := by
  let B := applyWord Q.val lead
  let C := signedFrame B p r
  have hw : w=lead++([i,j,k]++(rest++tail)) := by
    simpa only [hmid,List.cons_append,List.nil_append] using hp.split
  have hWhole : PrefixHeightLe Q.val (lead++([i,j,k]++(rest++tail))) (H+1) := by
    rw [←hw]
    exact hp.ceiling
  have hPath : PrefixHeightLe B [i,j,k] (H+1) :=
    ((prefixHeight_append_iff B [i,j,k] (rest++tail) (H+1)).mp
      ((prefixHeight_append_iff Q.val lead _ (H+1)).mp hWhole).2).1
  have hMap : ([0,1,2] : List (Fin 4)).map p.toFun=[i,j,k] := by
    simp only [List.map_cons,List.map_nil,h0,h1,h2]
  have hPathC : PrefixHeightLe C [0,1,2] (H+1) := by
    apply (signedFrame_forward_prefix B p r [0,1,2] (H+1)).mpr
    rwa [hMap]
  have hRC : HeightLe C H := (signedFrame_height B p r H).mpr hp.lowLeft
  have hHighC : ¬HeightLe (mutate C 0) H := by
    rw [show C=signedFrame B p r from rfl,signedFrame_mutate,h0,signedFrame_height]
    exact hp.highFirst
  have hsB := word_preserves_skew Q.val lead Q.property
  have hsC := signedFrame_skew B hsB p r
  have hmaC : MutationAcyclic C := (signedFrame_MA B hsB p r).mpr
    ((mutationAcyclic_word_iff Q.val lead).mpr ⟨w,hp.acyclic⟩)
  obtain ⟨o,ho⟩ := Foundation.ma_existence C hsC hmaC
  have hM := ScalarPathBudget.lead_totalProper_scalar_budget Q.val Q.property lead p r o ho
  have hBudget : scalarBudget Q.val≤H := by
    have hh := hp.budget
    unfold endpointHeightBudget at hh
    omega
  have hScalar : orderMarkov C o≤(H:Int) := by
    have habsm := Int.le_natAbs (a:=orderMarkov C o)
    change (orderMarkov C o).natAbs≤scalarBudget Q.val at hM
    omega
  have hProper := totalProper_proper C o ho
  change C=MixedUnitRelation.R c e f at hrep
  rw [hrep] at hRC hPathC hHighC hProper hScalar
  obtain ⟨hc,hcH,he,hf⟩ := FixedUnitTriangle.family_shape c e f H
    hRC hPathC hHighC o hProper hScalar
  have hH : 2≤H := by
    have hh := (hRC 0 2).1
    change -(H:Int)≤ -2 at hh
    omega
  have hFamily : C=MixedUnitFamily.R H c := by
    rw [hrep,he,hf]
    rfl
  obtain ⟨ho1,ho2,ho3,ho4,ho5,_,_,_⟩ := MixedUnitFamily.matrices H c hc hcH
  have hn3 : applyWord C [0,1,2]=MixedUnitFamily.O3 H c := by
    simp only [applyWord,hFamily,ho1,ho2,ho3]
  have hn4 : applyWord C [0,1,2,0]=MixedUnitFamily.O4 H c := by
    simp only [applyWord,hFamily,ho1,ho2,ho3,ho4]
  have hn5 : applyWord C [0,1,2,0,2]=MixedUnitFamily.O5 H c := by
    simp only [applyWord,hFamily,ho1,ho2,ho3,ho4,ho5]
  have ha3 : signedFrame (applyWord B [i,j,k]) p r=MixedUnitFamily.O3 H c := by
    simpa only [C,signedFrame_word,List.map_cons,List.map_nil,h0,h1,h2] using hn3
  have ha4 : signedFrame (applyWord B [i,j,k,i]) p r=MixedUnitFamily.O4 H c := by
    simpa only [C,signedFrame_word,List.map_cons,List.map_nil,h0,h1,h2] using hn4
  have ha5 : signedFrame (applyWord B [i,j,k,i,k]) p r=MixedUnitFamily.O5 H c := by
    simpa only [C,signedFrame_word,List.map_cons,List.map_nil,h0,h1,h2] using hn5
  have hHigh2 : ¬HeightLe (applyWord (mutate B i) [j,k]) H := by
    change ¬HeightLe (applyWord B [i,j,k]) H
    rw [←signedFrame_height _ p r H,ha3]
    exact (MixedUnitFamily.highs H c).2.2.1
  have hHigh3 : ¬HeightLe (applyWord (mutate B i) [j,k,i]) H := by
    change ¬HeightLe (applyWord B [i,j,k,i]) H
    rw [←signedFrame_height _ p r H,ha4]
    exact (MixedUnitFamily.highs H c).2.2.2
  have hLow4 : HeightLe (applyWord (mutate B i) [j,k,i,k]) H := by
    change HeightLe (applyWord B [i,j,k,i,k]) H
    rw [←signedFrame_height _ p r H,ha5]
    exact (MixedUnitFamily.bounds H c hH hc hcH).2.2.2.2.2.1
  have hNext2 : ∀ a,HeightLe (mutate (applyWord (mutate B i) [j,k]) a) (H+1) →
      a=i ∨ a=k := by
    intro a ha
    by_cases hk : p.invFun a=2
    · right
      have hh := congrArg p.toFun hk
      simpa only [p.right_inv,h2] using hh
    · left
      have hn : HeightLe (mutate (MixedUnitFamily.O3 H c) (p.invFun a)) (H+1) := by
        rw [←ha3,signedFrame_mutate,p.right_inv,signedFrame_height]
        exact ha
      have hh := congrArg p.toFun (FixedUnitTriangle.third_forward_only H c hH hc hcH
        (p.invFun a) hk hn)
      simpa only [p.right_inv,h0] using hh
  have hNext3 : ∀ a,HeightLe (mutate (applyWord (mutate B i) [j,k,i]) a) (H+1) →
      a=k ∨ a=i := by
    intro a ha
    by_cases hi : p.invFun a=0
    · right
      have hh := congrArg p.toFun hi
      simpa only [p.right_inv,h0] using hh
    · left
      have hn : HeightLe (mutate (MixedUnitFamily.O4 H c) (p.invFun a)) (H+1) := by
        rw [←ha4,signedFrame_mutate,p.right_inv,signedFrame_height]
        exact ha
      have hh := congrArg p.toFun (FixedUnitTriangle.fourth_forward_only H c hH hc hcH
        (p.invFun a) hi hn)
      simpa only [p.right_inv,h2] using hh
  have hwReturn : w=(lead++[i])++((j::k::rest)++tail) := by
    rw [hp.split,hmid]
    simp only [List.append_assoc,List.cons_append,List.nil_append]
  have hWholeReturn : PrefixHeightLe Q.val ((lead++[i])++((j::k::rest)++tail)) (H+1) := by
    rw [←hwReturn]
    exact hp.ceiling
  have hCeil : PrefixHeightLe (mutate B i) (j::k::rest) (H+1) := by
    have hh := ((prefixHeight_append_iff Q.val (lead++[i]) _ (H+1)).mp hWholeReturn).2
    rw [applyWord_append] at hh
    exact ((prefixHeight_append_iff (mutate B i) (j::k::rest) tail (H+1)).mp hh).1
  have hNR := PairWord.embedded_no_backtrack w (lead++[i]) (j::k::rest) tail
    hwReturn hp.reduced
  exact UnitForcedReturn.forced_four_return (mutate B i) i j k rest H (H+1)
    hCeil (by simpa only [hmid] using hp.lowReturn)
    (by simpa only [hmid] using hp.properHigh) hNR hHigh2 hHigh3 hLow4 hNext2 hNext3

theorem first_switch_triangle_impossible (Q : Rank4Input) (H : Nat)
    (w lead : List (Fin 4)) (i j k : Fin 4) (mid rest tail : List (Fin 4))
    (hp : Packet Q H w lead i j mid tail)
    (he : (i::j::mid)=[i,j]++k::rest)
    (p : Relabeling 4) (r : Bool) (c e f : Int)
    (h0 : p.toFun 0=i) (h1 : p.toFun 1=j) (h2 : p.toFun 2=k)
    (hrep : signedFrame (applyWord Q.val lead) p r=MixedUnitRelation.R c e f) : False := by
  have hm : mid=k::rest := (List.cons.inj (List.cons.inj he).2).2
  have hr := return_shape Q H w lead i j k mid rest tail hp hm p r c e f h0 h1 h2 hrep
  have hmid : mid=[k,i,k] := by rw [hm,hr]
  exact MixedUnitResidual.pattern_impossible Q H w lead i j k mid tail hp hmid
    p r c e f h0 h1 h2 hrep

theorem packet_first_switch_excludes_fixed_triangle (Q : Rank4Input) (H : Nat)
    (w lead : List (Fin 4)) (i j : Fin 4) (mid tail : List (Fin 4))
    (hp : Packet Q H w lead i j mid tail) :
    ∃ k rest,(i::j::mid)=[i,j]++k::rest ∧ k≠i ∧ k≠j ∧
      ¬(signedFrame (applyWord Q.val lead) (MixedUnitThreeFrame.tripleFrame i j k)
          (MixedUnitThreeFrame.flip (applyWord Q.val lead) i j) 0 2= -2 ∧
        signedFrame (applyWord Q.val lead) (MixedUnitThreeFrame.tripleFrame i j k)
          (MixedUnitThreeFrame.flip (applyWord Q.val lead) i j) 1 2=1) := by
  obtain ⟨k,rest,he,hki,hkj⟩ := UnitFirstSwitchTwo.packet_first_switch_two_only
    Q H w lead i j mid tail hp
  refine ⟨k,rest,he,hki,hkj,?_⟩
  rintro ⟨h02,h12⟩
  have hu : abs (applyWord Q.val lead i j)=1 := by
    simpa [mutate] using hp.unit
  have hs := word_preserves_skew Q.val lead Q.property
  have hrep := MixedUnitThreeFrame.computed_rep (applyWord Q.val lead) hs i j k
    hp.distinct hki hkj hu h02 h12
  obtain ⟨h0,h1,h2⟩ := MixedUnitThreeFrame.triple_slots i j k hp.distinct hki hkj
  exact first_switch_triangle_impossible Q H w lead i j k mid rest tail hp he
    (MixedUnitThreeFrame.tripleFrame i j k) (MixedUnitThreeFrame.flip (applyWord Q.val lead) i j)
    _ _ _ h0 h1 h2 hrep

#print axioms return_shape
#print axioms first_switch_triangle_impossible
#print axioms packet_first_switch_excludes_fixed_triangle
end Rank4Round2.FixedTriangleResidual
