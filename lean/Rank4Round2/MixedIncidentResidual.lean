import Rank4StructureRound2.MixedIncidentEqual
import Rank4Round2.MixedIncidentRerouting
import Rank4Round2.MixedUnitReverseFamily
import Rank4Round2.UnitFirstSwitchTwo

/-! Actual first-return/count lowering for the other incident family.
The family representation and positive bounded slopes remain explicit;
the proper scalar budget and actual MA come from the original Packet. -/
namespace Rank4Round2.MixedIncidentResidual
open QuiverProofs Rank4Coordinator Rank4CoordinatorR2 Rank4Round2
open ProperOrder ProperMutation ProperWiggle ResidualUnitExcursion
open Rank4ReviewRound2.PeakNormalization MixedUnitRelation MixedUnitActualEndpoint
open QuiverProofs.Rank4StructureRound2

theorem return_shape_and_count (Q : Rank4Input) (H : Nat)
    (w lead : List (Fin 4)) (i j k : Fin 4) (mid rest tail : List (Fin 4))
    (hp : Packet Q H w lead i j mid tail) (hmid : mid=k::rest)
    (p : Relabeling 4) (r : Bool) (t u : Int)
    (h0 : p.toFun 0=i) (h1 : p.toFun 1=j) (h2 : p.toFun 2=k)
    (ht : 1≤t) (hu : 1≤u) (htH : t≤(H:Int)) (huH : u≤(H:Int))
    (hrep : signedFrame (applyWord Q.val lead) p r=
      MixedIncidentFamilyHeight.R t u ((H:Int)+1)) :
    rest=[] ∧ overCount (applyWord Q.val lead) ([i,j,k]) H=2 := by
  have hH : 2≤H := by
    have hh := ((signedFrame_height _ p r H).mpr hp.lowLeft) 1 2
    rw [hrep] at hh
    change -(H:Int)≤2 ∧ 2≤(H:Int) at hh
    omega
  let f := (H:Int)+1-u
  obtain ⟨ho1,ho2,ho3,_,_,_,_,_⟩ := MixedUnitReverseFamily.matrices H t f ht htH
    (by dsimp [f];omega) (by dsimp [f];omega)
  obtain ⟨_,_,_,hLow⟩ := MixedUnitReverseFamily.old_bounds H t f hH ht htH
    (by dsimp [f];omega) (by dsimp [f];omega)
  have hLowShort : HeightLe (applyWord (signedFrame (applyWord Q.val lead) p r) [0,1,2]) H := by
    rw [hrep]
    change HeightLe (applyWord (MixedUnitReverseFamily.R H t f) [0,1,2]) H
    simpa only [applyWord,ho1,ho2,ho3] using hLow
  have hLowActual : HeightLe (applyWord (mutate (applyWord Q.val lead) i) [j,k]) H := by
    rw [signedFrame_word,signedFrame_height] at hLowShort
    simpa only [List.map_cons,List.map_nil,h0,h1,h2] using hLowShort
  have hr : rest=[] := by
    by_contra hn
    exact hp.properHigh [j,k] rest (by simp only [hmid,List.cons_append,List.nil_append]) hn hLowActual
  have hOldCount : overCount (MixedUnitReverseFamily.R H t f) [0,1,2] H=2 := by
    have hh1 : ¬HeightLe (MixedUnitReverseFamily.O1 H t f) H := by
      intro h;have hh := (h 1 3).1;change -(H:Int)≤ -((H:Int)+1) at hh;omega
    have hh2 : ¬HeightLe (MixedUnitReverseFamily.O2 H t f) H := by
      intro h;have hh := (h 1 3).2;change (H:Int)+1≤(H:Int) at hh;omega
    simp only [overCount,ho1,ho2,ho3,overBit,if_neg hh1,if_neg hh2,if_pos hLow]
  have hc : overCount (signedFrame (applyWord Q.val lead) p r) [0,1,2] H=2 := by
    rw [hrep]
    exact hOldCount
  rw [signedFrame_forward_count] at hc
  exact ⟨hr,by simpa only [List.map_cons,List.map_nil,h0,h1,h2] using hc⟩

theorem pattern_lowering (Q : Rank4Input) (H : Nat)
    (w lead : List (Fin 4)) (i j k : Fin 4) (mid rest tail : List (Fin 4))
    (hp : Packet Q H w lead i j mid tail) (hmid : mid=k::rest)
    (p : Relabeling 4) (r : Bool) (t u : Int)
    (h0 : p.toFun 0=i) (h1 : p.toFun 1=j) (h2 : p.toFun 2=k)
    (ht : 1≤t) (hu : 1≤u) (htH : t≤(H:Int)) (huH : u≤(H:Int))
    (hrep : signedFrame (applyWord Q.val lead) p r=
      MixedIncidentFamilyHeight.R t u ((H:Int)+1)) :
    ∃ new,(new=MixedUnitReverseRelation.long ∨ new=MixedIncidentRerouting.second) ∧
      let v := lead++(new.map p.toFun++tail.map (conjugate p cycle).invFun)
      Acyclic (applyWord Q.val v) ∧ PrefixHeightLe Q.val v (H+1) ∧
        overCount Q.val v H+2=overCount Q.val w H ∧ v.length=w.length+2 := by
  obtain ⟨hr,hCount⟩ := return_shape_and_count Q H w lead i j k mid rest tail hp hmid
    p r t u h0 h1 h2 ht hu htH huH hrep
  have hm : mid=[k] := by rw [hmid,hr]
  have hMap : MixedUnitReverseRelation.short.map p.toFun=[i,j,k] := by
    simp only [MixedUnitReverseRelation.short,List.map_cons,List.map_nil,h0,h1,h2]
  have hw : w=lead++(MixedUnitReverseRelation.short.map p.toFun++tail) := by
    rw [hMap]
    simpa only [hm,List.cons_append,List.nil_append] using hp.split
  let B := applyWord Q.val lead
  let C := signedFrame B p r
  have hH : 2≤H := by
    have hh := ((signedFrame_height B p r H).mpr hp.lowLeft) 1 2
    rw [hrep] at hh
    change -(H:Int)≤2 ∧ 2≤(H:Int) at hh
    omega
  have hsB := word_preserves_skew Q.val lead Q.property
  have hsC := signedFrame_skew B hsB p r
  have hmaC : MutationAcyclic C := (signedFrame_MA B hsB p r).mpr
    ((mutationAcyclic_word_iff Q.val lead).mpr ⟨w,hp.acyclic⟩)
  obtain ⟨o,ho⟩ := Foundation.ma_existence C hsC hmaC
  have hM := ScalarPathBudget.lead_totalProper_scalar_budget Q.val Q.property lead p r o ho
  have hBudget : scalarBudget Q.val≤H := by
    have hh := hp.budget;unfold endpointHeightBudget at hh;omega
  have hScalar : orderMarkov C o≤(H:Int) := by
    have ha := Int.le_natAbs (a:=orderMarkov C o)
    change (orderMarkov C o).natAbs≤scalarBudget Q.val at hM
    omega
  change C=MixedIncidentFamilyHeight.R t u ((H:Int)+1) at hrep
  rw [hrep] at hmaC ho hScalar
  have hRoutes := MixedIncidentEqual.actual_one_route_below EndpointFoundation.endpoint_bridge
    t u H hH ht hu htH huH hmaC o ho hScalar
  have hChoice : ∃ new,(new=MixedUnitReverseRelation.long ∨ new=MixedIncidentRerouting.second) ∧
      PrefixHeightLe C new H ∧ applyWord C new=
        relabel (applyWord C MixedUnitReverseRelation.short) cycle := by
    rcases hRoutes with hA|hB
    · refine ⟨MixedUnitReverseRelation.long,Or.inl rfl,?_,?_⟩
      · rwa [hrep]
      · rw [hrep];exact MixedUnitReverseRelation.endpoint (-t) (t-((H:Int)+1)) ((H:Int)+1-u)
    · refine ⟨MixedIncidentRerouting.second,Or.inr rfl,?_,?_⟩
      · rwa [hrep]
      · rw [hrep];exact MixedIncidentRerouting.second_endpoint t u ((H:Int)+1) ht hu
          (by omega) (by omega)
  obtain ⟨new,hRoute,hn,he⟩ := hChoice
  have hWhole : PrefixHeightLe Q.val (lead++(MixedUnitReverseRelation.short.map p.toFun++tail)) (H+1) := by
    rw [←hw];exact hp.ceiling
  have ha : Acyclic (applyWord Q.val (lead++(MixedUnitReverseRelation.short.map p.toFun++tail))) := by
    rw [←hw];exact hp.acyclic
  have hc : overCount B (MixedUnitReverseRelation.short.map p.toFun) H=2 := by rwa [hMap]
  obtain ⟨hCeil,hAcyclic,_⟩ := MixedIncidentRerouting.whole_signed_progress Q.val lead tail p r
    MixedUnitReverseRelation.short new cycle H he hn
    (by change 0<overCount B (MixedUnitReverseRelation.short.map p.toFun) H;rw [hc];omega) hWhole ha
  have hCross := MixedIncidentRerouting.whole_signed_count Q.val lead tail p r
    MixedUnitReverseRelation.short new cycle H he
  have hnActual := (signedFrame_forward_prefix B p r new H).mp hn
  have hZero := overCount_eq_zero B _ H hnActual
  rw [hc,hZero,←hw,Nat.add_zero] at hCross
  refine ⟨new,hRoute,hAcyclic,hCeil,hCross,?_⟩
  rw [hw]
  rcases hRoute with hRoute|hRoute <;> rw [hRoute] <;>
    simp [MixedUnitReverseRelation.long,MixedUnitReverseRelation.short,MixedIncidentRerouting.second]
  all_goals omega

theorem pattern_impossible (Q : Rank4Input) (H : Nat)
    (w lead : List (Fin 4)) (i j k : Fin 4) (mid rest tail : List (Fin 4))
    (hp : Packet Q H w lead i j mid tail) (hmid : mid=k::rest)
    (p : Relabeling 4) (r : Bool) (t u : Int)
    (h0 : p.toFun 0=i) (h1 : p.toFun 1=j) (h2 : p.toFun 2=k)
    (ht : 1≤t) (hu : 1≤u) (htH : t≤(H:Int)) (huH : u≤(H:Int))
    (hrep : signedFrame (applyWord Q.val lead) p r=
      MixedIncidentFamilyHeight.R t u ((H:Int)+1)) : False := by
  obtain ⟨new,_,ha,hh,hc,_⟩ := pattern_lowering Q H w lead i j k mid rest tail hp hmid
    p r t u h0 h1 h2 ht hu htH huH hrep
  have hMin := hp.countMinimum _ ha hh
  omega

#print axioms return_shape_and_count
#print axioms pattern_lowering
#print axioms pattern_impossible
end Rank4Round2.MixedIncidentResidual
