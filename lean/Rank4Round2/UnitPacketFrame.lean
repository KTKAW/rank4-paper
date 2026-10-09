import Rank4Round2.UnitFirstSwitchTwo
import Rank4Round2.MixedUnitThreeFrame

/-! Facts in any supplied signed frame of the actual two-letter switch.
Every proper scalar comes from the original input by an actual reverse
word. No TotalProper frame covariance or extra foundation premise occurs. -/
namespace Rank4Round2.UnitPacketFrame
open QuiverProofs Rank4Coordinator Rank4CoordinatorR2 Rank4Round2
open ProperOrder ProperMutation ResidualUnitExcursion
open Rank4ReviewRound2.PeakNormalization

theorem facts (Q : Rank4Input) (H : Nat)
    (w lead : List (Fin 4)) (i j k : Fin 4) (mid rest tail : List (Fin 4))
    (hp : Packet Q H w lead i j mid tail)
    (he : (i::j::mid)=[i,j]++k::rest)
    (p : Relabeling 4) (r : Bool)
    (h0 : p.toFun 0=i) (h1 : p.toFun 1=j) (h2 : p.toFun 2=k) :
    let C := signedFrame (applyWord Q.val lead) p r
    SkewSymmetric C ∧ MutationAcyclic C ∧ HeightLe C H ∧
      ¬HeightLe (mutate C 0) H ∧ PrefixHeightLe C [0,1,2] (H+1) ∧
      ¬HeightLe (applyWord C [0,1]) H ∧
      ∀ o,TotalProper C o → orderMarkov C o≤(H:Int) := by
  let B := applyWord Q.val lead
  let C := signedFrame B p r
  change SkewSymmetric C ∧ MutationAcyclic C ∧ HeightLe C H ∧
    ¬HeightLe (mutate C 0) H ∧ PrefixHeightLe C [0,1,2] (H+1) ∧
    ¬HeightLe (applyWord C [0,1]) H ∧
    ∀ o,TotalProper C o → orderMarkov C o≤(H:Int)
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
  have hsB := word_preserves_skew Q.val lead Q.property
  have hsC := signedFrame_skew B hsB p r
  have hmaC : MutationAcyclic C := (signedFrame_MA B hsB p r).mpr
    ((mutationAcyclic_word_iff Q.val lead).mpr ⟨w,hp.acyclic⟩)
  refine ⟨hsC,hmaC,(signedFrame_height B p r H).mpr hp.lowLeft,?_,hPathC,?_,?_⟩
  · rw [show C=signedFrame B p r from rfl,signedFrame_mutate,h0,signedFrame_height]
    exact hp.highFirst
  · rw [show C=signedFrame B p r from rfl,signedFrame_word,signedFrame_height]
    simp only [List.map_cons,List.map_nil,h0,h1]
    exact hp.properHigh [j] (k::rest)
      (by simp only [hmid,List.cons_append,List.nil_append]) (by simp)
  · intro o ho
    have hBudget : scalarBudget Q.val≤H := by
      have hh := hp.budget;unfold endpointHeightBudget at hh;omega
    have hM := ScalarPathBudget.lead_totalProper_scalar_budget Q.val Q.property lead p r o ho
    have hAbs := Int.le_natAbs (a:=orderMarkov C o)
    change (orderMarkov C o).natAbs≤scalarBudget Q.val at hM
    omega

#print axioms facts
end Rank4Round2.UnitPacketFrame
