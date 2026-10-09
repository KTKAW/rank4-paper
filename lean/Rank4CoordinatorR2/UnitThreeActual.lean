import Rank4CoordinatorR2.UnitThreeEscape

/-! The three-high unit-prefix bound in every actual caller frame. The
proper scalar budget is the original input budget, transported through
the actual prefix. No covariance of total proper frames is assumed. -/
namespace Rank4CoordinatorR2.UnitThreeActual
open QuiverProofs Rank4Coordinator Rank4CoordinatorR2 Rank4Round2
open ProperOrder ProperMutation ProperObstructionSoundness
open Rank4ReviewRound2.PeakNormalization

theorem actual_unit_three_alternative_bounded
    (Q : Rank4Input) (hma : MutationAcyclic Q.val) (lead : List (Fin 4))
    (i j : Fin 4) (hij : i≠j) (H : Nat) (hBudget : scalarBudget Q.val≤H)
    (hStart : HeightLe (applyWord Q.val lead) H)
    (hPath : PrefixHeightLe (applyWord Q.val lead) [i,j,i] (H+1))
    (hFirst : ¬HeightLe (mutate (applyWord Q.val lead) i) H)
    (hThird : ¬HeightLe (applyWord (applyWord Q.val lead) [i,j,i]) H)
    (hUnit : abs (applyWord Q.val lead i j)=1) :
    HeightLe (mutate (applyWord Q.val lead) j) (H+1) := by
  let B := applyWord Q.val lead
  let p := pivotFrame i j
  have hp := pivotFrame_slots i j hij
  have hp0 : p.toFun 0=i := hp.1
  have hp1 : p.toFun 1=j := hp.2
  let r : Bool := if B i j=1 then false else true
  let C := signedFrame B p r
  have hPair : B i j=1 ∨ B i j= -1 := by
    rcases le_total 0 (B i j) with hn|hn
    · rw [abs_of_nonneg hn] at hUnit;exact Or.inl hUnit
    · rw [abs_of_nonpos hn] at hUnit;exact Or.inr (by omega)
  have h01 : C 0 1=1 := by
    rcases hPair with hPair|hPair <;>
      simp [C,signedFrame,r,relabel,reverse,hp0,hp1,hPair]
  have hsB := word_preserves_skew Q.val lead Q.property
  have hsC := signedFrame_skew B hsB p r
  have hmaB := (mutationAcyclic_word_iff Q.val lead).mpr hma
  have hmaC : MutationAcyclic C := (signedFrame_MA B hsB p r).mpr hmaB
  have hw : ([0,1,0] : List (Fin 4)).map p.toFun=[i,j,i] := by
    simp only [List.map_cons,List.map_nil,hp0,hp1]
  have hStartC : HeightLe C H := by rw [show C=signedFrame B p r from rfl,signedFrame_height];exact hStart
  have hPathC : PrefixHeightLe C [0,1,0] (H+1) := by
    apply (signedFrame_forward_prefix B p r [0,1,0] (H+1)).mpr
    rwa [hw]
  have hFirstC : ¬HeightLe (mutate C 0) H := by
    rw [show C=signedFrame B p r from rfl,signedFrame_mutate,hp0,signedFrame_height]
    exact hFirst
  have hThirdC : ¬HeightLe (applyWord C [0,1,0]) H := by
    rw [show C=signedFrame B p r from rfl,signedFrame_word,hw,signedFrame_height]
    exact hThird
  have hScalarC : ∀ a q,TotalProper (relabel C a) q → orderMarkov (relabel C a) q≤(H:Int) := by
    intro a q hq
    let s := p.trans a
    have he : relabel C a=signedFrame B s r := by
      cases hr : r <;> funext u v <;>
        simp [C,signedFrame,s,Relabeling.trans,relabel,reverse,hr]
    have hp' : TotalProper (signedFrame B s r) q := by rwa [←he]
    have hBound := ScalarPathBudget.lead_totalProper_scalar_budget Q.val Q.property
      lead s r q hp'
    have hAbs := Int.le_natAbs (a:=orderMarkov (signedFrame B s r) q)
    rw [he]
    change (orderMarkov (signedFrame B s r) q).natAbs≤scalarBudget Q.val at hBound
    omega
  have h := UnitThreeEscape.positive_unit_alternative_bounded C hsC hmaC h01 H
    hStartC hPathC hFirstC hThirdC hScalarC
  rw [show C=signedFrame B p r from rfl,signedFrame_mutate,hp1,signedFrame_height] at h
  exact h

#print axioms actual_unit_three_alternative_bounded
end Rank4CoordinatorR2.UnitThreeActual
