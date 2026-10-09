import Rank4CoordinatorR2.ScalarFrameBudget

/-! The scalar of any supplied total-proper order at any signed actual
prefix is bounded by the six original input scalars. The reverse prefix
is an actual mutation word; no total-proper frame covariance is assumed. -/
namespace Rank4CoordinatorR2.ScalarPathBudget
open QuiverProofs Rank4Coordinator Rank4CoordinatorR2 Rank4Round2
open ProperOrder ProperMutation ProperWiggle
open Rank4ReviewRound2.PeakNormalization Rank4CoordinatorR2.ScalarFrameBudget

theorem word_undo (B : Matrix 4) (w : List (Fin 4)) :
    applyWord (applyWord B w) w.reverse=B := by
  induction w generalizing B with
  | nil => rfl
  | cons k w ih =>
    simp only [applyWord,List.reverse_cons,applyWord_append,ih,mutation_involutive]

theorem lead_totalProper_scalar_budget (B : Matrix 4) (hs : SkewSymmetric B)
    (lead : List (Fin 4)) (p : Relabeling 4) (r : Bool) (q : CyclicOrder)
    (hq : TotalProper (signedFrame (applyWord B lead) p r) q) :
    (orderMarkov (signedFrame (applyWord B lead) p r) q).natAbs≤scalarBudget B := by
  let C := signedFrame (applyWord B lead) p r
  let back := lead.reverse.map p.invFun
  have hsC : SkewSymmetric C := signedFrame_skew _ (word_preserves_skew B lead hs) p r
  have he : applyWord C back=signedFrame B p r := by
    simp only [C,back,signedFrame_word,map_inverse_word,word_undo]
  obtain ⟨u,htr,_⟩ := totalProper_lifts_word C hsC q hq back
  have hm := transport_markov hsC htr
  rw [he] at hm
  have hb := signed_frame_scalar_budget_bound B hs p r u
  rw [hm] at hb
  exact hb

#print axioms word_undo
#print axioms lead_totalProper_scalar_budget
end Rank4CoordinatorR2.ScalarPathBudget
