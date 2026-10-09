import Rank4CoordinatorR2.Foundation
import Rank4StructureRound2.StableWordAssembly

/-! The normalized strong-first whole-word trap is applied to every actual
input prefix, sign and vertex frame. Both properness bridges are supplied by
audited unconditional proofs. This excludes strong first pairs of a high
excursion; weak first pairs remain a separate global obligation. -/
namespace Rank4CoordinatorR2.StrongForward
open QuiverProofs Rank4Coordinator Rank4CoordinatorR2 Rank4Round2
open ProperOrder ProperObstructionSoundness
open Rank4ReviewRound2.PeakNormalization
open QuiverProofs.Rank4StructureRound2

 theorem mapped_no_backtrack (w : List (Fin 4)) (p : Relabeling 4)
    (hnr : ∀ u k v,w≠u++k::k::v) :
    ∀ u k v,w.map p.invFun≠u++k::k::v := by
  intro u k v he
  have hm := congrArg (List.map p.toFun) he
  rw [map_inverse_word] at hm
  have he' : w=u.map p.toFun++p.toFun k::p.toFun k::v.map p.toFun := by
    simpa only [List.map_append,List.map_cons] using hm
  exact hnr (u.map p.toFun) (p.toFun k) (v.map p.toFun) he'

theorem actual_strong_forward_no_return
    (Q : Rank4Input) (hma : MutationAcyclic Q.val) (lead : List (Fin 4))
    (i j : Fin 4) (hij : i≠j) (H : Nat)
    (hBudget : scalarBudget Q.val≤H)
    (hP : HeightLe (applyWord Q.val lead) (H+1))
    (hi : HeightLe (mutate (applyWord Q.val lead) i) H)
    (hj : HeightLe (mutate (applyWord Q.val lead) j) (H+1))
    (hout : ¬HeightLe (applyWord Q.val lead) H)
    (ha : 2≤abs (applyWord Q.val lead i j))
    (tail : List (Fin 4))
    (hnr : ∀ u k v,(j::tail)≠u++k::k::v)
    (hCeil : PrefixHeightLe (applyWord Q.val lead) (j::tail) (H+1))
    (hEnd : HeightLe (applyWord (applyWord Q.val lead) (j::tail)) H) : False := by
  let P := applyWord Q.val lead
  let pp := pivotFrame i j
  let B := relabel P pp
  have hsP : SkewSymmetric P := word_preserves_skew Q.val lead Q.property
  have hsB : SkewSymmetric B := relabel_skew P pp hsP
  have hslots := pivotFrame_slots i j hij
  have hpp0 : pp.toFun 0=i := hslots.1
  have hpp1 : pp.toFun 1=j := hslots.2
  have hBP : HeightLe B (H+1) := (heightLe_relabel_iff P pp (H+1)).mpr hP
  have hB0 : HeightLe (mutate B 0) H := by
    change HeightLe (mutate (relabel P pp) 0) H
    rw [mutate_relabel,heightLe_relabel_iff,hpp0]
    exact hi
  have hB1 : HeightLe (mutate B 1) (H+1) := by
    change HeightLe (mutate (relabel P pp) 1) (H+1)
    rw [mutate_relabel,heightLe_relabel_iff,hpp1]
    exact hj
  have hBa : 2≤abs (B 0 1) := by
    change 2≤abs (P (pp.toFun 0) (pp.toFun 1))
    rw [hpp0,hpp1]
    exact ha
  have hBo : ¬HeightLe B H := fun h => hout ((heightLe_relabel_iff P pp H).mp h)
  obtain ⟨p,r,a,b,c,d,E,f,hp0,hp1,ha',hb,hc,hf,hrep⟩ :=
    TwoStateFrame.half_peak_normalization B hsB H hBP hB0 hB1 hBo hBa
  let s := pp.trans p
  let C := signedFrame P s r
  have heq : C=TwoStateScalar.Q a b c d E f := hrep
  have hs0 : s.toFun 0=i := by
    change pp.toFun (p.toFun 0)=i
    rw [hp0,hpp0]
  have hs1 : s.toFun 1=j := by
    change pp.toFun (p.toFun 1)=j
    rw [hp1,hpp1]
  have hsC : SkewSymmetric C := signedFrame_skew P hsP s r
  have hCma : MutationAcyclic C := (signedFrame_MA P hsP s r).mpr
    ((mutationAcyclic_word_iff Q.val lead).mpr hma)
  have hC0 : HeightLe (mutate C 0) H := by
    rw [show C=signedFrame P s r from rfl,signedFrame_mutate,hs0,signedFrame_height]
    exact hi
  have hmapj : s.invFun j=1 := by rw [←hs1,s.left_inv]
  have hmapw : (j::tail).map s.invFun=1::tail.map s.invFun := by simp only [List.map_cons,hmapj]
  have hCceil : PrefixHeightLe C (1::tail.map s.invFun) (H+1) := by
    have h := (signedFrame_prefix P s r (j::tail) (H+1)).mpr hCeil
    rwa [hmapw] at h
  have hCend : HeightLe (applyWord C (1::tail.map s.invFun)) H := by
    rw [←hmapw,show C=signedFrame P s r from rfl,
      signedFrame_word,map_inverse_word,signedFrame_height]
    exact hEnd
  have hCnr : ∀ u k v,(1::tail.map s.invFun)≠u++k::k::v := by
    rw [←hmapw]
    exact mapped_no_backtrack (j::tail) s hnr
  obtain ⟨q,hq⟩ := Foundation.ma_existence C hsC hCma
  have hBound := ScalarPathBudget.lead_totalProper_scalar_budget Q.val Q.property
    lead s r q hq
  have hM : orderMarkov C q≤(H:Int) := by
    have hle := Int.le_natAbs (a:=orderMarkov C q)
    change (orderMarkov C q).natAbs≤scalarBudget Q.val at hBound
    omega
  rw [heq] at hC0 hCma hq hM hCceil hCend
  exact StableWordAssembly.normalized_reduced_strong_excursion_impossible
    EndpointFoundation.endpoint_bridge a b c d E f H ha' hb hc hf hC0 hCma q hq hM
    (tail.map s.invFun) hCnr hCceil hCend

#print axioms mapped_no_backtrack
#print axioms actual_strong_forward_no_return
end Rank4CoordinatorR2.StrongForward
