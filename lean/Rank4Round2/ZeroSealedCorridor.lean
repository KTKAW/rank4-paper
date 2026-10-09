import Rank4Round2.ZeroOrbitGeometry
import Rank4CoordinatorR2.ZeroFirstSwitch

/-! Actual zero-first corridors are sealed against third pivots. Before
the first low return an alternating zero-pair corridor has at most two high
states. The accepted exact MA and endpoint foundations are instantiated;
the input scalar budget and actual prefix are explicit. -/
namespace Rank4Round2.ZeroSealedCorridor
open QuiverProofs Rank4Coordinator Rank4CoordinatorR2 Rank4Round2
open ProperOrder ProperMutation ProperObstructionSoundness
open Rank4ReviewRound2.StrongPairIncident
open Rank4ReviewRound2.PeakNormalization

theorem actual_first_no_third
    (Q : Rank4Input) (hma : MutationAcyclic Q.val) (lead : List (Fin 4))
    (i j : Fin 4) (hij : i≠j) (H : Nat) (hBudget : scalarBudget Q.val≤H)
    (hP : HeightLe (applyWord Q.val lead) (H+1))
    (hLow : HeightLe (mutate (applyWord Q.val lead) i) H)
    (hNext : HeightLe (mutate (applyWord Q.val lead) j) (H+1))
    (hHigh : ¬HeightLe (applyWord Q.val lead) H) (hz : applyWord Q.val lead i j=0)
    (k : Fin 4) (hki : k≠i) (hkj : k≠j) :
    ¬HeightLe (mutate (applyWord Q.val lead) k) (H+1) := by
  intro hk
  let B := applyWord Q.val lead
  change B i j=0 at hz
  let p := pivotFrame i j
  let N := relabel B p
  have hsB := word_preserves_skew Q.val lead Q.property
  have hsN := relabel_skew B p hsB
  have hp := pivotFrame_slots i j hij
  have hp0 : p.toFun 0=i := hp.1
  have hp1 : p.toFun 1=j := hp.2
  have hzN : N 0 1=0 := by simpa only [N,relabel,hp0,hp1] using hz
  have hLowN : HeightLe (mutate N 0) H := by
    change HeightLe (mutate (relabel B p) 0) H
    rwa [mutate_relabel,heightLe_relabel_iff,hp0]
  have hIncN := ZeroOrbitGeometry.zero_incident_from_low N hsN 0 1 (by decide) hzN H hLowN
  have hCeilN : HeightLe N (H+1) := (heightLe_relabel_iff B p _).mpr hP
  have hHighN : ¬HeightLe N H := fun hh => hHigh ((heightLe_relabel_iff B p H).mp hh)
  have hTop : abs (N 2 3)=(H:Int)+1 := by
    rcases ZeroOrbitGeometry.opposite_top N hsN H hIncN hCeilN hHighN with hf|hf
    · rw [hf,abs_of_nonneg (show 0≤(H:Int)+1 by omega)]
    · rw [hf,abs_neg,abs_of_nonneg (show 0≤(H:Int)+1 by omega)]
  let t := p.invFun k
  have ht : t=2 ∨ t=3 := by
    have ht0 : t≠0 := by
      intro he
      have hh : k=i := by simpa only [t,he,hp0] using (p.right_inv k).symm
      exact hki hh
    have ht1 : t≠1 := by
      intro he
      have hh : k=j := by simpa only [t,he,hp1] using (p.right_inv k).symm
      exact hkj hh
    omega
  obtain ⟨s,r,hs0,hs1,hs2,hf⟩ := FirstStrongEntry.positive_opposite_at_two N hsN t ht
  let q := p.trans s
  let C := signedFrame B q r
  have hq0 : q.toFun 0=i := by simp [q,Relabeling.trans,hs0,hp0]
  have hq1 : q.toFun 1=j := by simp [q,Relabeling.trans,hs1,hp1]
  have hq2 : q.toFun 2=k := by
    change p.toFun (s.toFun 2)=k
    rw [hs2]
    exact p.right_inv k
  have hCF : C 2 3=(H:Int)+1 := by
    change signedFrame N s r 2 3=(H:Int)+1
    exact hf.trans hTop
  have hsC := signedFrame_skew B hsB q r
  have hzC : C 0 1=0 := by
    cases hr : r <;> simp [C,signedFrame,relabel,reverse,hr,hq0,hq1,hz]
  have hLowC : HeightLe (mutate C 0) H := by
    rw [show C=signedFrame B q r from rfl,signedFrame_mutate,hq0,signedFrame_height]
    exact hLow
  have hNextC : HeightLe (mutate C 1) (H+1) := by
    rw [show C=signedFrame B q r from rfl,signedFrame_mutate,hq1,signedFrame_height]
    exact hNext
  have hkC : HeightLe (mutate C 2) (H+1) := by
    rw [show C=signedFrame B q r from rfl,signedFrame_mutate,hq2,signedFrame_height]
    exact hk
  have hIncC := ZeroOrbitGeometry.zero_incident_from_low C hsC 0 1 (by decide) hzC H hLowC
  let b := C 0 2
  let c := -C 0 3
  let d := C 1 2
  let E := C 1 3
  have hrep : C=ZeroFirstSwitch.peak b c d E ((H:Int)+1) := by
    simpa only [ZeroFirstSwitch.peak,b,c,d,E,neg_neg,hzC,hCF] using (ofSix_reconstruct C hsC).symm
  have hneg : correction (-b) (-c)<0 := by
    have hh := (hLowC 2 3).2
    rw [hrep] at hh
    change (H:Int)+1+correction (-b) (-c)≤(H:Int) at hh
    omega
  obtain ⟨hb,hc⟩ := correction_negative_inputs (-b) (-c) hneg
  have hmaC : MutationAcyclic C := (signedFrame_MA B hsB q r).mpr
    ((mutationAcyclic_word_iff Q.val lead).mpr hma)
  obtain ⟨o,ho⟩ := Foundation.ma_existence C hsC hmaC
  have hM := ScalarPathBudget.lead_totalProper_scalar_budget Q.val Q.property lead q r o ho
  have habsm := Int.le_natAbs (a:=orderMarkov C o)
  have hScalar : orderMarkov C o≤(H:Int) := by
    change (orderMarkov C o).natAbs≤scalarBudget Q.val at hM
    omega
  have hProper := totalProper_proper C o ho
  rw [hrep] at hIncC hNextC hkC hProper hScalar
  exact ZeroFirstSwitch.normalized_first_no_two b c d E H (by omega) (by omega)
    hIncC hNextC o hProper hScalar hkC

theorem sealed_alternating_prefix
    (Q : Rank4Input) (hma : MutationAcyclic Q.val) (lead : List (Fin 4))
    (i j : Fin 4) (hij : i≠j) (H : Nat) (hBudget : scalarBudget Q.val≤H)
    (hP : HeightLe (applyWord Q.val lead) (H+1))
    (hLow : HeightLe (mutate (applyWord Q.val lead) i) H)
    (hNext : HeightLe (mutate (applyWord Q.val lead) j) (H+1))
    (hHigh : ¬HeightLe (applyWord Q.val lead) H) (hz : applyWord Q.val lead i j=0)
    (n : Nat)
    (hCeil : ∀ r≤n, HeightLe
      (applyWord (applyWord Q.val lead) (alternatingWord i j r)) (H+1))
    (hAllHigh : ∀ r<n, ¬HeightLe
      (applyWord (applyWord Q.val lead) (alternatingWord i j r)) H) :
    n≤2 ∧ ∀ r<n, ∀ k : Fin 4, k≠i → k≠j →
      ¬HeightLe (mutate (applyWord (applyWord Q.val lead)
        (alternatingWord i j r)) k) (H+1) := by
  let P := applyWord Q.val lead
  change P i j=0 at hz
  have hsP := word_preserves_skew Q.val lead Q.property
  have hmaP := (mutationAcyclic_word_iff Q.val lead).mpr hma
  have hTwoLow (hn : 1<n) : HeightLe (mutate (mutate P j) i) H := by
    have hT := hAllHigh 1 hn
    have hNextAll := hCeil 1 (by omega)
    change ¬HeightLe (mutate P j) H at hT
    change HeightLe (mutate P j) (H+1) at hNextAll
    exact ZeroOrbitGeometry.actual_second_high_other_low Foundation.ma_existence
      EndpointFoundation.endpoint_bridge P hsP hmaP i j hij hz H hP hHigh hLow hNextAll hT
  have hLength : n≤2 := by
    by_contra hn
    have hh := hAllHigh 2 (by omega)
    change ¬HeightLe (mutate (mutate P j) i) H at hh
    exact hh (hTwoLow (by omega))
  refine ⟨hLength,?_⟩
  intro r hr k hki hkj
  have hCases : r=0 ∨ r=1 := by omega
  rcases hCases with rfl|rfl
  · exact actual_first_no_third Q hma lead i j hij H hBudget hP hLow hNext hHigh hz k hki hkj
  · have hLow' := hTwoLow hr
    have hHigh' := hAllHigh 1 hr
    change ¬HeightLe (mutate P j) H at hHigh'
    have hz' : mutate P j i j=0 := by simp [mutate,hz]
    have hBack : HeightLe (mutate (mutate P j) j) (H+1) := by rwa [mutation_involutive]
    have hlead : applyWord Q.val (lead++[j])=mutate P j := by
      simp only [applyWord_append,applyWord];rfl
    have hh := actual_first_no_third Q hma (lead++[j]) i j hij H hBudget
      (by rwa [hlead]) (by rwa [hlead]) (by rwa [hlead])
      (by rwa [hlead]) (by rwa [hlead]) k hki hkj
    rw [hlead] at hh
    exact hh

theorem zero_first_return_shape
    (Q : Rank4Input) (hma : MutationAcyclic Q.val) (lead : List (Fin 4))
    (i j : Fin 4) (hij : i≠j) (H : Nat) (hBudget : endpointHeightBudget Q≤H)
    (hP : HeightLe (applyWord Q.val lead) (H+1))
    (hLow : HeightLe (mutate (applyWord Q.val lead) i) H)
    (hNext : HeightLe (mutate (applyWord Q.val lead) j) (H+1))
    (hHigh : ¬HeightLe (applyWord Q.val lead) H) (hz : applyWord Q.val lead i j=0)
    (tail : List (Fin 4)) (hReduced : ∀ u k v,(j::tail)≠u++k::k::v)
    (hPath : PrefixHeightLe (applyWord Q.val lead) (j::tail) (H+1))
    (_hEnd : HeightLe (applyWord (applyWord Q.val lead) (j::tail)) H)
    (hFirst : ∀ u v,(j::tail)=u++v → v≠[] →
      ¬HeightLe (applyWord (applyWord Q.val lead) u) H) :
    tail=[] ∨ tail=[i] := by
  have hScalar : scalarBudget Q.val≤H := by unfold endpointHeightBudget at hBudget;omega
  let P := applyWord Q.val lead
  change P i j=0 at hz
  cases tail with
  | nil => exact Or.inl rfl
  | cons k rest =>
    have hT := hFirst [j] (k::rest) rfl (by simp)
    change ¬HeightLe (mutate P j) H at hT
    have hLow2 := ZeroOrbitGeometry.actual_second_high_other_low Foundation.ma_existence
      EndpointFoundation.endpoint_bridge P (word_preserves_skew Q.val lead Q.property)
      ((mutationAcyclic_word_iff Q.val lead).mpr hma) i j hij hz H hP hHigh hLow hNext hT
    have hBack : HeightLe (mutate (mutate P j) j) (H+1) := by rwa [mutation_involutive]
    have hzT : mutate P j i j=0 := by simp [mutate,hz]
    have hlead : applyWord Q.val (lead++[j])=mutate P j := by
      simp only [applyWord_append,applyWord];rfl
    have hkj : k≠j := by
      intro he
      subst k
      exact hReduced [] j rest rfl
    have hk : k=i := by
      by_contra hki
      have hn := actual_first_no_third Q hma (lead++[j]) i j hij H hScalar
        (by rwa [hlead]) (by rwa [hlead]) (by rwa [hlead])
        (by rwa [hlead]) (by rwa [hlead]) k hki hkj
      rw [hlead] at hn
      exact hn (hPath [j,k] rest rfl)
    subst k
    have hr : rest=[] := by
      by_contra hn
      have hh := hFirst [j,i] rest rfl hn
      exact hh hLow2
    subst rest
    exact Or.inr rfl

/-- Exact zero instance of the coordinator's weak-first-return interface.
Only the weak magnitude premise is replaced by the actual zero equality. -/
theorem zero_first_return_pair
    (Q : Rank4Input) (hma : MutationAcyclic Q.val) (lead : List (Fin 4))
    (i j : Fin 4) (hij : i≠j) (H : Nat) (hBudget : endpointHeightBudget Q≤H)
    (hP : HeightLe (applyWord Q.val lead) (H+1))
    (hLow : HeightLe (mutate (applyWord Q.val lead) i) H)
    (hNext : HeightLe (mutate (applyWord Q.val lead) j) (H+1))
    (hHigh : ¬HeightLe (applyWord Q.val lead) H) (hz : applyWord Q.val lead i j=0)
    (tail : List (Fin 4)) (hReduced : ∀ u k v,(j::tail)≠u++k::k::v)
    (hPath : PrefixHeightLe (applyWord Q.val lead) (j::tail) (H+1))
    (hEnd : HeightLe (applyWord (applyWord Q.val lead) (j::tail)) H)
    (hFirst : ∀ u v,(j::tail)=u++v → v≠[] →
      ¬HeightLe (applyWord (applyWord Q.val lead) u) H) :
    ∀ k∈(j::tail),k=i ∨ k=j := by
  rcases zero_first_return_shape Q hma lead i j hij H hBudget hP hLow hNext hHigh hz
    tail hReduced hPath hEnd hFirst with rfl|rfl
  · intro k hk
    exact Or.inr (by simpa using hk)
  · intro k hk
    have hm : k=j ∨ k=i := by simpa only [List.mem_cons,List.not_mem_nil,or_false] using hk
    exact hm.symm

#print axioms actual_first_no_third
#print axioms sealed_alternating_prefix
#print axioms zero_first_return_shape
#print axioms zero_first_return_pair
end Rank4Round2.ZeroSealedCorridor
