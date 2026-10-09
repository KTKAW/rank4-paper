import Rank4CoordinatorR2.HighExcursion
import Rank4Round2.ZeroSealedCorridor

/-! Unconditional reduction of a failure of bounded MA reachability to an
actual unit excursion in a legal height/count/length minimum. All zero and
strong first pairs are discharged. The final lowering supplier is explicit
and remains open; this file does not assert all-input height coverage. -/
namespace Rank4CoordinatorR2.ResidualUnitExcursion
open QuiverProofs Rank4Coordinator Rank4CoordinatorR2 Rank4Round2

structure Packet (Q : Rank4Input) (H : Nat) (w lead : List (Fin 4))
    (i j : Fin 4) (mid tail : List (Fin 4)) : Prop where
  budget : endpointHeightBudget Q≤H
  acyclic : Acyclic (applyWord Q.val w)
  ceiling : PrefixHeightLe Q.val w (H+1)
  countMinimum : ∀ v,Acyclic (applyWord Q.val v) → PrefixHeightLe Q.val v (H+1) →
    overCount Q.val w H≤overCount Q.val v H
  lengthMinimum : ∀ v,Acyclic (applyWord Q.val v) → PrefixHeightLe Q.val v (H+1) →
    overCount Q.val v H=overCount Q.val w H → w.length≤v.length
  reduced : ∀ u k v,w≠u++k::k::v
  split : w=lead++((i::j::mid)++tail)
  distinct : i≠j
  lowLeft : HeightLe (applyWord Q.val lead) H
  highFirst : ¬HeightLe (mutate (applyWord Q.val lead) i) H
  unit : abs (mutate (applyWord Q.val lead) i i j)=1
  lowReturn : HeightLe (applyWord (mutate (applyWord Q.val lead) i) (j::mid)) H
  properHigh : ∀ u v,(j::mid)=u++v → v≠[] →
    ¬HeightLe (applyWord (mutate (applyWord Q.val lead) i) u) H
  thirdPivot : ∃ k∈(i::j::mid),k≠i ∧ k≠j

theorem exists_packet_of_no_bounded_witness (Q : Rank4Input)
    (hma : MutationAcyclic Q.val)
    (hNo : ¬∃ v,Acyclic (applyWord Q.val v) ∧
      PrefixHeightLe Q.val v (endpointHeightBudget Q)) :
    ∃ H w lead i j mid tail,Packet Q H w lead i j mid tail := by
  obtain ⟨M,w,ha,hh,hHeightMin,hCountMin,hLengthMin⟩ :=
    exists_profile_minimal_witness Q.val Q.property hma
  have hM : endpointHeightBudget Q<M := by
    by_contra hn
    exact hNo ⟨w,ha,prefixHeight_mono _ w M _ (by omega) hh⟩
  let H := M-1
  have hBudget : endpointHeightBudget Q≤H := by dsimp [H];omega
  have hMH : M=H+1 := by dsimp [H];omega
  have hCeil : PrefixHeightLe Q.val w (H+1) := by rwa [←hMH]
  have hCount : ∀ v,Acyclic (applyWord Q.val v) → PrefixHeightLe Q.val v (H+1) →
      overCount Q.val w H≤overCount Q.val v H := by
    intro v hav hv
    exact hCountMin v hav (by rwa [hMH])
  have hLength : ∀ v,Acyclic (applyWord Q.val v) → PrefixHeightLe Q.val v (H+1) →
      overCount Q.val v H=overCount Q.val w H → w.length≤v.length := by
    intro v hav hv hc
    exact hLengthMin v hav (by rwa [hMH]) hc
  have hStart : HeightLe Q.val H :=
    heightLe_mono _ _ H hBudget (initial_height_budget Q)
  have hEnd : HeightLe (applyWord Q.val w) H :=
    heightLe_mono _ _ H hBudget (Foundation.acyclic_endpoint_budget Q w ha)
  have hOut : ¬PrefixHeightLe Q.val w H := by
    intro h
    have hm := hHeightMin H w ha h
    dsimp [H] at hm
    omega
  obtain ⟨lead,i,rest,hw,hLeft,hHigh⟩ := HighExcursion.first_crossing Q.val w H hStart hOut
  have hEndRest : HeightLe (applyWord (mutate (applyWord Q.val lead) i) rest) H := by
    rwa [hw,applyWord_append] at hEnd
  obtain ⟨old,tail,hRest,hOldNe,hOldEnd,hProper⟩ :=
    HighExcursion.first_return (mutate (applyWord Q.val lead) i) rest H hHigh hEndRest
  cases old with
  | nil => exact False.elim (hOldNe rfl)
  | cons j mid =>
    have hwAll : w=lead++i::j::(mid++tail) := by rw [hw,hRest];rfl
    have hnr := profile_minimal_no_backtrack Q.val M w ha hh hCountMin hLengthMin
    have hij : i≠j := by
      intro he
      subst j
      exact hnr lead i (mid++tail) hwAll
    have hWeak := HighExcursion.first_pair_is_weak Q H w lead (mid++tail) i j hij
      hwAll ha hCeil hnr hBudget hLeft hHigh
    let pre := lead++[i]
    have he : applyWord Q.val pre=mutate (applyWord Q.val lead) i := by
      simp only [pre,applyWord_append,applyWord]
    have hwSplit : w=pre++((j::mid)++tail) := by
      simpa only [pre,List.append_assoc] using hwAll
    have hSuffix := ((Rank4Round2.prefixHeight_append_iff Q.val pre ((j::mid)++tail) (H+1)).mp
      (by rwa [←hwSplit])).2
    have hOldCeil := ((Rank4Round2.prefixHeight_append_iff (applyWord Q.val pre)
      (j::mid) tail (H+1)).mp hSuffix).1
    have hP := hOldCeil [] (j::mid) rfl
    have hi : HeightLe (mutate (applyWord Q.val pre) i) H := by
      rw [he,mutation_involutive];exact hLeft
    have hj := hOldCeil [j] mid rfl
    have hnrOld := PairWord.embedded_no_backtrack w pre (j::mid) tail hwSplit hnr
    have hOldH : HeightLe (applyWord (applyWord Q.val pre) (j::mid)) H := by rwa [he]
    have hProper' : ∀ u v,(j::mid)=u++v → v≠[] →
        ¬HeightLe (applyWord (applyWord Q.val pre) u) H := by rwa [he]
    have hParent : ¬HeightLe (applyWord Q.val pre) H := by rwa [he]
    have hUnit : abs (mutate (applyWord Q.val lead) i i j)=1 := by
      by_contra hn
      have hz : applyWord Q.val pre i j=0 := by
        rw [he];have hnon := abs_nonneg (mutate (applyWord Q.val lead) i i j)
        have habs : abs (mutate (applyWord Q.val lead) i i j)=0 := by omega
        exact abs_eq_zero.mp habs
      have hp := ZeroSealedCorridor.zero_first_return_pair Q hma pre i j hij H hBudget
        hP hi hj hParent hz mid hnrOld hOldCeil hOldH hProper'
      have hpAll : ∀ k∈(i::j::mid),k=i ∨ k=j := by
        intro k hk
        rcases List.mem_cons.mp hk with hk|hk
        · exact Or.inl hk
        · exact hp k hk
      have hwBlock : w=lead++((i::j::mid)++tail) := hwAll
      have hBlockEnd : HeightLe (applyWord Q.val (lead++(i::j::mid))) H := by
        rwa [applyWord_append]
      have hzCount := Foundation.constant_pair_has_zero_overCount Q M w ha hh hCountMin
        hLengthMin hBudget lead (i::j::mid) tail i j hij hwBlock hpAll hLeft hBlockEnd
      change overCount (applyWord Q.val lead) (i::j::mid) H=0 at hzCount
      simp only [overCount,overBit,if_neg hHigh] at hzCount
      omega
    have hwBlock : w=lead++((i::j::mid)++tail) := hwAll
    have hBlockEnd : HeightLe (applyWord Q.val (lead++(i::j::mid))) H := by
      rwa [applyWord_append]
    have hover : 0<overCount (applyWord Q.val lead) (i::j::mid) H := by
      simp only [overCount,overBit,if_neg hHigh];omega
    have hThird := Foundation.third_pivot_in_high_excursion Q M w ha hh hCountMin
      hLengthMin hBudget lead (i::j::mid) tail i j hij hwBlock hLeft hBlockEnd hover
    exact ⟨H,w,lead,i,j,mid,tail,hBudget,ha,hCeil,hCount,hLength,hnr,
      hwBlock,hij,hLeft,hHigh,hUnit,hOldEnd,hProper,hThird⟩

/-- The exact local progress obligation still needed on the live route.
The data are actual words and strict count reduction, not membership in an
unproved certificate language. This proposition is not assumed globally. -/
def UnitProfileLowering4 : Prop :=
  ∀ (Q : Rank4Input) (H : Nat) (w lead : List (Fin 4)) (i j : Fin 4)
    (mid tail : List (Fin 4)),Packet Q H w lead i j mid tail →
    ∃ v,Acyclic (applyWord Q.val v) ∧ PrefixHeightLe Q.val v (H+1) ∧
      overCount Q.val v H<overCount Q.val w H

theorem bounded_witness_of_unit_profile_lowering (hLower : UnitProfileLowering4)
    (Q : Rank4Input) (hma : MutationAcyclic Q.val) :
    ∃ v,Acyclic (applyWord Q.val v) ∧ PrefixHeightLe Q.val v (endpointHeightBudget Q) := by
  by_contra hn
  obtain ⟨H,w,lead,i,j,mid,tail,h⟩ := exists_packet_of_no_bounded_witness Q hma hn
  obtain ⟨v,hav,hv,hc⟩ := hLower Q H w lead i j mid tail h
  have hm := h.countMinimum v hav hv
  omega

#print axioms exists_packet_of_no_bounded_witness
#print axioms bounded_witness_of_unit_profile_lowering
end Rank4CoordinatorR2.ResidualUnitExcursion
