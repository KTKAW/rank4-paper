import Rank4CoordinatorR2.StrongForward

/-! Actual-word decomposition and the unconditional weak-first-pair
consequence. No hypothetical return/switch certificate or new path bound
is introduced by these bookkeeping lemmas. -/
namespace Rank4CoordinatorR2.HighExcursion
open QuiverProofs Rank4Coordinator Rank4CoordinatorR2 Rank4Round2

/-- A bounded start and an unbounded reached prefix have an actual first
one-step crossing. The statement does not select an endpoint or cap length. -/
theorem first_crossing (B : Matrix 4) (w : List (Fin 4)) (H : Nat)
    (hStart : HeightLe B H) (hOut : ¬PrefixHeightLe B w H) :
    ∃ lead i tail, w=lead++i::tail ∧ HeightLe (applyWord B lead) H ∧
      ¬HeightLe (mutate (applyWord B lead) i) H := by
  induction w generalizing B with
  | nil => exact False.elim (hOut ((prefixHeight_nil B H).mpr hStart))
  | cons k w ih =>
    by_cases hk : HeightLe (mutate B k) H
    · have hw : ¬PrefixHeightLe (mutate B k) w H := by
        intro h
        exact hOut ((prefixHeight_cons B k w H).mpr ⟨hStart,h⟩)
      obtain ⟨lead,i,tail,he,hL,hP⟩ := ih (mutate B k) hk hw
      exact ⟨k::lead,i,tail,congrArg (List.cons k) he,hL,hP⟩
    · exact ⟨[],k,w,rfl,hStart,hk⟩

/-- The high part is stopped at its first actual return below H. -/
theorem first_return (B : Matrix 4) (w : List (Fin 4)) (H : Nat)
    (hHigh : ¬HeightLe B H) (hEnd : HeightLe (applyWord B w) H) :
    ∃ old tail, w=old++tail ∧ old≠[] ∧ HeightLe (applyWord B old) H ∧
      (∀ u v,old=u++v → v≠[] → ¬HeightLe (applyWord B u) H) := by
  induction w generalizing B with
  | nil => exact False.elim (hHigh hEnd)
  | cons k w ih =>
    by_cases hk : HeightLe (mutate B k) H
    · refine ⟨[k],w,rfl,by simp,hk,?_⟩
      intro u v he hv
      cases u with
      | nil => exact hHigh
      | cons l u =>
        have ht : []=u++v := (List.cons.inj he).2
        have hv0 : v=[] := (List.append_eq_nil_iff.mp ht.symm).2
        exact False.elim (hv hv0)
    · obtain ⟨old,tail,he,hne,hL,hPrefix⟩ := ih (mutate B k) hk hEnd
      refine ⟨k::old,tail,congrArg (List.cons k) he,by simp,hL,?_⟩
      intro u v huv hv
      cases u with
      | nil => exact hHigh
      | cons l u =>
        have hl : k=l := (List.cons.inj huv).1
        subst l
        have ht : old=u++v := (List.cons.inj huv).2
        exact hPrefix u v ht hv

/-- If an actual reduced acyclicizing word crosses above the original
budget, its first two pivot labels cannot form a strong pair. -/
theorem first_pair_is_weak
    (Q : Rank4Input) (H : Nat) (w lead tail : List (Fin 4))
    (i j : Fin 4) (hij : i≠j) (hw : w=lead++i::j::tail)
    (ha : Acyclic (applyWord Q.val w)) (hCeil : PrefixHeightLe Q.val w (H+1))
    (hnr : ∀ u k v,w≠u++k::k::v)
    (hBudget : endpointHeightBudget Q≤H)
    (hLeft : HeightLe (applyWord Q.val lead) H)
    (hHigh : ¬HeightLe (mutate (applyWord Q.val lead) i) H) :
    abs (mutate (applyWord Q.val lead) i i j)≤1 := by
  by_contra hn
  have hPair : 2≤abs (mutate (applyWord Q.val lead) i i j) := by omega
  let pre := lead++[i]
  have hw' : w=pre++(j::tail) := by simpa only [pre,List.append_assoc] using hw
  have he : applyWord Q.val pre=mutate (applyWord Q.val lead) i := by
    simp only [pre,applyWord_append,applyWord]
  have hsuf := ((Rank4Round2.prefixHeight_append_iff Q.val pre (j::tail) (H+1)).mp
    (by rwa [←hw'])).2
  have hP : HeightLe (applyWord Q.val pre) (H+1) := hsuf [] (j::tail) rfl
  have hj : HeightLe (mutate (applyWord Q.val pre) j) (H+1) := hsuf [j] tail rfl
  have hi : HeightLe (mutate (applyWord Q.val pre) i) H := by
    rw [he,mutation_involutive]
    exact hLeft
  have hR : HeightLe (applyWord (applyWord Q.val pre) (j::tail)) H := by
    have hend := Foundation.acyclic_endpoint_budget Q w ha
    rw [hw',applyWord_append] at hend
    exact heightLe_mono _ _ H hBudget hend
  have hnrSuf : ∀ u k v,(j::tail)≠u++k::k::v :=
    PairWord.embedded_no_backtrack w pre (j::tail) [] (by simpa using hw') hnr
  have hScalar : scalarBudget Q.val≤H := by unfold endpointHeightBudget at hBudget;omega
  apply StrongForward.actual_strong_forward_no_return Q ⟨w,ha⟩ pre i j hij H
    hScalar hP hi hj (by rwa [he]) (by rwa [he]) tail hnrSuf hsuf hR

#print axioms first_crossing
#print axioms first_return
#print axioms first_pair_is_weak
end Rank4CoordinatorR2.HighExcursion
