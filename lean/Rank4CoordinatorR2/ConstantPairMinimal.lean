import Rank4CoordinatorR2.PairWord
import Rank4CoordinatorR2.MinimalSuperscalar
import Rank4ReviewRound2.ZeroPairMinimal
import Rank4ReviewRound2.StrongPairEndpoint

/-! Every pair weight is covered for an actual constant-two-vertex
excursion in a legal profile minimum: zero and unit cases reroute, while
strong pairs stay below the bound. This narrows the global obstruction to
blocks using at least three pivot vertices; it does not exclude those blocks.
MA-to-total-proper existence is the only remaining foundation premise. -/
namespace Rank4CoordinatorR2.ConstantPairMinimal
open QuiverProofs Rank4Coordinator Rank4CoordinatorR2 Rank4Round2
open ProperObstructionSoundness Rank4ReviewRound2.StrongPairIncident

theorem constant_strong_prefixes (hExist : MAHasTotalProper4)
    (Q : Rank4Input) (hma : MutationAcyclic Q.val)
    (lead old : List (Fin 4)) (i j : Fin 4) (hij : i≠j) (H : Nat)
    (hBudget : scalarBudget Q.val≤H)
    (hStart : HeightLe (applyWord Q.val lead) H)
    (hCeil : PrefixHeightLe (applyWord Q.val lead) old (H+1))
    (hEnd : HeightLe (applyWord (applyWord Q.val lead) old) H)
    (hPair : 2≤abs (applyWord Q.val lead i j))
    (hp : ∀ k∈old,k=i ∨ k=j) (hnr : ∀ u k v,old≠u++k::k::v) :
    PrefixHeightLe (applyWord Q.val lead) old H := by
  have go (a b : Fin 4) (hab : a≠b)
      (hPair' : 2≤abs (applyWord Q.val lead a b))
      (he : old=alternatingWord a b old.length) :
      PrefixHeightLe (applyWord Q.val lead) old H := by
    have hAll : ∀ k≤old.length, HeightLe
        (applyWord (applyWord Q.val lead) (alternatingWord a b k)) (H+1) := by
      intro k hk
      obtain ⟨tail,ht⟩ := PairWord.alternating_prefix_decomposition a b old.length k hk
      exact hCeil (alternatingWord a b k) tail (he.trans ht)
    have hEnd' : HeightLe
        (applyWord (applyWord Q.val lead) (alternatingWord a b old.length)) H := by
      rwa [←he]
    have hh := Rank4ReviewRound2.StrongPairEndpoint.bounded_alternating_prefixes
      hExist old.length Q hma lead a b hab H hBudget hStart hAll hEnd' hPair'
    rwa [←he] at hh
  rcases PairWord.pair_word_is_alternating old i j hij hp hnr with he|he
  · exact go i j hij hPair he
  · have hs := word_preserves_skew Q.val lead Q.property
    have hPair' : 2≤abs (applyWord Q.val lead j i) := by
      rw [hs j i,abs_neg]
      exact hPair
    exact go j i (Ne.symm hij) hPair' he

theorem constant_pair_has_zero_overCount
    (hExist : MAHasTotalProper4) (Q : Rank4Input) (M : Nat) (w : List (Fin 4))
    (ha : Acyclic (applyWord Q.val w)) (hh : PrefixHeightLe Q.val w M)
    (hcount : ∀ v, Acyclic (applyWord Q.val v) → PrefixHeightLe Q.val v M →
      overCount Q.val w (M-1)≤overCount Q.val v (M-1))
    (hlength : ∀ v, Acyclic (applyWord Q.val v) → PrefixHeightLe Q.val v M →
      overCount Q.val v (M-1)=overCount Q.val w (M-1) → w.length≤v.length)
    (hBudget : endpointHeightBudget Q≤M-1)
    (lead old tail : List (Fin 4)) (i j : Fin 4) (hij : i≠j)
    (hw : w=lead++(old++tail)) (hp : ∀ k∈old,k=i ∨ k=j)
    (hLeft : HeightLe (applyWord Q.val lead) (M-1))
    (hRight : HeightLe (applyWord Q.val (lead++old)) (M-1)) :
    overCount (applyWord Q.val lead) old (M-1)=0 := by
  by_cases hz : applyWord Q.val lead i j=0
  · exact Rank4ReviewRound2.ZeroPairMinimal.no_constant_zero_excursion
      hExist EndpointFoundation.endpoint_bridge Q M w ha hh hcount hBudget
      lead old tail i j hij hw hz hp hLeft hRight
  by_cases hu : abs (applyWord Q.val lead i j)=1
  · by_contra hn
    have hpos : 0<overCount (applyWord Q.val lead) old (M-1) := by omega
    exact MinimalSuperscalar.no_constant_unit_excursion hExist EndpointFoundation.endpoint_bridge
      Q M w ha hh hcount lead old tail i j hij hw hu hp hLeft hRight hpos
  · have habs : 0<abs (applyWord Q.val lead i j) := abs_pos.mpr hz
    have hPair : 2≤abs (applyWord Q.val lead i j) := by omega
    have hnr := profile_minimal_no_backtrack Q.val M w ha hh hcount hlength
    have hnrOld := PairWord.embedded_no_backtrack w lead old tail hw hnr
    have hh' := hh
    rw [hw] at hh'
    obtain ⟨_,hSuffix⟩ := (Rank4Round2.prefixHeight_append_iff Q.val lead (old++tail) M).mp hh'
    have hOld := ((Rank4Round2.prefixHeight_append_iff (applyWord Q.val lead) old tail M).mp hSuffix).1
    have hCeil : PrefixHeightLe (applyWord Q.val lead) old ((M-1)+1) :=
      Rank4Round2.prefixHeight_mono _ old M _ (by omega) hOld
    have hEnd : HeightLe (applyWord (applyWord Q.val lead) old) (M-1) := by
      rwa [applyWord_append] at hRight
    have hScalar : scalarBudget Q.val≤M-1 := by
      unfold endpointHeightBudget at hBudget
      omega
    have hBound := constant_strong_prefixes hExist Q ⟨w,ha⟩ lead old i j hij
      (M-1) hScalar hLeft hCeil hEnd hPair hp hnrOld
    exact overCount_eq_zero _ old (M-1) hBound

theorem third_pivot_in_high_excursion
    (hExist : MAHasTotalProper4) (Q : Rank4Input) (M : Nat) (w : List (Fin 4))
    (ha : Acyclic (applyWord Q.val w)) (hh : PrefixHeightLe Q.val w M)
    (hcount : ∀ v, Acyclic (applyWord Q.val v) → PrefixHeightLe Q.val v M →
      overCount Q.val w (M-1)≤overCount Q.val v (M-1))
    (hlength : ∀ v, Acyclic (applyWord Q.val v) → PrefixHeightLe Q.val v M →
      overCount Q.val v (M-1)=overCount Q.val w (M-1) → w.length≤v.length)
    (hBudget : endpointHeightBudget Q≤M-1)
    (lead old tail : List (Fin 4)) (i j : Fin 4) (hij : i≠j)
    (hw : w=lead++(old++tail))
    (hLeft : HeightLe (applyWord Q.val lead) (M-1))
    (hRight : HeightLe (applyWord Q.val (lead++old)) (M-1))
    (hover : 0<overCount (applyWord Q.val lead) old (M-1)) :
    ∃ k∈old,k≠i ∧ k≠j := by
  classical
  by_contra! hn
  have hp : ∀ k∈old,k=i ∨ k=j := by
    intro k hk
    by_cases hi : k=i
    · exact Or.inl hi
    · exact Or.inr (hn k hk hi)
  have hz := constant_pair_has_zero_overCount hExist Q M w ha hh hcount hlength hBudget
    lead old tail i j hij hw hp hLeft hRight
  omega

#print axioms constant_strong_prefixes
#print axioms constant_pair_has_zero_overCount
#print axioms third_pivot_in_high_excursion
end Rank4CoordinatorR2.ConstantPairMinimal
