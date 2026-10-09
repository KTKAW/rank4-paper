import Rank4Round2.ZeroInitialBudget
import Rank4Round2.WordBounds

/-! Constant zero-pair excursions have four actual labeled states. Above
the original input budget, bounded endpoints admit a bounded route of length
at most two with exactly the same endpoint. This does not decompose blocks
that switch pivot pairs.
-/
namespace Rank4ReviewRound2.ZeroPairBlock
open QuiverProofs Rank4Coordinator Rank4Round2 Rank4CoordinatorR2
open ProperObstructionSoundness

def node (B : Matrix 4) (i j : Fin 4) (r s : Bool) : Matrix 4 :=
  if s then mutate (if r then mutate B i else B) j
    else if r then mutate B i else B

theorem transition (B : Matrix 4) (hs : SkewSymmetric B) (i j : Fin 4) (hij : i≠j) (hz : B i j=0)
    (r s k : Bool) :
    mutate (node B i j r s) (if k then j else i)=
      if k then node B i j r (!s) else node B i j (!r) s := by
  have hc := mutate_zero_commute_at B hs i j hij hz
  cases r <;> cases s <;> cases k <;>
    simp [node,mutation_involutive]
  all_goals simp only [hc,mutation_involutive]

theorem orbit_word (B : Matrix 4) (hs : SkewSymmetric B) (i j : Fin 4) (hij : i≠j) (hz : B i j=0)
    (w : List (Fin 4)) (hp : ∀ k∈w,k=i ∨ k=j) :
    ∃ r s, applyWord B w=node B i j r s := by
  have hall : ∀ (w : List (Fin 4)) (r s : Bool),
      (∀ k∈w,k=i ∨ k=j) → ∃ u v, applyWord (node B i j r s) w=node B i j u v := by
    intro w
    induction w with
    | nil => intro r s _; exact ⟨r,s,rfl⟩
    | cons k w ih =>
      intro r s h
      have hk := h k (by simp)
      have ht : ∀ l∈w,l=i ∨ l=j := fun l hl => h l (by simp [hl])
      rcases hk with hk|hk
      · subst k
        have he := transition B hs i j hij hz r s false
        change mutate (node B i j r s) i=node B i j (!r) s at he
        change ∃ u v, applyWord (mutate (node B i j r s) i) w=node B i j u v
        rw [he]
        exact ih _ _ ht
      · subst k
        have he := transition B hs i j hij hz r s true
        change mutate (node B i j r s) j=node B i j r (!s) at he
        change ∃ u v, applyWord (mutate (node B i j r s) j) w=node B i j u v
        rw [he]
        exact ih _ _ ht
  exact hall w false false hp

theorem bounded_route
    (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4)
    (Q : Rank4Input) (lead : List (Fin 4)) (i j : Fin 4) (hij : i≠j)
    (hma : MutationAcyclic (applyWord Q.val lead)) (H : Nat)
    (hBudget : endpointHeightBudget Q≤H)
    (hB : HeightLe (applyWord Q.val lead) H)
    (hz : applyWord Q.val lead i j=0)
    (old : List (Fin 4)) (hp : ∀ k∈old,k=i ∨ k=j)
    (hend : HeightLe (applyWord (applyWord Q.val lead) old) H) :
    ∃ new : List (Fin 4), new.length≤2 ∧
      PrefixHeightLe (applyWord Q.val lead) new H ∧
      applyWord (applyWord Q.val lead) new=applyWord (applyWord Q.val lead) old := by
  let B := applyWord Q.val lead
  have hsB : SkewSymmetric B := word_preserves_skew Q.val lead Q.property
  obtain ⟨r,s,he⟩ := orbit_word B hsB i j hij hz old hp
  change HeightLe (applyWord B old) H at hend
  rw [he] at hend
  cases r <;> cases s
  · exact ⟨[],by decide,(prefixHeight_nil B H).mpr hB,he.symm⟩
  · refine ⟨[j],by simp,?_,he.symm⟩
    exact (prefixHeight_cons B j [] H).mpr ⟨hB,(prefixHeight_nil _ H).mpr hend⟩
  · refine ⟨[i],by simp,?_,he.symm⟩
    exact (prefixHeight_cons B i [] H).mpr ⟨hB,(prefixHeight_nil _ H).mpr hend⟩
  · by_cases h0 : HeightLe (mutate B i) H
    · refine ⟨[i,j],by simp,?_,he.symm⟩
      simp only [prefixHeight_cons,prefixHeight_nil]
      exact ⟨hB,h0,hend⟩
    · have hsP := mutation_preserves_skew B i hsB
      have hmaP := (mutationAcyclic_iff B i).mpr hma
      have hL : HeightLe (mutate (mutate B i) i) H := by
        rwa [mutation_involutive]
      have hzP : mutate B i i j=0 := by
        have hzB : B i j=0 := hz
        simp [mutate,hzB]
      have hprefix : applyWord Q.val (lead++[i])=mutate B i := by
        simp only [applyWord_append,applyWord]; rfl
      have hscalar := ZeroInitialBudget.normalized_zero_scalar_le_input hExist
        Q.val Q.property (lead++[i]) i j hij H
        (by rwa [hprefix]) (by rwa [hprefix]) (by rwa [hprefix])
        (by rwa [hprefix]) (by rwa [hprefix])
      rw [hprefix] at hscalar
      have hM : ZeroUniformGuard.normalizedScalar (mutate B i) i j≤(H:Int) := by
        unfold endpointHeightBudget at hBudget
        omega
      have hn := ZeroUniformGuard.arbitrary_zero_strict_guard hExist hEnd
        (mutate B i) hsP hmaP i j hij H hL hend h0 hzP hM
      rw [mutation_involutive] at hn
      refine ⟨[j,i],by simp,hn,?_⟩
      rw [he]
      change mutate (mutate B j) i=mutate (mutate B i) j
      exact (mutate_zero_commute_at B hsB i j hij hz).symm

theorem witness_progress
    (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4)
    (Q : Rank4Input) (lead old tail : List (Fin 4)) (i j : Fin 4) (hij : i≠j) (H K : Nat)
    (hBudget : endpointHeightBudget Q≤H) (hHK : H≤K)
    (hB : HeightLe (applyWord Q.val lead) H)
    (hz : applyWord Q.val lead i j=0)
    (hp : ∀ k∈old,k=i ∨ k=j)
    (hend : HeightLe (applyWord (applyWord Q.val lead) old) H)
    (hPath : PrefixHeightLe Q.val (lead++(old++tail)) K)
    (ha : Acyclic (applyWord Q.val (lead++(old++tail)))) :
    ∃ new : List (Fin 4), new.length≤2 ∧
      PrefixHeightLe Q.val (lead++(new++tail)) K ∧
      Acyclic (applyWord Q.val (lead++(new++tail))) ∧
      overCount Q.val (lead++(new++tail)) H+
        overCount (applyWord Q.val lead) old H=
          overCount Q.val (lead++(old++tail)) H := by
  have hma : MutationAcyclic (applyWord Q.val lead) := by
    refine ⟨old++tail,?_⟩
    rwa [applyWord_append] at ha
  obtain ⟨new,hlen,hpre,he⟩ := bounded_route hExist hEnd Q lead i j hij hma H
    hBudget hB hz old hp hend
  obtain ⟨hLead,hSuffix⟩ := (prefixHeight_append_iff Q.val lead (old++tail) K).mp hPath
  have ht := ((prefixHeight_append_iff (applyWord Q.val lead) old tail K).mp hSuffix).2
  refine ⟨new,hlen,?_,?_,?_⟩
  · apply prefixHeight_append Q.val lead _ K hLead
    apply prefixHeight_append _ new tail K (prefixHeight_mono _ _ H K hHK hpre)
    rwa [he]
  · rw [applyWord_append,applyWord_append,he,←applyWord_append,←applyWord_append]
    exact ha
  · rw [overCount_append Q.val lead,overCount_append Q.val lead,
      overCount_append,overCount_append,he,overCount_eq_zero _ new H hpre]
    omega

#print axioms transition
#print axioms bounded_route
#print axioms witness_progress
end Rank4ReviewRound2.ZeroPairBlock
