import Rank4ReviewRound2.StrongPairIncident

/-! Finite word bookkeeping for the constant-pair consumer. No matrix
semantics, classical decision, or coverage premise is introduced. -/
namespace Rank4CoordinatorR2.PairWord
open QuiverProofs Rank4ReviewRound2.StrongPairIncident

theorem alternating_prefix_decomposition (i j : Fin 4) (n k : Nat) (hk : k≤n) :
    ∃ tail, alternatingWord i j n=alternatingWord i j k++tail := by
  induction k generalizing n i j with
  | zero => exact ⟨alternatingWord i j n,rfl⟩
  | succ k ih =>
    cases n with
    | zero => omega
    | succ n =>
      obtain ⟨tail,he⟩ := ih j i n (by omega)
      exact ⟨tail,congrArg (List.cons j) he⟩

theorem headed_pair_word_alternating (w : List (Fin 4)) (i j : Fin 4) (hij : i≠j)
    (hp : ∀ k∈w,k=i ∨ k=j)
    (hnr : ∀ u k v,w≠u++k::k::v)
    (hfirst : ∀ k tail,w=k::tail → k=j) :
    w=alternatingWord i j w.length := by
  induction w generalizing i j with
  | nil => rfl
  | cons k w ih =>
    have hk := hfirst k w rfl
    subst k
    have ht : ∀ k∈w,k=j ∨ k=i := fun k hk => (hp k (by simp [hk])).symm
    have hnr' : ∀ u k v,w≠u++k::k::v := by
      intro u k v he
      apply hnr (j::u) k v
      simpa only [List.cons_append] using congrArg (List.cons j) he
    have hfirst' : ∀ k tail,w=k::tail → k=i := by
      intro k tail he
      have h := hp k (by simp [he])
      rcases h with h|h
      · exact h
      · subst k
        exact False.elim (hnr [] j tail (by simp only [List.nil_append,he]))
    have he := ih j i (Ne.symm hij) ht hnr' hfirst'
    exact congrArg (List.cons j) he

theorem pair_word_is_alternating (w : List (Fin 4)) (i j : Fin 4) (hij : i≠j)
    (hp : ∀ k∈w,k=i ∨ k=j) (hnr : ∀ u k v,w≠u++k::k::v) :
    w=alternatingWord i j w.length ∨ w=alternatingWord j i w.length := by
  cases w with
  | nil => exact Or.inl rfl
  | cons k w =>
    have hk := hp k (by simp)
    rcases hk with hk|hk
    · subst k
      apply Or.inr
      exact headed_pair_word_alternating (i::w) j i (Ne.symm hij)
        (fun k hk => (hp k hk).symm) hnr
        (fun k tail he => (List.cons.inj he).1.symm)
    · subst k
      apply Or.inl
      exact headed_pair_word_alternating (j::w) i j hij hp hnr
        (fun k tail he => (List.cons.inj he).1.symm)

theorem embedded_no_backtrack (w lead old tail : List (Fin 4))
    (hw : w=lead++(old++tail)) (hnr : ∀ u k v,w≠u++k::k::v) :
    ∀ u k v,old≠u++k::k::v := by
  intro u k v he
  apply hnr (lead++u) k (v++tail)
  rw [hw,he]
  simp only [List.append_assoc,List.cons_append]

#print axioms pair_word_is_alternating
#print axioms embedded_no_backtrack
end Rank4CoordinatorR2.PairWord
