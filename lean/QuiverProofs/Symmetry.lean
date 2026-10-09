import QuiverProofs.Mutation

namespace QuiverProofs

/-- A vertex permutation in new-to-old convention, with both inverse laws. -/
structure Relabeling (n : Nat) where
  toFun : Fin n → Fin n
  invFun : Fin n → Fin n
  left_inv : ∀ i, invFun (toFun i) = i
  right_inv : ∀ i, toFun (invFun i) = i

def Relabeling.symm {n : Nat} (p : Relabeling n) : Relabeling n :=
  ⟨p.invFun, p.toFun, p.right_inv, p.left_inv⟩

def Relabeling.identity (n : Nat) : Relabeling n :=
  ⟨id, id, fun _ => rfl, fun _ => rfl⟩

def Relabeling.trans {n : Nat} (p q : Relabeling n) : Relabeling n :=
  ⟨p.toFun ∘ q.toFun, q.invFun ∘ p.invFun,
   by intro i; simp [p.left_inv, q.left_inv],
   by intro i; simp [p.right_inv, q.right_inv]⟩

theorem Relabeling.injective {n : Nat} (p : Relabeling n) {i j : Fin n}
    (h : p.toFun i = p.toFun j) : i = j := by
  have := congrArg p.invFun h
  simpa only [p.left_inv] using this

def relabel {n : Nat} (B : Matrix n) (p : Relabeling n) : Matrix n :=
  fun i j => B (p.toFun i) (p.toFun j)

theorem relabel_identity {n : Nat} (B : Matrix n) : relabel B (.identity n) = B := rfl

theorem relabel_trans {n : Nat} (B : Matrix n) (p q : Relabeling n) :
    relabel (relabel B p) q = relabel B (p.trans q) := rfl

theorem relabel_inverse {n : Nat} (B : Matrix n) (p : Relabeling n) :
    relabel (relabel B p) p.symm = B := by
  funext i j
  simp [relabel, Relabeling.symm, p.right_inv]

theorem mutate_relabel {n : Nat} (B : Matrix n) (p : Relabeling n) (k : Fin n) :
    mutate (relabel B p) k = relabel (mutate B (p.toFun k)) p := by
  funext i j
  have hi : p.toFun i = p.toFun k ↔ i = k := ⟨p.injective, congrArg p.toFun⟩
  have hj : p.toFun j = p.toFun k ↔ j = k := ⟨p.injective, congrArg p.toFun⟩
  simp only [mutate, relabel, hi, hj]

theorem word_relabel {n : Nat} (B : Matrix n) (p : Relabeling n)
    (word : List (Fin n)) :
    applyWord (relabel B p) word = relabel (applyWord B (word.map p.toFun)) p := by
  induction word generalizing B with
  | nil => rfl
  | cons k ks ih => simpa only [applyWord, List.map_cons, mutate_relabel] using ih (mutate B (p.toFun k))

theorem acyclic_relabel_iff {n : Nat} (B : Matrix n) (p : Relabeling n) :
    Acyclic (relabel B p) ↔ Acyclic B := by
  constructor
  · rintro ⟨rank, hr⟩
    refine ⟨rank ∘ p.invFun, ?_⟩
    intro i j hij
    have h : 0 < relabel B p (p.invFun i) (p.invFun j) := by
      simpa only [relabel, p.right_inv] using hij
    exact hr _ _ h
  · rintro ⟨rank, hr⟩
    exact ⟨rank ∘ p.toFun, fun i j h => hr _ _ h⟩

theorem MA_relabel_iff {n : Nat} (B : Matrix n) (p : Relabeling n) :
    MutationAcyclic (relabel B p) ↔ MutationAcyclic B := by
  constructor
  · rintro ⟨word, h⟩
    rw [word_relabel] at h
    exact ⟨word.map p.toFun, (acyclic_relabel_iff _ p).mp h⟩
  · rintro ⟨word, h⟩
    refine ⟨word.map p.invFun, ?_⟩
    rw [word_relabel]
    apply (acyclic_relabel_iff _ p).mpr
    have hmap : (word.map p.invFun).map p.toFun = word := by
      clear h
      induction word with
      | nil => rfl
      | cons k ks ih => simp only [List.map_cons, p.right_inv, ih]
    simpa only [hmap] using h

def reverse {n : Nat} (B : Matrix n) : Matrix n := fun i j => -B i j

theorem reverse_involutive {n : Nat} (B : Matrix n) : reverse (reverse B) = B := by
  funext i j; simp [reverse]

theorem mutate_reverse {n : Nat} (B : Matrix n) (k : Fin n) :
    mutate (reverse B) k = reverse (mutate B k) := by
  funext i j
  simp only [mutate, reverse]
  split <;> simp only [correction_neg] <;> omega

theorem word_reverse {n : Nat} (B : Matrix n) (word : List (Fin n)) :
    applyWord (reverse B) word = reverse (applyWord B word) := by
  induction word generalizing B with
  | nil => rfl
  | cons k ks ih => simpa only [applyWord, mutate_reverse] using ih (mutate B k)

theorem reverse_skew {n : Nat} (B : Matrix n) (h : SkewSymmetric B) :
    SkewSymmetric (reverse B) := by intro i j; have := h i j; simp only [reverse]; omega

theorem relabel_skew {n : Nat} (B : Matrix n) (p : Relabeling n) (h : SkewSymmetric B) :
    SkewSymmetric (relabel B p) := fun i j => h (p.toFun i) (p.toFun j)

theorem word_preserves_skew {n : Nat} (B : Matrix n) (word : List (Fin n))
    (hB : SkewSymmetric B) : SkewSymmetric (applyWord B word) := by
  induction word generalizing B with
  | nil => exact hB
  | cons k ks ih => exact ih (mutate B k) (mutation_preserves_skew B k hB)

theorem finite_rank_bound (n : Nat) (rank : Fin n → Nat) :
    ∃ bound : Nat, ∀ i, rank i ≤ bound := by
  induction n with
  | zero => exact ⟨0, fun i => Fin.elim0 i⟩
  | succ n ih =>
    obtain ⟨bound, hb⟩ := ih (fun i => rank i.castSucc)
    refine ⟨bound + rank (Fin.last n), ?_⟩
    intro i
    by_cases hi : i.val < n
    · have heq : (⟨i.val, hi⟩ : Fin n).castSucc = i := by rfl
      have h := hb ⟨i.val, hi⟩
      rw [heq] at h
      omega
    · have heq : i = Fin.last n := by apply Fin.ext; simp; omega
      rw [heq]; omega

theorem acyclic_reverse_iff {n : Nat} (B : Matrix n) (hB : SkewSymmetric B) :
    Acyclic (reverse B) ↔ Acyclic B := by
  have forward : ∀ C : Matrix n, SkewSymmetric C → Acyclic C → Acyclic (reverse C) := by
    intro C hC h
    obtain ⟨rank, hr⟩ := h
    obtain ⟨bound, hb⟩ := finite_rank_bound n rank
    refine ⟨fun i => bound - rank i, ?_⟩
    intro i j hij
    have hs := hC i j
    have hji : 0 < C j i := by simp only [reverse] at hij; omega
    have hlt := hr j i hji
    have hi := hb i
    have hj := hb j
    change bound - rank i < bound - rank j
    omega
  constructor
  · intro h
    simpa only [reverse_involutive] using forward (reverse B) (reverse_skew B hB) h
  · exact forward B hB

theorem MA_reverse_iff {n : Nat} (B : Matrix n) (hB : SkewSymmetric B) :
    MutationAcyclic (reverse B) ↔ MutationAcyclic B := by
  constructor
  · rintro ⟨word, h⟩
    rw [word_reverse] at h
    exact ⟨word, (acyclic_reverse_iff _ (word_preserves_skew B word hB)).mp h⟩
  · rintro ⟨word, h⟩
    refine ⟨word, ?_⟩
    rw [word_reverse]
    exact (acyclic_reverse_iff _ (word_preserves_skew B word hB)).mpr h

theorem mutationAcyclic_word_iff {n : Nat} (B : Matrix n) (word : List (Fin n)) :
    MutationAcyclic (applyWord B word) ↔ MutationAcyclic B := by
  induction word generalizing B with
  | nil => rfl
  | cons k ks ih =>
    simp only [applyWord]
    exact (ih (mutate B k)).trans (mutationAcyclic_iff B k)

end QuiverProofs
