import QuiverProofs.CensusCore

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace QuiverProofs.Census

theorem matrixCode_codeMatrix (n : Nat) (hn : n < 15625) :
    matrixCode (codeMatrix n) = n := by
  simp only [matrixCode, codeMatrix, ofSix]
  omega

theorem codeMatrix_injective (i j : Fin 15625)
    (h : codeMatrix i.val = codeMatrix j.val) : i=j := by
  have heq := congrArg matrixCode h
  rw [matrixCode_codeMatrix i.val i.isLt, matrixCode_codeMatrix j.val j.isLt] at heq
  exact Fin.ext heq

theorem representative_bounded (i : Fin 695) : BoundedTwo (representative i) :=
  codeMatrix_bounded _

theorem representative_skew (i : Fin 695) : SkewSymmetric (representative i) :=
  codeMatrix_skew _

theorem permutation_table_distinct : ∀ p q : Fin 24,
    (∀ i : Fin 4, permFun p.val i = permFun q.val i) → p=q := by decide

theorem representative_code_bounds : ∀ i : Fin 695,
    representativeCodes.get i.val < 15625 := by decide

theorem representative_adjacent_codes : ∀ i : Fin 694,
    representativeCodes.get i.val < representativeCodes.get (i.val+1) := by decide

/-- The finite canonicality table checks all 695×24 relabelings. -/
theorem representative_minimal_table : ∀ (i : Fin 695) (p : Fin 24),
    representativeCodes.get i.val ≤ matrixCode (relabel (representative i) (permutation p)) := by decide

theorem representative_matrixCode (i : Fin 695) :
    matrixCode (representative i) = representativeCodes.get i.val :=
  matrixCode_codeMatrix _ (representative_code_bounds i)

theorem adjacent_strict_implies_strict (f : Nat → Nat) (bound : Nat)
    (h : ∀ i, i+1 < bound → f i < f (i+1)) :
    ∀ n, n < bound → ∀ m, m < n → f m < f n := by
  intro n
  induction n with
  | zero => intro hn m hm; omega
  | succ n ih =>
    intro hn m hm
    have hstep := h n hn
    by_cases hmn : m=n
    · subst m; exact hstep
    · have hprev := ih (by omega) m (by omega)
      omega

theorem representative_codes_increasing (i j : Fin 695) (hij : i < j) :
    representativeCodes.get i.val < representativeCodes.get j.val := by
  apply adjacent_strict_implies_strict representativeCodes.get 695
    (fun k hk => representative_adjacent_codes ⟨k, by omega⟩)
    j.val j.isLt i.val
  exact hij

theorem representative_codes_injective (i j : Fin 695)
    (h : representativeCodes.get i.val = representativeCodes.get j.val) : i=j := by
  by_cases hij : i<j
  · have := representative_codes_increasing i j hij
    omega
  · by_cases hji : j<i
    · have := representative_codes_increasing j i hji
      omega
    · apply Fin.ext; omega

theorem representative_minimal (i : Fin 695) (p : Relabeling 4) :
    matrixCode (representative i) ≤ matrixCode (relabel (representative i) p) := by
  obtain ⟨k,hk⟩ := permutation_exhaustive p
  have heq : relabel (representative i) p = relabel (representative i) (permutation k) := by
    funext u v
    simp only [relabel, hk]
  rw [heq, representative_matrixCode]
  exact representative_minimal_table i k

/-- Different indices represent different isomorphism classes under every
vertex relabeling, not just distinct labeled matrices. -/
theorem representatives_pairwise_nonisomorphic (i j : Fin 695) (p : Relabeling 4)
    (h : relabel (representative i) p = representative j) : i=j := by
  have hforward := representative_minimal i p
  rw [h] at hforward
  have hinverse : relabel (representative j) p.symm = representative i := by
    rw [← h]
    exact relabel_inverse _ p
  have hback := representative_minimal j p.symm
  rw [hinverse] at hback
  have heq : matrixCode (representative i) = matrixCode (representative j) := by omega
  rw [representative_matrixCode, representative_matrixCode] at heq
  exact representative_codes_injective i j heq

theorem ma_indices_injective (i j : Fin 561)
    (h : maRepCodes.get i.val = maRepCodes.get j.val) : i=j := by
  have hinc : ∀ a b : Fin 561, a<b → maRepCodes.get a.val < maRepCodes.get b.val := by
    intro a b hab
    exact adjacent_strict_implies_strict maRepCodes.get 561
      (fun k hk => ma_adjacent_indices ⟨k, by omega⟩) b.val b.isLt a.val hab
  by_cases hij : i<j
  · have := hinc i j hij; omega
  · by_cases hji : j<i
    · have := hinc j i hji; omega
    · apply Fin.ext; omega

/-- The 561 positive representatives belong to 561 different relabeling classes. -/
theorem ma_representatives_pairwise_nonisomorphic (i j : Fin 561) (p : Relabeling 4)
    (h : relabel (maRepresentative i) p = maRepresentative j) : i=j := by
  have heq := representatives_pairwise_nonisomorphic
    ⟨maRepCodes.get i.val, ma_source_indices i⟩
    ⟨maRepCodes.get j.val, ma_source_indices j⟩ p h
  exact ma_indices_injective i j (congrArg Fin.val heq)

def compose (p q : Relabeling 4) : Relabeling 4 :=
  p.trans q

end QuiverProofs.Census
