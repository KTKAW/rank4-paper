import QuiverProofs.ProperOrder

/-! Exhaustive topological coordinates for arbitrary acyclic rank-four matrices.
The finite target type has a proved bound; no MA transport is presumed. -/
set_option maxHeartbeats 2000000
namespace QuiverProofs.AcyclicTargets

private theorem sort_four (r : Fin 4 → Nat) :
    ∃ p : Fin 24, r ((Census.permutation p).toFun 0) ≤ r ((Census.permutation p).toFun 1) ∧
      r ((Census.permutation p).toFun 1) ≤ r ((Census.permutation p).toFun 2) ∧
      r ((Census.permutation p).toFun 2) ≤ r ((Census.permutation p).toFun 3) := by
  by_cases h0 : r 0 ≤ r 1
  · by_cases h1 : r 0 ≤ r 2
    · by_cases h2 : r 0 ≤ r 3
      · by_cases h3 : r 1 ≤ r 2
        · by_cases h4 : r 1 ≤ r 3
          · by_cases h5 : r 2 ≤ r 3
            · exact ⟨0, by change r 0 ≤ r 1 ∧ r 1 ≤ r 2 ∧ r 2 ≤ r 3; omega⟩
            · exact ⟨1, by change r 0 ≤ r 1 ∧ r 1 ≤ r 3 ∧ r 3 ≤ r 2; omega⟩
          · exact ⟨4, by change r 0 ≤ r 3 ∧ r 3 ≤ r 1 ∧ r 1 ≤ r 2; omega⟩
        · by_cases h4 : r 1 ≤ r 3
          · exact ⟨2, by change r 0 ≤ r 2 ∧ r 2 ≤ r 1 ∧ r 1 ≤ r 3; omega⟩
          · by_cases h5 : r 2 ≤ r 3
            · exact ⟨3, by change r 0 ≤ r 2 ∧ r 2 ≤ r 3 ∧ r 3 ≤ r 1; omega⟩
            · exact ⟨5, by change r 0 ≤ r 3 ∧ r 3 ≤ r 2 ∧ r 2 ≤ r 1; omega⟩
      · by_cases h3 : r 1 ≤ r 2
        · exact ⟨18, by change r 3 ≤ r 0 ∧ r 0 ≤ r 1 ∧ r 1 ≤ r 2; omega⟩
        · exact ⟨19, by change r 3 ≤ r 0 ∧ r 0 ≤ r 2 ∧ r 2 ≤ r 1; omega⟩
    · by_cases h2 : r 0 ≤ r 3
      · by_cases h3 : r 1 ≤ r 3
        · exact ⟨12, by change r 2 ≤ r 0 ∧ r 0 ≤ r 1 ∧ r 1 ≤ r 3; omega⟩
        · exact ⟨13, by change r 2 ≤ r 0 ∧ r 0 ≤ r 3 ∧ r 3 ≤ r 1; omega⟩
      · by_cases h3 : r 2 ≤ r 3
        · exact ⟨16, by change r 2 ≤ r 3 ∧ r 3 ≤ r 0 ∧ r 0 ≤ r 1; omega⟩
        · exact ⟨22, by change r 3 ≤ r 2 ∧ r 2 ≤ r 0 ∧ r 0 ≤ r 1; omega⟩
  · by_cases h1 : r 0 ≤ r 2
    · by_cases h2 : r 0 ≤ r 3
      · by_cases h3 : r 2 ≤ r 3
        · exact ⟨6, by change r 1 ≤ r 0 ∧ r 0 ≤ r 2 ∧ r 2 ≤ r 3; omega⟩
        · exact ⟨7, by change r 1 ≤ r 0 ∧ r 0 ≤ r 3 ∧ r 3 ≤ r 2; omega⟩
      · by_cases h3 : r 1 ≤ r 3
        · exact ⟨10, by change r 1 ≤ r 3 ∧ r 3 ≤ r 0 ∧ r 0 ≤ r 2; omega⟩
        · exact ⟨20, by change r 3 ≤ r 1 ∧ r 1 ≤ r 0 ∧ r 0 ≤ r 2; omega⟩
    · by_cases h2 : r 0 ≤ r 3
      · by_cases h3 : r 1 ≤ r 2
        · exact ⟨8, by change r 1 ≤ r 2 ∧ r 2 ≤ r 0 ∧ r 0 ≤ r 3; omega⟩
        · exact ⟨14, by change r 2 ≤ r 1 ∧ r 1 ≤ r 0 ∧ r 0 ≤ r 3; omega⟩
      · by_cases h3 : r 1 ≤ r 2
        · by_cases h4 : r 1 ≤ r 3
          · by_cases h5 : r 2 ≤ r 3
            · exact ⟨9, by change r 1 ≤ r 2 ∧ r 2 ≤ r 3 ∧ r 3 ≤ r 0; omega⟩
            · exact ⟨11, by change r 1 ≤ r 3 ∧ r 3 ≤ r 2 ∧ r 2 ≤ r 0; omega⟩
          · exact ⟨21, by change r 3 ≤ r 1 ∧ r 1 ≤ r 2 ∧ r 2 ≤ r 0; omega⟩
        · by_cases h4 : r 1 ≤ r 3
          · exact ⟨15, by change r 2 ≤ r 1 ∧ r 1 ≤ r 3 ∧ r 3 ≤ r 0; omega⟩
          · by_cases h5 : r 2 ≤ r 3
            · exact ⟨17, by change r 2 ≤ r 3 ∧ r 3 ≤ r 1 ∧ r 1 ≤ r 0; omega⟩
            · exact ⟨23, by change r 3 ≤ r 2 ∧ r 2 ≤ r 1 ∧ r 1 ≤ r 0; omega⟩

/-- Every acyclic skew matrix has a permutation with all six upper entries
nonnegative. The ranking may have ties and need not be a permutation. -/
theorem acyclic_has_topological_coordinates (B : Matrix 4)
    (hB : SkewSymmetric B) (hA : Acyclic B) :
    ∃ p : ProperOrder.CyclicOrder,
      0 ≤ B (p.toFun 0) (p.toFun 1) ∧ 0 ≤ B (p.toFun 0) (p.toFun 2) ∧
      0 ≤ B (p.toFun 0) (p.toFun 3) ∧ 0 ≤ B (p.toFun 1) (p.toFun 2) ∧
      0 ≤ B (p.toFun 1) (p.toFun 3) ∧ 0 ≤ B (p.toFun 2) (p.toFun 3) := by
  obtain ⟨rank, hr⟩ := hA
  obtain ⟨k, h01, h12, h23⟩ := sort_four rank
  let p := Census.permutation k
  have nonnegative : ∀ i j, rank (p.toFun i) ≤ rank (p.toFun j) →
      0 ≤ B (p.toFun i) (p.toFun j) := by
    intro i j hij
    have hs := hB (p.toFun i) (p.toFun j)
    by_cases he : 0 < B (p.toFun j) (p.toFun i)
    · have := hr _ _ he; omega
    · omega
  refine ⟨p, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact nonnegative 0 1 h01
  · exact nonnegative 0 2 (Nat.le_trans h01 h12)
  · exact nonnegative 0 3 (Nat.le_trans (Nat.le_trans h01 h12) h23)
  · exact nonnegative 1 2 h12
  · exact nonnegative 1 3 (Nat.le_trans h12 h23)
  · exact nonnegative 2 3 h23

private theorem nonnegative_arrows_increase (a b c d e f : Int)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (he : 0 ≤ e) (hf : 0 ≤ f) :
    ∀ i j : Fin 4, 0 < ofSix a b c d e f i j → i < j := by
  intro i j hij
  have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  have hj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
  rcases hi with rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl <;>
    simp only [ofSix] at hij <;> omega

/-- Acyclic quivers have a single representative in which every vertex is
proper. This is initial properness, not the total-properness theorem. -/
theorem acyclic_has_proper_order (B : Matrix 4)
    (hB : SkewSymmetric B) (hA : Acyclic B) :
    ∃ p : ProperOrder.CyclicOrder, ∀ v, ProperOrder.ProperVertex B p v := by
  obtain ⟨p,ha,hb,hc,hd,he,hf⟩ := acyclic_has_topological_coordinates B hB hA
  have hrec := ofSix_reconstruct (relabel B p) (relabel_skew B p hB)
  have inc : ∀ i j : Fin 4, 0 < relabel B p i j → i < j := by
    rw [← hrec]
    exact nonnegative_arrows_increase _ _ _ _ _ _ ha hb hc hd he hf
  refine ⟨p, ?_⟩
  intro v u w huv hvw
  have huv' := inc (p.invFun u) (p.invFun v) (by
    simpa only [relabel, p.right_inv] using huv)
  have hvw' := inc (p.invFun v) (p.invFun w) (by
    simpa only [relabel, p.right_inv] using hvw)
  exact Or.inl ⟨huv',hvw'⟩

/-- An explicit finite box containing every nonnegative tuple of coefficient m.
The bound m (rather than sqrt(m)) is deliberately loose, but exact and finite. -/
abbrev TargetBox (m : Nat) := Fin 6 → Fin (m + 1)

def targetMarkov {m : Nat} (q : TargetBox m) : Int :=
  Algebra.markov (q 0).val (q 1).val (q 2).val (q 3).val (q 4).val (q 5).val

def targetPfaffian {m : Nat} (q : TargetBox m) : Int :=
  Algebra.pfaffian (q 0).val (q 1).val (q 2).val (q 3).val (q 4).val (q 5).val

private theorem nonneg_le_square (x : Int) (hx : 0 ≤ x) : x ≤ x^2 := by
  by_cases hz : x=0
  · subst x; decide
  · have h1 : 0 ≤ x-1 := by omega
    have := Int.mul_nonneg hx h1
    grind

/-- The finite target box is complete for every integral invariant value,
without a resource cutoff or a bound on the original quiver's entries. -/
theorem target_box_complete (a b c d e f : Int)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (he : 0 ≤ e) (hf : 0 ≤ f)
    (m : Nat) (hm : Algebra.markov a b c d e f = m) :
    ∃ q : TargetBox m,
      (q 0).val = a ∧ (q 1).val = b ∧ (q 2).val = c ∧
      (q 3).val = d ∧ (q 4).val = e ∧ (q 5).val = f := by
  obtain ⟨ha2,hb2,hc2,hd2,he2,hf2⟩ :=
    Algebra.coordinate_squares_le_markov a b c d e f ha hb hc hd he hf
  have ha1 := nonneg_le_square a ha
  have hb1 := nonneg_le_square b hb
  have hc1 := nonneg_le_square c hc
  have hd1 := nonneg_le_square d hd
  have he1 := nonneg_le_square e he
  have hf1 := nonneg_le_square f hf
  let q : TargetBox m := fun i => match i.val with
    | 0 => ⟨a.toNat, by omega⟩ | 1 => ⟨b.toNat, by omega⟩
    | 2 => ⟨c.toNat, by omega⟩ | 3 => ⟨d.toNat, by omega⟩
    | 4 => ⟨e.toNat, by omega⟩ | _ => ⟨f.toNat, by omega⟩
  refine ⟨q, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp [q] <;> omega

/-- Absence from the finite box excludes every nonnegative topological tuple.
The missing MA-to-proper-invariant theorem is not part of this implication. -/
theorem absent_targets_excludes_topological_tuple (m : Nat) (D : Int)
    (h : ∀ q : TargetBox m, ¬(targetMarkov q = m ∧ targetPfaffian q ^ 2 = D))
    (a b c d e f : Int)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (he : 0 ≤ e) (hf : 0 ≤ f) :
    ¬(Algebra.markov a b c d e f = m ∧ Algebra.pfaffian a b c d e f ^ 2 = D) := by
  rintro ⟨hm, hD⟩
  obtain ⟨q,h0,h1,h2,h3,h4,h5⟩ := target_box_complete a b c d e f ha hb hc hd he hf m hm
  apply h q
  simpa only [targetMarkov, targetPfaffian, h0,h1,h2,h3,h4,h5] using And.intro hm hD

end QuiverProofs.AcyclicTargets
