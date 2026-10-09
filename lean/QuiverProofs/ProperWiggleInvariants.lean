import QuiverProofs.ProperWiggle

namespace QuiverProofs.ProperWiggleInvariants
open ProperOrder ProperWiggle Census
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

private theorem same_symm {p q : CyclicOrder} (h : SameCyclicOrder p q) :
    SameCyclicOrder q p := fun u v w => (h u v w).symm
private theorem same_trans {p q r : CyclicOrder}
    (h : SameCyclicOrder p q) (g : SameCyclicOrder q r) : SameCyclicOrder p r :=
  fun u v w => (h u v w).trans (g u v w)

private theorem permutation_eq_of_toFun_eq (p q : CyclicOrder)
    (h : p.toFun=q.toFun) : p=q := by
  have hi : p.invFun=q.invFun := by
    funext i
    apply p.injective
    rw [p.right_inv,h,q.right_inv]
  cases p
  cases q
  simp_all

def canonicalIndex (k : Fin 24) : Fin 6 := match k.val with
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5
  | 6 => 3 | 7 => 5 | 8 => 4 | 9 => 0 | 10 => 2 | 11 => 1
  | 12 => 1 | 13 => 4 | 14 => 5 | 15 => 2 | 16 => 0 | 17 => 3
  | 18 => 0 | 19 => 2 | 20 => 3 | 21 => 4 | 22 => 1 | _ => 5

theorem canonical_index_correct : ∀ k : Fin 24,
    SameCyclicOrder (permutation k) (order (canonicalIndex k)) := by decide

private theorem markov_canonical_six (a b c d e f : Int) (k : Fin 24) :
    orderMarkov (ofSix a b c d e f) (permutation k) =
      orderMarkov (ofSix a b c d e f) (order (canonicalIndex k)) := by
  have hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=8 ∨ k=9 ∨
    k=10 ∨ k=11 ∨ k=12 ∨ k=13 ∨ k=14 ∨ k=15 ∨ k=16 ∨ k=17 ∨ k=18 ∨ k=19 ∨
    k=20 ∨ k=21 ∨ k=22 ∨ k=23 := by omega
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change Algebra.markov a b c d e f = Algebra.markov a b c d e f
    unfold Algebra.markov Algebra.squareSum Algebra.cycleTerms
    grind
  · change Algebra.markov a c b e d (-f) = Algebra.markov a c b e d (-f)
    unfold Algebra.markov Algebra.squareSum Algebra.cycleTerms
    grind
  · change Algebra.markov b a c (-d) f e = Algebra.markov b a c (-d) f e
    unfold Algebra.markov Algebra.squareSum Algebra.cycleTerms
    grind
  · change Algebra.markov b c a f (-d) (-e) = Algebra.markov b c a f (-d) (-e)
    unfold Algebra.markov Algebra.squareSum Algebra.cycleTerms
    grind
  · change Algebra.markov c a b (-e) (-f) d = Algebra.markov c a b (-e) (-f) d
    unfold Algebra.markov Algebra.squareSum Algebra.cycleTerms
    grind
  · change Algebra.markov c b a (-f) (-e) (-d) = Algebra.markov c b a (-f) (-e) (-d)
    unfold Algebra.markov Algebra.squareSum Algebra.cycleTerms
    grind
  · change Algebra.markov (-a) d e b c f = Algebra.markov b c a f (-d) (-e)
    unfold Algebra.markov Algebra.squareSum Algebra.cycleTerms
    grind
  · change Algebra.markov (-a) e d c b (-f) = Algebra.markov c b a (-f) (-e) (-d)
    unfold Algebra.markov Algebra.squareSum Algebra.cycleTerms
    grind
  · change Algebra.markov d (-a) e (-b) f c = Algebra.markov c a b (-e) (-f) d
    unfold Algebra.markov Algebra.squareSum Algebra.cycleTerms
    grind
  · change Algebra.markov d e (-a) f (-b) (-c) = Algebra.markov a b c d e f
    unfold Algebra.markov Algebra.squareSum Algebra.cycleTerms
    grind
  · change Algebra.markov e (-a) d (-c) (-f) b = Algebra.markov b a c (-d) f e
    unfold Algebra.markov Algebra.squareSum Algebra.cycleTerms
    grind
  · change Algebra.markov e d (-a) (-f) (-c) (-b) = Algebra.markov a c b e d (-f)
    unfold Algebra.markov Algebra.squareSum Algebra.cycleTerms
    grind
  · change Algebra.markov (-b) (-d) f a c e = Algebra.markov a c b e d (-f)
    unfold Algebra.markov Algebra.squareSum Algebra.cycleTerms
    grind
  · change Algebra.markov (-b) f (-d) c a (-e) = Algebra.markov c a b (-e) (-f) d
    unfold Algebra.markov Algebra.squareSum Algebra.cycleTerms
    grind
  · change Algebra.markov (-d) (-b) f (-a) e c = Algebra.markov c b a (-f) (-e) (-d)
    unfold Algebra.markov Algebra.squareSum Algebra.cycleTerms
    grind
  · change Algebra.markov (-d) f (-b) e (-a) (-c) = Algebra.markov b a c (-d) f e
    unfold Algebra.markov Algebra.squareSum Algebra.cycleTerms
    grind
  · change Algebra.markov f (-b) (-d) (-c) (-e) a = Algebra.markov a b c d e f
    unfold Algebra.markov Algebra.squareSum Algebra.cycleTerms
    grind
  · change Algebra.markov f (-d) (-b) (-e) (-c) (-a) = Algebra.markov b c a f (-d) (-e)
    unfold Algebra.markov Algebra.squareSum Algebra.cycleTerms
    grind
  · change Algebra.markov (-c) (-e) (-f) a b d = Algebra.markov a b c d e f
    unfold Algebra.markov Algebra.squareSum Algebra.cycleTerms
    grind
  · change Algebra.markov (-c) (-f) (-e) b a (-d) = Algebra.markov b a c (-d) f e
    unfold Algebra.markov Algebra.squareSum Algebra.cycleTerms
    grind
  · change Algebra.markov (-e) (-c) (-f) (-a) d b = Algebra.markov b c a f (-d) (-e)
    unfold Algebra.markov Algebra.squareSum Algebra.cycleTerms
    grind
  · change Algebra.markov (-e) (-f) (-c) d (-a) (-b) = Algebra.markov c a b (-e) (-f) d
    unfold Algebra.markov Algebra.squareSum Algebra.cycleTerms
    grind
  · change Algebra.markov (-f) (-c) (-e) (-b) (-d) a = Algebra.markov a c b e d (-f)
    unfold Algebra.markov Algebra.squareSum Algebra.cycleTerms
    grind
  · change Algebra.markov (-f) (-e) (-c) (-d) (-b) (-a) = Algebra.markov c b a (-f) (-e) (-d)
    unfold Algebra.markov Algebra.squareSum Algebra.cycleTerms
    grind

theorem markov_canonical (B : Matrix 4) (hB : SkewSymmetric B) (k : Fin 24) :
    orderMarkov B (permutation k) = orderMarkov B (order (canonicalIndex k)) := by
  rw [← ofSix_reconstruct B hB]
  exact markov_canonical_six _ _ _ _ _ _ k

/-- The Markov coefficient is a cyclic-order invariant over arbitrary
integer weights: changing the linear starting point does not change it. -/
theorem markov_cyclic (B : Matrix 4) (hB : SkewSymmetric B)
    (p q : CyclicOrder) (hpq : SameCyclicOrder p q) : orderMarkov B p=orderMarkov B q := by
  obtain ⟨k,hk⟩ := permutation_exhaustive p
  obtain ⟨l,hl⟩ := permutation_exhaustive q
  have hp := permutation_eq_of_toFun_eq p (permutation k) hk
  have hq := permutation_eq_of_toFun_eq q (permutation l) hl
  subst p
  subst q
  have he := six_orders_distinct (canonicalIndex k) (canonicalIndex l)
    (same_trans (same_symm (canonical_index_correct k)) (same_trans hpq (canonical_index_correct l)))
  rw [markov_canonical B hB k,markov_canonical B hB l,he]

private theorem markov_swap_six (a b c d e f : Int) (k : Fin 4)
    (h : (ofSix a b c d e f) k (nextPosition k)=0) :
    orderMarkov (ofSix a b c d e f) (swapPositions k) = Algebra.markov a b c d e f := by
  have hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
  rcases hk with rfl | rfl | rfl | rfl
  · change a=0 at h
    change Algebra.markov (-a) d e b c f=Algebra.markov a b c d e f
    unfold Algebra.markov Algebra.squareSum Algebra.cycleTerms
    grind
  · change d=0 at h
    change Algebra.markov b a c (-d) f e=Algebra.markov a b c d e f
    unfold Algebra.markov Algebra.squareSum Algebra.cycleTerms
    grind
  · change f=0 at h
    change Algebra.markov a c b e d (-f)=Algebra.markov a b c d e f
    unfold Algebra.markov Algebra.squareSum Algebra.cycleTerms
    grind
  · change -c=0 at h
    change Algebra.markov (-e) (-f) (-c) d (-a) (-b)=Algebra.markov a b c d e f
    unfold Algebra.markov Algebra.squareSum Algebra.cycleTerms
    grind

/-- Swapping any cyclically consecutive nonadjacent vertices preserves the
coefficient. The wrap-around positions 3 and 0 are included. -/
theorem markov_adjacent_swap (B : Matrix 4) (hB : SkewSymmetric B)
    (p : CyclicOrder) (a : Fin 4)
    (h : B (p.toFun a) (p.toFun (nextPosition a))=0) :
    orderMarkov B (swapAdjacent p a)=orderMarkov B p := by
  change orderMarkov (relabel B p) (swapPositions a)=_
  have hQ := relabel_skew B p hB
  have he := ofSix_reconstruct (relabel B p) hQ
  have hz : relabel B p a (nextPosition a)=0 := h
  rw [←he] at hz ⊢
  exact markov_swap_six _ _ _ _ _ _ a hz

theorem markov_wiggle_step (B : Matrix 4) (hB : SkewSymmetric B)
    {p q : CyclicOrder} (h : WiggleStep B p q) : orderMarkov B p=orderMarkov B q := by
  obtain ⟨r,a,hpr,ha,hrq⟩ := h
  exact (markov_cyclic B hB p r hpr).trans
    ((markov_adjacent_swap B hB r a ha).symm.trans (markov_cyclic B hB _ q hrq))

/-- Semantic constancy on the complete wiggle class, for paths of any length.
This does not claim invariance under ordinary mutation at a fixed order. -/
theorem markov_wiggle_invariant (B : Matrix 4) (hB : SkewSymmetric B)
    {p q : CyclicOrder} (h : WiggleEquivalent B p q) : orderMarkov B p=orderMarkov B q := by
  induction h with
  | same h => exact markov_cyclic B hB _ _ h
  | step h => exact markov_wiggle_step B hB h
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- Every cyclic order has a linear representative starting at any chosen vertex. -/
theorem exists_first_representative (p : CyclicOrder) (k : Fin 4) :
    ∃ r : CyclicOrder, SameCyclicOrder p r ∧ r.toFun 0=k := by
  obtain ⟨i,hi⟩ := permutation_exhaustive p
  have hp := permutation_eq_of_toFun_eq p (permutation i) hi
  subst p
  have ht : ∀ (i : Fin 24) (k : Fin 4), ∃ j : Fin 24,
      SameCyclicOrder (permutation i) (permutation j) ∧ (permutation j).toFun 0=k := by decide
  obtain ⟨j,hj,hk⟩ := ht i k
  exact ⟨permutation j,hj,hk⟩

end QuiverProofs.ProperWiggleInvariants
