import QuiverProofs.Invariants
import QuiverProofs.Symmetry

namespace QuiverProofs.ClassSeparation

private theorem fin4 (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega

theorem pfaffian_square_relabel (B : Matrix 4) (hB : SkewSymmetric B)
    (p : Relabeling 4) : matrixPfaffian (relabel B p)^2 = matrixPfaffian B^2 := by
  rw [← ofSix_reconstruct B hB]
  have h01 : p.toFun 0 ≠ p.toFun 1 := fun h => (by decide : (0 : Fin 4) ≠ 1) (p.injective h)
  have h02 : p.toFun 0 ≠ p.toFun 2 := fun h => (by decide : (0 : Fin 4) ≠ 2) (p.injective h)
  have h03 : p.toFun 0 ≠ p.toFun 3 := fun h => (by decide : (0 : Fin 4) ≠ 3) (p.injective h)
  have h12 : p.toFun 1 ≠ p.toFun 2 := fun h => (by decide : (1 : Fin 4) ≠ 2) (p.injective h)
  have h13 : p.toFun 1 ≠ p.toFun 3 := fun h => (by decide : (1 : Fin 4) ≠ 3) (p.injective h)
  have h23 : p.toFun 2 ≠ p.toFun 3 := fun h => (by decide : (2 : Fin 4) ≠ 3) (p.injective h)
  rcases fin4 (p.toFun 0) with h0|h0|h0|h0 <;>
    rcases fin4 (p.toFun 1) with h1|h1|h1|h1 <;>
    rcases fin4 (p.toFun 2) with h2|h2|h2|h2 <;>
    rcases fin4 (p.toFun 3) with h3|h3|h3|h3 <;>
    simp_all [matrixPfaffian,relabel,ofSix] <;> grind

def MutationIsomorphic (B C : Matrix 4) : Prop :=
  ∃ word : List (Fin 4), ∃ p : Relabeling 4, applyWord B word = relabel C p

theorem mutation_isomorphic_pfaffian (B C : Matrix 4)
    (hB : SkewSymmetric B) (hC : SkewSymmetric C)
    (h : MutationIsomorphic B C) : matrixPfaffian B^2 = matrixPfaffian C^2 := by
  obtain ⟨word,p,he⟩ := h
  rw [← pfaffian_square_word B word hB,he,pfaffian_square_relabel C hC p]

def printed (i : Fin 5) : Matrix 4 := match i.val with
  | 0 => ofSix (-2) (-2) 1 (-1) 2 (-2)
  | 1 => ofSix (-2) (-1) 1 (-1) 1 (-2)
  | 2 => ofSix (-2) (-1) 1 1 (-2) 2
  | 3 => ofSix (-2) (-1) 2 (-2) (-1) (-2)
  | _ => ofSix (-2) 0 2 (-2) 0 (-2)

theorem printed_skew (i : Fin 5) : SkewSymmetric (printed i) := by
  have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
  rcases hi with rfl|rfl|rfl|rfl|rfl <;> exact ofSix_skew _ _ _ _ _ _

theorem five_distinct_mutation_classes (i j : Fin 5) (h : i≠j) :
    ¬ MutationIsomorphic (printed i) (printed j) := by
  intro hm
  have he := mutation_isomorphic_pfaffian _ _ (printed_skew i) (printed_skew j) hm
  have hd : ∀ i j : Fin 5, i≠j → matrixPfaffian (printed i)^2 ≠ matrixPfaffian (printed j)^2 := by decide
  exact hd i j h he

theorem square_mod_four (a : Int) : a^2 % 4 = 0 ∨ a^2 % 4 = 1 := by
  have hr : a%4=0 ∨ a%4=1 ∨ a%4=2 ∨ a%4=3 := by omega
  have he : a^2%4=((a%4)*(a%4))%4 := by simp [Int.pow_succ,Int.mul_emod]
  rcases hr with h|h|h|h <;> rw [he,h] <;> decide

theorem difference_squares_mod_four (a b : Int) : (a^2-b^2)%4 ≠ 2 := by
  have ha := square_mod_four a
  have hb := square_mod_four b
  rw [Int.sub_emod]
  rcases ha with ha|ha <;> rcases hb with hb|hb <;> rw [ha,hb] <;> decide

theorem residual_pfaffian (a b c : Int) :
    matrixPfaffian (ofSix (-a) (-b) (-c) (-1) 1 (-1)) = a+b+c := by
  simp [matrixPfaffian,ofSix]

theorem box_pfaffian (a b : Int) :
    matrixPfaffian (ofSix a 0 (-b) b 0 a) = a^2-b^2 := by
  simp [matrixPfaffian,ofSix]; grind

theorem square_eq_cases (a b : Int) (h : a^2=b^2) : a=b ∨ a= -b := by
  have hp : (a-b)*(a+b)=0 := by grind
  rcases Int.mul_eq_zero.mp hp with h|h <;> omega

theorem residual_not_box (a b c x y : Int) (h : (a+b+c)%4=2) :
    ¬ MutationIsomorphic (ofSix (-a) (-b) (-c) (-1) 1 (-1))
        (ofSix x 0 (-y) y 0 x) := by
  intro hm
  have he := mutation_isomorphic_pfaffian _ _ (ofSix_skew _ _ _ _ _ _) (ofSix_skew _ _ _ _ _ _) hm
  rw [residual_pfaffian,box_pfaffian] at he
  have heq := square_eq_cases (a+b+c) (x^2-y^2) he
  have hn := difference_squares_mod_four x y
  rcases heq with heq|heq
  · rw [heq] at h; exact hn h
  · rw [heq,Int.neg_emod] at h; omega

theorem residual_diagonal_distinct (s t : Int) (hs : 0≤s) (ht : 0≤t) (hst : s≠t) :
    ¬ MutationIsomorphic (ofSix (-s) (-s) (-s) (-1) 1 (-1))
        (ofSix (-t) (-t) (-t) (-1) 1 (-1)) := by
  intro hm
  have he := mutation_isomorphic_pfaffian _ _ (ofSix_skew _ _ _ _ _ _) (ofSix_skew _ _ _ _ _ _) hm
  rw [residual_pfaffian,residual_pfaffian] at he
  have hh := square_eq_cases (s+s+s) (t+t+t) he
  have : s=t := by omega
  exact hst this

theorem residual_diagonal_not_box (t x y : Int) (ht : t%4=2) :
    ¬ MutationIsomorphic (ofSix (-t) (-t) (-t) (-1) 1 (-1))
        (ofSix x 0 (-y) y 0 x) := by
  apply residual_not_box
  omega

end QuiverProofs.ClassSeparation
