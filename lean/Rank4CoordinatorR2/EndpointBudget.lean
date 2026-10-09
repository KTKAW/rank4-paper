import Rank4Coordinator.HeightBound
import QuiverProofs.ProperObstructionSoundness
import Mathlib.Tactic.Linarith

/-! An explicit computable bound on the initial matrix and every actual
acyclic endpoint, conditional on the named properness bridges. This is an
endpoint bound only: no mutation-path prefix bound is asserted. -/
namespace Rank4CoordinatorR2
open QuiverProofs Rank4Coordinator QuiverProofs.Census QuiverProofs.ProperOrder
  QuiverProofs.ProperWiggle QuiverProofs.ProperMutation
  QuiverProofs.ProperObstructionSoundness

def entryBudget (B : Matrix 4) : Nat :=
  (B 0 1).natAbs+(B 0 2).natAbs+(B 0 3).natAbs+
    (B 1 2).natAbs+(B 1 3).natAbs+(B 2 3).natAbs

def scalarBudget (B : Matrix 4) : Nat :=
  (orderMarkov B (order 0)).natAbs+(orderMarkov B (order 1)).natAbs+
    (orderMarkov B (order 2)).natAbs+(orderMarkov B (order 3)).natAbs+
    (orderMarkov B (order 4)).natAbs+(orderMarkov B (order 5)).natAbs

def endpointHeightBudget (Q : Rank4Input) : Nat := entryBudget Q.val+scalarBudget Q.val

private theorem abs_entry_bound (x : Int) (H : Nat) (h : x.natAbs≤H) :
    -(H:Int)≤x ∧ x≤(H:Int) := by
  have hp := Int.le_natAbs (a:=x)
  have hn := Int.le_natAbs (a:=-x)
  simp only [Int.natAbs_neg] at hn
  constructor <;> omega

theorem heightLe_of_upper_abs (B : Matrix 4) (hB : SkewSymmetric B) (H : Nat)
    (h01 : (B 0 1).natAbs≤H) (h02 : (B 0 2).natAbs≤H)
    (h03 : (B 0 3).natAbs≤H) (h12 : (B 1 2).natAbs≤H)
    (h13 : (B 1 3).natAbs≤H) (h23 : (B 2 3).natAbs≤H) : HeightLe B H := by
  have ha := abs_entry_bound _ H h01
  have hb := abs_entry_bound _ H h02
  have hc := abs_entry_bound _ H h03
  have hd := abs_entry_bound _ H h12
  have he := abs_entry_bound _ H h13
  have hf := abs_entry_bound _ H h23
  rw [← ofSix_reconstruct B hB]
  intro i j
  have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  have hj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
  rcases hi with rfl|rfl|rfl|rfl <;> rcases hj with rfl|rfl|rfl|rfl <;>
    simp only [ofSix] <;> omega

theorem initial_height_budget (Q : Rank4Input) : HeightLe Q.val (endpointHeightBudget Q) := by
  apply heightLe_of_upper_abs Q.val Q.property
  all_goals unfold endpointHeightBudget entryBudget; omega

theorem entry_height_budget (B : Matrix 4) (hB : SkewSymmetric B) :
    HeightLe B (entryBudget B) := by
  apply heightLe_of_upper_abs B hB
  all_goals unfold entryBudget; omega

theorem cyclic_scalar_budget (B : Matrix 4) (hB : SkewSymmetric B) (p : CyclicOrder) :
    (orderMarkov B p).natAbs≤scalarBudget B := by
  obtain ⟨i,hi⟩ := cyclic_order_exhaustive p
  rw [ProperWiggleInvariants.markov_cyclic B hB p (order i) hi]
  have hi6 : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 := by omega
  rcases hi6 with rfl|rfl|rfl|rfl|rfl|rfl <;> unfold scalarBudget <;> omega

private theorem abs_le_of_square_le (x m : Int) (hs : x^2≤m) : x.natAbs≤m.natAbs := by
  have hx2 : (x.natAbs:Int)^2=x^2 := by
    simpa only [pow_two] using Int.natAbs_mul_self' x
  have hm := Int.le_natAbs (a:=m)
  by_cases hz : x.natAbs=0
  · rw [hz]; omega
  · have hn : 1≤(x.natAbs:Int) := by omega
    have hp := mul_nonneg (show 0≤(x.natAbs:Int) by omega)
      (show 0≤(x.natAbs:Int)-1 by omega)
    have hx : (x.natAbs:Int)≤x^2 := by nlinarith [hp,hx2]
    omega

theorem topological_height_budget (C : Matrix 4) (hC : SkewSymmetric C)
    (q : CyclicOrder) (hq : Topological C q) :
    HeightLe C (orderMarkov C q).natAbs := by
  obtain ⟨ha,hb,hc,hd,he,hf⟩ := Algebra.coordinate_squares_le_markov
    _ _ _ _ _ _ hq.1 hq.2.1 hq.2.2.1 hq.2.2.2.1 hq.2.2.2.2.1 hq.2.2.2.2.2
  have hrel := heightLe_of_upper_abs (relabel C q) (relabel_skew C q hC)
    (orderMarkov C q).natAbs (abs_le_of_square_le _ _ ha) (abs_le_of_square_le _ _ hb)
    (abs_le_of_square_le _ _ hc) (abs_le_of_square_le _ _ hd)
    (abs_le_of_square_le _ _ he) (abs_le_of_square_le _ _ hf)
  intro i j
  have hh := hrel (q.invFun i) (q.invFun j)
  simpa only [relabel,q.right_inv] using hh

/-- Every actual acyclic endpoint is bounded by this computed budget. The
proof says nothing about intermediate matrices along its supplied word. -/
theorem acyclic_endpoint_budget (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4)
    (Q : Rank4Input) (w : List (Fin 4)) (ha : Acyclic (applyWord Q.val w)) :
    HeightLe (applyWord Q.val w) (endpointHeightBudget Q) := by
  obtain ⟨p,hp⟩ := hExist Q.val Q.property ⟨w,ha⟩
  obtain ⟨r,htr,hpr⟩ := totalProper_lifts_word Q.val Q.property p hp w
  have hC := word_preserves_skew Q.val w Q.property
  obtain ⟨q,hq,hrq⟩ := hEnd _ hC ha r hpr
  have hM := transport_markov Q.property htr
  have hMq := ProperWiggleInvariants.markov_wiggle_invariant _ hC hrq
  have hscalar : orderMarkov (applyWord Q.val w) q=orderMarkov Q.val p := hMq.symm.trans hM
  have hh := topological_height_budget _ hC q hq
  rw [hscalar] at hh
  have hb := cyclic_scalar_budget Q.val Q.property p
  intro i j
  have he := hh i j
  unfold endpointHeightBudget
  constructor <;> omega

#eval endpointHeightBudget ⟨ofSix 0 1 0 1 0 1,ofSix_skew _ _ _ _ _ _⟩
#print axioms endpointHeightBudget
#print axioms initial_height_budget
#print axioms cyclic_scalar_budget
#print axioms topological_height_budget
#print axioms acyclic_endpoint_budget
end Rank4CoordinatorR2
