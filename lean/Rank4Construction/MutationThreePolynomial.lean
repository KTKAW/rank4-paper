import Rank4Formula.FormulaLanguage
import QuiverProofs.Symmetry

/-!
On a fixed closed sign chamber, mutation at vertex 3 is a polynomial map in
the six upper entries.  All inequalities are weak, so the three sign
boundaries are included.
-/

namespace Rank4Construction
open Rank4Formula QuiverProofs

def MutationThreeSignChamber (q : SixTuple) : Prop :=
  q 2 ≤ 0 ∧ 0 ≤ q 4 ∧ 0 ≤ q 5

/-- Upper entries of `mutate (ofTuple q) 3` on the sign chamber. -/
def mutationThreePolynomialTuple (q : SixTuple) : SixTuple := fun i =>
  match i.val with
  | 0 => q 0 + q 2 * q 4
  | 1 => q 1 + q 2 * q 5
  | 2 => -q 2
  | 3 => q 3
  | 4 => -q 4
  | _ => -q 5

private theorem correction_nonpos_neg_nonneg
    (c e : Int) (hc : c ≤ 0) (he : 0 ≤ e) :
    correction c (-e) = c * e := by
  have hc0 : max c 0 = 0 := by omega
  have hne0 : max (-e) 0 = 0 := by omega
  have hnc : max (-c) 0 = -c := by omega
  have he0 : max e 0 = e := by omega
  simp [correction, hc0, hne0, hnc, he0, Int.neg_mul]

private theorem correction_nonneg_neg_nonneg
    (e f : Int) (he : 0 ≤ e) (hf : 0 ≤ f) :
    correction e (-f) = 0 := by
  have he0 : max e 0 = e := by omega
  have hnf0 : max (-f) 0 = 0 := by omega
  have hne0 : max (-e) 0 = 0 := by omega
  have hf0 : max f 0 = f := by omega
  simp [correction, he0, hnf0, hne0, hf0]

/-- A genuine matrix identity, including the lower triangle, under the
closed sign guard. -/
theorem mutationThreePolynomialTuple_eq
    (q : SixTuple) (hsgn : MutationThreeSignChamber q) :
    ofTuple (mutationThreePolynomialTuple q) = mutate (ofTuple q) 3 := by
  rcases hsgn with ⟨hc, he, hf⟩
  have hce := correction_nonpos_neg_nonneg (q 2) (q 4) hc he
  have hcf := correction_nonpos_neg_nonneg (q 2) (q 5) hc hf
  have hef := correction_nonneg_neg_nonneg (q 4) (q 5) he hf
  have hskew : SkewSymmetric (ofTuple q) :=
    ofSix_skew (q 0) (q 1) (q 2) (q 3) (q 4) (q 5)
  have hrec := ofSix_reconstruct (mutate (ofTuple q) 3)
    (mutation_preserves_skew (ofTuple q) 3 hskew)
  simpa [ofTuple, mutationThreePolynomialTuple, mutate, ofSix,
    hce, hcf, hef] using hrec

/-- The polynomial tuple has the same mutation-acyclic status as the input. -/
theorem mutationThreePolynomialTuple_MA_iff
    (q : SixTuple) (hsgn : MutationThreeSignChamber q) :
    MutationAcyclic (ofTuple (mutationThreePolynomialTuple q)) ↔
      MutationAcyclic (ofTuple q) := by
  rw [mutationThreePolynomialTuple_eq q hsgn]
  exact mutationAcyclic_iff (ofTuple q) 3

#print axioms mutationThreePolynomialTuple_eq
#print axioms mutationThreePolynomialTuple_MA_iff

end Rank4Construction
