import Rank4Round3.ClassifierBridge
import Rank4Round3.MutationSignPullback
import QuiverProofs.Symmetry

/-!
The archive's total executable MA decision, exposed as a six-coordinate
Boolean invariant. Its computation still uses an input-dependent finite
mutation bound; these theorems do not make it a fixed polynomial-sign formula.
-/

namespace Rank4Round6.Foundations

open Rank4Formula Rank4Round3 QuiverProofs

/-- Total executable MA invariant on all integer upper triangles. -/
def maInvariant (q : SixTuple) : Bool := classifySix q

theorem maInvariant_MA_iff (q : SixTuple) :
    maInvariant q = true ↔ MutationAcyclic (ofTuple q) := by
  simpa only [maInvariant] using classifySix_MA_iff q

theorem maInvariant_NMA_iff (q : SixTuple) :
    maInvariant q = false ↔ ¬ MutationAcyclic (ofTuple q) := by
  simpa only [maInvariant] using classifySix_NMA_iff q

private theorem bool_eq_of_true_iff {a b : Bool}
    (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

theorem maInvariant_mutation (q : SixTuple) (k : Fin 4) :
    maInvariant (mutatedUpper q k) = maInvariant q := by
  apply bool_eq_of_true_iff
  rw [maInvariant_MA_iff (mutatedUpper q k), maInvariant_MA_iff q,
    mutatedUpper_matrix]
  exact mutationAcyclic_iff (ofTuple q) k

/-- The upper six coordinates after a finite mutation word. -/
def wordSix (q : SixTuple) (w : List (Fin 4)) : SixTuple :=
  upperTuple (applyWord (ofTuple q) w)

theorem wordSix_matrix (q : SixTuple) (w : List (Fin 4)) :
    ofTuple (wordSix q w) = applyWord (ofTuple q) w := by
  exact ofTuple_upperTuple _
    (word_preserves_skew (ofTuple q) w
      (ofSix_skew (q 0) (q 1) (q 2) (q 3) (q 4) (q 5)))

theorem maInvariant_word (q : SixTuple) (w : List (Fin 4)) :
    maInvariant (wordSix q w) = maInvariant q := by
  apply bool_eq_of_true_iff
  rw [maInvariant_MA_iff (wordSix q w), maInvariant_MA_iff q,
    wordSix_matrix]
  exact mutationAcyclic_word_iff (ofTuple q) w

/-- The upper six coordinates after a vertex relabeling. -/
def relabelSix (q : SixTuple) (p : Relabeling 4) : SixTuple :=
  upperTuple (relabel (ofTuple q) p)

theorem relabelSix_matrix (q : SixTuple) (p : Relabeling 4) :
    ofTuple (relabelSix q p) = relabel (ofTuple q) p := by
  exact ofTuple_upperTuple _
    (relabel_skew (ofTuple q) p
      (ofSix_skew (q 0) (q 1) (q 2) (q 3) (q 4) (q 5)))

theorem maInvariant_relabel (q : SixTuple) (p : Relabeling 4) :
    maInvariant (relabelSix q p) = maInvariant q := by
  apply bool_eq_of_true_iff
  rw [maInvariant_MA_iff (relabelSix q p), maInvariant_MA_iff q,
    relabelSix_matrix]
  exact MA_relabel_iff (ofTuple q) p

/-- The upper six coordinates after reversing every arrow. -/
def reverseSix (q : SixTuple) : SixTuple :=
  upperTuple (reverse (ofTuple q))

theorem reverseSix_coordinates (q : SixTuple) (i : Fin 6) :
    reverseSix q i = -(q i) := by
  fin_cases i <;> rfl

theorem reverseSix_matrix (q : SixTuple) :
    ofTuple (reverseSix q) = reverse (ofTuple q) := by
  exact ofTuple_upperTuple _
    (reverse_skew (ofTuple q)
      (ofSix_skew (q 0) (q 1) (q 2) (q 3) (q 4) (q 5)))

theorem maInvariant_reverse (q : SixTuple) :
    maInvariant (reverseSix q) = maInvariant q := by
  apply bool_eq_of_true_iff
  rw [maInvariant_MA_iff (reverseSix q), maInvariant_MA_iff q,
    reverseSix_matrix]
  exact MA_reverse_iff (ofTuple q)
    (ofSix_skew (q 0) (q 1) (q 2) (q 3) (q 4) (q 5))

#print axioms maInvariant
#print axioms maInvariant_MA_iff
#print axioms maInvariant_NMA_iff
#print axioms maInvariant_mutation
#print axioms maInvariant_word
#print axioms maInvariant_relabel
#print axioms maInvariant_reverse

end Rank4Round6.Foundations
