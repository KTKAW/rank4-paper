import QuiverProofs.Disconnected

/-!
# Direct polynomial sign formula for disconnected rank-four quivers

All definitions inspect only the six original integer entries. The decision
rule is a fixed finite Boolean combination of polynomial equalities and
inequalities. The result is restricted to disconnected support.
-/

namespace Rank4Construction
open QuiverProofs

/-- The seven possible nontrivial support cuts of a four-vertex input. -/
def DisconnectedSix (a b c d e f : Int) : Prop :=
  (a = 0 ∧ b = 0 ∧ c = 0) ∨
  (a = 0 ∧ d = 0 ∧ e = 0) ∨
  (b = 0 ∧ d = 0 ∧ f = 0) ∨
  (c = 0 ∧ e = 0 ∧ f = 0) ∨
  (b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0) ∨
  (a = 0 ∧ c = 0 ∧ d = 0 ∧ f = 0) ∨
  (a = 0 ∧ b = 0 ∧ e = 0 ∧ f = 0)

/-- A signed cyclic triangle in the non-mutation-acyclic Markov region.
This formula contains only polynomial arithmetic and comparisons. -/
def BadTriangle (x y z : Int) : Prop :=
  (2 ≤ x ∧ 2 ≤ y ∧ 2 ≤ z ∧ x^2 + y^2 + z^2 - x*y*z ≤ 4) ∨
  (2 ≤ -x ∧ 2 ≤ -y ∧ 2 ≤ -z ∧
    (-x)^2 + (-y)^2 + (-z)^2 - (-x)*(-y)*(-z) ≤ 4)

/-- Four induced triangle tests, computed directly from the six entries. -/
def BadTriangleSix (a b c d e f : Int) : Prop :=
  BadTriangle a d (-b) ∨ BadTriangle a e (-c) ∨
  BadTriangle b f (-c) ∨ BadTriangle d f (-e)

theorem badTriangle_iff_signed (x y z : Int) :
    BadTriangle x y z ↔ SignedTriangleRegion x y z := by
  rfl

/-- Exact direct formula for every disconnected integral four-vertex quiver.
The hypothesis is itself a finite algebraic sign condition. -/
theorem disconnected_NMA_formula (a b c d e f : Int)
    (hcut : DisconnectedSix a b c d e f) :
    ¬ MutationAcyclic (ofSix a b c d e f) ↔
      BadTriangleSix a b c d e f := by
  have hs : SkewSymmetric (ofSix a b c d e f) := ofSix_skew a b c d e f
  have hc : DisconnectedCut (ofSix a b c d e f) := by
    simpa only [DisconnectedSix, DisconnectedCut, ofSix] using hcut
  have hd : DisconnectedSupport (ofSix a b c d e f) :=
    disconnected_cut_support _ hs hc
  simpa only [BadTriangleSix, TriangleObstruction4, ofSix,
    ← badTriangle_iff_signed] using disconnected_NMA_iff (ofSix a b c d e f) hs hd

/-- The same disconnected criterion in the MA direction. -/
theorem disconnected_MA_formula (a b c d e f : Int)
    (hcut : DisconnectedSix a b c d e f) :
    MutationAcyclic (ofSix a b c d e f) ↔
      ¬ BadTriangleSix a b c d e f := by
  have h := disconnected_NMA_formula a b c d e f hcut
  constructor
  · intro hMA hBad
    exact (h.mpr hBad) hMA
  · intro hNoBad
    apply Classical.byContradiction
    intro hNotMA
    exact hNoBad (h.mp hNotMA)

#print axioms disconnected_NMA_formula
#print axioms disconnected_MA_formula

end Rank4Construction
