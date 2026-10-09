import Rank4Round8.Arithmetic.AlternatingLineParity

/-!
A direct arithmetic fast path on actual six-tuple inputs. It recognizes the
exact nonnegative alternating ray using six integer comparisons and returns
the proved parity label. `none` means the input lies outside this ray; no
classification is inferred there.
-/

namespace Rank4Round8.Arithmetic

open Rank4Formula Rank7Adversarial QuiverProofs

def OnAlternatingLine (q : SixTuple) : Prop :=
  q 0 = -2 ∧ q 1 = q 2 + 2 ∧ q 3 = -(q 2) ∧
    q 4 = 2 - q 2 ∧ q 5 = 0 ∧ 0 ≤ q 2

instance (q : SixTuple) : Decidable (OnAlternatingLine q) := by
  unfold OnAlternatingLine
  infer_instance

theorem onAlternatingLine_iff (q : SixTuple) :
    OnAlternatingLine q ↔ ∃ t : Nat, q = alternatingLine t := by
  constructor
  · rintro ⟨h0, h1, h3, h4, h5, hn⟩
    have hnat : (((q 2).toNat : Nat) : Int) = q 2 :=
      Int.toNat_of_nonneg hn
    refine ⟨(q 2).toNat, ?_⟩
    funext i
    fin_cases i <;>
      simp [alternatingLine, h0, h1, h3, h4, h5, hnat] <;> omega
  · rintro ⟨t, rfl⟩
    simp [OnAlternatingLine, alternatingLine, add_comm]

/-- `none` is an honest unknown result for inputs outside this ray. -/
def classifyLineTuple (q : SixTuple) : Option Bool :=
  if OnAlternatingLine q then
    some (classifyAlternatingLine (q 2).toNat)
  else none

theorem classifyLineTuple_isSome_iff (q : SixTuple) :
    classifyLineTuple q ≠ none ↔ OnAlternatingLine q := by
  by_cases h : OnAlternatingLine q <;> simp [classifyLineTuple, h]

theorem classifyLineTuple_spec (q : SixTuple) (b : Bool)
    (h : classifyLineTuple q = some b) :
    b = true ↔ MutationAcyclic (ofTuple q) := by
  by_cases hOn : OnAlternatingLine q
  · obtain ⟨t, ht⟩ := (onAlternatingLine_iff q).mp hOn
    have hparam : (q 2).toNat = t := by
      rw [ht]
      simp [alternatingLine]
    have hq' : q = alternatingLine (q 2).toNat := by
      rw [hparam]
      exact ht
    simp [classifyLineTuple, hOn] at h
    cases h
    rw [hq']
    exact classifyAlternatingLine_iff (q 2).toNat
  · simp [classifyLineTuple, hOn] at h

#print axioms onAlternatingLine_iff
#print axioms classifyLineTuple_spec

end Rank4Round8.Arithmetic
