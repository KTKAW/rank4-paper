import QuiverProofs.ProperObstructionSoundness
import Mathlib.Tactic.Linarith

/-! Necessary scalar bounds for connected topological endpoints. These
statements contain no MA-to-total-properness assumption and no reachability
or classification assertion. -/
namespace Rank4CoordinatorR2
open QuiverProofs QuiverProofs.Census QuiverProofs.ProperOrder
  QuiverProofs.ProperObstructionSoundness

private theorem small_connected_markov : ∀ a b c d e f : Fin 2,
    ConnectedSupport (ofSix a.val b.val c.val d.val e.val f.val) →
    3 ≤ Algebra.markov a.val b.val c.val d.val e.val f.val := by decide

/-- Every connected nonnegative integer tuple has scalar at least three.
Only the hypothetical low-scalar case is reduced to a finite unit box. -/
theorem connected_nonnegative_markov (a b c d e f : Int)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (he : 0 ≤ e) (hf : 0 ≤ f)
    (hconn : ConnectedSupport (ofSix a b c d e f)) :
    3 ≤ Algebra.markov a b c d e f := by
  by_contra h
  have hm : Algebra.markov a b c d e f < 3 := by omega
  obtain ⟨ha2,hb2,hc2,hd2,he2,hf2⟩ :=
    Algebra.coordinate_squares_le_markov a b c d e f ha hb hc hd he hf
  have ha1 : a ≤ 1 := by nlinarith [ha2]
  have hb1 : b ≤ 1 := by nlinarith [hb2]
  have hc1 : c ≤ 1 := by nlinarith [hc2]
  have hd1 : d ≤ 1 := by nlinarith [hd2]
  have he1 : e ≤ 1 := by nlinarith [he2]
  have hf1 : f ≤ 1 := by nlinarith [hf2]
  let aa : Fin 2 := ⟨a.toNat, by omega⟩
  let bb : Fin 2 := ⟨b.toNat, by omega⟩
  let cc : Fin 2 := ⟨c.toNat, by omega⟩
  let dd : Fin 2 := ⟨d.toNat, by omega⟩
  let ee : Fin 2 := ⟨e.toNat, by omega⟩
  let ff : Fin 2 := ⟨f.toNat, by omega⟩
  have ea : (aa.val : Int) = a := by dsimp [aa]; omega
  have eb : (bb.val : Int) = b := by dsimp [bb]; omega
  have ec : (cc.val : Int) = c := by dsimp [cc]; omega
  have ed : (dd.val : Int) = d := by dsimp [dd]; omega
  have eeq : (ee.val : Int) = e := by dsimp [ee]; omega
  have ef : (ff.val : Int) = f := by dsimp [ff]; omega
  have hsmall := small_connected_markov aa bb cc dd ee ff
  rw [ea,eb,ec,ed,eeq,ef] at hsmall
  exact h (hsmall hconn)

theorem connected_topological_markov (C : Matrix 4) (hC : SkewSymmetric C)
    (hconn : ConnectedSupport C) (q : CyclicOrder) (hq : Topological C q) :
    3 ≤ orderMarkov C q := by
  have hrec := ofSix_reconstruct (relabel C q) (relabel_skew C q hC)
  have hconnq := connected_relabel C q hconn
  rw [← hrec] at hconnq
  exact connected_nonnegative_markov _ _ _ _ _ _
    hq.1 hq.2.1 hq.2.2.1 hq.2.2.2.1 hq.2.2.2.2.1 hq.2.2.2.2.2 hconnq

#print axioms connected_nonnegative_markov
#print axioms connected_topological_markov
end Rank4CoordinatorR2
