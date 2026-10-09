import Rank4Round2.ZeroWeakExits
import Rank4ReviewRound2.ZeroWeakBlock

/-! The reviewed dominance reduction discharges every phase-zero/one/two/three
outward root guard in either nonunit residual block, including swapped phases.
Phase four/nine and unit residuals remain explicit boundaries.
-/
namespace Rank4Round2.ZeroWeakConsumers
open QuiverProofs Rank4Coordinator Rank4Round2 ProperObstructionSoundness

private theorem ten (i : Fin 10) :
    i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 := by omega

theorem nonunit_outward_roots (c d e w : Int)
    (hc : 2≤c) (hd : 2≤d) (hw : 2≤w) (hde : d<e) (hec : e<c)
    (i : Fin 10) (h4 : i≠4) (h9 : i≠9) :
    Regions.IsRoot (mutate (UnitZeroStrip.node d c e w i) 2) 2 := by
  have he : 2≤e := by omega
  have hf : 2≤c+w := by omega
  have hdf : d<c+w := by omega
  have hprod := Int.mul_le_mul_of_nonneg_right hd (show 0≤c+w by omega)
  have hE : c+w<d*(c+w)-e := by omega
  have h0 := Rank4ReviewRound2.ZeroWeakBlock.phase_zero_root d c e w hc he hw hde
  have h1 := ZeroWeakExits.phase_one_root c d e w hc (by omega) he hf hdf
  have h2 := ZeroWeakExits.phase_two_root c d e w (by omega) hw hf hdf (by omega)
  have h3 := ZeroWeakExits.phase_three_root c d e w hc hw (by omega) (by omega)
  have hswap (j : Fin 10)
      (h : Regions.IsRoot (mutate (UnitZeroStrip.node d c e w j) 2) 2) :
      Regions.IsRoot (mutate (UnitZeroStrip.node d c e w (UnitZeroStrip.swapPhase j)) 2) 2 := by
    rw [UnitZeroStrip.swapped,mutate_relabel]
    exact Regions.IsRoot.relabelled h UnitZeroStrip.sigma
  rcases ten i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact False.elim (h4 rfl)
  · exact hswap 0 h0
  · exact hswap 1 h1
  · exact hswap 2 h2
  · exact hswap 3 h3
  · exact False.elim (h9 rfl)

theorem actual_MA_overflow_roots
    (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4)
    (c d e f : Int) (H : Nat) (hc : 2≤c) (hd : 0<d) (he : 0<e)
    (h0 : HeightLe (mutate (zeroPeak 1 c d e f) 0) H)
    (h1 : HeightLe (mutate (zeroPeak 1 c d e f) 1) H)
    (hf : (H:Int)<f) (hover : f+(H:Int)<c+d*e)
    (hma : MutationAcyclic (zeroPeak 1 c d e f)) :
    d<e ∧ e<c ∧ ∀ w : Int, (w=f-c ∨ w=d*e-f) → 2≤w →
      ∀ i : Fin 10, i≠4 → i≠9 →
        Regions.IsRoot (mutate (UnitZeroStrip.node d c e w i) 2) 2 := by
  have ho := Rank4ReviewRound2.ZeroUnitDominance.zero_unit_MA_overflow_dominance
    hExist hEnd c d e f H hc hd he h0 h1 hf hover hma
  have heH := h0 1 3
  have hcH := h0 0 3
  rw [zeroPeak_zero 1 c d e f (by decide) (by omega)] at heH hcH
  simp only [ofSix] at heH hcH
  have hd2 : 2≤d := by
    by_contra hn
    have hd1 : d=1 := by omega
    rw [hd1] at hover
    simp only [one_mul] at hover
    omega
  refine ⟨ho.1,ho.2,?_⟩
  intro w _ hw i h4 h9
  exact nonunit_outward_roots c d e w hc hd2 hw ho.1 ho.2 i h4 h9

#print axioms nonunit_outward_roots
#print axioms actual_MA_overflow_roots
end Rank4Round2.ZeroWeakConsumers
