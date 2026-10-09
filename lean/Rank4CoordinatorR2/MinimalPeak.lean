import Rank4CoordinatorR2.MinimalWitness
import Rank4Round2.UnitWitnessProgress
import Rank4Round2.ZeroWitnessProgress

/-! Exact residual obligations for an isolated strict peak in a legally
selected witness. The known properness bridges remain explicit. Equal-height
blocks are not covered by these local statements. -/
namespace Rank4CoordinatorR2
open QuiverProofs Rank4Coordinator Rank4Round2 ProperObstructionSoundness

theorem profile_minimal_no_unit_peak
    (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4)
    (Q : Matrix 4) (hs : SkewSymmetric Q) (M : Nat) (w : List (Fin 4))
    (ha : Acyclic (applyWord Q w)) (hh : PrefixHeightLe Q w M)
    (hcount : ∀ v, Acyclic (applyWord Q v) → PrefixHeightLe Q v M →
      overCount Q w (M-1)≤overCount Q v (M-1))
    (lead tail : List (Fin 4)) (i j : Fin 4) (hij : i≠j)
    (hw : w=lead++([i,j]++tail))
    (hLeft : HeightLe (applyWord Q lead) (M-1))
    (hRight : HeightLe (mutate (mutate (applyWord Q lead) i) j) (M-1))
    (hParent : ¬HeightLe (mutate (applyWord Q lead) i) (M-1)) :
    |mutate (applyWord Q lead) i i j|≠1 := by
  intro hunit
  rw [hw] at ha hh hcount
  obtain ⟨p,r,_,hnew,hanew,hdrop⟩ := unit_peak_in_witness_progress
    hExist hEnd Q hs lead tail i j hij (M-1) M (by omega)
    hLeft hRight hParent hunit hh ha
  have hmin := hcount (lead++orderedUnitWord p i tail) hanew hnew
  omega

theorem profile_minimal_zero_peak_has_small_incident
    (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4)
    (Q : Matrix 4) (hs : SkewSymmetric Q) (M : Nat) (w : List (Fin 4))
    (ha : Acyclic (applyWord Q w)) (hh : PrefixHeightLe Q w M)
    (hcount : ∀ v, Acyclic (applyWord Q v) → PrefixHeightLe Q v M →
      overCount Q w (M-1)≤overCount Q v (M-1))
    (lead tail : List (Fin 4)) (i j : Fin 4) (hij : i≠j)
    (hw : w=lead++([i,j]++tail))
    (hLeft : HeightLe (applyWord Q lead) (M-1))
    (hRight : HeightLe (mutate (mutate (applyWord Q lead) i) j) (M-1))
    (hParent : ¬HeightLe (mutate (applyWord Q lead) i) (M-1))
    (hz : mutate (applyWord Q lead) i i j=0) :
    ¬ (∀ l : Fin 4, l≠i → l≠j →
      2≤|mutate (applyWord Q lead) i i l| ∧
      2≤|mutate (applyWord Q lead) i j l|) := by
  intro hInc
  rw [hw] at ha hh hcount
  obtain ⟨hnew,hanew,hdrop⟩ := zero_min2_peak_in_witness_progress
    hExist hEnd Q hs lead tail i j hij (M-1) M (by omega)
    hLeft hRight hParent hz hInc hh ha
  have hmin := hcount (lead++([j,i]++tail)) hanew hnew
  omega

#print axioms profile_minimal_no_unit_peak
#print axioms profile_minimal_zero_peak_has_small_incident
end Rank4CoordinatorR2
