import Rank4CoordinatorR2.MinimalPeak
import Rank4CoordinatorR2.UnitBlock
import Rank4StructureRound2.InitialPeakBudget
import Rank4Round2.ZeroInitialBudget

/-! A legally profile-minimal actual witness above the original computed
endpoint budget has no isolated top point and no constant-unit-pair top
excursion. Maximal blocks with changed pivots remain a separate obligation. -/
namespace Rank4CoordinatorR2.MinimalSuperscalar
open QuiverProofs Rank4Coordinator Rank4CoordinatorR2 Rank4Round2
open ProperObstructionSoundness

theorem no_isolated_peak (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4)
    (Q : Rank4Input) (M : Nat) (w : List (Fin 4))
    (ha : Acyclic (applyWord Q.val w)) (hh : PrefixHeightLe Q.val w M)
    (hcount : ∀ v, Acyclic (applyWord Q.val v) → PrefixHeightLe Q.val v M →
      overCount Q.val w (M-1)≤overCount Q.val v (M-1))
    (hbudget : endpointHeightBudget Q≤M-1)
    (lead tail : List (Fin 4)) (i j : Fin 4) (hij : i≠j)
    (hw : w=lead++([i,j]++tail))
    (hLeft : HeightLe (applyWord Q.val lead) (M-1))
    (hRight : HeightLe (mutate (mutate (applyWord Q.val lead) i) j) (M-1))
    (hParent : ¬HeightLe (mutate (applyWord Q.val lead) i) (M-1)) : False := by
  have hma : MutationAcyclic Q.val := ⟨w,ha⟩
  have he : applyWord Q.val (lead++[i])=mutate (applyWord Q.val lead) i := by
    simp only [applyWord_append,applyWord]
  have hpair := Rank4StructureRound2.InitialPeakBudget.endpoint_budget_strict_peak_pair_small
    hExist hEnd Q hma (lead++[i]) i j hij (M-1) hbudget
    (by rw [he,mutation_involutive]; exact hLeft)
    (by rwa [he]) (by rwa [he])
  rw [he] at hpair
  by_cases hz : mutate (applyWord Q.val lead) i i j=0
  · have ha' := ha
    have hh' := hh
    rw [hw] at ha' hh'
    obtain ⟨hnew,hanew,hdrop⟩ := ZeroInitialBudget.zero_peak_initial_budget_progress
      hExist hEnd Q lead tail i j hij (M-1) M hbudget (by omega)
      hLeft hRight hParent hz hh' ha'
    have hmin := hcount (lead++([j,i]++tail)) hanew hnew
    rw [hw] at hmin
    omega
  · have hp : 0<abs (mutate (applyWord Q.val lead) i i j) := abs_pos.mpr hz
    have hu : abs (mutate (applyWord Q.val lead) i i j)=1 := by omega
    exact profile_minimal_no_unit_peak hExist hEnd Q.val Q.property M w ha hh hcount
      lead tail i j hij hw hLeft hRight hParent hu

theorem no_constant_unit_excursion (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4)
    (Q : Rank4Input) (M : Nat) (w : List (Fin 4))
    (ha : Acyclic (applyWord Q.val w)) (hh : PrefixHeightLe Q.val w M)
    (hcount : ∀ v, Acyclic (applyWord Q.val v) → PrefixHeightLe Q.val v M →
      overCount Q.val w (M-1)≤overCount Q.val v (M-1))
    (lead old tail : List (Fin 4)) (i j : Fin 4) (hij : i≠j)
    (hw : w=lead++(old++tail)) (hu : abs (applyWord Q.val lead i j)=1)
    (hp : ∀ k∈old,k=i ∨ k=j)
    (hLeft : HeightLe (applyWord Q.val lead) (M-1))
    (hRight : HeightLe (applyWord Q.val (lead++old)) (M-1))
    (hover : 0<overCount (applyWord Q.val lead) old (M-1)) : False := by
  have ha' := ha
  have hh' := hh
  rw [hw] at ha' hh'
  obtain ⟨new,p,_,hnew,hanew,hdrop⟩ := UnitBlock.unit_block_in_witness_progress
    hExist hEnd Q.val Q.property lead old tail i j hij hu hp (M-1) M (by omega)
    hLeft hRight hh' ha' hover
  have hmin := hcount (lead++(new++tail.map p.invFun)) hanew hnew
  rw [hw] at hmin
  omega

#print axioms no_isolated_peak
#print axioms no_constant_unit_excursion
end Rank4CoordinatorR2.MinimalSuperscalar
