import Rank4ReviewRound2.ZeroPairBlock

/-! A legal minimum of the over-height count cannot contain a constant
zero-pair excursion above the computed initial budget. This only eliminates
the stated actual subword; pivot-switching decomposition is separate.+-/
namespace Rank4ReviewRound2.ZeroPairMinimal
open QuiverProofs Rank4Coordinator Rank4Round2 Rank4CoordinatorR2
open ProperObstructionSoundness

theorem no_constant_zero_excursion
    (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4)
    (Q : Rank4Input) (M : Nat) (w : List (Fin 4))
    (ha : Acyclic (applyWord Q.val w)) (hh : PrefixHeightLe Q.val w M)
    (hcount : ∀ v, Acyclic (applyWord Q.val v) → PrefixHeightLe Q.val v M →
      overCount Q.val w (M-1)≤overCount Q.val v (M-1))
    (hBudget : endpointHeightBudget Q≤M-1)
    (lead old tail : List (Fin 4)) (i j : Fin 4) (hij : i≠j)
    (hw : w=lead++(old++tail)) (hz : applyWord Q.val lead i j=0)
    (hp : ∀ k∈old,k=i ∨ k=j)
    (hLeft : HeightLe (applyWord Q.val lead) (M-1))
    (hRight : HeightLe (applyWord Q.val (lead++old)) (M-1)) :
    overCount (applyWord Q.val lead) old (M-1)=0 := by
  have ha' := ha
  have hh' := hh
  rw [hw] at ha' hh'
  have hend : HeightLe (applyWord (applyWord Q.val lead) old) (M-1) := by
    rwa [applyWord_append] at hRight
  obtain ⟨new,_,hnew,hanew,hdrop⟩ := ZeroPairBlock.witness_progress
    hExist hEnd Q lead old tail i j hij (M-1) M hBudget (by omega)
    hLeft hz hp hend hh' ha'
  have hmin := hcount (lead++(new++tail)) hanew hnew
  rw [hw] at hmin
  omega

#print axioms no_constant_zero_excursion
end Rank4ReviewRound2.ZeroPairMinimal
