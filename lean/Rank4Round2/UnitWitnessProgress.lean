import Rank4Round2.UnitOrderedBounds

/-! Insert an actual strict unit detour after an arbitrary lead of an
acyclicizing witness. It preserves the supplied whole-path ceiling and drops
the over-H count by exactly one. Properness bridges remain explicit.
-/
namespace Rank4Round2
open QuiverProofs Rank4Coordinator Census ProperObstructionSoundness
open Rank4ReviewRound2.PeakNormalization

theorem unit_peak_in_witness_progress
    (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4)
    (Q : Matrix 4) (hs : SkewSymmetric Q) (lead tail : List (Fin 4))
    (i j : Fin 4) (hij : i≠j) (H K : Nat) (hHK : H≤K)
    (hLeft : HeightLe (applyWord Q lead) H)
    (hRight : HeightLe (mutate (mutate (applyWord Q lead) i) j) H)
    (hParent : ¬HeightLe (mutate (applyWord Q lead) i) H)
    (hunit : |mutate (applyWord Q lead) i i j|=1)
    (hPath : PrefixHeightLe Q (lead++([i,j]++tail)) K)
    (ha : Acyclic (applyWord Q (lead++([i,j]++tail)))) :
    ∃ (p : Relabeling 4) (r : Bool),
      (p,r)=normalizationFrame (mutate (applyWord Q lead) i) i j ∧
      PrefixHeightLe Q (lead++orderedUnitWord p i tail) K ∧
      Acyclic (applyWord Q (lead++orderedUnitWord p i tail)) ∧
      overCount Q (lead++orderedUnitWord p i tail) H + 1 =
        overCount Q (lead++([i,j]++tail)) H := by
  let B := mutate (applyWord Q lead) i
  have hsB : SkewSymmetric B := mutation_preserves_skew _ i (word_preserves_skew Q lead hs)
  have hL : mutate B i=applyWord Q lead := mutation_involutive _ i
  have haLocal : Acyclic (applyWord (mutate B i) ([i,j]++tail)) := by
    rw [hL]
    rwa [applyWord_append] at ha
  have hmaB : MutationAcyclic B :=
    (mutationAcyclic_iff B i).mp ⟨[i,j]++tail,haLocal⟩
  obtain ⟨p,r,hframe,_,hall⟩ := unit_strict_peak_ordered_bounded_progress hExist hEnd
    B hsB hmaB i j hij H (by rwa [hL]) hRight hParent hunit
  have hstats := hall tail
  obtain ⟨hPrefix,hSuffix⟩ := (prefixHeight_append_iff Q lead ([i,j]++tail) K).mp hPath
  have hnewBound := hstats.2.2 K hHK (by rwa [hL])
  have hnewAcyclic := hstats.2.1 haLocal
  refine ⟨p,r,hframe,?_,?_,?_⟩
  · apply prefixHeight_append Q lead _ K hPrefix
    rwa [←hL]
  · rw [applyWord_append,←hL]
    exact hnewAcyclic
  · rw [overCount_append,overCount_append,←hL]
    omega

#print axioms unit_peak_in_witness_progress
end Rank4Round2
