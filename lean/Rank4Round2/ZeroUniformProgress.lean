import Rank4Round2.ZeroUniformGuard

/-! Insert the superscalar zero-pivot square after any actual witness prefix.
The endpoint and suffix remain identical, the supplied whole ceiling is
preserved, and the over-H count drops by one. Bridges remain explicit.
-/
namespace Rank4Round2.ZeroUniformProgress
open QuiverProofs Rank4Coordinator Rank4Round2 Census ProperObstructionSoundness

theorem zero_superscalar_peak_in_witness_progress
    (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4)
    (Q : Matrix 4) (hs : SkewSymmetric Q) (lead tail : List (Fin 4))
    (i j : Fin 4) (hij : i≠j) (H K : Nat) (hHK : H≤K)
    (hLeft : HeightLe (applyWord Q lead) H)
    (hRight : HeightLe (mutate (mutate (applyWord Q lead) i) j) H)
    (hParent : ¬HeightLe (mutate (applyWord Q lead) i) H)
    (hz : mutate (applyWord Q lead) i i j=0)
    (hScalar : ZeroUniformGuard.normalizedScalar (mutate (applyWord Q lead) i) i j≤(H:Int))
    (hPath : PrefixHeightLe Q (lead++([i,j]++tail)) K)
    (ha : Acyclic (applyWord Q (lead++([i,j]++tail)))) :
    PrefixHeightLe Q (lead++([j,i]++tail)) K ∧
      Acyclic (applyWord Q (lead++([j,i]++tail))) ∧
      overCount Q (lead++([j,i]++tail)) H + 1 =
        overCount Q (lead++([i,j]++tail)) H := by
  let B := mutate (applyWord Q lead) i
  have hsB : SkewSymmetric B := mutation_preserves_skew _ i (word_preserves_skew Q lead hs)
  have hL : mutate B i=applyWord Q lead := mutation_involutive _ i
  have haLocal : Acyclic (applyWord (mutate B i) ([i,j]++tail)) := by
    rw [hL]
    rwa [applyWord_append] at ha
  have hmaB : MutationAcyclic B :=
    (mutationAcyclic_iff B i).mp ⟨[i,j]++tail,haLocal⟩
  have hn := ZeroUniformGuard.arbitrary_zero_strict_guard hExist hEnd B hsB hmaB i j hij H
    (by rwa [hL]) hRight hParent hz hScalar
  have hend := zero_square_endpoint_at B hsB i j hij hz
  have hold : applyWord (mutate B i) [i,j]=mutate B j := by
    simp only [applyWord,mutation_involutive]
  have hcount : overCount (mutate B i) ([j,i]++tail) H+1=
      overCount (mutate B i) ([i,j]++tail) H := by
    have h := strict_peak_overCount B i j [j,i] tail (Relabeling.identity 4) H
      hParent hRight (by simpa only [relabel_identity] using hend) hn
    simpa [Relabeling.identity] using h
  obtain ⟨hPrefix,hSuffix⟩ := (prefixHeight_append_iff Q lead ([i,j]++tail) K).mp hPath
  have hOldBound : PrefixHeightLe (mutate B i) ([i,j]++tail) K := by rwa [hL]
  have ht := ((prefixHeight_append_iff (mutate B i) [i,j] tail K).mp hOldBound).2
  rw [hold] at ht
  have hNewBound : PrefixHeightLe (mutate B i) ([j,i]++tail) K := by
    apply prefixHeight_append _ [j,i] tail K (prefixHeight_mono _ _ H K hHK hn)
    rwa [hend]
  rw [applyWord_append,hold] at haLocal
  refine ⟨?_,?_,?_⟩
  · apply prefixHeight_append Q lead _ K hPrefix
    rwa [←hL]
  · rw [applyWord_append,←hL,applyWord_append,hend]
    exact haLocal
  · rw [overCount_append Q lead ([j,i]++tail),overCount_append Q lead ([i,j]++tail),←hL]
    omega

#print axioms zero_superscalar_peak_in_witness_progress
end Rank4Round2.ZeroUniformProgress
