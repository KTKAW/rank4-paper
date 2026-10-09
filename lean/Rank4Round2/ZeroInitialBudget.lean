import Rank4Round2.ZeroUniformProgress
import Rank4CoordinatorR2.ScalarPathBudget

/-! Zero-pivot strict peaks in actual witnesses are reduced above the
computed initial endpoint budget. A total-proper class is supplied only by
the explicit MA bridge; its scalar is transported along the actual reverse
prefix, bounded by the six input scalars, and identified in the zero cone.
-/
namespace Rank4Round2.ZeroInitialBudget
open QuiverProofs Rank4Coordinator Rank4CoordinatorR2 Rank4Round2
open ProperOrder ProperMutation ProperObstructionSoundness
open Rank4ReviewRound2.PeakNormalization

theorem normalized_zero_scalar_le_input
    (hExist : MAHasTotalProper4)
    (Q : Matrix 4) (hs : SkewSymmetric Q) (lead : List (Fin 4))
    (i j : Fin 4) (hij : i≠j) (H : Nat)
    (hi : HeightLe (mutate (applyWord Q lead) i) H)
    (hj : HeightLe (mutate (applyWord Q lead) j) H)
    (hout : ¬HeightLe (applyWord Q lead) H)
    (hz : applyWord Q lead i j=0) (hma : MutationAcyclic (applyWord Q lead)) :
    ZeroUniformGuard.normalizedScalar (applyWord Q lead) i j≤(scalarBudget Q:Int) := by
  let B := applyWord Q lead
  have hsB : SkewSymmetric B := word_preserves_skew Q lead hs
  obtain ⟨p,r,a,b,c,d,e,f,hpr,_,ha,_,hb,hc,hd,he,hf,hrep,_,_⟩ :=
    strict_peak_normalization B hsB i j hij H hi hj hout
  have ha0 : a=0 := by simpa [B,hz] using ha
  rw [ha0] at hrep
  have hQ : signedFrame B p r=zeroPeak b c d e f := hrep
  obtain ⟨q,hq⟩ := hExist (signedFrame B p r) (signedFrame_skew B hsB p r)
    ((signedFrame_MA B hsB p r).mpr hma)
  have hq' : TotalProper (zeroPeak b c d e f) q := by rwa [hQ] at hq
  have hv := zeroPeak_proper_markov b c d e f hb hc hd he (by omega) q
    (totalProper_proper _ q hq')
  change orderMarkov (zeroPeak b c d e f) q=zeroMarkov b c d e f at hv
  have hbnd := ScalarPathBudget.lead_totalProper_scalar_budget Q hs lead p r q hq
  change (orderMarkov (signedFrame B p r) q).natAbs≤scalarBudget Q at hbnd
  rw [hQ,hv] at hbnd
  have hscalar : ZeroUniformGuard.normalizedScalar B i j=zeroMarkov b c d e f := by
    unfold ZeroUniformGuard.normalizedScalar
    rw [←hpr]
    change orderMarkov (signedFrame B p r) (order 0)=_
    rw [hQ,zeroMarkov_eq]
    rfl
  change ZeroUniformGuard.normalizedScalar B i j≤_
  rw [hscalar]
  have hle := Int.le_natAbs (a:=zeroMarkov b c d e f)
  omega

theorem zero_peak_initial_budget_progress
    (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4)
    (Q : Rank4Input) (lead tail : List (Fin 4))
    (i j : Fin 4) (hij : i≠j) (H K : Nat)
    (hBudget : endpointHeightBudget Q≤H) (hHK : H≤K)
    (hLeft : HeightLe (applyWord Q.val lead) H)
    (hRight : HeightLe (mutate (mutate (applyWord Q.val lead) i) j) H)
    (hParent : ¬HeightLe (mutate (applyWord Q.val lead) i) H)
    (hz : mutate (applyWord Q.val lead) i i j=0)
    (hPath : PrefixHeightLe Q.val (lead++([i,j]++tail)) K)
    (ha : Acyclic (applyWord Q.val (lead++([i,j]++tail)))) :
    PrefixHeightLe Q.val (lead++([j,i]++tail)) K ∧
      Acyclic (applyWord Q.val (lead++([j,i]++tail))) ∧
      overCount Q.val (lead++([j,i]++tail)) H + 1 =
        overCount Q.val (lead++([i,j]++tail)) H := by
  let B := mutate (applyWord Q.val lead) i
  have hL : mutate B i=applyWord Q.val lead := mutation_involutive _ i
  have haLocal : Acyclic (applyWord (mutate B i) ([i,j]++tail)) := by
    rw [hL]
    rwa [applyWord_append] at ha
  have hmaB : MutationAcyclic B :=
    (mutationAcyclic_iff B i).mp ⟨[i,j]++tail,haLocal⟩
  have he : applyWord Q.val (lead++[i])=B := by
    simp only [applyWord_append,applyWord]; rfl
  have hscalar := normalized_zero_scalar_le_input hExist Q.val Q.property
    (lead++[i]) i j hij H (by rwa [he,hL]) (by rwa [he])
    (by rwa [he]) (by rwa [he]) (by rwa [he])
  rw [he] at hscalar
  have hM : ZeroUniformGuard.normalizedScalar B i j≤(H:Int) := by
    unfold endpointHeightBudget at hBudget
    omega
  exact ZeroUniformProgress.zero_superscalar_peak_in_witness_progress
    hExist hEnd Q.val Q.property lead tail i j hij H K hHK
    hLeft hRight hParent hz hM hPath ha

#print axioms normalized_zero_scalar_le_input
#print axioms zero_peak_initial_budget_progress
end Rank4Round2.ZeroInitialBudget
