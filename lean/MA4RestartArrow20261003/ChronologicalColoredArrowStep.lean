import MA4RestartArrow20261003.CurrentColoredActualFrame
import MA4RestartArrow20261003.RedColoredFamily
import MA4RestartArrow20261003.GreenColoredFamily
import MA4RestartCoordinator20261003.ChronologicalIntervalSelector
import MA4RestartCoordinator20261003.SortedNextArrowProjection
namespace QuiverProofs.MA4RestartArrow20261003.ChronologicalColoredArrowStep
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open QuiverProofs MAExistenceLiterature MAExistenceCoefficients MAExistenceCompanions
open MAExistenceTeamBRootPositivity MAExistenceTeamDJointSeed MAExistenceSupportChronology
open MAExistenceTeamCTriangleOutside MAExistenceTeamCCertificateTransport
open MA4RestartWeightedQuiverModel MA4RestartFreePathProjectives MA4RestartModelExt MA4RestartResolvedModelEuler
open MA4RestartArrow20261003.AdjacentExceptionalFrame MA4RestartArrow20261003.SignedAdjacentLeftHom
open MA4RestartArrow20261003.ActualFrameChronology MA4RestartArrow20261003.ActualLeftSweep
open MA4RestartArrow20261003.LeftFamilyFrame MA4RestartArrow20261003.LeftTracedReplacement
open MA4RestartArrow20261003.CurrentColoredActualFrame
open MA4RestartArrow20261003.RedColoredFamily MA4RestartArrow20261003.GreenColoredFamily
open MA4RestartChronologicalIntervalSelector MA4RestartSortedNextArrowProjection MA4RestartOldUnselectedPivotBoundary
set_option maxHeartbeats 0
local instance actualHasExt (B : Matrix 4) (K : Type) [Field K] :
    HasExt.{0} (Representation B K) := representation_hasExt B K
local instance actualEnoughProjectives (B : Matrix 4) (K : Type) [Field K] :
    EnoughProjectives (Representation B K) := representation_enoughProjectives B K
local instance actualFiniteBiproducts (B : Matrix 4) (K : Type) [Field K] :
    HasFiniteBiproducts (Representation B K) := Abelian.hasFiniteBiproducts

theorem principalSeed_red_next_arrowSigns
    (B₀ U : Matrix 4) (K : Type) [Field K] (hB₀ : SkewSymmetric B₀)
    (hs : Cosquare.add U (Cosquare.transpose U) = initialCompanion B₀)
    (ha : Cosquare.add U (Cosquare.scale (-1) (Cosquare.transpose U)) = reverse B₀)
    (w : List (Fin 4)) (hInv : SeedInv B₀ w)
    (hOld : UnorderedActualRealization (vertexFunctor B₀ K) (principalSeed B₀ w).2)
    (k : Fin 4) (hk : columnColor (principalSeed B₀ w).2 k = false) :
    ArrowSigns (principalSeed B₀ (w ++ [k])).1
      (coefficientCompanion B₀ (principalSeed B₀ (w ++ [k])).2)
      (columnColor (principalSeed B₀ (w ++ [k])).2) := by
  obtain ⟨p,q,hqt,hCompat,hGBR,hNumeric,hEuler,hIn,hOut,hExact⟩ :=
    principalSeed_red_leftSweep_interval_signs B₀ U hB₀ hs ha w hInv k hk
  let D := columnRelabel (principalSeed B₀ w).2 p
  let t := p.invFun k
  let c := columnColor D
  obtain ⟨M,hM,hDim,hDims,hSame⟩ := current_normalized_colored_frame B₀ U K hB₀ hs ha
    w hInv hOld p hNumeric
  have hc : c t = false := by simpa only [c,D,t,columnColor,columnRelabel,p.right_inv] using hk
  have hBlock : ∀ a b, a < b → c a = false → c b = true → False := by
    intro a b hab hca hcb
    have h := hGBR (p.toFun b) (p.toFun a) hcb hca
    simp only [p.left_inv] at h
    omega
  have hSelected : ∀ i, q ≤ i → i < t → pairing U (column D i) (column D t) ≤ 0 := by
    intro i hqi hit
    have hi := hIn i hqi hit
    have he := hEuler i t hit
    have hsk := principalSeed_skew B₀ hB₀ w (p.toFun t) (p.toFun i)
    change (relabel (principalSeed B₀ w).1 p) t i = -(relabel (principalSeed B₀ w).1 p) i t at hsk
    change pairing U (column D i) (column D t) = -(relabel (principalSeed B₀ w).1 p) i t at he
    dsimp only [t,D] at hi he hsk ⊢
    omega
  have hOutsideGreen : ∀ a, a < q → c a = true → ∀ f : M a ⟶ M t, f = 0 := by
    intro a haq hca
    exact (red_unselected_before_left_endpoint B₀ K U hB₀ hs ha w hInv p hNumeric M hM
      hDim t q a hqt haq hOut).1
  have hOutsideRed : ∀ a, a < q → c a = false → Orthogonal (M a) (M t) := by
    intro a haq hca
    have h := red_unselected_before_left_endpoint B₀ K U hB₀ hs ha w hInv p hNumeric M hM
      hDim t q a hqt haq hOut
    exact ⟨h.1,(h.2 (hca.trans hc.symm)).1⟩
  obtain ⟨N,hN,hND,hNS,hNI⟩ := construct_terminal_colored_red_family B₀ U D K hB₀ hs ha
    M hM c hDims t q hqt hc hBlock hSame hSelected hOutsideGreen hOutsideRed
  dsimp only [D,t] at hND hNS hNI
  rw [hExact] at hND hNS hNI
  exact chronological_next_arrows_of_terminal_color_gates B₀ U K hB₀ hs ha w hInv k
    (p.trans (leftPermutation t q hqt)) N hN (fun a b => (hND a).2 b) hNS hNI

theorem principalSeed_green_next_arrowSigns
    (B₀ U : Matrix 4) (K : Type) [Field K] (hB₀ : SkewSymmetric B₀)
    (hs : Cosquare.add U (Cosquare.transpose U) = initialCompanion B₀)
    (ha : Cosquare.add U (Cosquare.scale (-1) (Cosquare.transpose U)) = reverse B₀)
    (w : List (Fin 4)) (hInv : SeedInv B₀ w)
    (hOld : UnorderedActualRealization (vertexFunctor B₀ K) (principalSeed B₀ w).2)
    (k : Fin 4) (hk : columnColor (principalSeed B₀ w).2 k = true) :
    ArrowSigns (principalSeed B₀ (w ++ [k])).1
      (coefficientCompanion B₀ (principalSeed B₀ (w ++ [k])).2)
      (columnColor (principalSeed B₀ (w ++ [k])).2) := by
  obtain ⟨p,q,htq,hCompat,hGBR,hNumeric,hEuler,hIn,hOut,hExact⟩ :=
    principalSeed_green_rightSweep_interval_signs B₀ U hB₀ hs ha w hInv k hk
  let D := columnRelabel (principalSeed B₀ w).2 p
  let t := p.invFun k
  let c := columnColor D
  obtain ⟨M,hM,hDim,hDims,hSame⟩ := current_normalized_colored_frame B₀ U K hB₀ hs ha
    w hInv hOld p hNumeric
  have hc : c t = true := by simpa only [c,D,t,columnColor,columnRelabel,p.right_inv] using hk
  have hBlock : ∀ a b, a < b → c a = false → c b = true → False := by
    intro a b hab hca hcb
    have h := hGBR (p.toFun b) (p.toFun a) hcb hca
    simp only [p.left_inv] at h
    omega
  have hSelected : ∀ i, t < i → i ≤ q → pairing U (column D t) (column D i) ≤ 0 := by
    intro i hti hiq
    have hi := hIn i hti hiq
    have he := hEuler t i hti
    change pairing U (column D t) (column D i) = -(relabel (principalSeed B₀ w).1 p) t i at he
    dsimp only [t,D] at hi he ⊢
    omega
  have hOutsideRed : ∀ b, q < b → c b = false → ∀ f : M t ⟶ M b, f = 0 := by
    intro b hqb hcb
    exact (green_unselected_after_right_endpoint B₀ K U hB₀ hs ha w hInv p hNumeric M hM
      hDim t q b htq hqb hOut).1
  have hOutsideGreen : ∀ b, q < b → c b = true → Orthogonal (M t) (M b) := by
    intro b hqb hcb
    have h := green_unselected_after_right_endpoint B₀ K U hB₀ hs ha w hInv p hNumeric M hM
      hDim t q b htq hqb hOut
    exact ⟨h.1,(h.2 (hc.trans hcb.symm)).1⟩
  obtain ⟨N,hN,hND,hNS,hNI⟩ := construct_terminal_colored_green_family B₀ U D K hB₀ hs ha
    M hM c hDims t q htq hc hBlock hSame hSelected hOutsideRed hOutsideGreen
  dsimp only [D,t] at hND hNS hNI
  rw [hExact] at hND hNS hNI
  exact chronological_next_arrows_of_terminal_color_gates B₀ U K hB₀ hs ha w hInv k
    (p.trans (rightPermutation t q htq)) N hN (fun a b => (hND a).2 b) hNS hNI

theorem principalSeed_next_arrowSigns
    (B₀ U : Matrix 4) (K : Type) [Field K] (hB₀ : SkewSymmetric B₀)
    (hs : Cosquare.add U (Cosquare.transpose U) = initialCompanion B₀)
    (ha : Cosquare.add U (Cosquare.scale (-1) (Cosquare.transpose U)) = reverse B₀)
    (w : List (Fin 4)) (hInv : SeedInv B₀ w)
    (hOld : UnorderedActualRealization (vertexFunctor B₀ K) (principalSeed B₀ w).2)
    (k : Fin 4) :
    ArrowSigns (principalSeed B₀ (w ++ [k])).1
      (coefficientCompanion B₀ (principalSeed B₀ (w ++ [k])).2)
      (columnColor (principalSeed B₀ (w ++ [k])).2) := by
  cases hk : columnColor (principalSeed B₀ w).2 k with
  | false => exact principalSeed_red_next_arrowSigns B₀ U K hB₀ hs ha w hInv hOld k hk
  | true => exact principalSeed_green_next_arrowSigns B₀ U K hB₀ hs ha w hInv hOld k hk
#print axioms principalSeed_red_next_arrowSigns
#print axioms principalSeed_green_next_arrowSigns
#print axioms principalSeed_next_arrowSigns
end QuiverProofs.MA4RestartArrow20261003.ChronologicalColoredArrowStep
