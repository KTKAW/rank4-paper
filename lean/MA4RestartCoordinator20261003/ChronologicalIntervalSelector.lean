import QuiverProofs.MAExistenceSupportChronology

/-! Exact chronological selectors retain BOTH interval sign gates together
with the actual next-column identity, from the SAME selected p and s.
This exposes old numeric data needed by the actual colored-family proof. -/
namespace QuiverProofs.MA4RestartChronologicalIntervalSelector
open MAExistenceLiterature MAExistenceCompanions MAExistenceCoefficients
open MAExistenceTeamDJointSeed MAExistenceTeamBRootPositivity
open MAExistenceAuxiliaryOrders MAExistenceTeamBAdjacentHurwitz
open MAExistenceTeamCCertificateTransport
open MAExistenceSupportChronology Cosquare
set_option maxHeartbeats 0
private theorem proper_ordered (B : Matrix 4) (p : ProperOrder.CyclicOrder)
    (k : Fin 4) (hp : ProperOrder.ProperVertex B p k) :
    ProperOrder.ProperVertex (relabel B p) (.identity 4) (p.invFun k) := by
  intro u v hut htv
  have hu : 0 < B (p.toFun u) k := by simpa [relabel, p.right_inv] using hut
  have hv : 0 < B k (p.toFun v) := by simpa [relabel, p.right_inv] using htv
  have hcyc := hp (p.toFun u) (p.toFun v) hu hv
  simpa only [ProperOrder.Between, p.left_inv, Relabeling.identity, id_eq] using hcyc

private theorem pairing_columnRelabel (U C : Matrix 4) (p : Relabeling 4) (i j : Fin 4) :
    pairing U (column (columnRelabel C p) i) (column (columnRelabel C p) j) =
      coefficientBilinear U C (p.toFun i) (p.toFun j) := by
  simp only [pairing, column, columnRelabel, coefficientBilinear, mul, transpose]
  ring

private theorem ordered_Euler_forward (B U C : Matrix 4) (p : Relabeling 4)
    (he : coefficientBilinear U C = MAExistenceTeamBOrderMutation.labeledUnipotent B p)
    (i j : Fin 4) (hij : i < j) :
    pairing U (column (columnRelabel C p) i) (column (columnRelabel C p) j) =
      -(relabel B p) i j := by
  have hne : p.toFun i ≠ p.toFun j := fun h => by have := p.injective h; omega
  rw [pairing_columnRelabel, he]
  simp [MAExistenceTeamBOrderMutation.labeledUnipotent, p.left_inv, hij, hne, relabel]


theorem principalSeed_green_rightSweep_interval_signs (B₀ U₀ : Matrix 4)
    (hB₀ : SkewSymmetric B₀)
    (hs₀ : add U₀ (transpose U₀) = initialCompanion B₀)
    (ha₀ : add U₀ (scale (-1) (transpose U₀)) = reverse B₀)
    (w : List (Fin 4)) (h : SeedInv B₀ w) (k : Fin 4)
    (hk : columnColor (principalSeed B₀ w).2 k = true) :
    ∃ (p : ProperOrder.CyclicOrder) (s : Fin 4) (hts : p.invFun k ≤ s),
      Compatible (principalSeed B₀ w).1 (columnColor (principalSeed B₀ w).2) k p ∧
      GreenBeforeRed (columnColor (principalSeed B₀ w).2) p ∧
      OrderedRootFrame B₀ U₀ (columnRelabel (principalSeed B₀ w).2 p) ∧
      (∀ a b, a < b → pairing U₀
        (column (columnRelabel (principalSeed B₀ w).2 p) a)
        (column (columnRelabel (principalSeed B₀ w).2 p) b) =
          -(relabel (principalSeed B₀ w).1 p) a b) ∧
      (∀ j, p.invFun k < j → j ≤ s → 0 ≤ (relabel (principalSeed B₀ w).1 p) (p.invFun k) j) ∧
      (∀ j, j ≠ p.invFun k → ¬ (p.invFun k < j ∧ j ≤ s) → (relabel (principalSeed B₀ w).1 p) (p.invFun k) j ≤ 0) ∧
      negateColumn (rightSweep U₀ (columnRelabel (principalSeed B₀ w).2 p)
        (p.invFun k) s) s =
        columnRelabel (principalSeed B₀ (w ++ [k])).2
          (p.trans (rightPermutation (p.invFun k) s hts)) := by
  let B := (principalSeed B₀ w).1
  let C := (principalSeed B₀ w).2
  have hB := principalSeed_skew B₀ hB₀ w
  have hc := seedInv_signCoherent B₀ hB₀ w h
  have hcol := MAExistenceAuxiliaryOrders.companion_colorAdmissible B _ hB
    h.companion.1 (columnColor C) h.arrowSigns h.admissible
  obtain ⟨p, hp, hcolors⟩ := MAExistenceAuxiliaryOrders.colorAdmissible_has_extensions
    B hB (columnColor C) hcol k
  have hproper := compatible_colorBlock_proper B (columnColor C) k p hp hcolors
  have hside : ∀ j, 0 < (relabel B p) (p.invFun k) j → p.invFun k < j := by
    intro j hj
    have hb : 0 < B k (p.toFun j) := by simpa [relabel, p.right_inv] using hj
    have hh : p.invFun k < p.invFun (p.toFun j) := by
      cases hcolor : columnColor C (p.toFun j)
      · exact hcolors k (p.toFun j) hk hcolor
      · exact hp k (p.toFun j) (Or.inl ⟨hb, by change columnColor C k = _ at hk; simp [hk, hcolor]⟩)
    simpa only [p.left_inv] using hh
  obtain ⟨s, hts, hin, hout⟩ := proper_green_has_rightInterval (relabel B p)
    (relabel_skew B p hB) (p.invFun k) (proper_ordered B p k hproper) hside
  have heuler := coefficientBilinear_eq_compatible B₀ U₀ B C hB hs₀ ha₀
    h.exchangeOrigin h.companion (columnColor C) h.arrowSigns k p hp
  have hg : ∀ a, 0 ≤ columnRelabel C p a (p.invFun k) := by
    simpa [columnRelabel, p.right_inv, C] using ((color_iff_green hc k).mp hk).1
  have he := green_rightSweep_coefficients U₀ (relabel B p) (columnRelabel C p)
    (p.invFun k) s hts hg (fun j hj => ordered_Euler_forward B U₀ C p heuler _ _ hj)
    hin hout
  have hn : (principalSeed B₀ (w ++ [k])).2 = mutateCoefficients B C k := by
    rw [principalSeed, evolve_append_singleton]
    rfl
  refine ⟨p, s, hts, hp, hcolors,
    seedInv_compatible_orderedRootFrame B₀ U₀ hB₀ hs₀ ha₀ w h k p hp,
    (fun a b hab => ordered_Euler_forward B U₀ C p heuler a b hab), hin, hout, ?_⟩
  rw [hn]
  rw [← columnRelabel_trans]
  have hrel := columnRelabel_mutateCoefficients B C p (p.invFun k)
  simp only [p.right_inv] at hrel
  rw [hrel]
  exact he

theorem principalSeed_red_leftSweep_interval_signs (B₀ U₀ : Matrix 4)
    (hB₀ : SkewSymmetric B₀)
    (hs₀ : add U₀ (transpose U₀) = initialCompanion B₀)
    (ha₀ : add U₀ (scale (-1) (transpose U₀)) = reverse B₀)
    (w : List (Fin 4)) (h : SeedInv B₀ w) (k : Fin 4)
    (hk : columnColor (principalSeed B₀ w).2 k = false) :
    ∃ (p : ProperOrder.CyclicOrder) (s : Fin 4) (hst : s ≤ p.invFun k),
      Compatible (principalSeed B₀ w).1 (columnColor (principalSeed B₀ w).2) k p ∧
      GreenBeforeRed (columnColor (principalSeed B₀ w).2) p ∧
      OrderedRootFrame B₀ U₀ (columnRelabel (principalSeed B₀ w).2 p) ∧
      (∀ a b, a < b → pairing U₀
        (column (columnRelabel (principalSeed B₀ w).2 p) a)
        (column (columnRelabel (principalSeed B₀ w).2 p) b) =
          -(relabel (principalSeed B₀ w).1 p) a b) ∧
      (∀ j, s ≤ j → j < p.invFun k → (relabel (principalSeed B₀ w).1 p) (p.invFun k) j ≤ 0) ∧
      (∀ j, j ≠ p.invFun k → ¬ (s ≤ j ∧ j < p.invFun k) → 0 ≤ (relabel (principalSeed B₀ w).1 p) (p.invFun k) j) ∧
      negateColumn (leftSweep U₀ (columnRelabel (principalSeed B₀ w).2 p)
        (p.invFun k) s) s =
        columnRelabel (principalSeed B₀ (w ++ [k])).2
          (p.trans (leftPermutation (p.invFun k) s hst)) := by
  let B := (principalSeed B₀ w).1
  let C := (principalSeed B₀ w).2
  have hB := principalSeed_skew B₀ hB₀ w
  have hc := seedInv_signCoherent B₀ hB₀ w h
  have hcol := MAExistenceAuxiliaryOrders.companion_colorAdmissible B _ hB
    h.companion.1 (columnColor C) h.arrowSigns h.admissible
  obtain ⟨p, hp, hcolors⟩ := MAExistenceAuxiliaryOrders.colorAdmissible_has_extensions
    B hB (columnColor C) hcol k
  have hproper := compatible_colorBlock_proper B (columnColor C) k p hp hcolors
  have hside : ∀ j, 0 < (relabel B p) j (p.invFun k) → j < p.invFun k := by
    intro j hj
    have hb : 0 < B (p.toFun j) k := by simpa [relabel, p.right_inv] using hj
    have hh : p.invFun (p.toFun j) < p.invFun k := by
      cases hcolor : columnColor C (p.toFun j)
      · exact hp (p.toFun j) k (Or.inl ⟨hb, by change columnColor C k = _ at hk; simp [hk, hcolor]⟩)
      · exact hcolors (p.toFun j) k hcolor hk
    simpa only [p.left_inv] using hh
  obtain ⟨s, hst, hin, hout⟩ := proper_red_has_leftInterval (relabel B p)
    (relabel_skew B p hB) (p.invFun k) (proper_ordered B p k hproper) hside
  have heuler := coefficientBilinear_eq_compatible B₀ U₀ B C hB hs₀ ha₀
    h.exchangeOrigin h.companion (columnColor C) h.arrowSigns k p hp
  have hr : ∀ a, columnRelabel C p a (p.invFun k) ≤ 0 := by
    simpa [columnRelabel, p.right_inv, C] using ((color_iff_red hc k).mp hk).1
  have he := red_leftSweep_coefficients U₀ (relabel B p) (columnRelabel C p)
    (relabel_skew B p hB) (p.invFun k) s hst hr
    (fun j hj => ordered_Euler_forward B U₀ C p heuler _ _ hj) hin hout
  have hn : (principalSeed B₀ (w ++ [k])).2 = mutateCoefficients B C k := by
    rw [principalSeed, evolve_append_singleton]
    rfl
  refine ⟨p, s, hst, hp, hcolors,
    seedInv_compatible_orderedRootFrame B₀ U₀ hB₀ hs₀ ha₀ w h k p hp,
    (fun a b hab => ordered_Euler_forward B U₀ C p heuler a b hab), hin, hout, ?_⟩
  rw [hn]
  rw [← columnRelabel_trans]
  have hrel := columnRelabel_mutateCoefficients B C p (p.invFun k)
  simp only [p.right_inv] at hrel
  rw [hrel]
  exact he
#check principalSeed_green_rightSweep_interval_signs
#check principalSeed_red_leftSweep_interval_signs
#print axioms principalSeed_green_rightSweep_interval_signs
#print axioms principalSeed_red_leftSweep_interval_signs
end QuiverProofs.MA4RestartChronologicalIntervalSelector
