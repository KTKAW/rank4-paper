import QuiverProofs.MAExistenceTeamDJointSeed

/-! Outside-pivot triangle interfaces.

The finite reductions were explicitly transferred by the MA closure coordinator
from the reviewed TriangleReview checkpoint, SHA256
476fc14d23af10a5408b72610a9d3af9e68527b8b4e1c49ec23b801bc8fd4d9f.
The unchanged-weight subsets below are proved from current data. In the mixed
case, the actual positive-root Euler exclusion is still an explicit supply
obligation; no initialization-and-preservation theorem is asserted here.
-/
namespace QuiverProofs.MAExistenceTeamCTriangleOutside
open QuiverProofs MAExistenceLiterature MAExistenceCompanions
open MAExistenceAuxiliaryOrders MAExistenceTeamBCompanionClosure
open MAExistenceCoefficients MAExistenceTeamDJointSeed
open MAExistenceTeamBRootPositivity MAExistenceTeamCRootSigns
open MAExistenceTeamCSeedStep MAExistenceTeamCCertificateTransport Cosquare
set_option maxHeartbeats 0
set_option maxRecDepth 1000

/-- Reverse precisely the arrows joining equally colored vertices. -/
def normalizedExchange (B : Matrix 4) (g : Colors) : Matrix 4 := fun i j =>
  if g i = g j then -B i j else B i j

def noDirectedTriangle (B : Matrix 4) (i j l : Fin 4) : Prop :=
  ¬ ((0 < B i j ∧ 0 < B j l ∧ 0 < B l i) ∨
     (B i j < 0 ∧ B j l < 0 ∧ B l i < 0))

/-- The finite color reduction has no weight bound; all zeros are included. -/
private theorem triangleColor_iff_no_normalized_cycle (B : Matrix 4)
    (hB : SkewSymmetric B) (g : Colors) (i j l : Fin 4) :
    triangleColorAdmissible B g i j l ↔
      noDirectedTriangle (normalizedExchange B g) i j l := by
  have hji := hB j i
  have hlj := hB l j
  have hil := hB i l
  cases hi : g i <;> cases hj : g j <;> cases hl : g l <;>
    by_cases h1 : 0 < B i j <;> by_cases h2 : 0 < B j l <;>
    by_cases h3 : 0 < B l i <;>
    simp [triangleColorAdmissible, positiveColorEdge, normalizedExchange,
      noDirectedTriangle, hi, hj, hl, h1, h2, h3] <;> omega

theorem triangleCompanion_iff_no_normalized_cycle (B A : Matrix 4)
    (hB : SkewSymmetric B) (hA : ∀ i j, A i j = A j i)
    (g : Colors) (hs : ArrowSigns B A g) (i j l : Fin 4) :
    triangleCompanionAdmissible B A i j l ↔
      noDirectedTriangle (normalizedExchange B g) i j l := by
  have hcolor : triangleCompanionAdmissible B A i j l ↔
      triangleColorAdmissible B g i j l := by
    constructor <;> intro h he1 he2 he3
    · rw [positiveColorEdge_companion B A hB hA g hs i j he1,
        positiveColorEdge_companion B A hB hA g hs j l he2,
        positiveColorEdge_companion B A hB hA g hs l i he3]
      exact h he1 he2 he3
    · have hc := h he1 he2 he3
      rw [positiveColorEdge_companion B A hB hA g hs i j he1,
        positiveColorEdge_companion B A hB hA g hs j l he2,
        positiveColorEdge_companion B A hB hA g hs l i he3] at hc
      exact hc
  exact hcolor.trans (triangleColor_iff_no_normalized_cycle B hB g i j l)

def colorSign (g : Colors) (i : Fin 4) : Int := if g i then 1 else -1

/-- Pullback Euler matrix after making each actual column positive. -/
def normalizedEuler (E : Matrix 4) (g : Colors) : Matrix 4 := fun i j =>
  colorSign g i * colorSign g j * E i j

def eulerArrow (E : Matrix 4) (i j : Fin 4) : Prop :=
  0 < E i j ∨ E j i < 0

/-- Convention check: the Hom/Ext Euler orientation reverses the monochromatic
exchange arrows. The factor two uses the repository's original labels. -/
theorem normalizedEuler_arrow (B A E : Matrix 4) (g : Colors)
    (hB : SkewSymmetric B) (hA : QuasiCartanCompanion B A)
    (hs : ArrowSigns B A g)
    (he : ∀ i j, 2 * E i j = A i j - B i j)
    (i j : Fin 4) (hij : i ≠ j) :
    eulerArrow (normalizedEuler E g) i j ↔
      0 < normalizedExchange B g i j := by
  have hb := hB j i
  have ha := hA.1 j i
  have heij := he i j
  have heji := he j i
  rcases Int.natAbs_eq_natAbs_iff.mp (hA.2.2 i j hij) with habs | habs
  · by_cases hp : 0 < B i j
    · have hsij := hs i j hp
      cases hi : g i <;> cases hj : g j <;>
        simp [normalizedEuler, colorSign, eulerArrow, normalizedExchange, hi, hj] <;>
        simp [hi, hj] at hsij <;> omega
    · by_cases hn : B i j < 0
      · have hrev : 0 < B j i := by omega
        have hsji := hs j i hrev
        cases hi : g i <;> cases hj : g j <;>
          simp [normalizedEuler, colorSign, eulerArrow, normalizedExchange, hi, hj] <;>
          simp [hi, hj] at hsji <;> omega
      · have hz : B i j = 0 := by omega
        cases hi : g i <;> cases hj : g j <;>
          simp [normalizedEuler, colorSign, eulerArrow, normalizedExchange, hi, hj] <;> omega
  · by_cases hp : 0 < B i j
    · have hsij := hs i j hp
      cases hi : g i <;> cases hj : g j <;>
        simp [normalizedEuler, colorSign, eulerArrow, normalizedExchange, hi, hj] <;>
        simp [hi, hj] at hsij <;> omega
    · by_cases hn : B i j < 0
      · have hrev : 0 < B j i := by omega
        have hsji := hs j i hrev
        cases hi : g i <;> cases hj : g j <;>
          simp [normalizedEuler, colorSign, eulerArrow, normalizedExchange, hi, hj] <;>
          simp [hi, hj] at hsji <;> omega
      · have hz : B i j = 0 := by omega
        cases hi : g i <;> cases hj : g j <;>
          simp [normalizedEuler, colorSign, eulerArrow, normalizedExchange, hi, hj] <;> omega

def noEulerThreeCycle (E : Matrix 4) (i j l : Fin 4) : Prop :=
  ¬ (eulerArrow E i j ∧ eulerArrow E j l ∧ eulerArrow E l i) ∧
  ¬ (eulerArrow E j i ∧ eulerArrow E l j ∧ eulerArrow E i l)

/-- An exact finite interface for the outside triangle: no next admissibility
is assumed, but a genuine Euler-root exclusion would still have to supply hn. -/
theorem triangleCompanion_of_noEulerThreeCycle (B A E : Matrix 4) (g : Colors)
    (hB : SkewSymmetric B) (hA : QuasiCartanCompanion B A)
    (hs : ArrowSigns B A g)
    (he : ∀ i j, 2 * E i j = A i j - B i j)
    (i j l : Fin 4) (hij : i ≠ j) (hjl : j ≠ l) (hli : l ≠ i)
    (hn : noEulerThreeCycle (normalizedEuler E g) i j l) :
    triangleCompanionAdmissible B A i j l := by
  apply (triangleCompanion_iff_no_normalized_cycle B A hB hA.1 g hs i j l).mpr
  intro hc
  have normSkew : SkewSymmetric (normalizedExchange B g) := by
    intro a b
    have hb := hB a b
    cases ha : g a <;> cases hc : g b <;>
      simp only [normalizedExchange, ha, hc, Bool.false_eq_true,
        Bool.true_eq_false, ↓reduceIte] <;> omega
  rcases hc with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact hn.1 ⟨(normalizedEuler_arrow B A E g hB hA hs he i j hij).mpr h1,
      (normalizedEuler_arrow B A E g hB hA hs he j l hjl).mpr h2,
      (normalizedEuler_arrow B A E g hB hA hs he l i hli).mpr h3⟩
  · have h1' : 0 < normalizedExchange B g j i := by have := normSkew j i; omega
    have h2' : 0 < normalizedExchange B g l j := by have := normSkew l j; omega
    have h3' : 0 < normalizedExchange B g i l := by have := normSkew i l; omega
    exact hn.2 ⟨(normalizedEuler_arrow B A E g hB hA hs he j i hij.symm).mpr h1',
      (normalizedEuler_arrow B A E g hB hA hs he l j hjl.symm).mpr h2',
      (normalizedEuler_arrow B A E g hB hA hs he i l hli.symm).mpr h3'⟩


private theorem correction_opposite_weak (x y : Int)
    (h : (0 ≤ x ∧ y ≤ 0) ∨ (x ≤ 0 ∧ 0 ≤ y)) : correction x y = 0 := by
  rcases h with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · have hnx : max (-x) 0 = 0 := by omega
    have hyz : max y 0 = 0 := by omega
    simp [correction, hnx, hyz]
  · have hxz : max x 0 = 0 := by omega
    have hny : max (-y) 0 = 0 := by omega
    simp [correction, hxz, hny]

/-- An unmixed pair retains both the exchange and companion entries. Zero
weights and arbitrarily large positive weights are included. -/
theorem nonincident_entries_unchanged_of_unmixed_weights
    (B A : Matrix 4) (g : Colors) (k i j : Fin 4)
    (hik : i ≠ k) (hjk : j ≠ k) (hB : SkewSymmetric B)
    (hA : QuasiCartanCompanion B A) (hs : ArrowSigns B A g)
    (hm : pivotWeight B g k i = 0 ↔ pivotWeight B g k j = 0) :
    mutate B k i j = B i j ∧ localMutation B A g k i j = A i j := by
  have hb := hB i k
  have hcorr : correction (B i k) (B k j) = 0 := by
    apply correction_opposite_weak
    cases hk : g k
    · simp only [pivotWeight, hk, Bool.false_eq_true, ↓reduceIte] at hm
      by_cases hi : B k i < 0
      · have hmaxi : max (-B k i) 0 ≠ 0 := by omega
        have hmaxj : max (-B k j) 0 ≠ 0 := fun h => hmaxi (hm.mpr h)
        exact Or.inl ⟨by omega, by omega⟩
      · have hmaxi : max (-B k i) 0 = 0 := by omega
        have hmaxj := hm.mp hmaxi
        exact Or.inr ⟨by omega, by omega⟩
    · simp only [pivotWeight, hk, ↓reduceIte] at hm
      by_cases hi : 0 < B k i
      · have hmaxi : max (B k i) 0 ≠ 0 := by omega
        have hmaxj : max (B k j) 0 ≠ 0 := fun h => hmaxi (hm.mpr h)
        exact Or.inr ⟨by omega, by omega⟩
      · have hmaxi : max (B k i) 0 = 0 := by omega
        have hmaxj := hm.mp hmaxi
        exact Or.inl ⟨by omega, by omega⟩
  exact ⟨by simp [mutate, hik, hjk, hcorr],
    localMutation_unmixed B A g k i j hik hjk hB hA hs hm⟩

/-- Outside triangles wholly selected or wholly unselected are unchanged.
This uses current triangle parity; no next signs or next parity is supplied. -/
theorem outside_triangle_of_unmixed_weights
    (B A : Matrix 4) (g : Colors) (k i j l : Fin 4)
    (hik : i ≠ k) (hjk : j ≠ k) (hlk : l ≠ k)
    (hB : SkewSymmetric B) (hA : QuasiCartanCompanion B A)
    (hs : ArrowSigns B A g) (ht : triangleCompanionAdmissible B A i j l)
    (hij : pivotWeight B g k i = 0 ↔ pivotWeight B g k j = 0)
    (hjl : pivotWeight B g k j = 0 ↔ pivotWeight B g k l = 0) :
    triangleCompanionAdmissible (mutate B k) (localMutation B A g k) i j l := by
  have he1 := nonincident_entries_unchanged_of_unmixed_weights B A g k i j
    hik hjk hB hA hs hij
  have he2 := nonincident_entries_unchanged_of_unmixed_weights B A g k j l
    hjk hlk hB hA hs hjl
  have he3 := nonincident_entries_unchanged_of_unmixed_weights B A g k l i
    hlk hik hB hA hs (hij.trans hjl).symm
  unfold triangleCompanionAdmissible at *
  simpa only [he1.1, he1.2, he2.1, he2.2, he3.1, he3.2] using ht

/-- The finite Euler matrix is exactly the pairing on actual columns made
positive by their current colors, with the fixed initial labels preserved. -/
theorem normalizedEuler_eq_pairing (U₀ C : Matrix 4) (i j : Fin 4) :
    normalizedEuler (coefficientBilinear U₀ C) (columnColor C) i j =
      pairing U₀ (fun t => colorSign (columnColor C) i * C t i)
        (fun t => colorSign (columnColor C) j * C t j) := by
  simp only [normalizedEuler, coefficientBilinear, mul, transpose, pairing]
  grind


/-- The positive representative of an actual coefficient column. -/
def positiveColumn (C : Matrix 4) (j : Fin 4) : Vector4 :=
  fun i => colorSign (columnColor C) j * C i j

/-- Current actual seed data gives positive real-root representatives of all
next columns before either next arrow signs or next triangles is supplied. -/
theorem principalSeed_next_positive_realRoots (B₀ : Matrix 4)
    (hB₀ : SkewSymmetric B₀) (w : List (Fin 4)) (k : Fin 4)
    (h : SeedInv B₀ w) :
    ∀ j, RealRoot (initialCompanion B₀)
        (positiveColumn (principalSeed B₀ (w ++ [k])).2 j) ∧
      ∀ i, 0 ≤ positiveColumn (principalSeed B₀ (w ++ [k])).2 j i := by
  have hn := coefficientMutation_rooted_signCoherent_quasiCartan B₀
    (principalSeed B₀ w).1 (principalSeed B₀ w).2 hB₀
    (principalSeed_skew B₀ hB₀ w) k h.companion h.arrowSigns h.admissible h.roots
  have he : principalSeed B₀ (w ++ [k]) = mutateSeed (principalSeed B₀ w) k :=
    evolve_append_singleton B₀ identityCoefficients w k
  have hroots : ∀ j, RealRoot (initialCompanion B₀)
      (column (principalSeed B₀ (w ++ [k])).2 j) := by
    simpa only [he, mutateSeed] using hn.1
  have hcoh : SignCoherent (principalSeed B₀ (w ++ [k])).2 := by
    simpa only [he, mutateSeed] using hn.2.1
  have hA₀ := initialCompanion_quasiCartan B₀ hB₀
  intro j
  rcases hcoh j with hg | hr
  · have hc := color_green hg
    have hecol : positiveColumn (principalSeed B₀ (w ++ [k])).2 j =
        column (principalSeed B₀ (w ++ [k])).2 j := by
      funext t; simp [positiveColumn, colorSign, hc, column]
    rw [hecol]
    exact ⟨hroots j, hg.1⟩
  · have hc := color_red hr
    have hroot := realRoot_neg _ hA₀.1 hA₀.2.1 (hroots j)
    have hpos : ∀ i, 0 ≤ -(principalSeed B₀ (w ++ [k])).2 i j := by
      intro i; have := hr.1 i; omega
    have hecol : positiveColumn (principalSeed B₀ (w ++ [k])).2 j =
        fun t => -(principalSeed B₀ (w ++ [k])).2 t j := by
      funext t; simp [positiveColumn, colorSign, hc]
    rw [hecol]
    exact ⟨hroot, hpos⟩

/-- Actual chronological outside-triangle transfer for the unmixed subset.
The current seed supplies its roots, coherence and Gram update; no next-state
arrow signs or cycle data is assumed. -/
theorem principalSeed_outside_triangle_of_unmixed_weights (B₀ : Matrix 4)
    (hB₀ : SkewSymmetric B₀) (w : List (Fin 4)) (k i j l : Fin 4)
    (h : SeedInv B₀ w) (hik : i ≠ k) (hjk : j ≠ k) (hlk : l ≠ k)
    (hij : i ≠ j) (hjl : j ≠ l) (hli : l ≠ i)
    (hijw : pivotWeight (principalSeed B₀ w).1 (columnColor (principalSeed B₀ w).2) k i = 0 ↔
      pivotWeight (principalSeed B₀ w).1 (columnColor (principalSeed B₀ w).2) k j = 0)
    (hjlw : pivotWeight (principalSeed B₀ w).1 (columnColor (principalSeed B₀ w).2) k j = 0 ↔
      pivotWeight (principalSeed B₀ w).1 (columnColor (principalSeed B₀ w).2) k l = 0) :
    triangleCompanionAdmissible (principalSeed B₀ (w ++ [k])).1
      (coefficientCompanion B₀ (principalSeed B₀ (w ++ [k])).2) i j l := by
  have hB := principalSeed_skew B₀ hB₀ w
  have hcoh := seedInv_signCoherent B₀ hB₀ w h
  have hg : columnColor (principalSeed B₀ w).2 k = true →
      ∀ t, 0 ≤ (principalSeed B₀ w).2 t k :=
    fun hc => ((color_iff_green hcoh k).mp hc).1
  have hr : columnColor (principalSeed B₀ w).2 k = false →
      ∀ t, (principalSeed B₀ w).2 t k ≤ 0 :=
    fun hc => ((color_iff_red hcoh k).mp hc).1
  have ht := companionAdmissible4_triangle _ _ hB h.companion.1 h.admissible
    i j l hij hli.symm hjl
  have hn := outside_triangle_of_unmixed_weights _ _ _ k i j l
    hik hjk hlk hB h.companion h.arrowSigns ht hijw hjlw
  have he : principalSeed B₀ (w ++ [k]) = mutateSeed (principalSeed B₀ w) k :=
    evolve_append_singleton B₀ identityCoefficients w k
  have heA := coefficientCompanion_mutation_local B₀ (principalSeed B₀ w).1
    (principalSeed B₀ w).2 (columnColor (principalSeed B₀ w).2) k hg hr
  simpa only [he, mutateSeed, heA] using hn

/-- The outside mixed-case interface retains actual origin and original
labels. The supplied next arrow signs are independent; `hn` is the still-open
three-positive-root Euler exclusion, not a proved mutation law. -/
theorem principalSeed_outside_triangle_of_noEulerThreeCycle
    (B₀ U₀ : Matrix 4) (hB₀ : SkewSymmetric B₀)
    (hU₀s : add U₀ (transpose U₀) = initialCompanion B₀)
    (hU₀a : add U₀ (scale (-1) (transpose U₀)) = reverse B₀)
    (w : List (Fin 4)) (k i j l : Fin 4) (h : SeedInv B₀ w)
    (_hik : i ≠ k) (_hjk : j ≠ k) (_hlk : l ≠ k)
    (hij : i ≠ j) (hjl : j ≠ l) (hli : l ≠ i)
    (hs : ArrowSigns (principalSeed B₀ (w ++ [k])).1
      (coefficientCompanion B₀ (principalSeed B₀ (w ++ [k])).2)
      (columnColor (principalSeed B₀ (w ++ [k])).2))
    (hn : noEulerThreeCycle
      (normalizedEuler (coefficientBilinear U₀ (principalSeed B₀ (w ++ [k])).2)
        (columnColor (principalSeed B₀ (w ++ [k])).2)) i j l) :
    triangleCompanionAdmissible (principalSeed B₀ (w ++ [k])).1
      (coefficientCompanion B₀ (principalSeed B₀ (w ++ [k])).2) i j l := by
  have hB := principalSeed_skew B₀ hB₀ w
  have hcoh := seedInv_signCoherent B₀ hB₀ w h
  have hg : columnColor (principalSeed B₀ w).2 k = true →
      ∀ t, 0 ≤ (principalSeed B₀ w).2 t k :=
    fun hc => ((color_iff_green hcoh k).mp hc).1
  have hr : columnColor (principalSeed B₀ w).2 k = false →
      ∀ t, (principalSeed B₀ w).2 t k ≤ 0 :=
    fun hc => ((color_iff_red hcoh k).mp hc).1
  have hnext := coefficientMutation_rooted_signCoherent_quasiCartan B₀
    (principalSeed B₀ w).1 (principalSeed B₀ w).2 hB₀ hB k
    h.companion h.arrowSigns h.admissible h.roots
  have he : principalSeed B₀ (w ++ [k]) = mutateSeed (principalSeed B₀ w) k :=
    evolve_append_singleton B₀ identityCoefficients w k
  have hAnext : QuasiCartanCompanion (principalSeed B₀ (w ++ [k])).1
      (coefficientCompanion B₀ (principalSeed B₀ (w ++ [k])).2) := by
    simpa only [he, mutateSeed] using hnext.2.2
  have hEnext : (principalSeed B₀ (w ++ [k])).1 =
      mul (mul (transpose (principalSeed B₀ (w ++ [k])).2) B₀)
        (principalSeed B₀ (w ++ [k])).2 := by
    simpa only [he, mutateSeed] using exchange_coefficientBasis_update B₀
      (principalSeed B₀ w).1 (principalSeed B₀ w).2 hB
      (columnColor (principalSeed B₀ w).2) k hg hr h.exchangeOrigin
  obtain ⟨hpartS, hpartA⟩ := coefficientBilinear_parts B₀ U₀
    (principalSeed B₀ (w ++ [k])).1 (principalSeed B₀ (w ++ [k])).2 hU₀s hU₀a hEnext
  have hparts : ∀ a b,
      2 * coefficientBilinear U₀ (principalSeed B₀ (w ++ [k])).2 a b =
        coefficientCompanion B₀ (principalSeed B₀ (w ++ [k])).2 a b -
          (principalSeed B₀ (w ++ [k])).1 a b := by
    intro a b
    have hsab := congrFun (congrFun hpartS a) b
    have haab := congrFun (congrFun hpartA a) b
    simp only [add, transpose, scale, reverse] at hsab haab
    omega
  exact triangleCompanion_of_noEulerThreeCycle _ _ _ _
    (principalSeed_skew B₀ hB₀ _) hAnext hs hparts i j l hij hjl hli hn


private theorem noEulerThreeCycle_of_triangle (B A E : Matrix 4) (g : Colors)
    (hB : SkewSymmetric B) (hA : QuasiCartanCompanion B A)
    (hs : ArrowSigns B A g)
    (he : ∀ i j, 2 * E i j = A i j - B i j)
    (i j l : Fin 4) (hij : i ≠ j) (hjl : j ≠ l) (hli : l ≠ i)
    (ht : triangleCompanionAdmissible B A i j l) :
    noEulerThreeCycle (normalizedEuler E g) i j l := by
  have hn := (triangleCompanion_iff_no_normalized_cycle B A hB hA.1 g hs i j l).mp ht
  have normSkew : SkewSymmetric (normalizedExchange B g) := by
    intro a b
    have hb := hB a b
    cases ha : g a <;> cases hc : g b <;>
      simp only [normalizedExchange, ha, hc, Bool.false_eq_true,
        Bool.true_eq_false, ↓reduceIte] <;> omega
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact hn (Or.inl ⟨(normalizedEuler_arrow B A E g hB hA hs he i j hij).mp h1,
      (normalizedEuler_arrow B A E g hB hA hs he j l hjl).mp h2,
      (normalizedEuler_arrow B A E g hB hA hs he l i hli).mp h3⟩)
  · rintro ⟨h1, h2, h3⟩
    have h1' := (normalizedEuler_arrow B A E g hB hA hs he j i hij.symm).mp h1
    have h2' := (normalizedEuler_arrow B A E g hB hA hs he l j hjl.symm).mp h2
    have h3' := (normalizedEuler_arrow B A E g hB hA hs he i l hli.symm).mp h3
    have hs1 := normSkew i j
    have hs2 := normSkew j l
    have hs3 := normSkew l i
    exact hn (Or.inr ⟨by omega, by omega, by omega⟩)

/-- Unrestricted acyclic initialization supplies the local Euler exclusion.
This is INIT only; its mixed-case STEP remains unproved. -/
theorem initial_noEulerThreeCycle (B₀ U₀ : Matrix 4)
    (hB₀ : SkewSymmetric B₀) (hAc : Acyclic B₀)
    (hU₀s : add U₀ (transpose U₀) = initialCompanion B₀)
    (hU₀a : add U₀ (scale (-1) (transpose U₀)) = reverse B₀)
    (i j l : Fin 4) (hij : i ≠ j) (hjl : j ≠ l) (hli : l ≠ i) :
    noEulerThreeCycle (normalizedEuler U₀ (fun _ => true)) i j l := by
  have hA := initialCompanion_quasiCartan B₀ hB₀
  have hs := initialCompanion_arrowSigns B₀ hB₀
  have ht := companionAdmissible4_triangle B₀ _ hB₀ hA.1
    (initialCompanion_admissible B₀ hB₀ hAc) i j l hij hli.symm hjl
  have hparts : ∀ a b, 2 * U₀ a b = initialCompanion B₀ a b - B₀ a b := by
    intro a b
    have hsab := congrFun (congrFun hU₀s a) b
    have haab := congrFun (congrFun hU₀a a) b
    simp only [add, transpose, scale, reverse] at hsab haab
    omega
  exact noEulerThreeCycle_of_triangle B₀ _ U₀ (fun _ => true) hB₀ hA hs
    hparts i j l hij hjl hli ht

end QuiverProofs.MAExistenceTeamCTriangleOutside
