import QuiverProofs.ProperObstructionSoundness

/-!
Direct components of Neville's Section 5 construction, with the project's
convention `B i j > 0` for an arrow `i → j`.  No sign coherence, admissibility,
or existence of mutation-closed certificates is assumed in this module.
-/
namespace QuiverProofs.MAExistenceLiterature
open ProperOrder ProperWiggle ProperMutation

/-- `true` denotes green and `false` denotes red.  These are supplied colors;
the definition does not assert that principal coefficients supply them. -/
abbrev Colors := Fin 4 → Bool

/-- Neville Definition 5.3: reverse red-to-green arrows, and add the return
arrow for a two-path through `k` whose endpoints have the opposite color. -/
def AuxiliaryArrow (B : Matrix 4) (green : Colors) (k i j : Fin 4) : Prop :=
  (0 < B i j ∧ ¬(green i = false ∧ green j = true)) ∨
  (0 < B j i ∧ green j = false ∧ green i = true) ∨
  (0 < B j k ∧ 0 < B k i ∧ green i = green j ∧ green i ≠ green k)

def Compatible (B : Matrix 4) (green : Colors) (k : Fin 4)
    (p : CyclicOrder) : Prop :=
  ∀ i j, AuxiliaryArrow B green k i j → p.invFun i < p.invFun j

/-- A color-block extension puts the green block before the red block. -/
def GreenBeforeRed (green : Colors) (p : CyclicOrder) : Prop :=
  ∀ i j, green i = true → green j = false → p.invFun i < p.invFun j

/-- The combinatorial properness step of the literature construction.  It
holds for arbitrary integer matrices, including zero edges and disconnected
supports.  Existence of such orders is a separate obligation. -/
theorem compatible_colorBlock_proper (B : Matrix 4) (green : Colors)
    (k : Fin 4) (p : CyclicOrder) (h : Compatible B green k p)
    (hcolor : GreenBeforeRed green p) : ProperVertex B p k := by
  intro u w huk hkw
  cases hu : green u <;> cases hk : green k <;> cases hw : green w
  · exact Or.inl ⟨h u k (Or.inl ⟨huk, by simp [hu, hk]⟩),
      h k w (Or.inl ⟨hkw, by simp [hk, hw]⟩)⟩
  · exact Or.inr (Or.inr ⟨hcolor w u hw hu,
      h u k (Or.inl ⟨huk, by simp [hu, hk]⟩)⟩)
  · exact Or.inr (Or.inl ⟨hcolor k w hk hw,
      h w u (Or.inr (Or.inr ⟨huk, hkw, by simp [hw, hu], by simp [hw, hk]⟩))⟩)
  · exact Or.inr (Or.inl ⟨h k w (Or.inl ⟨hkw, by simp [hk, hw]⟩),
      hcolor w u hw hu⟩)
  · exact Or.inl ⟨hcolor u k hu hk,
      h k w (Or.inl ⟨hkw, by simp [hk, hw]⟩)⟩
  · exact Or.inr (Or.inr ⟨h w u (Or.inr (Or.inr ⟨huk, hkw,
      by simp [hw, hu], by simp [hw, hk]⟩)), hcolor u k hu hk⟩)
  · exact Or.inl ⟨h u k (Or.inl ⟨huk, by simp [hu, hk]⟩),
      hcolor k w hk hw⟩
  · exact Or.inl ⟨h u k (Or.inl ⟨huk, by simp [hu, hk]⟩),
      h k w (Or.inl ⟨hkw, by simp [hk, hw]⟩)⟩

/-- Per-vertex auxiliary extensions give the actual class semantics, allowing
a different representative for each vertex. -/
theorem auxiliary_orders_properClass (B : Matrix 4) (green : Colors)
    (p : CyclicOrder)
    (h : ∀ k, ∃ q : CyclicOrder, WiggleEquivalent B p q ∧
      Compatible B green k q ∧ GreenBeforeRed green q) : ProperClass B p := by
  intro k
  obtain ⟨q, hpq, hq, hcolor⟩ := h k
  exact ⟨q, hpq, compatible_colorBlock_proper B green k q hq hcolor⟩

/-- Frozen-to-mutable entries mutate by the same exchange rule.  There is no
assumption about their column signs. -/
def mutateCoefficients {n : Nat} (B C : Matrix n) (k : Fin n) : Matrix n :=
  fun i j => if j = k then -C i j
    else C i j + correction (C i k) (B k j)

/-- The green-column linear recurrence, translated without sign reversal. -/
theorem mutateCoefficients_green {n : Nat} (B C : Matrix n) (k : Fin n)
    (hgreen : ∀ i, 0 ≤ C i k) (i j : Fin n) :
    mutateCoefficients B C k i j =
      if j = k then -C i j else C i j + C i k * max (B k j) 0 := by
  unfold mutateCoefficients
  split
  · rfl
  · have hx := hgreen i
    have hmax : max (C i k) 0 = C i k := by omega
    have hneg : max (-C i k) 0 = 0 := by omega
    simp only [correction, hmax, hneg, Int.zero_mul, Int.sub_zero]

/-- The red-column linear recurrence uses the negative exchange entry. -/
theorem mutateCoefficients_red {n : Nat} (B C : Matrix n) (k : Fin n)
    (hred : ∀ i, C i k ≤ 0) (i j : Fin n) :
    mutateCoefficients B C k i j =
      if j = k then -C i j else C i j + C i k * max (-B k j) 0 := by
  unfold mutateCoefficients
  split
  · rfl
  · have hx := hred i
    have hmax : max (C i k) 0 = 0 := by omega
    have hneg : max (-C i k) 0 = -C i k := by omega
    simp only [correction, hmax, hneg, Int.zero_mul]
    grind

/-- The initial quasi-Cartan companion.  Its existence by itself says nothing
about admissibility after mutations. -/
def initialCompanion {n : Nat} (B : Matrix n) : Matrix n :=
  fun i j => if i = j then 2 else -((B i j).natAbs : Int)

def QuasiCartanCompanion {n : Nat} (B A : Matrix n) : Prop :=
  (∀ i j, A i j = A j i) ∧ (∀ i, A i i = 2) ∧
  (∀ i j, i ≠ j → (A i j).natAbs = (B i j).natAbs)

theorem initialCompanion_quasiCartan {n : Nat} (B : Matrix n)
    (hB : SkewSymmetric B) : QuasiCartanCompanion B (initialCompanion B) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    simp only [initialCompanion, eq_comm]
    rw [hB i j, Int.natAbs_neg]
  · intro i
    simp [initialCompanion]
  · intro i j hij
    simp [initialCompanion, hij]

theorem initialCompanion_offDiagonal_nonpos {n : Nat} (B : Matrix n)
    (i j : Fin n) (hij : i ≠ j) : initialCompanion B i j ≤ 0 := by
  simp only [initialCompanion, hij, if_false]
  omega

end QuiverProofs.MAExistenceLiterature
