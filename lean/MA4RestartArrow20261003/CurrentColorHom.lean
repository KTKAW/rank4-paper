import MA4RestartArrow20261003.FrameReordering

/-! Derive current colored Hom constraints from current ArrowSigns and
actual old Euler dimensions. These laws do not assert next-color transport
and add no field to SeedInv. Matrices have all four original indices. -/
namespace QuiverProofs.MA4RestartArrow20261003.CurrentColorHom
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open QuiverProofs.MA4RestartArrow20261003.AdjacentExceptionalFrame
open QuiverProofs.MA4RestartArrow20261003.FrameReordering
open QuiverProofs.MACompletionPairPurity
open QuiverProofs.MACompletionScalarEndomorphisms
universe w v u z
variable {K : Type w} [Field K] {C : Type u}
  [Category.{v} C] [Abelian C] [Linear K C] [HasExt.{z} C]
set_option maxHeartbeats 0

/-- In the current ordered frame, same-color nonzero Hom would contradict
current ArrowSigns. Actual pair purity handles also zero edges. -/
theorem same_color_hom_zero
    (F : Fin 4 → C ⥤ ModuleCat.{v} K) (M : Fin 4 → C)
    (hM : ExceptionalFrame F M)
    (hHered : ∀ T : C, HasProjectiveDimensionLT T 2)
    (B A : Fin 4 → Fin 4 → Int) (g : Fin 4 → Bool)
    (hB : ∀ a b, B a b = -B b a)
    (hSigns : ∀ a b, 0 < B a b → (0 < A a b ↔ g a = false ∧ g b = true))
    (dH dE : Fin 4 → Fin 4 → ℕ)
    (hHZ : ∀ a b, dH a b = 0 ↔ ∀ f : M a ⟶ M b, f = 0)
    (hEZ : ∀ a b, dE a b = 0 ↔ ∀ x : Ext (M a) (M b) 1, x = 0)
    (hEuler : ∀ a b, a < b → (dH a b : Int) - (dE a b : Int) =
      -(if g a = g b then 1 else -1) * B a b)
    (hComp : ∀ a b, a < b → A b a = -B a b)
    (a b : Fin 4) (hab : a < b) (hSame : g a = g b) :
    ∀ f : M a ⟶ M b, f = 0 := by
  have hNonneg : 0 ≤ B a b := by
    by_contra h
    have hb : 0 < B b a := by rw [hB b a]; omega
    have ha : 0 < A b a := by rw [hComp a b hab]; omega
    have hc := (hSigns b a hb).mp ha
    rw [hc.2, hc.1] at hSame
    contradiction
  letI := local_end_of_scalar_end (M a) (hM.nonzeroId a) (hM.scalarEnd a)
  letI := local_end_of_scalar_end (M b) (hM.nonzeroId b) (hM.scalarEnd b)
  have hPure := dimension_purity_of_rigid (M a) (M b) hHered
    (hM.reverseExt a b hab) (hM.rigid a) (hM.rigid b)
    (dH a b) (dE a b) (hHZ a b) (hEZ a b)
  have he := hEuler a b hab
  simp only [if_pos hSame, neg_one_mul] at he
  have hz : dH a b = 0 := by rcases hPure with h | h <;> omega
  exact (hHZ a b).mp hz

/-- A red object before a green object in a current Euler order must be
orthogonal in both directions. In particular, reordering the color blocks
cannot create an unsupported exceptional-frame supplier. -/
theorem red_before_green_orthogonal
    (F : Fin 4 → C ⥤ ModuleCat.{v} K) (M : Fin 4 → C)
    (hM : ExceptionalFrame F M)
    (hHered : ∀ T : C, HasProjectiveDimensionLT T 2)
    (B A : Fin 4 → Fin 4 → Int) (g : Fin 4 → Bool)
    (hB : ∀ a b, B a b = -B b a)
    (hSigns : ∀ a b, 0 < B a b → (0 < A a b ↔ g a = false ∧ g b = true))
    (dH dE : Fin 4 → Fin 4 → ℕ)
    (hHZ : ∀ a b, dH a b = 0 ↔ ∀ f : M a ⟶ M b, f = 0)
    (hEZ : ∀ a b, dE a b = 0 ↔ ∀ x : Ext (M a) (M b) 1, x = 0)
    (hEuler : ∀ a b, a < b → (dH a b : Int) - (dE a b : Int) =
      -(if g a = g b then 1 else -1) * B a b)
    (hComp : ∀ a b, a < b → A a b = -B a b ∧ A b a = -B a b)
    (a b : Fin 4) (hab : a < b) (ha : g a = false) (hb : g b = true) :
    ((∀ f : M a ⟶ M b, f = 0) ∧ (∀ x : Ext (M a) (M b) 1, x = 0)) ∧
    ((∀ f : M b ⟶ M a, f = 0) ∧ (∀ x : Ext (M b) (M a) 1, x = 0)) := by
  have hz : B a b = 0 := by
    by_cases hp : 0 < B a b
    · have hA := (hSigns a b hp).mpr ⟨ha, hb⟩
      rw [(hComp a b hab).1] at hA
      omega
    · by_cases hn : B a b < 0
      · have hp' : 0 < B b a := by rw [hB b a]; omega
        have hA : 0 < A b a := by rw [(hComp a b hab).2]; omega
        have hC := (hSigns b a hp').mp hA
        rw [hb] at hC
        simp at hC
      · omega
  have he : (dH a b : Int) - (dE a b : Int) = 0 := by
    rw [hEuler a b hab, hz, mul_zero]
  exact ⟨pair_orthogonal_of_euler_zero (M a) (M b) hHered
    (hM.reverseExt a b hab) (hM.rigid a) (hM.rigid b)
    (hM.nonzeroId a) (hM.nonzeroId b) (hM.scalarEnd a) (hM.scalarEnd b)
    (dH a b) (dE a b) (hHZ a b) (hEZ a b) he,
    hM.reverseHom a b hab, hM.reverseExt a b hab⟩

#print axioms same_color_hom_zero
#print axioms red_before_green_orthogonal
end QuiverProofs.MA4RestartArrow20261003.CurrentColorHom
