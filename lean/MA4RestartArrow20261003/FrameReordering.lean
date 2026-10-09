import MA4RestartArrow20261003.AdjacentExceptionalFrame

/-! Reorder actual objects using current numerical upperness and old pair
purity. No new realization, rigidity or next invariant is supplied. Actual
model Hom/Ext dimension identities remain an explicit old-data interface. -/
namespace QuiverProofs.MA4RestartArrow20261003.FrameReordering
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open QuiverProofs.MA4RestartArrow20261003.AdjacentExceptionalFrame
open QuiverProofs.MACompletionPairPurity
open QuiverProofs.MACompletionScalarEndomorphisms
universe w v u z
variable {K : Type w} [Field K] {C : Type u}
  [Category.{v} C] [Abelian C] [Linear K C] [HasExt.{z} C]
set_option maxHeartbeats 0

/-- In a rigid scalar-End pair with reverse Ext zero, Euler zero forces
both forward Hom and forward Ext zero. The dimension tests concern the
actual old pair, not objects constructed from an isolated root. -/
theorem pair_orthogonal_of_euler_zero (X Y : C)
    (hHered : ∀ T : C, HasProjectiveDimensionLT T 2)
    (hReverseExt : ∀ x : Ext Y X 1, x = 0)
    (hRigidX : ∀ x : Ext X X 1, x = 0)
    (hRigidY : ∀ x : Ext Y Y 1, x = 0)
    (hIdX : 𝟙 X ≠ 0) (hIdY : 𝟙 Y ≠ 0)
    (hEndX : ∀ g : X ⟶ X, ∃ c : K, g = c • 𝟙 X)
    (hEndY : ∀ g : Y ⟶ Y, ∃ c : K, g = c • 𝟙 Y)
    (dH dE : ℕ)
    (hHZ : dH = 0 ↔ ∀ g : X ⟶ Y, g = 0)
    (hEZ : dE = 0 ↔ ∀ x : Ext X Y 1, x = 0)
    (hEuler : (dH : Int) - (dE : Int) = 0) :
    (∀ g : X ⟶ Y, g = 0) ∧ (∀ x : Ext X Y 1, x = 0) := by
  letI := local_end_of_scalar_end X hIdX hEndX
  letI := local_end_of_scalar_end Y hIdY hEndY
  have hPure := dimension_purity_of_rigid X Y hHered hReverseExt
    hRigidX hRigidY dH dE hHZ hEZ
  have hBoth : dH = 0 ∧ dE = 0 := by rcases hPure with h | h <;> omega
  exact ⟨hHZ.mp hBoth.1, hEZ.mp hBoth.2⟩

/-- A bijective reorder whose actual old Euler matrix is upper triangular
is still an exceptional frame. For pairs whose order flips, old pair purity
and the new lower numerical zero derive both categorical vanishings. -/
theorem exceptional_frame_reorder
    (F : Fin 4 → C ⥤ ModuleCat.{v} K) (M : Fin 4 → C)
    (hM : ExceptionalFrame F M)
    (hHered : ∀ T : C, HasProjectiveDimensionLT T 2)
    (dH dE : Fin 4 → Fin 4 → ℕ)
    (hHZ : ∀ a b, dH a b = 0 ↔ ∀ g : M a ⟶ M b, g = 0)
    (hEZ : ∀ a b, dE a b = 0 ↔ ∀ x : Ext (M a) (M b) 1, x = 0)
    (p : Fin 4 ≃ Fin 4)
    (hUpper : ∀ a b, a < b → (dH (p b) (p a) : Int) - (dE (p b) (p a) : Int) = 0) :
    ExceptionalFrame F (fun a => M (p a)) := by
  have hPair : ∀ a b, a < b →
      (∀ g : M (p b) ⟶ M (p a), g = 0) ∧
      (∀ x : Ext (M (p b)) (M (p a)) 1, x = 0) := by
    intro a b hab
    by_cases hOrder : p a < p b
    · exact ⟨hM.reverseHom (p a) (p b) hOrder, hM.reverseExt (p a) (p b) hOrder⟩
    · have hne : p a ≠ p b := by intro h; have := p.injective h; omega
      have hRev : p b < p a := by omega
      exact pair_orthogonal_of_euler_zero (M (p b)) (M (p a)) hHered
        (hM.reverseExt (p b) (p a) hRev)
        (hM.rigid (p b)) (hM.rigid (p a))
        (hM.nonzeroId (p b)) (hM.nonzeroId (p a))
        (hM.scalarEnd (p b)) (hM.scalarEnd (p a))
        (dH (p b) (p a)) (dE (p b) (p a))
        (hHZ (p b) (p a)) (hEZ (p b) (p a)) (hUpper a b hab)
  exact ⟨(fun a => hM.rigid (p a)), (fun a => hM.scalarEnd (p a)),
    (fun a => hM.nonzeroId (p a)), (fun a b => hM.finiteVertices (p a) b),
    (fun a b hab => (hPair a b hab).1), (fun a b hab => (hPair a b hab).2)⟩

#print axioms pair_orthogonal_of_euler_zero
#print axioms exceptional_frame_reorder
end QuiverProofs.MA4RestartArrow20261003.FrameReordering
