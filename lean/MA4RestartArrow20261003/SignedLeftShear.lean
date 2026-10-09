import Mathlib.Tactic.Ring
import Mathlib.Data.Fin.Basic

/-! Exact sign bookkeeping for the left adjacent shear. All four vertex
coordinates participate in the sign test. The inputs concern old signed
columns and the actual kernel/cokernel dimension formula. -/
namespace QuiverProofs.MA4RestartArrow20261003.SignedLeftShear
set_option maxHeartbeats 0

/-- Positive normalization of the actual shear is a signed copy of the
numerical shear. Zero coordinates are included in the global branch test. -/
theorem signed_left_shear_normalization
    (x y u v q : Fin 4 → Int) (sx sy n : Int)
    (hx : sx = 1 ∨ sx = -1) (hy : sy = 1 ∨ sy = -1)
    (hu : ∀ a, u a = sx * x a) (hv : ∀ a, v a = sy * y a)
    (hq : ∀ a, q a = if (∀ b, 0 ≤ u b - n * v b)
      then u a - n * v a else -(u a - n * v a)) :
    ∃ sq : Int, (sq = 1 ∨ sq = -1) ∧
      (∀ a, q a = sq * (x a - (sx * sy * n) * y a)) := by
  let sq := if (∀ b, 0 ≤ u b - n * v b) then sx else -sx
  refine ⟨sq, ?_, ?_⟩
  · dsimp [sq]
    split_ifs <;> rcases hx with hx | hx <;> simp [hx]
  · intro a
    rw [hq a, hu a, hv a]
    dsimp [sq]
    by_cases h : ∀ b, 0 ≤ u b - n * v b
    · rw [if_pos h, if_pos h]
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> ring
    · rw [if_neg h, if_neg h]
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> ring

/-- Negating the signed pivot keeps its actual positive dimension vector
by simultaneously reversing its sign. -/
theorem negate_pivot_dimension (x u : Fin 4 → Int) (sx : Int)
    (hx : sx = 1 ∨ sx = -1) (hu : ∀ a, u a = sx * x a) :
    ((-sx = 1 ∨ -sx = -1) ∧ ∀ a, u a = (-sx) * (-x a)) := by
  constructor
  · rcases hx with hx | hx <;> simp [hx]
  · intro a; rw [hu a]; ring

#print axioms signed_left_shear_normalization
#print axioms negate_pivot_dimension
end QuiverProofs.MA4RestartArrow20261003.SignedLeftShear
