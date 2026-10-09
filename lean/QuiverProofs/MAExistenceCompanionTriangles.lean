import QuiverProofs.MAExistenceCompanions

/-! The scalar cancellation case in companion mutation. The triangle sign
premise is explicit; this file does not assert its all-word preservation. -/
namespace QuiverProofs.MAExistenceCompanionTriangles

/-- For a directed two-path of weights `x,y`, triangle admissibility fixes
the companion sign even when the third edge cancels or changes orientation. -/
theorem mixed_triangle_natAbs (x y z a c : Int)
    (hx : 0 < x) (hy : 0 < y)
    (ha : a.natAbs = z.natAbs) (hc : c.natAbs = y.natAbs)
    (htriangle : 0 < a * c * (-x) ↔ z < 0) :
    (a + x * c).natAbs = (z + x * y).natAbs := by
  rcases Int.natAbs_eq_natAbs_iff.mp ha with ha | ha <;>
    rcases Int.natAbs_eq_natAbs_iff.mp hc with hc | hc <;>
    rw [ha, hc] at htriangle ⊢
  · have hxy : 0 < x * y := Int.mul_pos hx hy
    have hz : z = 0 := by
      by_cases hn : z < 0
      · have hp := htriangle.mpr hn
        have he : z * -y * -x = z * (x * y) := by grind
        rw [he] at hp
        have hm : z * (x * y) < 0 := Int.mul_neg_of_neg_of_pos hn hxy
        omega
      · by_cases hp : 0 < z
        · have hm : z * -y * -x > 0 := by
            have he : z * -y * -x = z * (x * y) := by grind
            rw [he]
            exact Int.mul_pos hp hxy
          exact False.elim (hn (htriangle.mp hm))
        · omega
    simp [hz, Int.natAbs_mul, Int.natAbs_neg]
  · have hxy : 0 < x * y := Int.mul_pos hx hy
    have hz : z = 0 := by
      by_cases hn : z < 0
      · have hp := htriangle.mpr hn
        have he : -z * y * -x = z * (x * y) := by grind
        rw [he] at hp
        have hm : z * (x * y) < 0 := Int.mul_neg_of_neg_of_pos hn hxy
        omega
      · by_cases hp : 0 < z
        · have hm : -z * y * -x > 0 := by
            have he : -z * y * -x = z * (x * y) := by grind
            rw [he]
            exact Int.mul_pos hp hxy
          exact False.elim (hn (htriangle.mp hm))
        · omega
    simp [hz]
  · have he : -z + x * -y = -(z + x * y) := by grind
    rw [he, Int.natAbs_neg]

end QuiverProofs.MAExistenceCompanionTriangles
