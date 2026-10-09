import Rank4Round2.WordRerouting

/-! An exact, guarded zero-pivot peak replacement. The extra cancellation
inequality is stated explicitly and is necessary for this two-step detour.
-/
namespace Rank4Round2
open QuiverProofs Rank4Coordinator

private theorem four (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega

theorem mutate_zero_commute (B : Matrix 4) (skew : SkewSymmetric B)
    (hz : B 0 1=0) : mutate (mutate B 0) 1 = mutate (mutate B 1) 0 := by
  have h10 : B 1 0=0 := by have := skew 1 0; omega
  funext i j
  rcases four i with rfl|rfl|rfl|rfl <;>
    rcases four j with rfl|rfl|rfl|rfl <;>
    simp [mutate,hz,h10,correction] <;> omega

def zeroPeak (b c d e f : Int) : Matrix 4 := ofSix 0 b (-c) d (-e) f

theorem zeroPeak_zero (b c d e f : Int) (hb : 0<b) (hc : 0<c) :
    mutate (zeroPeak b c d e f) 0 = ofSix 0 (-b) c d (-e) (f-b*c) := by
  funext i j
  rcases four i with rfl|rfl|rfl|rfl <;>
    rcases four j with rfl|rfl|rfl|rfl <;>
    simp [zeroPeak,mutate,ofSix,correction] <;> grind

theorem zeroPeak_double (b c d e f : Int)
    (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e) :
    mutate (mutate (zeroPeak b c d e f) 0) 1 =
      ofSix 0 (-b) c (-d) e (f-b*c-d*e) := by
  rw [zeroPeak_zero b c d e f hb hc]
  funext i j
  rcases four i with rfl|rfl|rfl|rfl <;>
    rcases four j with rfl|rfl|rfl|rfl <;>
    simp [mutate,ofSix,correction] <;> grind

theorem zero_square_endpoint (B : Matrix 4) (skew : SkewSymmetric B)
    (hz : B 0 1=0) :
    applyWord (mutate B 0) [1,0] = mutate B 1 := by
  simp only [applyWord]
  rw [mutate_zero_commute B skew hz,mutation_involutive]

theorem zero_square_prefix_iff (B : Matrix 4) (skew : SkewSymmetric B)
    (hz : B 0 1=0) (H : Nat)
    (h0 : HeightLe (mutate B 0) H) (h1 : HeightLe (mutate B 1) H) :
    PrefixHeightLe (mutate B 0) [1,0] H ↔ HeightLe (mutate (mutate B 0) 1) H := by
  simp only [prefixHeight_cons,prefixHeight_nil]
  have endeq := zero_square_endpoint B skew hz
  simp only [applyWord] at endeq
  rw [endeq]
  exact ⟨fun h=>h.2.1,fun h=>⟨h0,h,h1⟩⟩

/-- With bounded children the sole additional condition is the explicit
opposite-edge cancellation bound; all four incident magnitudes are fixed. -/
theorem zeroPeak_detour_iff (b c d e f : Int) (H : Nat)
    (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e)
    (h0 : HeightLe (mutate (zeroPeak b c d e f) 0) H)
    (h1 : HeightLe (mutate (zeroPeak b c d e f) 1) H) :
    PrefixHeightLe (mutate (zeroPeak b c d e f) 0) [1,0] H ↔
      -(H:Int)≤f-b*c-d*e ∧ f-b*c-d*e≤(H:Int) := by
  rw [zero_square_prefix_iff (zeroPeak b c d e f) (ofSix_skew _ _ _ _ _ _)
    (by simp [zeroPeak,ofSix]) H h0 h1,
    zeroPeak_double b c d e f hb hc hd he,heightLe_ofSix_iff]
  have hB := h0 0 2
  have hC := h0 0 3
  have hD := h1 1 2
  have hE := h1 1 3
  simp [zeroPeak,mutate,ofSix,correction] at hB hC hD hE
  omega

example : HeightLe (mutate (zeroPeak 2 2 2 2 3) 0) 2 := by decide
example : HeightLe (mutate (zeroPeak 2 2 2 2 3) 1) 2 := by decide
example : ¬ PrefixHeightLe (mutate (zeroPeak 2 2 2 2 3) 0) [1,0] 2 := by
  rw [zeroPeak_detour_iff 2 2 2 2 3 2 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)]
  decide

#print axioms mutate_zero_commute
#print axioms zero_square_endpoint
#print axioms zeroPeak_detour_iff
end Rank4Round2
