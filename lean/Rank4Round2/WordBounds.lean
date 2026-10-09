import Rank4Round2.OverHeightCount

namespace Rank4Round2
open QuiverProofs Rank4Coordinator

theorem heightLe_mono (B : Matrix 4) (H K : Nat) (hHK : H≤K)
    (h : HeightLe B H) : HeightLe B K := by
  intro i j
  have h := h i j
  omega

theorem prefixHeight_mono (B : Matrix 4) (w : List (Fin 4)) (H K : Nat)
    (hHK : H≤K) (h : PrefixHeightLe B w H) : PrefixHeightLe B w K :=
  fun u v he => heightLe_mono _ H K hHK (h u v he)

theorem prefixHeight_append_iff (B : Matrix 4) (u v : List (Fin 4)) (H : Nat) :
    PrefixHeightLe B (u++v) H ↔
      PrefixHeightLe B u H ∧ PrefixHeightLe (applyWord B u) v H := by
  constructor
  · intro h
    constructor
    · intro a b he
      apply h a (b++v)
      rw [←List.append_assoc,he]
    · intro a b he
      rw [←applyWord_append]
      apply h (u++a) b
      rw [List.append_assoc,he]
  · rintro ⟨hu,hv⟩
    exact prefixHeight_append B u v H hu hv

#print axioms prefixHeight_append_iff
end Rank4Round2
