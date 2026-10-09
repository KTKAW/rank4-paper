import Rank4Round2.OverHeightCount

/-! Transport local prefix guards and progress through arrow reversal.
Together with inverse-label suffix transport this covers both signs without
introducing a global supplier of successful local replacements.
-/
namespace Rank4Round2
open QuiverProofs Rank4Coordinator

theorem heightLe_reverse_iff (B : Matrix 4) (H : Nat) :
    HeightLe (reverse B) H ↔ HeightLe B H := by
  constructor <;> intro h i j
  · have h := h i j
    simp only [reverse] at h
    constructor <;> omega
  · have h := h i j
    simp only [reverse]
    constructor <;> omega

theorem prefixHeight_reverse_iff (B : Matrix 4) (w : List (Fin 4)) (H : Nat) :
    PrefixHeightLe (reverse B) w H ↔ PrefixHeightLe B w H := by
  induction w generalizing B with
  | nil => simp only [prefixHeight_nil,heightLe_reverse_iff]
  | cons k w ih =>
    simp only [prefixHeight_cons,mutate_reverse,heightLe_reverse_iff,ih]

theorem overCount_reverse (B : Matrix 4) (w : List (Fin 4)) (H : Nat) :
    overCount (reverse B) w H = overCount B w H := by
  induction w generalizing B with
  | nil => rfl
  | cons k w ih =>
    simp only [overCount,mutate_reverse,overBit,heightLe_reverse_iff,ih]

theorem signed_reroute_endpoint (B : Matrix 4) (old new tail : List (Fin 4))
    (p : Relabeling 4)
    (he : applyWord B new = reverse (relabel (applyWord B old) p)) :
    applyWord B (new++tail.map p.invFun) =
      reverse (relabel (applyWord B (old++tail)) p) := by
  rw [applyWord_append,he,word_reverse,word_relabel,map_inverse_word,applyWord_append]

theorem signed_reroute_prefixHeight (B : Matrix 4) (old new tail : List (Fin 4))
    (p : Relabeling 4) (H : Nat)
    (he : applyWord B new = reverse (relabel (applyWord B old) p))
    (hn : PrefixHeightLe B new H)
    (ht : PrefixHeightLe (applyWord B old) tail H) :
    PrefixHeightLe B (new++tail.map p.invFun) H := by
  apply prefixHeight_append B new _ H hn
  rw [he,prefixHeight_reverse_iff]
  exact (prefixHeight_relabel_iff _ p tail H).mpr ht

theorem signed_reroute_acyclic (B : Matrix 4) (skew : SkewSymmetric B)
    (old new tail : List (Fin 4)) (p : Relabeling 4)
    (he : applyWord B new = reverse (relabel (applyWord B old) p))
    (ha : Acyclic (applyWord B (old++tail))) :
    Acyclic (applyWord B (new++tail.map p.invFun)) := by
  rw [signed_reroute_endpoint B old new tail p he]
  apply (acyclic_reverse_iff _ (relabel_skew _ p (word_preserves_skew B _ skew))).mpr
  exact (acyclic_relabel_iff _ p).mpr ha

theorem signed_reroute_count (B : Matrix 4) (old new tail : List (Fin 4))
    (p : Relabeling 4) (H : Nat)
    (he : applyWord B new = reverse (relabel (applyWord B old) p))
    (hc : overCount B new H + 1 = overCount B old H) :
    overCount B (new++tail.map p.invFun) H + 1 = overCount B (old++tail) H := by
  rw [overCount_append,he,overCount_reverse,overCount_relabel,overCount_append]
  omega

#print axioms signed_reroute_endpoint
#print axioms signed_reroute_acyclic
#print axioms signed_reroute_count
end Rank4Round2
