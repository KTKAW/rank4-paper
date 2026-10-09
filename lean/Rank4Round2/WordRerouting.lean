import Rank4Round2.PeakAlgebra

/-! Word/frame transport for the live local plateau replacements. These
lemmas require actual local height proofs; they do not assume global coverage.
-/
namespace Rank4Round2
open QuiverProofs Rank4Coordinator

instance heightLeDecidable (B : Matrix 4) (H : Nat) : Decidable (HeightLe B H) := by
  unfold HeightLe
  infer_instance

theorem prefixHeight_nil (B : Matrix 4) (H : Nat) :
    PrefixHeightLe B [] H ↔ HeightLe B H := by
  constructor
  · intro h
    exact h [] [] rfl
  · intro h u v he
    cases u with
    | nil => exact h
    | cons k u => simp at he

theorem prefixHeight_cons (B : Matrix 4) (k : Fin 4) (w : List (Fin 4)) (H : Nat) :
    PrefixHeightLe B (k::w) H ↔ HeightLe B H ∧ PrefixHeightLe (mutate B k) w H := by
  constructor
  · intro h
    refine ⟨h [] (k::w) rfl, ?_⟩
    intro u v he
    exact h (k::u) v (congrArg (List.cons k) he)
  · rintro ⟨hb,ht⟩ u v he
    cases u with
    | nil => exact hb
    | cons a u =>
      have hak : k=a := (List.cons.inj he).1
      subst a
      exact ht u v (List.cons.inj he).2

theorem prefixHeight_append (B : Matrix 4) (u v : List (Fin 4)) (H : Nat)
    (hu : PrefixHeightLe B u H) (hv : PrefixHeightLe (applyWord B u) v H) :
    PrefixHeightLe B (u++v) H := by
  induction u generalizing B with
  | nil => exact hv
  | cons k u ih =>
    obtain ⟨hb,ht⟩ := (prefixHeight_cons B k u H).mp hu
    exact (prefixHeight_cons B k (u++v) H).mpr ⟨hb,ih (mutate B k) ht hv⟩

theorem heightLe_relabel_iff (B : Matrix 4) (p : Relabeling 4) (H : Nat) :
    HeightLe (relabel B p) H ↔ HeightLe B H := by
  constructor
  · intro h i j
    simpa only [relabel,p.right_inv] using h (p.invFun i) (p.invFun j)
  · exact fun h i j => h (p.toFun i) (p.toFun j)

theorem prefixHeight_relabel_iff (B : Matrix 4) (p : Relabeling 4)
    (w : List (Fin 4)) (H : Nat) :
    PrefixHeightLe (relabel B p) (w.map p.invFun) H ↔ PrefixHeightLe B w H := by
  induction w generalizing B with
  | nil => simp only [List.map_nil,prefixHeight_nil,heightLe_relabel_iff]
  | cons k w ih =>
    simp only [List.map_cons,prefixHeight_cons,mutate_relabel,p.right_inv,
      heightLe_relabel_iff,ih]

theorem map_inverse_word (w : List (Fin 4)) (p : Relabeling 4) :
    (w.map p.invFun).map p.toFun = w := by
  induction w with
  | nil => rfl
  | cons k w ih => simp only [List.map_cons,p.right_inv,ih]

/-- An endpoint up to relabeling requires the inverse label map on the whole
remaining suffix; the local equality alone cannot justify suffix reuse. -/
theorem reroute_endpoint (B : Matrix 4) (old new tail : List (Fin 4))
    (p : Relabeling 4) (he : applyWord B new = relabel (applyWord B old) p) :
    applyWord B (new++tail.map p.invFun) = relabel (applyWord B (old++tail)) p := by
  rw [applyWord_append,he,word_relabel,map_inverse_word,applyWord_append]

theorem reroute_prefixHeight (B : Matrix 4) (old new tail : List (Fin 4))
    (p : Relabeling 4) (H : Nat)
    (he : applyWord B new = relabel (applyWord B old) p)
    (hnew : PrefixHeightLe B new H)
    (htail : PrefixHeightLe (applyWord B old) tail H) :
    PrefixHeightLe B (new++tail.map p.invFun) H := by
  apply prefixHeight_append B new _ H hnew
  rw [he]
  exact (prefixHeight_relabel_iff _ p tail H).mpr htail

#print axioms reroute_endpoint
#print axioms reroute_prefixHeight
end Rank4Round2
