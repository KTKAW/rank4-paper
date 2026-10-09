import MA4EulerMonoEpiTriangleConsumer01a0fee4
import QuiverProofs.MAExistenceTeamCTriangleOutside
import QuiverProofs.MAExistenceSupportChronology

/-! Exact conditional categorical-to-numerical Euler No3 bridge.
Objects, local End rings, hereditary bound, reverse Ext and forward purity
are explicit inputs. No numerical root/frame realization is constructed here. -/
namespace MA4EulerRealizedNo301a0fee4
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open QuiverProofs MAExistenceTeamCTriangleOutside MAExistenceSupportChronology
open MAExistenceTeamBRootPositivity MAExistenceTeamBAdjacentHurwitz
open MAExistenceTeamCCertificateTransport MAExistenceCoefficients Cosquare
open MA4EulerMonoEpiTriangleConsumer01a0fee4
universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
set_option maxHeartbeats 0

/- Rotation changes labels only; no upper-order premise is transported. -/
omit [Category C] [Abelian C] [HasExt C] in
theorem no3_rotate (E : Matrix 4) (i j l : Fin 4)
    (h : noEulerThreeCycle E i j l) : noEulerThreeCycle E j l i := by
  constructor
  · rintro ⟨a,b,c⟩; exact h.1 ⟨c,a,b⟩
  · rintro ⟨a,b,c⟩; exact h.2 ⟨c,a,b⟩

omit [Category C] [Abelian C] [HasExt C] in
theorem no3_swap_first (E : Matrix 4) (i j l : Fin 4)
    (h : noEulerThreeCycle E i j l) : noEulerThreeCycle E j i l := by
  constructor
  · rintro ⟨a,b,c⟩; exact h.2 ⟨a,c,b⟩
  · rintro ⟨a,b,c⟩; exact h.1 ⟨a,c,b⟩

omit [Category C] [Abelian C] [HasExt C] in
theorem no3_ordered_of_noForbidden (E : Matrix 4)
    (hupper : ∀ a b, b < a → E a b = 0)
    (a b c : Fin 4) (hab : a < b) (hbc : b < c)
    (hp : ¬ ((0 < E a b ∧ 0 < E b c ∧ E a c < 0) ∨
              (E a b < 0 ∧ E b c < 0 ∧ 0 < E a c))) :
    noEulerThreeCycle E a b c := by
  have hba := hupper b a hab
  have hcb := hupper c b hbc
  have hca := hupper c a (lt_trans hab hbc)
  simp only [noEulerThreeCycle, eulerArrow, hba, hcb, hca, lt_irrefl,
    or_false, false_or]
  exact ⟨fun h => hp (.inl h), fun h => hp (.inr h)⟩

/- The exact six orderings of three distinct labels reduce to the given upper
order. E itself is never permuted and upper form is never assumed invariant. -/
omit [Category C] [Abelian C] [HasExt C] in
theorem no3_all_labels_of_upper_noForbidden (E : Matrix 4)
    (hupper : ∀ a b, b < a → E a b = 0)
    (hpattern : ∀ a b c, a < b → b < c →
      ¬ ((0 < E a b ∧ 0 < E b c ∧ E a c < 0) ∨
         (E a b < 0 ∧ E b c < 0 ∧ 0 < E a c)))
    (i j l : Fin 4) (hij : i ≠ j) (hjl : j ≠ l) (hli : l ≠ i) :
    noEulerThreeCycle E i j l := by
  have sorted (a b c : Fin 4) (hab : a < b) (hbc : b < c) :
      noEulerThreeCycle E a b c :=
    no3_ordered_of_noForbidden E hupper a b c hab hbc (hpattern a b c hab hbc)
  have orders : (i < j ∧ j < l) ∨ (i < l ∧ l < j) ∨
      (j < i ∧ i < l) ∨ (j < l ∧ l < i) ∨
      (l < i ∧ i < j) ∨ (l < j ∧ j < i) := by omega
  rcases orders with ⟨a,b⟩ | ⟨a,b⟩ | ⟨a,b⟩ | ⟨a,b⟩ | ⟨a,b⟩ | ⟨a,b⟩
  · exact sorted i j l a b
  · exact no3_rotate E l i j (no3_swap_first E i l j (sorted i l j a b))
  · exact no3_swap_first E j i l (sorted j i l a b)
  · exact no3_rotate E l i j (no3_rotate E j l i (sorted j l i a b))
  · exact no3_rotate E l i j (sorted l i j a b)
  · exact no3_rotate E l i j (no3_rotate E j l i
      (no3_swap_first E l j i (sorted l j i a b)))

/-- Categorical consumers exclude the two forbidden patterns in the original
upper order using only explicit realization and purity inputs. -/
theorem realized_noForbidden (X : Fin 4 → C) (E : Matrix 4)
    (hHered : ∀ T : C, HasProjectiveDimensionLT T 2)
    (hEnd : ∀ a, IsLocalRing (End (X a)))
    (hreverse : ∀ a b, a < b → ∀ e : Ext (X b) (X a) 1, e = 0)
    (hpos : ∀ a b, a < b → 0 < E a b →
      (∃ f : X a ⟶ X b, f ≠ 0) ∧ (∀ e : Ext (X a) (X b) 1, e = 0))
    (hneg : ∀ a b, a < b → E a b < 0 →
      (∀ f : X a ⟶ X b, f = 0) ∧ (∃ e : Ext (X a) (X b) 1, e ≠ 0))
    (a b c : Fin 4) (hab : a < b) (hbc : b < c) :
    ¬ ((0 < E a b ∧ 0 < E b c ∧ E a c < 0) ∨
       (E a b < 0 ∧ E b c < 0 ∧ 0 < E a c)) := by
  have hac := lt_trans hab hbc
  letI := hEnd a; letI := hEnd b; letI := hEnd c
  rintro (⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩)
  · obtain ⟨hXY,hExtXY⟩ := hpos a b hab h1
    obtain ⟨hYZ,_⟩ := hpos b c hbc h2
    obtain ⟨hXZ,hExtXZ⟩ := hneg a c hac h3
    exact hom_hom_ext_consumer (X a) (X b) (X c) hHered
      hXY hYZ hXZ hExtXY hExtXZ (hreverse b c hbc)
  · obtain ⟨_,hExtXY⟩ := hneg a b hab h1
    obtain ⟨_,hExtYZ⟩ := hneg b c hbc h2
    obtain ⟨hXZ,_⟩ := hpos a c hac h3
    exact ext_ext_hom_consumer (X a) (X b) (X c) hHered
      hExtXY hExtYZ hXZ (hreverse a b hab) (hreverse b c hbc)
      (hreverse a c hac)

/-- Actual numerical noEulerThreeCycle, with all categorical inputs visible. -/
theorem realized_upper_noEulerThreeCycle (X : Fin 4 → C) (E : Matrix 4)
    (hupper : ∀ a b, b < a → E a b = 0)
    (hHered : ∀ T : C, HasProjectiveDimensionLT T 2)
    (hEnd : ∀ a, IsLocalRing (End (X a)))
    (hreverse : ∀ a b, a < b → ∀ e : Ext (X b) (X a) 1, e = 0)
    (hpos : ∀ a b, a < b → 0 < E a b →
      (∃ f : X a ⟶ X b, f ≠ 0) ∧ (∀ e : Ext (X a) (X b) 1, e = 0))
    (hneg : ∀ a b, a < b → E a b < 0 →
      (∀ f : X a ⟶ X b, f = 0) ∧ (∃ e : Ext (X a) (X b) 1, e ≠ 0))
    (i j l : Fin 4) (hij : i ≠ j) (hjl : j ≠ l) (hli : l ≠ i) :
    noEulerThreeCycle E i j l :=
  no3_all_labels_of_upper_noForbidden E hupper
    (realized_noForbidden X E hHered hEnd hreverse hpos hneg) i j l hij hjl hli

/-- Supplied natural Hom/Ext dimensions imply the sign interface when their
zero tests, purity and full numerical Euler identification are explicit. -/
theorem realized_dimensions_noEulerThreeCycle (X : Fin 4 → C) (E : Matrix 4)
    (dimHom dimExt : Fin 4 → Fin 4 → Nat)
    (hupper : ∀ a b, b < a → E a b = 0)
    (hHered : ∀ T : C, HasProjectiveDimensionLT T 2)
    (hEnd : ∀ a, IsLocalRing (End (X a)))
    (hreverse : ∀ a b, a < b → ∀ e : Ext (X b) (X a) 1, e = 0)
    (hHomZero : ∀ a b, dimHom a b = 0 ↔ ∀ f : X a ⟶ X b, f = 0)
    (hExtZero : ∀ a b, dimExt a b = 0 ↔ ∀ e : Ext (X a) (X b) 1, e = 0)
    (hEuler : ∀ a b, E a b = (dimHom a b : Int) - (dimExt a b : Int))
    (hPurity : ∀ a b, a < b → dimHom a b = 0 ∨ dimExt a b = 0)
    (i j l : Fin 4) (hij : i ≠ j) (hjl : j ≠ l) (hli : l ≠ i) :
    noEulerThreeCycle E i j l := by
  classical
  refine realized_upper_noEulerThreeCycle X E hupper hHered hEnd hreverse
    ?_ ?_ i j l hij hjl hli
  · intro a b hab hp
    have he := hEuler a b
    rcases hPurity a b hab with hh | hx
    · omega
    · constructor
      · by_contra hn
        push_neg at hn
        have hh := (hHomZero a b).mpr hn
        omega
      · exact (hExtZero a b).mp hx
  · intro a b hab hn
    have he := hEuler a b
    rcases hPurity a b hab with hh | hx
    · constructor
      · exact (hHomZero a b).mp hh
      · by_contra hz
        push_neg at hz
        have hx := (hExtZero a b).mpr hz
        omega
    · omega

#print axioms realized_upper_noEulerThreeCycle
#print axioms realized_dimensions_noEulerThreeCycle
end MA4EulerRealizedNo301a0fee4
