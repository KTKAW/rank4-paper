import Rank4Round2.WordBounds

/-! Literal first-return bookkeeping for two successive forced pivots.
The actual state high/low and child restrictions remain explicit inputs. -/
namespace Rank4Round2.UnitForcedReturn
open QuiverProofs Rank4Coordinator Rank4Round2

theorem forced_four_return (P : Matrix 4) (i j k : Fin 4)
    (rest : List (Fin 4)) (H F : Nat)
    (hCeil : PrefixHeightLe P (j::k::rest) F)
    (hEnd : HeightLe (applyWord P (j::k::rest)) H)
    (hProper : ∀ u v,(j::k::rest)=u++v → v≠[] → ¬HeightLe (applyWord P u) H)
    (hNR : ∀ u a v,(j::k::rest)≠u++a::a::v)
    (hHigh2 : ¬HeightLe (applyWord P [j,k]) H)
    (hHigh3 : ¬HeightLe (applyWord P [j,k,i]) H)
    (hLow4 : HeightLe (applyWord P [j,k,i,k]) H)
    (hNext2 : ∀ a,HeightLe (mutate (applyWord P [j,k]) a) F → a=i ∨ a=k)
    (hNext3 : ∀ a,HeightLe (mutate (applyWord P [j,k,i]) a) F → a=k ∨ a=i) :
    rest=[i,k] := by
  cases rest with
  | nil => exact False.elim (hHigh2 hEnd)
  | cons a rest =>
    have hA : HeightLe (mutate (applyWord P [j,k]) a) F := hCeil [j,k,a] rest rfl
    rcases hNext2 a hA with ha|ha
    · subst a
      cases rest with
      | nil => exact False.elim (hHigh3 hEnd)
      | cons b rest =>
        have hB : HeightLe (mutate (applyWord P [j,k,i]) b) F := hCeil [j,k,i,b] rest rfl
        rcases hNext3 b hB with hb|hb
        · subst b
          have hr : rest=[] := by
            by_contra hn
            exact (hProper [j,k,i,k] rest rfl hn) hLow4
          subst rest
          rfl
        · subst b
          exact False.elim (hNR [j,k] i rest rfl)
    · subst a
      exact False.elim (hNR [j] k rest rfl)

#print axioms forced_four_return
end Rank4Round2.UnitForcedReturn
