import Rank4ReviewRound2.StrongPairColumn
import Rank4Round2.WordBounds

/-! Incident edges stay below H throughout a constant alternating strong-pair
corridor with bounded endpoints and ceiling H+1. No MA bridge is used here.
This does not bound the number of opposite-edge top states. -/
namespace Rank4ReviewRound2.StrongPairIncident
open QuiverProofs Rank4Coordinator Rank4CoordinatorR2 Rank4Round2
open StrongPairColumn

def IncidentLe (B : Matrix 4) (i j : Fin 4) (H : Nat) : Prop :=
  ∀ l, (-(H:Int)≤B i l ∧ B i l≤(H:Int)) ∧
    (-(H:Int)≤B j l ∧ B j l≤(H:Int))

def alternatingWord (i j : Fin 4) : Nat → List (Fin 4)
  | 0 => []
  | n+1 => j :: alternatingWord j i n

theorem incident_step (B : Matrix 4) (hs : SkewSymmetric B)
    (i j : Fin 4) (hij : i≠j) (H : Nat) (ha : 2≤abs (B i j))
    (hOld : IncidentLe B i j H)
    (hFirst : HeightLe (mutate B j) (H+1))
    (hNext : HeightLe (mutate (mutate B j) i) (H+1)) :
    IncidentLe (mutate B j) j i H := by
  have hs' := mutation_preserves_skew B j hs
  intro l
  have hj : -(H:Int)≤mutate B j j l ∧ mutate B j j l≤(H:Int) := by
    have ht := (hOld l).2
    simp only [mutate,true_or,if_true]
    omega
  refine ⟨hj,?_⟩
  by_cases hli : l=i
  · subst l
    have ht := hs' i i
    omega
  by_cases hlj : l=j
  · subst l
    have ht := (hOld j).1
    simp only [mutate,or_true,if_true]
    omega
  exact frozen_column_survives B hs i j l hij (Ne.symm hli) (Ne.symm hlj)
    H ha (hOld l).1 (hOld l).2 hFirst hNext

theorem all_incident_below (n : Nat) (B : Matrix 4) (hs : SkewSymmetric B)
    (i j : Fin 4) (hij : i≠j) (H : Nat) (ha : 2≤abs (B i j))
    (hStart : IncidentLe B i j H)
    (hCeil : ∀ r≤n, HeightLe (applyWord B (alternatingWord i j r)) (H+1))
    (hEnd : HeightLe (applyWord B (alternatingWord i j n)) H) :
    ∀ r≤n, IncidentLe (applyWord B (alternatingWord i j r)) i j H := by
  induction n generalizing B i j with
  | zero =>
    intro r hr
    have he : r=0 := by omega
    subst r
    exact hStart
  | succ n ih =>
    have hs' := mutation_preserves_skew B j hs
    have hp : 2≤abs (mutate B j j i) := by
      simp only [mutate,true_or,if_true,abs_neg,hs j i,abs_neg]
      exact ha
    have hNew : IncidentLe (mutate B j) j i H := by
      cases n with
      | zero =>
        change HeightLe (mutate B j) H at hEnd
        exact fun l => ⟨hEnd j l,hEnd i l⟩
      | succ m =>
        exact incident_step B hs i j hij H ha hStart
          (hCeil 1 (by omega)) (hCeil 2 (by omega))
    have hTail : ∀ r≤n, HeightLe
        (applyWord (mutate B j) (alternatingWord j i r)) (H+1) := by
      intro r hr
      exact hCeil (r+1) (by omega)
    have hTailEnd : HeightLe
        (applyWord (mutate B j) (alternatingWord j i n)) H := hEnd
    have ht := ih (mutate B j) hs' j i (Ne.symm hij) hp hNew hTail hTailEnd
    intro r hr
    cases r with
    | zero => exact hStart
    | succ q =>
      have hh := ht q (by omega)
      exact fun l => ⟨(hh l).2,(hh l).1⟩

theorem bounded_endpoints_incident_below (n : Nat) (B : Matrix 4)
    (hs : SkewSymmetric B) (i j : Fin 4) (hij : i≠j) (H : Nat)
    (ha : 2≤abs (B i j)) (hStart : HeightLe B H)
    (hCeil : ∀ r≤n, HeightLe (applyWord B (alternatingWord i j r)) (H+1))
    (hEnd : HeightLe (applyWord B (alternatingWord i j n)) H) :
    ∀ r≤n, IncidentLe (applyWord B (alternatingWord i j r)) i j H :=
  all_incident_below n B hs i j hij H ha (fun l => ⟨hStart i l,hStart j l⟩)
    hCeil hEnd

#print axioms incident_step
#print axioms all_incident_below
#print axioms bounded_endpoints_incident_below
end Rank4ReviewRound2.StrongPairIncident
