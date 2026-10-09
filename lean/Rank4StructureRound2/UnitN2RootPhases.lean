import Rank4StructureRound2.UnitN2Opposite
import Rank4StructureRound2.UnitN2Incident

/-! The first-top equalities in the two proved local n2 sign cones follow
from the actual low predecessor, first-high state, and ceiling. These
consumers retain their sign-cone and smaller/larger-side hypotheses. -/
namespace QuiverProofs.Rank4StructureRound2.UnitN2RootPhases
open Census ProperOrder ProperWiggle ProperMutation ProperObstructionSoundness
open Rank4Coordinator Rank4Round2
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
private theorem four (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega

theorem opposite_first_top (b c d E f : Int) (H : Nat)
    (hb : 1≤b) (hc : 1≤c) (hd : 1≤d) (hbd : d<b) (hE : 0≤E)
    (hR : HeightLe (UnitN2Opposite.root b c d E f) H)
    (hout : ¬HeightLe (mutate (UnitN2Opposite.root b c d E f) 0) H)
    (hceil : HeightLe (mutate (UnitN2Opposite.root b c d E f) 0) (H+1)) :
    f+b*c=(H:Int)+1 := by
  obtain ⟨hP,_⟩:=UnitN2Opposite.first_two b c d E f (f+b*c) (by omega) (by omega) hE hbd rfl
  have hbH:=hR 0 2
  have hcH:=hR 0 3
  have hEH:=hR 1 3
  have hfH:=hR 2 3
  simp only [UnitN2Opposite.root,ofSix] at hbH hcH hEH hfH
  have hH : 1≤(H:Int) := by omega
  have hbc : 1≤b*c := by nlinarith [mul_nonneg (show 0≤b-1 by omega) (show 0≤c-1 by omega)]
  have htop : f+b*c≤(H:Int)+1 := by
    have h:=hceil 2 3
    rw [hP] at h
    simpa only [ofSix,Nat.cast_add,Nat.cast_one] using h.2
  have hhigh : (H:Int)<f+b*c := by
    by_contra hh
    apply hout
    rw [hP]
    intro i j
    rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
      simp only [ofSix] <;> omega
  omega

theorem incident_first_top (b t d u f : Int) (H : Nat)
    (hb : 1≤b) (ht : 1≤t) (hu : 1≤u) (hbd : b<d)
    (hR : HeightLe (UnitN2Incident.root b t d u f) H)
    (hout : ¬HeightLe (mutate (UnitN2Incident.root b t d u f) 0) H)
    (hceil : HeightLe (mutate (UnitN2Incident.root b t d u f) 0) (H+1)) :
    u+t=(H:Int)+1 := by
  obtain ⟨hP,_⟩:=UnitN2Incident.first_two b t d u f (u+t) (by omega) (by omega) (by omega) hbd rfl
  have hbH:=hR 0 2
  have htH:=hR 0 3
  have hdH:=hR 1 2
  have hfH:=hR 2 3
  simp only [UnitN2Incident.root,ofSix] at hbH htH hdH hfH
  have hH : 1≤(H:Int) := by omega
  have htop : u+t≤(H:Int)+1 := by
    have h:=hceil 1 3
    rw [hP] at h
    simp only [ofSix,Nat.cast_add,Nat.cast_one] at h
    omega
  have hhigh : (H:Int)<u+t := by
    by_contra hh
    apply hout
    rw [hP]
    intro i j
    rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
      simp only [ofSix] <;> omega
  omega

theorem opposite_actual_triangle (hEnd : EndpointTopological4)
    (b c d E f : Int) (H : Nat)
    (hb : 1≤b) (hc : 1≤c) (hd : 1≤d) (hbd : d<b) (hE : 0≤E)
    (hR : HeightLe (UnitN2Opposite.root b c d E f) H)
    (hout : ¬HeightLe (mutate (UnitN2Opposite.root b c d E f) 0) H)
    (hceil : HeightLe (mutate (UnitN2Opposite.root b c d E f) 0) (H+1))
    (hThird : HeightLe (applyWord (UnitN2Opposite.root b c d E f) [0,1,2]) (H+1))
    (hma : MutationAcyclic (UnitN2Opposite.root b c d E f))
    (p : CyclicOrder) (hp : TotalProper (UnitN2Opposite.root b c d E f) p)
    (hBudget : orderMarkov (UnitN2Opposite.root b c d E f) p≤(H:Int)) :
    b=2 ∧ d=1 ∧ E=0 := by
  have hTop:=opposite_first_top b c d E f H hb hc hd hbd hE hR hout hceil
  have hNecessary : 2*abs (matrixPfaffian (UnitN2Opposite.root b c d E f))≤
      orderMarkov (UnitN2Opposite.root b c d E f) p :=
    SuperScalarPeak.MA_totalProper_pfaffian_bound hEnd _ (ofSix_skew _ _ _ _ _ _) hma p hp
  exact UnitN2Opposite.opposite_first_triangle b c d E f H hb hc hd hbd hE hR hTop hThird
    p (totalProper_proper _ p hp) hNecessary hBudget

theorem incident_actual_triangle (hEnd : EndpointTopological4)
    (b t d u f : Int) (H : Nat)
    (hb : 1≤b) (ht : 1≤t) (hu : 1≤u) (hbd : b<d)
    (hR : HeightLe (UnitN2Incident.root b t d u f) H)
    (hout : ¬HeightLe (mutate (UnitN2Incident.root b t d u f) 0) H)
    (hceil : HeightLe (mutate (UnitN2Incident.root b t d u f) 0) (H+1))
    (hThird : HeightLe (applyWord (UnitN2Incident.root b t d u f) [0,1,2]) (H+1))
    (hma : MutationAcyclic (UnitN2Incident.root b t d u f))
    (p : CyclicOrder) (hp : TotalProper (UnitN2Incident.root b t d u f) p)
    (hBudget : orderMarkov (UnitN2Incident.root b t d u f) p≤(H:Int)) :
    b=1 ∧ d=2 ∧ 1≤(H:Int)+1-f ∧ (H:Int)+1-f≤(H:Int) := by
  have hTop:=incident_first_top b t d u f H hb ht hu hbd hR hout hceil
  have hNecessary : 2*abs (matrixPfaffian (UnitN2Incident.root b t d u f))≤
      orderMarkov (UnitN2Incident.root b t d u f) p :=
    SuperScalarPeak.MA_totalProper_pfaffian_bound hEnd _ (ofSix_skew _ _ _ _ _ _) hma p hp
  apply UnitN2Incident.incident_first_triangle b t d u f H hb ht hu hbd hR hTop hThird
  omega

#print axioms opposite_first_top
#print axioms incident_first_top
#print axioms opposite_actual_triangle
#print axioms incident_actual_triangle
end QuiverProofs.Rank4StructureRound2.UnitN2RootPhases
