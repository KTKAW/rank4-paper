import Rank4StructureRound2.UnitN2IncidentCone
import Rank4StructureRound2.UnitN2PositiveCone

/-! All frozen-row signs for a cyclic selected triangle with unequal b,d.
Actual first/two high states and third ceiling allow only the fixed
(1,-2,1) phase or the negative-row (1,-1,2) family. Equality b=d and
acyclic/zero selected triangles are separate coordinator-owned cases. -/
namespace QuiverProofs.Rank4StructureRound2.UnitN2CyclicStrict
open Census ProperOrder ProperWiggle ProperMutation ProperObstructionSoundness
open Rank4Coordinator Rank4Round2
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

def R (b c d e f : Int) : Matrix 4:=ofSix 1 (-b) c d e f
private theorem four (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega

theorem negative_first (b c d e f : Int) (hb : 0≤b) (hc : c≤0) :
    mutate (R b c d e f) 0=ofSix (-1) b (-c) (d-b) (e+c) f := by
  funext i j
  rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
    simp [R,mutate,ofSix,correction,max_eq_left hb,max_eq_right hc,
      max_eq_right (show -b≤0 by omega),max_eq_left (show 0≤ -c by omega)] <;> ring

theorem positive_first (b c d e f : Int) (hb : 0≤b) (hc : 0≤c) :
    mutate (R b c d e f) 0=ofSix (-1) b (-c) (d-b) e (f+b*c) := by
  funext i j
  rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
    simp [R,mutate,ofSix,correction,max_eq_left hb,max_eq_left hc,
      max_eq_right (show -b≤0 by omega),max_eq_right (show -c≤0 by omega)] <;> ring

theorem actual_phases (hEnd : EndpointTopological4)
    (b c d e f : Int) (H : Nat) (hb : 1≤b) (hd : 1≤d) (hneq : b≠d)
    (hR : HeightLe (R b c d e f) H)
    (hout : ¬HeightLe (mutate (R b c d e f) 0) H)
    (hceil : HeightLe (mutate (R b c d e f) 0) (H+1))
    (hSecond : HeightLe (applyWord (R b c d e f) [0,1]) (H+1))
    (hSecondHigh : ¬HeightLe (applyWord (R b c d e f) [0,1]) H)
    (hThird : HeightLe (applyWord (R b c d e f) [0,1,2]) (H+1))
    (hma : MutationAcyclic (R b c d e f))
    (p : CyclicOrder) (hp : TotalProper (R b c d e f) p)
    (hBudget : orderMarkov (R b c d e f) p≤(H:Int)) :
    (b=2 ∧ d=1 ∧ e=0) ∨
      (b=1 ∧ d=2 ∧ c<0 ∧ e<0 ∧ -(e+c)=(H:Int)+1 ∧
        1≤(H:Int)+1-f ∧ (H:Int)+1-f≤(H:Int)) := by
  have hbH:=hR 0 2
  have hcH:=hR 0 3
  have hdH:=hR 1 2
  have heH:=hR 1 3
  have hfH:=hR 2 3
  simp only [R,ofSix] at hbH hcH hdH heH hfH
  have hH : 1≤(H:Int) := by omega
  by_cases hcpos : 0<c
  · have hc1 : 1≤c := by omega
    have hP:=positive_first b c d e f (by omega) (by omega)
    have hbc : 1≤b*c := by nlinarith [mul_nonneg (show 0≤b-1 by omega) (show 0≤c-1 by omega)]
    have hTop : f+b*c=(H:Int)+1 := by
      have htop:=hceil 2 3
      rw [hP] at htop
      simp only [ofSix,Nat.cast_add,Nat.cast_one] at htop
      have hhigh : (H:Int)<f+b*c := by
        by_contra hh
        apply hout
        rw [hP]
        intro i j
        rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
          simp only [ofSix] <;> omega
      omega
    by_cases hE : 0≤e
    · by_cases hbd : b<d
      · have hN : 2*abs (matrixPfaffian (R b c d e f))≤orderMarkov (R b c d e f) p :=
          SuperScalarPeak.MA_totalProper_pfaffian_bound hEnd _ (ofSix_skew _ _ _ _ _ _) hma p hp
        have hpf : matrixPfaffian (R b c d e f)=f+b*e+c*d := by simp [matrixPfaffian,R,ofSix]
        rw [hpf] at hN
        have hh:=le_abs_self (f+b*e+c*d)
        nlinarith [mul_nonneg (show 0≤d-b by omega) (show 0≤c by omega),
          mul_nonneg (show 0≤b by omega) hE]
      · have hdb : d<b := by omega
        have hS : applyWord (R b c d e f) [0,1] 2 3=(H:Int)+1+(b-d)*e := by
          simp only [applyWord,hP]
          simp [mutate,ofSix,correction,max_eq_left hE,max_eq_right (show -e≤0 by omega),
            max_eq_left (show 0≤b-d by omega),max_eq_right (show d-b≤0 by omega)]
          nlinarith
        have hT:=hSecond 2 3
        rw [hS] at hT
        simp only [Nat.cast_add,Nat.cast_one] at hT
        have he0 : e=0 := by nlinarith [mul_nonneg (show 0≤b-d-1 by omega) hE]
        subst e
        have hResult:=UnitN2RootPhases.opposite_actual_triangle hEnd b c d 0 f H
          hb hc1 hd hdb (by decide) hR hout hceil hThird hma p hp hBudget
        exact .inl ⟨hResult.1,hResult.2.1,rfl⟩
    · have heNeg : e<0 := by omega
      by_cases hbd : b<d
      · have heq : R b c d e f=UnitN2PositiveCone.R b c d (-e) f := by
          simp only [R,UnitN2PositiveCone.R,neg_neg]
        rw [heq] at hR hout hceil hSecond hSecondHigh hThird hma hp hBudget
        exact False.elim (UnitN2PositiveCone.actual_impossible hEnd b c d (-e) f H
          hb hc1 hd (by omega) hbd hR hout hceil hSecond hSecondHigh hThird hma p hp hBudget)
      · have hdb : d<b := by omega
        have heq : R b c d e f=UnitN2Opposite.root b c d (-e) f := by
          simp only [R,UnitN2Opposite.root,neg_neg]
        rw [heq] at hR hout hceil hThird hma hp hBudget
        have hResult:=UnitN2RootPhases.opposite_actual_triangle hEnd b c d (-e) f H
          hb hc1 hd hdb (by omega) hR hout hceil hThird hma p hp hBudget
        exact .inl ⟨hResult.1,hResult.2.1,by omega⟩
  · have hcNon : c≤0 := by omega
    have hP:=negative_first b c d e f (by omega) hcNon
    have hcNeg : c<0 := by
      by_contra hh
      have hc0 : c=0 := by omega
      apply hout
      rw [hP]
      intro i j
      rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
        simp only [ofSix] <;> omega
    have heNeg : e<0 := by
      by_contra hh
      have he0 : 0≤e := by omega
      apply hout
      rw [hP]
      intro i j
      rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
        simp only [ofSix] <;> omega
    have heq : R b c d e f=UnitN2IncidentCone.R b (-c) d (-e) f := by
      simp only [R,UnitN2IncidentCone.R,UnitN2Incident.root,neg_neg]
    rw [heq] at hR hout hceil hThird hma hp hBudget
    obtain ⟨hb1,hd2,hTop,hw1,hwH⟩:=UnitN2IncidentCone.actual_triangle hEnd b (-c) d (-e) f H
      hb (by omega) hd (by omega) hR hout hceil hThird hma p hp hBudget
    exact .inr ⟨hb1,hd2,hcNeg,heNeg,by omega,hw1,hwH⟩

#print axioms negative_first
#print axioms positive_first
#print axioms actual_phases
end QuiverProofs.Rank4StructureRound2.UnitN2CyclicStrict
