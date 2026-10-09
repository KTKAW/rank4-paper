import Rank4StructureRound2.UnitN2RootPhases
import Rank4StructureRound2.MixedIncidentEqual

/-! Full negative frozen-row sign cone for a cyclic selected triangle.
The first-high and third-ceiling actual path force the larger-side phase
b=1,d=2. Smaller/equal sides violate proper scalar/Pfaffian budget. -/
namespace QuiverProofs.Rank4StructureRound2.UnitN2IncidentCone
open Census ProperOrder ProperWiggle ProperMutation ProperObstructionSoundness
open Rank4Coordinator Rank4Round2
set_option maxHeartbeats 12000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
private theorem four (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
abbrev R:=UnitN2Incident.root

private theorem negative_seed : ∀ i : Fin 6,
    ¬ProperClassTable (ofSix 1 (-1) (-1) 1 (-1) (-1)) i := by decide
private theorem seed_classes : ∀ s : Fin 2,∀ i : Fin 6,
    ProperClassTable (ofSix 1 (-1) (-1) 1 (-1) (s.val:Int)) i →
    component (supportMask (ofSix 1 (-1) (-1) 1 (-1) (s.val:Int))) i=
      component (supportMask (ofSix 1 (-1) (-1) 1 (-1) (s.val:Int))) 0 := by decide

theorem proper_nonnegative_f (b t d u f : Int)
    (hb : 1≤b) (ht : 1≤t) (hd : 1≤d) (hu : 1≤u)
    (p : CyclicOrder) (hp : ProperClass (R b t d u f) p) : 0≤f := by
  by_contra hf
  let seed:=ofSix 1 (-1) (-1) 1 (-1) (-1)
  have hm : supportMask (R b t d u f)=supportMask seed := by
    simp [R,UnitN2Incident.root,seed,supportMask,supportBit,ofSix,
      show b≠0 by omega,show t≠0 by omega,show d≠0 by omega,
      show u≠0 by omega,show f≠0 by omega]
  have hs : ∀ i j,0<R b t d u f i j ↔ 0<seed i j := by
    intro i j
    rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
      simp [R,UnitN2Incident.root,seed,ofSix] <;> omega
  obtain ⟨i,hi⟩:=cyclic_order_exhaustive p
  have ht':=(properClass_iff_table _ (ofSix_skew _ _ _ _ _ _) p i hi).mp hp
  have hz:=(ChamberProperness.properClassTable_sign_iff _ seed hm hs i).mp ht'
  exact negative_seed i hz

theorem proper_scalar (b t d u f : Int)
    (hb : 1≤b) (ht : 1≤t) (hd : 1≤d) (hu : 1≤u) (hf : 0≤f)
    (p : CyclicOrder) (hp : ProperClass (R b t d u f) p) :
    orderMarkov (R b t d u f) p=
      1+b^2+t^2+d^2+u^2+f^2-b*d+t*u+b*t*f-d*u*f-d*t*f := by
  let s : Fin 2:=if f=0 then 0 else 1
  let seed:=ofSix 1 (-1) (-1) 1 (-1) (s.val:Int)
  have hm : supportMask (R b t d u f)=supportMask seed := by
    by_cases hz : f=0 <;> simp [R,UnitN2Incident.root,seed,s,supportMask,supportBit,ofSix,hz,
      show b≠0 by omega,show t≠0 by omega,show d≠0 by omega,show u≠0 by omega]
  have hs : ∀ i j,0<R b t d u f i j ↔ 0<seed i j := by
    intro i j
    by_cases hz : f=0 <;>
      rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
      simp [R,UnitN2Incident.root,seed,s,ofSix,hz] <;> omega
  obtain ⟨i,hi⟩:=cyclic_order_exhaustive p
  have ht':=(properClass_iff_table _ (ofSix_skew _ _ _ _ _ _) p i hi).mp hp
  have hz:=(ChamberProperness.properClassTable_sign_iff _ seed hm hs i).mp ht'
  have hW : WiggleEquivalent (R b t d u f) p (order 0) := by
    apply (wiggle_iff_component _ (ofSix_skew _ _ _ _ _ _) p (order 0) i 0 hi
      (fun _ _ _ => Iff.rfl)).mpr
    change component (supportMask (R b t d u f)) i=component (supportMask (R b t d u f)) 0
    rw [hm]
    exact seed_classes s i hz
  have hInv : orderMarkov (R b t d u f) p=orderMarkov (R b t d u f) (order 0) :=
    ProperWiggleInvariants.markov_wiggle_invariant _ (ofSix_skew _ _ _ _ _ _) hW
  rw [hInv]
  change Algebra.markov 1 (-b) (-t) d (-u) f=_
  unfold Algebra.markov Algebra.squareSum Algebra.cycleTerms
  ring

theorem first_matrix (b t d u f : Int) (hb : 0≤b) (ht : 0≤t) (hu : 0≤u) :
    mutate (R b t d u f) 0=ofSix (-1) b t (d-b) (-(u+t)) f := by
  funext i j
  rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
    simp [R,UnitN2Incident.root,mutate,ofSix,correction,
      max_eq_left hb,max_eq_left ht,max_eq_left hu,
      max_eq_right (show -b≤0 by omega),max_eq_right (show -t≤0 by omega),
      max_eq_right (show -u≤0 by omega)] <;> ring

theorem first_top (b t d u f : Int) (H : Nat)
    (hb : 1≤b) (ht : 1≤t) (hd : 1≤d) (hu : 1≤u)
    (hR : HeightLe (R b t d u f) H)
    (hout : ¬HeightLe (mutate (R b t d u f) 0) H)
    (hceil : HeightLe (mutate (R b t d u f) 0) (H+1)) : u+t=(H:Int)+1 := by
  have hP:=first_matrix b t d u f (by omega) (by omega) (by omega)
  have hbH:=hR 0 2
  have htH:=hR 0 3
  have hdH:=hR 1 2
  have hfH:=hR 2 3
  simp only [R,UnitN2Incident.root,ofSix] at hbH htH hdH hfH
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

theorem smaller_third_edge (b t d u f F : Int)
    (hb : 0≤b) (ht : 0≤t) (hu : 0≤u) (hf : 0≤f) (hbd : d≤b) (hTop : u+t=F) :
    applyWord (R b t d u f) [0,1,2] 1 3=F+(b-d)*f := by
  have hP:=first_matrix b t d u f hb ht hu
  have hS : mutate (ofSix (-1) b t (d-b) (-F) f) 1=ofSix 1 d (t-F) (b-d) F f := by
    funext i j
    rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
      simp [mutate,ofSix,correction,max_eq_left hb,max_eq_left ht,max_eq_left hf,
        max_eq_left (show 0≤F by omega),max_eq_right (show -F≤0 by omega),
        max_eq_left (show 0≤b-d by omega),max_eq_right (show d-b≤0 by omega)] <;> ring
  rw [hTop] at hP
  simp only [applyWord,hP,hS]
  simp [mutate,ofSix,correction,max_eq_left hf,max_eq_right (show -f≤0 by omega),
    max_eq_left (show 0≤b-d by omega),max_eq_right (show d-b≤0 by omega)]

theorem actual_triangle (hEnd : EndpointTopological4)
    (b t d u f : Int) (H : Nat) (hb : 1≤b) (ht : 1≤t) (hd : 1≤d) (hu : 1≤u)
    (hR : HeightLe (R b t d u f) H)
    (hout : ¬HeightLe (mutate (R b t d u f) 0) H)
    (hceil : HeightLe (mutate (R b t d u f) 0) (H+1))
    (hThird : HeightLe (applyWord (R b t d u f) [0,1,2]) (H+1))
    (hma : MutationAcyclic (R b t d u f))
    (p : CyclicOrder) (hp : TotalProper (R b t d u f) p)
    (hBudget : orderMarkov (R b t d u f) p≤(H:Int)) :
    b=1 ∧ d=2 ∧ u+t=(H:Int)+1 ∧ 1≤(H:Int)+1-f ∧ (H:Int)+1-f≤(H:Int) := by
  have hTop:=first_top b t d u f H hb ht hd hu hR hout hceil
  have hProper:=totalProper_proper _ p hp
  have hf0:=proper_nonnegative_f b t d u f hb ht hd hu p hProper
  have hN : 2*abs (matrixPfaffian (R b t d u f))≤orderMarkov (R b t d u f) p :=
    SuperScalarPeak.MA_totalProper_pfaffian_bound hEnd _ (ofSix_skew _ _ _ _ _ _) hma p hp
  have hfH:=hR 2 3
  simp only [R,UnitN2Incident.root,ofSix] at hfH
  by_cases hbd : b<d
  · obtain ⟨hb1,hd2,hw1,hwH⟩:=UnitN2RootPhases.incident_actual_triangle hEnd b t d u f H
      hb ht hu hbd hR hout hceil hThird hma p hp hBudget
    exact ⟨hb1,hd2,hTop,hw1,hwH⟩
  · have hdb : d≤b := by omega
    have hT:=hThird 1 3
    rw [smaller_third_edge b t d u f ((H:Int)+1) (by omega) (by omega) (by omega) hf0 hdb hTop] at hT
    simp only [Nat.cast_add,Nat.cast_one] at hT
    have hNN : 2*abs (f-b*u-t*d)≤orderMarkov (R b t d u f) p := by
      simpa [matrixPfaffian,R,UnitN2Incident.root,ofSix,sub_eq_add_neg] using hN
    have hPf : 2*(b*u+t*d-f)≤(H:Int) := by
      have hn:=neg_le_abs (f-b*u-t*d)
      omega
    by_cases hEq : d=b
    · subst d
      have hb1 : b=1 := by
        by_contra hh
        have hb2 : 2≤b := by omega
        nlinarith [mul_nonneg (show 0≤b-2 by omega) (show 0≤u+t by omega)]
      subst b
      have hm:=proper_scalar 1 t 1 u f (by decide) ht (by decide) hu hf0 p hProper
      have hpos : u^2+f^2-u*f≥0 := by nlinarith [sq_nonneg (u-f),mul_nonneg (show 0≤u by omega) hf0]
      nlinarith [mul_nonneg (show 0≤t-1 by omega) (show 0≤u by omega),
        mul_nonneg (show 0≤t-1 by omega) (show 0≤t by omega)]
    · have hdb' : 1≤b-d := by omega
      have hfz : f=0 := by nlinarith [mul_nonneg (show 0≤b-d-1 by omega) hf0]
      nlinarith [mul_nonneg (show 0≤b-1 by omega) (show 0≤u by omega),
        mul_nonneg (show 0≤d-1 by omega) (show 0≤t by omega)]

#print axioms proper_nonnegative_f
#print axioms proper_scalar
#print axioms actual_triangle
end QuiverProofs.Rank4StructureRound2.UnitN2IncidentCone
