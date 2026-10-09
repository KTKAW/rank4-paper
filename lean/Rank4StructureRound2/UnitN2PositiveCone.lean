import Rank4StructureRound2.UnitN2PositiveScalar
import Rank4StructureRound2.ConnectedScalarLower
import Rank4StructureRound2.MixedIncidentEqual
import Rank4CoordinatorR2.UnitThreeScalar

/-! The c>0,d>b cyclic-triangle n2 cone is excluded for actual MA inputs
above their supplied proper scalar budget. Exact actual second-high and
third-ceiling states determine the wall. No generic sum guard is assumed. -/
namespace QuiverProofs.Rank4StructureRound2.UnitN2PositiveCone
open Census ProperOrder ProperWiggle ProperMutation ProperObstructionSoundness
open Rank4Coordinator Rank4Round2 Rank4ReviewRound2.PeakNormalization
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

def R (b c d u f : Int) : Matrix 4:=ofSix 1 (-b) c d (-u) f
private theorem four (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega

theorem first_matrix (b c d u f : Int) (hb : 0≤b) (hc : 0≤c) (hu : 0≤u) :
    mutate (R b c d u f) 0=ofSix (-1) b (-c) (d-b) (-u) (f+b*c) := by
  funext i j
  rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
    simp [R,mutate,ofSix,correction,max_eq_left hb,max_eq_left hc,max_eq_left hu,
      max_eq_right (show -b≤0 by omega),max_eq_right (show -c≤0 by omega),
      max_eq_right (show -u≤0 by omega)] <;> ring

theorem second_matrix (b c d u f F : Int) (hb : 0≤b) (hc : 0≤c) (hu : 0≤u)
    (hbd : b<d) (hTop : f+b*c=F) :
    applyWord (R b c d u f) [0,1]=ofSix 1 b (-c-u) (b-d) u (F-(d-b)*u) := by
  have hP:=first_matrix b c d u f hb hc hu
  rw [hTop] at hP
  simp only [applyWord,hP]
  funext i j
  rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
    simp [mutate,ofSix,correction,max_eq_left hb,max_eq_left hc,max_eq_left hu,
      max_eq_right (show -b≤0 by omega),max_eq_right (show -c≤0 by omega),
      max_eq_right (show -u≤0 by omega),max_eq_left (show 0≤d-b by omega),
      max_eq_right (show b-d≤0 by omega)] <;> ring

theorem connected (b c d u f : Int) (hb : 1≤b) (hu : 1≤u) : ConnectedSupport (R b c d u f) := by
  apply (connected_iff_all_colorings _).mpr
  intro color hc i j
  have h01:=hc 0 1 (by simp [R,ofSix])
  have h02:=hc 0 2 (by simp [R,ofSix];omega)
  have h13:=hc 1 3 (by simp [R,ofSix];omega)
  rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;> simp_all

def swap12 : Relabeling 4 :=
  ⟨fun i=>match i.val with|0=>0|1=>2|2=>1|_=>3,
   fun i=>match i.val with|0=>0|1=>2|2=>1|_=>3,by decide,by decide⟩

theorem positive_image (c F : Int) :
    signedFrame (ofSix 1 (-1) c 2 (c-F) (F-c)) swap12 true=
      ofSix 1 (-1) (-c) 2 (c-F) (F-c) := by
  funext i j
  rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
    simp [signedFrame,swap12,relabel,reverse,ofSix] <;> ring

theorem actual_impossible (hEnd : EndpointTopological4)
    (b c d u f : Int) (H : Nat) (hb : 1≤b) (hc : 1≤c) (hd : 1≤d) (hu : 1≤u) (hbd : b<d)
    (hR : HeightLe (R b c d u f) H)
    (hout : ¬HeightLe (mutate (R b c d u f) 0) H)
    (hceil : HeightLe (mutate (R b c d u f) 0) (H+1))
    (hSecond : HeightLe (applyWord (R b c d u f) [0,1]) (H+1))
    (hSecondHigh : ¬HeightLe (applyWord (R b c d u f) [0,1]) H)
    (hThird : HeightLe (applyWord (R b c d u f) [0,1,2]) (H+1))
    (hma : MutationAcyclic (R b c d u f))
    (p : CyclicOrder) (hp : TotalProper (R b c d u f) p)
    (hBudget : orderMarkov (R b c d u f) p≤(H:Int)) : False := by
  let F:=(H:Int)+1
  let m:=d-b
  have hm1 : 1≤m := by dsimp [m];omega
  have hbH:=hR 0 2
  have hcH:=hR 0 3
  have hdH:=hR 1 2
  have huH:=hR 1 3
  have hfH:=hR 2 3
  simp only [R,ofSix] at hbH hcH hdH huH hfH
  have hH : 1≤(H:Int) := by omega
  have hF : 2≤F := by dsimp [F];omega
  have hbc : 1≤b*c := by nlinarith [mul_nonneg (show 0≤b-1 by omega) (show 0≤c-1 by omega)]
  have hP:=first_matrix b c d u f (by omega) (by omega) (by omega)
  have hTop : f+b*c=F := by
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
    dsimp [F]
    omega
  have hS:=second_matrix b c d u f F (by omega) (by omega) (by omega) hbd hTop
  have hSC:=hSecond 0 3
  have hSF:=hSecond 2 3
  rw [hS] at hSC hSF
  simp only [ofSix,Nat.cast_add,Nat.cast_one] at hSC hSF
  have hmu : 1≤m*u := by nlinarith [mul_nonneg (show 0≤m-1 by omega) (show 0≤u-1 by omega)]
  have hWall : c+u=F ∨ m*u=2*F := by
    by_contra hh
    have hhigh : HeightLe (applyWord (R b c d u f) [0,1]) H := by
      rw [hS]
      intro i j
      rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
        simp only [ofSix] <;> dsimp [F,m] at * <;> omega
    exact hSecondHigh hhigh
  have hIncident : c+u=F := by
    rcases hWall with hh|hh
    · exact hh
    · exfalso
      have hn : F-(d-b)*u= -F := by change m*u=2*F at hh;dsimp [m] at hh;omega
      have hS' : applyWord (R b c d u f) [0,1]=ofSix 1 b (-c-u) (b-d) u (-F) := by rw [hS,hn]
      have he : applyWord (R b c d u f) [0,1,2] 1 3=u-(d-b)*F := by
        change mutate (applyWord (R b c d u f) [0,1]) 2 1 3=_
        rw [hS']
        simp [mutate,ofSix,correction,max_eq_left (show 0≤F by omega),
          max_eq_right (show -F≤0 by omega),max_eq_left (show 0≤d-b by omega),
          max_eq_right (show b-d≤0 by omega)] <;> ring
      have hT:=hThird 1 3
      rw [he] at hT
      simp only [Nat.cast_add,Nat.cast_one] at hT
      exact UnitN2PositiveScalar.opposite_wall_impossible m c u F hm1 hc hu
        (by dsimp [F];omega) hh (by dsimp [F,m] at *;omega)
  have hdE : d=b+m := by dsimp [m];ring
  have hfE : f=F-b*c := by omega
  have hMarkov : orderMarkov (R b c d u f) p=UnitN2PositiveScalar.scalar b m c u F := by
    have ha:=Rank4CoordinatorR2.UnitThreeScalar.proper_scalar b c d u f hb hc hd hu p
      (totalProper_proper _ p hp)
    change orderMarkov (R b c d u f) p=_ at ha
    rw [ha]
    unfold UnitN2PositiveScalar.scalar
    rw [hdE,hfE,←hIncident]
    ring
  have hPf : matrixPfaffian (R b c d u f)=UnitN2PositiveScalar.pf b m u F := by
    simp only [matrixPfaffian,R,ofSix]
    unfold UnitN2PositiveScalar.pf
    rw [hdE,hfE,←hIncident]
    ring
  have hThree : 3≤orderMarkov (R b c d u f) p :=
    ConnectedScalarLower.actual_connected_scalar_three hEnd _ (ofSix_skew _ _ _ _ _ _)
      (connected b c d u f hb hu) hma p hp
  have hN : 2*abs (matrixPfaffian (R b c d u f))≤orderMarkov (R b c d u f) p :=
    SuperScalarPeak.MA_totalProper_pfaffian_bound hEnd _ (ofSix_skew _ _ _ _ _ _) hma p hp
  rw [hMarkov,hPf] at hN
  rw [hMarkov] at hThree hBudget
  have hdF : b+m≤F-1 := by dsimp [F,m];omega
  have hCeil : m*u≤2*F := by dsimp [m,F];omega
  have hB : UnitN2PositiveScalar.scalar b m c u F≤F-1 := by
    simpa only [F,add_sub_cancel_right] using hBudget
  obtain ⟨hb1,hmEq⟩:=UnitN2PositiveScalar.incident_wall_shape b m c u F hb hm1 hc hu hdF
    hIncident hCeil hThree hN hB
  have hd2 : d=2 := by omega
  have hfFinal : f=F-c := by nlinarith [hTop,hb1]
  have huFinal : -u=c-F := by omega
  have hShape : R b c d u f=ofSix 1 (-1) c 2 (c-F) (F-c) := by
    simp only [R,hb1,hd2,hfFinal,huFinal]
  have hM : UnitN2PositiveScalar.scalar b m c u F=4+c^2 := by
    rw [hb1,hmEq]
    unfold UnitN2PositiveScalar.scalar
    rw [←hIncident]
    ring
  have hFbound : c^2+5≤F := by nlinarith [hB,hM]
  by_cases hc1 : c=1
  · have hm5 : orderMarkov (R b c d u f) p=5 := by rw [hMarkov,hM,hc1];norm_num
    have hpf2 : (matrixPfaffian (R b c d u f))^2=4 := by
      rw [hPf,hb1,hmEq]
      unfold UnitN2PositiveScalar.pf
      rw [←hIncident,hc1]
      ring
    have hLow:=ScalarFivePfTwo.actual_MA_scalar_five_pf_two_below hEnd _
      (ofSix_skew _ _ _ _ _ _) hma p hp hm5 hpf2
    have hL:=hLow 1 3
    simp only [R,ofSix] at hL
    rw [hc1] at hIncident hFbound
    dsimp [F] at *
    omega
  · have hc2 : 2≤c := by omega
    have hmaP : MutationAcyclic (ofSix 1 (-1) c 2 (c-F) (F-c)) := by rwa [hShape] at hma
    have hmaN:= (signedFrame_MA _ (ofSix_skew _ _ _ _ _ _) swap12 true).mpr hmaP
    rw [positive_image] at hmaN
    exact MixedIncidentEqualCore.EqualSlopeModule.family_NMA c F hc2 hFbound hmaN

#print axioms positive_image
#print axioms actual_impossible
end QuiverProofs.Rank4StructureRound2.UnitN2PositiveCone
