import Rank4Round2.ZeroOrbitScalar
import Rank4Round2.ZeroFrameGuard
import Rank4ReviewRound2.StrongPairIncident

/-! The second high zero-pair state has a low other-pivot child. All
incident sign and zero walls are retained. A sign flip of the opposite top
is excluded by the actual MA proper scalar, not by bounded sampling. -/
namespace Rank4Round2.ZeroOrbitGeometry
open QuiverProofs Rank4Coordinator Rank4CoordinatorR2 Rank4Round2
open ProperObstructionSoundness
open Rank4ReviewRound2.StrongPairIncident
open Rank4ReviewRound2.PeakNormalization

def peak (b c d E : Int) (H : Nat) : Matrix 4 :=
  ofSix 0 b (-c) d E ((H:Int)+1)

private theorem four (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega

theorem peak_zero (b c d E : Int) (H : Nat) (hb : 0<b) (hc : 0<c) :
    mutate (peak b c d E H) 0=ofSix 0 (-b) c d E ((H:Int)+1-b*c) := by
  funext i j
  rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
    simp [peak,mutate,ofSix,correction,
      max_eq_left hb.le,max_eq_left hc.le,
      max_eq_right (show -b≤0 by omega),max_eq_right (show -c≤0 by omega)] <;> ring

theorem peak_one (b c d E : Int) (H : Nat) :
    mutate (peak b c d E H) 1=
      ofSix 0 b (-c) (-d) (-E) ((H:Int)+1+correction (-d) E) := by
  funext i j
  rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
    simp [peak,mutate,ofSix,correction] <;> ring

theorem peak_double (b c d E : Int) (H : Nat) (hb : 0<b) (hc : 0<c) :
    mutate (mutate (peak b c d E H) 1) 0=
      ofSix 0 (-b) c (-d) (-E) ((H:Int)+1+correction (-d) E-b*c) := by
  rw [peak_one]
  funext i j
  rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
    simp [mutate,ofSix,correction,
      max_eq_left hb.le,max_eq_left hc.le,
      max_eq_right (show -b≤0 by omega),max_eq_right (show -c≤0 by omega)] <;> ring

theorem second_high_correction_zero
    (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4)
    (b c d E : Int) (H : Nat) (hb : 0<b) (hc : 0<c)
    (hInc : IncidentLe (peak b c d E H) 0 1 H)
    (hT : HeightLe (mutate (peak b c d E H) 1) (H+1))
    (hHigh : ¬HeightLe (mutate (peak b c d E H) 1) H)
    (hma : MutationAcyclic (peak b c d E H)) : correction (-d) E=0 := by
  have hB := (hInc 2).1
  have hC := (hInc 3).1
  have hD := (hInc 2).2
  have hE := (hInc 3).2
  change -(H:Int)≤b ∧ b≤(H:Int) at hB
  change -(H:Int)≤ -c ∧ -c≤(H:Int) at hC
  change -(H:Int)≤d ∧ d≤(H:Int) at hD
  change -(H:Int)≤E ∧ E≤(H:Int) at hE
  have ht := hT 2 3
  rw [peak_one] at ht
  change -((H+1:Nat):Int)≤(H:Int)+1+correction (-d) E ∧
    (H:Int)+1+correction (-d) E≤((H+1:Nat):Int) at ht
  simp only [Nat.cast_add,Nat.cast_one] at ht
  have hnot : ¬(-(H:Int)≤(H:Int)+1+correction (-d) E ∧
      (H:Int)+1+correction (-d) E≤(H:Int)) := by
    intro hh
    apply hHigh
    rw [peak_one]
    intro i j
    rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
      simp only [ofSix] <;> omega
  have hCases : correction (-d) E=0 ∨ correction (-d) E= -2*((H:Int)+1) := by omega
  rcases hCases with hz|hflip
  · exact hz
  · have hneg : correction (-d) E<0 := by omega
    obtain ⟨hd,he⟩ := correction_negative_inputs (-d) E hneg
    have hcorr : correction (-d) E=d*E := by
      simp only [correction,max_eq_right (show -d≤0 by omega),max_eq_right he.le,
        max_eq_left (show 0≤ -(-d) by omega),max_eq_left (show 0≤ -E by omega)]
      ring
    have hprod : d*(-E)=2*((H:Int)+1) := by rw [hcorr] at hflip;nlinarith
    have hno := ZeroOrbitScalar.sign_flip_not_MA hExist hEnd b c d (-E) H
      (by omega) (by omega) (by omega) (by omega) hB.2 (by omega) hD.2 (by omega) hprod
    exact False.elim (hno (by simpa only [peak,neg_neg] using hma))

theorem normalized_second_high_other_low
    (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4)
    (b c d E : Int) (H : Nat) (hb : 0<b) (hc : 0<c)
    (hInc : IncidentLe (peak b c d E H) 0 1 H)
    (hLow : HeightLe (mutate (peak b c d E H) 0) H)
    (hT : HeightLe (mutate (peak b c d E H) 1) (H+1))
    (hHigh : ¬HeightLe (mutate (peak b c d E H) 1) H)
    (hma : MutationAcyclic (peak b c d E H)) :
    HeightLe (mutate (mutate (peak b c d E H) 1) 0) H := by
  have hz := second_high_correction_zero hExist hEnd b c d E H hb hc hInc hT hHigh hma
  have hB := (hInc 2).1
  have hC := (hInc 3).1
  have hD := (hInc 2).2
  have hE := (hInc 3).2
  have hF := hLow 2 3
  rw [peak_zero b c d E H hb hc] at hF
  change -(H:Int)≤b ∧ b≤(H:Int) at hB
  change -(H:Int)≤ -c ∧ -c≤(H:Int) at hC
  change -(H:Int)≤d ∧ d≤(H:Int) at hD
  change -(H:Int)≤E ∧ E≤(H:Int) at hE
  change -(H:Int)≤(H:Int)+1-b*c ∧ (H:Int)+1-b*c≤(H:Int) at hF
  rw [peak_double b c d E H hb hc,hz]
  intro i j
  rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
    simp only [ofSix] <;> omega

theorem zero_incident_from_low (B : Matrix 4) (hs : SkewSymmetric B)
    (i j : Fin 4) (hij : i≠j) (hz : B i j=0) (H : Nat)
    (hLow : HeightLe (mutate B i) H) : IncidentLe B i j H := by
  have hji : B j i=0 := by rw [hs j i,hz];rfl
  intro l
  constructor
  · have h := hLow i l
    simp only [mutate,true_or,if_true] at h
    omega
  · by_cases hl : l=i
    · subst l
      simp only [hji]
      omega
    · have h := hLow j l
      simp only [mutate,if_neg (show ¬(j=i ∨ l=i) by omega),hji] at h
      simpa [correction] using h

theorem opposite_top (B : Matrix 4) (hs : SkewSymmetric B) (H : Nat)
    (hInc : IncidentLe B 0 1 H) (hCeil : HeightLe B (H+1))
    (hHigh : ¬HeightLe B H) : B 2 3=(H:Int)+1 ∨ B 2 3= -((H:Int)+1) := by
  have hf := hCeil 2 3
  have h01 := (hInc 1).1
  have h02 := (hInc 2).1
  have h03 := (hInc 3).1
  have h12 := (hInc 2).2
  have h13 := (hInc 3).2
  have hnot : ¬(-(H:Int)≤B 2 3 ∧ B 2 3≤(H:Int)) := by
    intro h23
    apply hHigh
    rw [←ofSix_reconstruct B hs]
    intro i j
    rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
      simp only [ofSix] <;> omega
  omega

theorem actual_second_high_other_low
    (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4)
    (B : Matrix 4) (hs : SkewSymmetric B) (hma : MutationAcyclic B)
    (i j : Fin 4) (hij : i≠j) (hz : B i j=0) (H : Nat)
    (hP : HeightLe B (H+1)) (hHigh : ¬HeightLe B H)
    (hLow : HeightLe (mutate B i) H)
    (hNext : HeightLe (mutate B j) (H+1)) (hNextHigh : ¬HeightLe (mutate B j) H) :
    HeightLe (mutate (mutate B j) i) H := by
  let p := pivotFrame i j
  let N := relabel B p
  have hp := pivotFrame_slots i j hij
  have hp0 : p.toFun 0=i := hp.1
  have hp1 : p.toFun 1=j := hp.2
  have hsN := relabel_skew B p hs
  have hzN : N 0 1=0 := by simpa only [N,relabel,hp0,hp1] using hz
  have hLowN : HeightLe (mutate N 0) H := by
    change HeightLe (mutate (relabel B p) 0) H
    rwa [mutate_relabel,heightLe_relabel_iff,hp0]
  have hIncN := zero_incident_from_low N hsN 0 1 (by decide) hzN H hLowN
  have hCeilN : HeightLe N (H+1) := (heightLe_relabel_iff B p _).mpr hP
  have hHighN : ¬HeightLe N H := fun hh => hHigh ((heightLe_relabel_iff B p H).mp hh)
  have hTop := opposite_top N hsN H hIncN hCeilN hHighN
  let r : Bool := decide (N 2 3<0)
  let C := signedFrame B p r
  have hCF : C 2 3=(H:Int)+1 := by
    rcases hTop with hf|hf
    · have hn : ¬N 2 3<0 := by omega
      have hr : r=false := by simp [r,hn]
      change signedFrame B p r 2 3=(H:Int)+1
      rw [hr]
      exact hf
    · have hn : N 2 3<0 := by omega
      have hr : r=true := by simp [r,hn]
      change signedFrame B p r 2 3=(H:Int)+1
      rw [hr]
      change -N 2 3=(H:Int)+1
      omega
  have hsC := signedFrame_skew B hs p r
  have hzC : C 0 1=0 := by
    cases hr : r <;> simp [C,signedFrame,relabel,reverse,hr,hp0,hp1,hz]
  have hLowC : HeightLe (mutate C 0) H := by
    rw [show C=signedFrame B p r from rfl,signedFrame_mutate,hp0,signedFrame_height]
    exact hLow
  have hNextC : HeightLe (mutate C 1) (H+1) := by
    rw [show C=signedFrame B p r from rfl,signedFrame_mutate,hp1,signedFrame_height]
    exact hNext
  have hNextHighC : ¬HeightLe (mutate C 1) H := by
    rw [show C=signedFrame B p r from rfl,signedFrame_mutate,hp1,signedFrame_height]
    exact hNextHigh
  have hIncC := zero_incident_from_low C hsC 0 1 (by decide) hzC H hLowC
  let b := C 0 2
  let c := -C 0 3
  let d := C 1 2
  let E := C 1 3
  have hrep : C=peak b c d E H := by
    simpa only [peak,b,c,d,E,neg_neg,hzC,hCF] using (ofSix_reconstruct C hsC).symm
  have hneg : correction (-b) (-c)<0 := by
    have hh := (hLowC 2 3).2
    rw [hrep] at hh
    change (H:Int)+1+correction (-b) (-c)≤(H:Int) at hh
    omega
  obtain ⟨hb,hc⟩ := correction_negative_inputs (-b) (-c) hneg
  have hmaC : MutationAcyclic C := (signedFrame_MA B hs p r).mpr hma
  rw [hrep] at hmaC hIncC hLowC hNextC hNextHighC
  have hh := normalized_second_high_other_low hExist hEnd b c d E H
    (by omega) (by omega) hIncC hLowC hNextC hNextHighC hmaC
  rw [←hrep] at hh
  rw [show C=signedFrame B p r from rfl,signedFrame_mutate,signedFrame_mutate,hp0,hp1] at hh
  exact (signedFrame_height _ p r H).mp hh

#print axioms second_high_correction_zero
#print axioms normalized_second_high_other_low
#print axioms zero_incident_from_low
#print axioms opposite_top
#print axioms actual_second_high_other_low
end Rank4Round2.ZeroOrbitGeometry
