import Rank4Round2.NonzeroExitGeometry

/-! Every nonzero opposite-top exit from the stated preceding incident
bounds is excluded above the actual input scalar budget. Zero connectors
and suppliers of those incident bounds remain separate obligations.+-/
namespace Rank4Round2.NonzeroExitConsumer
open QuiverProofs Rank4Coordinator Rank4CoordinatorR2 Rank4Round2
open ProperOrder ProperWiggle ProperMutation ProperObstructionSoundness
open Rank4ReviewRound2.PeakNormalization FlatUnitBridge

private theorem four (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega

theorem acyclic_negative_connector (A b C d E : Int) (H : Nat)
    (hb : b<0) (hC : C≤0) (hd : d≤0) (hg : A<0 ∨ E≤0) :
    Acyclic (unitShape A b C d E H) := by
  by_cases hA : A<0
  · by_cases hE : 0≤E
    · refine ⟨fun i => match i.val with | 0=>3 | 1=>1 | 2=>0 | _=>2,?_⟩
      intro i j h
      rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
        simp [unitShape,ofSix] at * <;> omega
    · refine ⟨fun i => match i.val with | 0=>3 | 1=>2 | 2=>0 | _=>1,?_⟩
      intro i j h
      rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
        simp [unitShape,ofSix] at * <;> omega
  · have hE : E≤0 := by rcases hg with hg|hg <;> omega
    refine ⟨fun i => match i.val with | 0=>2 | 1=>3 | 2=>0 | _=>1,?_⟩
    intro i j h
    rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
      simp [unitShape,ofSix] at * <;> omega

theorem no_nonzero_exit
    (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4)
    (Q : Rank4Input) (lead : List (Fin 4)) (p : Relabeling 4) (r : Bool)
    (A b C d E : Int) (H : Nat) (hBudget : scalarBudget Q.val≤H)
    (hrep : signedFrame (applyWord Q.val lead) p r=unitShape A b C d E H)
    (hA : 2≤abs A) (hb : b≠0)
    (hP : HeightLe (unitShape A b C d E H) (H+1))
    (h0 : HeightLe (mutate (unitShape A b C d E H) 0) (H+1))
    (h2 : HeightLe (mutate (unitShape A b C d E H) 2) (H+1))
    (h03 : -(H:Int)≤mutate (unitShape A b C d E H) 0 0 3 ∧
      mutate (unitShape A b C d E H) 0 0 3≤(H:Int))
    (h13 : -(H:Int)≤mutate (unitShape A b C d E H) 0 1 3 ∧
      mutate (unitShape A b C d E H) 0 1 3≤(H:Int)) :
    ¬MutationAcyclic Q.val := by
  intro hma
  let P := unitShape A b C d E H
  let B := applyWord Q.val lead
  have hre : signedFrame B p r=P := hrep
  have hmaP : MutationAcyclic P := by
    rw [←hre]
    exact (signedFrame_MA _ (word_preserves_skew Q.val lead Q.property) p r).mpr
      ((mutationAcyclic_word_iff Q.val lead).mpr hma)
  obtain ⟨q,hq⟩ := hExist P (ofSix_skew _ _ _ _ _ _) hmaP
  have hq' : TotalProper (signedFrame B p r) q := by rwa [hre]
  have hbudget := ScalarPathBudget.lead_totalProper_scalar_budget Q.val Q.property lead p r q hq'
  rw [hre] at hbudget
  have habsm := Int.le_natAbs (a:=orderMarkov P q)
  have hM : orderMarkov P q≤(H:Int) := by omega
  have hn := QuiverProofs.Rank4StructureRound2.SuperScalarPeak.MA_totalProper_pfaffian_bound
    hEnd P (ofSix_skew _ _ _ _ _ _) hmaP q hq
  have hpf : matrixPfaffian P=A*((H:Int)+1)-b*E+C*d := by
    simp [P,unitShape,matrixPfaffian,ofSix]
  have hF : 0<(H:Int)+1 := by omega
  obtain ⟨hC,hClo,hElo,hUnit,hd,hE1⟩ := NonzeroExitGeometry.exit_geometry A b C d E H hb h0 h2 h03 h13
  by_cases hbp : 0<b
  · have hb1 := hUnit hbp
    subst b
    exact AllSignUnitBridge.no_low_totalProper_scalar_switch hEnd A 1 C d E H hA
      (by decide) hP h0 h2 q hq hM hmaP
  · have hbn : b<0 := by omega
    by_cases hd0 : d≤0
    · by_cases hac : A<0 ∨ E≤0
      · have ha := acyclic_negative_connector A b C d E H hbn hC hd0 hac
        obtain ⟨t,ht,hqt⟩ := hEnd P (ofSix_skew _ _ _ _ _ _) ha q hq
        have heq := ProperWiggleInvariants.markov_wiggle_invariant P (ofSix_skew _ _ _ _ _ _) hqt
        have hh := topological_height_budget P (ofSix_skew _ _ _ _ _ _) t ht
        have hf := (hh 2 3).2
        change (H:Int)+1≤((orderMarkov P t).natAbs:Int) at hf
        rw [←heq] at hf
        have hm0 : 0≤orderMarkov P q := by have h := abs_nonneg (matrixPfaffian P); omega
        rw [Int.natCast_natAbs,abs_of_nonneg hm0] at hf
        omega
      · have hapos : 2≤A := by
          have ha0 : 0≤A := by omega
          rw [abs_of_nonneg ha0] at hA
          exact hA
        have hbE := mul_nonneg (show 0≤ -b by omega) (show 0≤E by omega)
        have hCd := mul_nonneg (show 0≤ -C by omega) (show 0≤ -d by omega)
        have hAf := mul_nonneg (show 0≤A-2 by omega) (show 0≤(H:Int)+1 by omega)
        have hp : 2*((H:Int)+1)≤matrixPfaffian P := by rw [hpf]; nlinarith
        have ha := le_abs_self (matrixPfaffian P)
        omega
    · have hd1 : d=1 := by omega
      have he : E≤0 := hE1 hd1
      subst d
      by_cases hapos : 2≤A
      · have hAlt := NonzeroExitGeometry.alternate_neighbor A b C E H hapos hbn he hP
        let s := p.trans (vertexSwap 0 1)
        have hs0 : s.toFun 0=p.toFun 1 := by simp [s,Relabeling.trans,vertexSwap]
        have hs1 : s.toFun 1=p.toFun 0 := by simp [s,Relabeling.trans,vertexSwap]
        have hs2 : s.toFun 2=p.toFun 2 := by
          change p.toFun ((Equiv.swap (0:Fin 4) 1) 2)=p.toFun 2
          congr 1
        have hs3 : s.toFun 3=p.toFun 3 := by
          change p.toFun ((Equiv.swap (0:Fin 4) 1) 3)=p.toFun 3
          congr 1
        have hcoord : ∀ i j, abs (B (p.toFun i) (p.toFun j))=abs (P i j) := by
          intro i j
          rw [←hre]
          cases r <;> simp [signedFrame,relabel,reverse,abs_neg]
        have haS : 2≤abs (B (s.toFun 0) (s.toFun 1)) := by
          rw [hs0,hs1,hcoord]
          simpa [P,unitShape,ofSix,abs_neg] using hA
        have hbS : abs (B (s.toFun 0) (s.toFun 2))=1 := by
          rw [hs0,hs2,hcoord]
          simp [P,unitShape,ofSix]
        have hfS : abs (B (s.toFun 2) (s.toFun 3))=(H:Int)+1 := by
          rw [hs2,hs3,hcoord]
          simp [P,unitShape,ofSix,abs_of_nonneg (show 0≤(H:Int)+1 by omega)]
        have hOrig : HeightLe B (H+1) := (signedFrame_height B p r _).mp (by rwa [hre])
        have hOrig1 : HeightLe (mutate B (p.toFun 1)) (H+1) := by
          have hh : HeightLe (mutate (signedFrame B p r) 1) (H+1) := by rwa [hre]
          rw [signedFrame_mutate] at hh
          exact (signedFrame_height _ p r _).mp hh
        have hOrig2 : HeightLe (mutate B (p.toFun 2)) (H+1) := by
          have hh : HeightLe (mutate (signedFrame B p r) 2) (H+1) := by rwa [hre]
          rw [signedFrame_mutate] at hh
          exact (signedFrame_height _ p r _).mp hh
        exact AllFrameUnitBridge.arbitrary_label_unit_switch hExist hEnd Q lead s H hBudget
          haS hbS hfS hOrig (by rwa [hs0]) (by rwa [hs2]) hma
      · have han : A≤ -2 := by
          by_cases hnn : 0≤A
          · rw [abs_of_nonneg hnn] at hA; omega
          · rw [abs_of_nonpos (show A≤0 by omega)] at hA; omega
        have hbE := mul_nonneg (show 0≤ -b by omega) (show 0≤ -E by omega)
        have hAf := mul_nonneg (show 0≤ -A-2 by omega) (show 0≤(H:Int)+1 by omega)
        have hp : matrixPfaffian P≤ -2*((H:Int)+1) := by rw [hpf]; nlinarith
        have ha := neg_le_abs (matrixPfaffian P)
        omega

#print axioms acyclic_negative_connector
#print axioms no_nonzero_exit
end Rank4Round2.NonzeroExitConsumer
