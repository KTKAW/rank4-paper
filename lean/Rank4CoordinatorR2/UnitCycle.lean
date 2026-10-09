import Rank4CoordinatorR2.UnitPentagon
import Rank4Round2.UnitOrderedProgress

/-! Actual constant-unit-pair orbit and bounded routes. The semantic strict
unit guard retains its two named properness bridges explicitly. -/
namespace Rank4CoordinatorR2.UnitCycle
open QuiverProofs Rank4Coordinator Rank4Round2
open Census ProperObstructionSoundness Rank4ReviewRound2.PeakNormalization
open Rank4CoordinatorR2.UnitPentagon

def cyclePrefix (v : Fin 5) : List (Fin 4) :=
  match v.val with
  | 0 => [] | 1 => [0] | 2 => [0,1] | 3 => [0,1,0] | _ => [0,1,0,1]
def node (B : Matrix 4) (v : Fin 5) : Matrix 4 := applyWord B (cyclePrefix v)

theorem swap_twice (B : Matrix 4) :
    relabel (relabel B Forks.swap01) Forks.swap01=B := by
  exact relabel_inverse B Forks.swap01

theorem backward_edge (B : Matrix 4) (hs : SkewSymmetric B) (hu : |B 0 1|=1) :
    mutate B 1=relabel (node B 4) Forks.swap01 := by
  have he := unit_five_absolute B hs hu
  have hh := congrArg (fun C => mutate C 0) he
  change mutate (mutate (node B 4) 0) 0=mutate (relabel B Forks.swap01) 0 at hh
  rw [mutation_involutive,mutate_relabel] at hh
  change node B 4=relabel (mutate B 1) Forks.swap01 at hh
  have ht := congrArg (fun C => relabel C Forks.swap01) hh
  change relabel (node B 4) Forks.swap01=
    relabel (relabel (mutate B 1) Forks.swap01) Forks.swap01 at ht
  rw [swap_twice] at ht
  exact ht.symm

theorem forward_closing (B : Matrix 4) (hs : SkewSymmetric B) (hu : |B 0 1|=1) :
    mutate (node B 4) 0=relabel B Forks.swap01 := unit_five_absolute B hs hu

theorem alternate_low (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4)
    (B : Matrix 4) (hs : SkewSymmetric B) (hma : MutationAcyclic B)
    (i j : Fin 4) (hij : i≠j) (H : Nat)
    (hi : HeightLe (mutate B i) H) (hj : HeightLe (mutate B j) H)
    (hout : ¬HeightLe B H) (hu : |B i j|=1) :
    PrefixHeightLe (mutate B i) [j,i,j] H := by
  obtain ⟨p0,r0,a,b,c,d,e,f,hframe0,hslots,_,_,_,_,_,_,_,_,_,_⟩ :=
    strict_peak_normalization B hs i j hij H hi hj hout
  obtain ⟨p,r,hframe,hpref,_⟩ :=
    unit_strict_peak_ordered_progress hExist hEnd B hs hma i j hij H hi hj hout hu
  have heq : p=p0 := congrArg Prod.fst (hframe.trans hframe0.symm)
  subst p0
  have hw : (orderedUnitLocal p i).map p.toFun=[j,i,j] := by
    rcases hslots with h|h
    · simp [orderedUnitLocal,h.1,h.2]
    · have hn : p.toFun 0≠i := by rw [h.1]; exact hij.symm
      simp only [orderedUnitLocal,if_neg hn]
      simp only [List.map_cons,List.map_nil,h.1,h.2]
  rwa [hw] at hpref

theorem node_skew (B : Matrix 4) (hs : SkewSymmetric B) (v : Fin 5) :
    SkewSymmetric (node B v) := word_preserves_skew B _ hs

theorem node_MA (B : Matrix 4) (hma : MutationAcyclic B) (v : Fin 5) :
    MutationAcyclic (node B v) := by
  have hall : ∀ w : List (Fin 4), MutationAcyclic (applyWord B w) := by
    intro w
    induction w generalizing B with
    | nil => exact hma
    | cons k w ih => exact ih (mutate B k) ((mutationAcyclic_iff B k).mpr hma)
  exact hall _

theorem node_unit (B : Matrix 4) (hu : |B 0 1|=1) (v : Fin 5) :
    |node B v 0 1|=1 := by
  have hv : v=0 ∨ v=1 ∨ v=2 ∨ v=3 ∨ v=4 := by omega
  rcases hv with rfl|rfl|rfl|rfl|rfl <;>
    simp [node,cyclePrefix,applyWord,mutate,abs_neg,hu]

theorem short_to_node (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4)
    (B : Matrix 4) (hs : SkewSymmetric B) (hma : MutationAcyclic B)
    (hu : |B 0 1|=1) (H : Nat) (hB : HeightLe B H)
    (v : Fin 5) (hv : HeightLe (node B v) H) :
    ∃ (w : List (Fin 4)) (p : Relabeling 4), w.length≤3 ∧
      PrefixHeightLe B w H ∧ applyWord B w=relabel (node B v) p := by
  have he := backward_edge B hs hu
  have hc := forward_closing B hs hu
  have hv5 : v=0 ∨ v=1 ∨ v=2 ∨ v=3 ∨ v=4 := by omega
  rcases hv5 with rfl|rfl|rfl|rfl|rfl
  · exact ⟨[],.identity 4,by decide,(prefixHeight_nil B H).mpr hB,rfl⟩
  · refine ⟨[0],.identity 4,by decide,?_,rfl⟩
    exact (prefixHeight_cons B 0 [] H).mpr ⟨hB,(prefixHeight_nil _ H).mpr hv⟩
  · by_cases h1 : HeightLe (node B 1) H
    · refine ⟨[0,1],.identity 4,by decide,?_,rfl⟩
      simp only [prefixHeight_cons,prefixHeight_nil]
      exact ⟨hB,h1,hv⟩
    · have hl := alternate_low hExist hEnd (node B 1) (node_skew B hs 1)
        (node_MA B hma 1) 0 1 (by decide) H
        (by simpa only [node,cyclePrefix,applyWord,mutation_involutive] using hB)
        hv h1 (node_unit B hu 1)
      change PrefixHeightLe (mutate (mutate B 0) 0) [1,0,1] H at hl
      rw [mutation_involutive] at hl
      refine ⟨[1,0,1],Forks.swap01,by decide,hl,?_⟩
      simp only [applyWord,he,mutate_relabel]
      change relabel (mutate (mutate (node B 4) 1) 0) Forks.swap01=_
      simp only [node,cyclePrefix,applyWord,mutation_involutive]
  · by_cases h4 : HeightLe (node B 4) H
    · refine ⟨[1,0],Forks.swap01,by decide,?_,?_⟩
      · simp only [prefixHeight_cons,prefixHeight_nil]
        refine ⟨hB,?_,?_⟩
        · rw [he,heightLe_relabel_iff]; exact h4
        · rw [he,mutate_relabel,heightLe_relabel_iff]
          simpa only [Forks.swap01,node,cyclePrefix,applyWord,mutation_involutive] using hv
      · simp only [applyWord,he,mutate_relabel]
        simp only [Forks.swap01,node,cyclePrefix,applyWord,mutation_involutive]
    · have hs4 := node_skew B hs 4
      have hu4 := node_unit B hu 4
      have hl := alternate_low hExist hEnd (node B 4) hs4 (node_MA B hma 4)
        0 1 (by decide) H
        (by rw [hc,heightLe_relabel_iff]; exact hB)
        (by simpa only [node,cyclePrefix,applyWord,mutation_involutive] using hv)
        h4 hu4
      rw [hc] at hl
      have hm : ([0,1,0] : List (Fin 4)).map Forks.swap01.invFun=[1,0,1] := rfl
      rw [←hm,prefixHeight_relabel_iff] at hl
      exact ⟨[0,1,0],.identity 4,by decide,hl,rfl⟩
  · refine ⟨[1],Forks.swap01,by decide,?_,?_⟩
    · simp only [prefixHeight_cons,prefixHeight_nil]
      refine ⟨hB,?_⟩
      rw [he,heightLe_relabel_iff]
      exact hv
    · exact he

#print axioms alternate_low
#print axioms short_to_node
end Rank4CoordinatorR2.UnitCycle
