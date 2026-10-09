import Rank4StructureRound2.TwoStateScalar
import Rank4CoordinatorR2.ScalarPathBudget

/-! Sign normalization for a two-state block, preserving pivots 0 and 1.
Reversal and swapping only vertices 2,3 make both the pivot and opposite
entry positive. The entry and exit mutation labels stay fixed. -/
namespace QuiverProofs.Rank4StructureRound2.TwoStateFrame
open Census ProperOrder ProperWiggle ProperMutation ProperObstructionSoundness
open Rank4Coordinator Rank4CoordinatorR2.FlatHalfShape
open Rank4ReviewRound2.PeakNormalization TwoStateScalar
set_option maxHeartbeats 4000000

def swap23 : Relabeling 4 :=
  ⟨fun i=>match i.val with | 0=>0 | 1=>1 | 2=>3 | _=>2,
   fun i=>match i.val with | 0=>0 | 1=>1 | 2=>3 | _=>2,by decide,by decide⟩

theorem positive_pair_opposite_frame (B : Matrix 4) (hs : SkewSymmetric B) :
    ∃ (p : Relabeling 4) (r : Bool),p.toFun 0=0 ∧ p.toFun 1=1 ∧
      signedFrame B p r 0 1=abs (B 0 1) ∧ signedFrame B p r 2 3=abs (B 2 3) := by
  have h32 := hs 3 2
  by_cases ha : 0≤B 0 1
  · by_cases hf : 0≤B 2 3
    · refine ⟨.identity 4,false,?_,?_,?_,?_⟩ <;>
        simp [signedFrame,relabel,Relabeling.identity,abs_of_nonneg ha,abs_of_nonneg hf]
    · have hf' : B 2 3≤0 := by omega
      refine ⟨swap23,false,?_,?_,?_,?_⟩ <;>
        simp [signedFrame,relabel,swap23,h32,abs_of_nonneg ha,abs_of_nonpos hf']
  · have ha' : B 0 1≤0 := by omega
    by_cases hf : 0≤B 2 3
    · refine ⟨swap23,true,?_,?_,?_,?_⟩ <;>
        simp [signedFrame,relabel,reverse,swap23,h32,abs_of_nonpos ha',abs_of_nonneg hf]
    · have hf' : B 2 3≤0 := by omega
      refine ⟨.identity 4,true,?_,?_,?_,?_⟩ <;>
        simp [signedFrame,relabel,reverse,Relabeling.identity,abs_of_nonpos ha',abs_of_nonpos hf']

theorem half_peak_normalization (B : Matrix 4) (hs : SkewSymmetric B) (H : Nat)
    (hP : HeightLe B (H+1)) (h0 : HeightLe (mutate B 0) H)
    (h1 : HeightLe (mutate B 1) (H+1)) (hout : ¬HeightLe B H)
    (hpair : 2≤abs (B 0 1)) :
    ∃ (p : Relabeling 4) (r : Bool) (a b c d E f : Int),
      p.toFun 0=0 ∧ p.toFun 1=1 ∧ 2≤a ∧ 0<b ∧ 0<c ∧ f=(H:Int)+1 ∧
      signedFrame B p r=Q a b c d E f := by
  have htop := opposite_top B hs H hP h0 h1 hpair hout
  obtain ⟨p,r,hp0,hp1,hpair',hopposite⟩ := positive_pair_opposite_frame B hs
  let C := signedFrame B p r
  have hC : SkewSymmetric C := signedFrame_skew B hs p r
  have hf : C 2 3=(H:Int)+1 := hopposite.trans htop
  have ha : 2≤C 0 1 := by
    change 2≤signedFrame B p r 0 1
    rw [hpair']; exact hpair
  have hC0 : HeightLe (mutate C 0) H := by
    rw [signedFrame_mutate,hp0,signedFrame_height];exact h0
  have hlast := hC0 2 3
  change -(H:Int)≤C 2 3+correction (C 2 0) (C 0 3) ∧
    C 2 3+correction (C 2 0) (C 0 3)≤(H:Int) at hlast
  have hsign := correction_negative_inputs (C 2 0) (C 0 3)
    (show correction (C 2 0) (C 0 3)<0 by omega)
  have h20 := hC 2 0
  refine ⟨p,r,C 0 1,C 0 2,-C 0 3,C 1 2,C 1 3,C 2 3,hp0,hp1,ha,
    by omega,by omega,hf,?_⟩
  simpa only [Q,Int.neg_neg] using (ofSix_reconstruct C hC).symm

#print axioms positive_pair_opposite_frame
#print axioms half_peak_normalization
end QuiverProofs.Rank4StructureRound2.TwoStateFrame
