import Rank4CoordinatorR2.FlatSwitch
import Rank4StructureRound2.TwoStateFrame
import Rank4Round2.AllSignUnitBridge
import Rank4CoordinatorR2.EndpointFoundation

/-! At a high half-entry through a strong pivot pair, neither complementary
vertex can give a next state inside the ceiling above the original scalar
budget. This constrains the first state only; arbitrary later pivot changes
and full plateau coverage remain separate obligations. -/
namespace Rank4CoordinatorR2.FirstStrongEntry
open QuiverProofs Rank4Coordinator Rank4CoordinatorR2 Rank4Round2
open ProperObstructionSoundness Rank4ReviewRound2.PeakNormalization
open QuiverProofs.Rank4StructureRound2.TwoStateFrame

theorem positive_opposite_at_two (B : Matrix 4) (hs : SkewSymmetric B)
    (k : Fin 4) (hk : k=2 ∨ k=3) :
    ∃ (p : Relabeling 4) (r : Bool), p.toFun 0=0 ∧ p.toFun 1=1 ∧
      p.toFun 2=k ∧ signedFrame B p r 2 3=abs (B 2 3) := by
  have h32 := hs 3 2
  rcases hk with rfl|rfl
  · by_cases hf : 0≤B 2 3
    · refine ⟨.identity 4,false,?_,?_,?_,?_⟩ <;>
        simp [signedFrame,relabel,Relabeling.identity,abs_of_nonneg hf]
    · have hf' : B 2 3≤0 := by omega
      refine ⟨.identity 4,true,?_,?_,?_,?_⟩ <;>
        simp [signedFrame,relabel,reverse,Relabeling.identity,abs_of_nonpos hf']
  · by_cases hf : 0≤B 2 3
    · refine ⟨swap23,true,?_,?_,?_,?_⟩ <;>
        simp [signedFrame,relabel,reverse,swap23,h32,abs_of_nonneg hf]
    · have hf' : B 2 3≤0 := by omega
      refine ⟨swap23,false,?_,?_,?_,?_⟩ <;>
        simp [signedFrame,relabel,swap23,h32,abs_of_nonpos hf']

theorem actual_first_entry_no_third_pivot
    (hExist : MAHasTotalProper4) (Q : Rank4Input)
    (hma : MutationAcyclic Q.val) (lead : List (Fin 4))
    (i j : Fin 4) (hij : i≠j) (H : Nat)
    (hBudget : scalarBudget Q.val≤H)
    (hP : HeightLe (applyWord Q.val lead) (H+1))
    (hi : HeightLe (mutate (applyWord Q.val lead) i) H)
    (hj : HeightLe (mutate (applyWord Q.val lead) j) (H+1))
    (hout : ¬HeightLe (applyWord Q.val lead) H)
    (ha : 2≤abs (applyWord Q.val lead i j))
    (k : Fin 4) (hki : k≠i) (hkj : k≠j) :
    ¬HeightLe (mutate (applyWord Q.val lead) k) (H+1) := by
  intro hk
  let P := applyWord Q.val lead
  let pp := pivotFrame i j
  let B := relabel P pp
  have hsP : SkewSymmetric P := word_preserves_skew Q.val lead Q.property
  have hsB : SkewSymmetric B := relabel_skew P pp hsP
  have hs := pivotFrame_slots i j hij
  have hp0 : pp.toFun 0=i := hs.1
  have hp1 : pp.toFun 1=j := hs.2
  have hBP : HeightLe B (H+1) := (heightLe_relabel_iff P pp (H+1)).mpr hP
  have hB0 : HeightLe (mutate B 0) H := by
    change HeightLe (mutate (relabel P pp) 0) H
    rw [mutate_relabel,heightLe_relabel_iff,hp0]
    exact hi
  have hB1 : HeightLe (mutate B 1) (H+1) := by
    change HeightLe (mutate (relabel P pp) 1) (H+1)
    rw [mutate_relabel,heightLe_relabel_iff,hp1]
    exact hj
  have hBa : 2≤abs (B 0 1) := by
    change 2≤abs (P (pp.toFun 0) (pp.toFun 1))
    rw [hp0,hp1]
    exact ha
  have hBo : ¬HeightLe B H := fun h => hout ((heightLe_relabel_iff P pp H).mp h)
  have htop := FlatHalfShape.opposite_top B hsB H hBP hB0 hB1 hBa hBo
  let t := pp.invFun k
  have ht : t=2 ∨ t=3 := by
    have ht0 : t≠0 := by
      intro h
      have he : k=i := by simpa [t,h,hp0] using (pp.right_inv k).symm
      exact hki he
    have ht1 : t≠1 := by
      intro h
      have he : k=j := by simpa [t,h,hp1] using (pp.right_inv k).symm
      exact hkj he
    omega
  have hBt : HeightLe (mutate B t) (H+1) := by
    change HeightLe (mutate (relabel P pp) (pp.invFun k)) (H+1)
    rw [mutate_relabel,pp.right_inv,heightLe_relabel_iff]
    exact hk
  have hunit := FlatSwitch.switch_forces_unit B hsB H htop hB0 t ht hBt
  obtain ⟨p,r,hp0',hp1',hp2',hf⟩ := positive_opposite_at_two B hsB t ht
  let C := signedFrame B p r
  have hsC : SkewSymmetric C := signedFrame_skew B hsB p r
  have hF : C 2 3=(H:Int)+1 := hf.trans htop
  have hCA : 2≤abs (C 0 1) := by
    cases r <;> simpa [C,signedFrame,relabel,reverse,hp0',hp1',abs_neg] using hBa
  have hCb : abs (C 0 2)=1 := by
    cases r <;> simpa [C,signedFrame,relabel,reverse,hp0',hp2',abs_neg] using hunit
  have hCP : HeightLe C (H+1) := (signedFrame_height B p r (H+1)).mpr hBP
  have hC0 : HeightLe (mutate C 0) (H+1) := by
    rw [show C=signedFrame B p r from rfl,signedFrame_mutate,hp0',signedFrame_height]
    intro u v
    have hv := hB0 u v
    constructor <;> omega
  have hC2 : HeightLe (mutate C 2) (H+1) := by
    rw [show C=signedFrame B p r from rfl,signedFrame_mutate,hp2',signedFrame_height]
    exact hBt
  let S := FlatUnitBridge.unitShape (C 0 1) (C 0 2) (C 0 3) (C 1 2) (C 1 3) H
  have heq : C=S := by
    simpa only [S,FlatUnitBridge.unitShape,hF] using (ofSix_reconstruct C hsC).symm
  have hrep : signedFrame (applyWord Q.val lead) (pp.trans p) r=S := heq
  have hcontra := AllSignUnitBridge.no_initial_scalar_budget_switch hExist
    EndpointFoundation.endpoint_bridge Q lead (pp.trans p) r
    (C 0 1) (C 0 2) (C 0 3) (C 1 2) (C 1 3) H hBudget hrep hCA hCb
    (by change HeightLe S (H+1); rwa [←heq])
    (by change HeightLe (mutate S 0) (H+1); rwa [←heq])
    (by change HeightLe (mutate S 2) (H+1); rwa [←heq])
  exact hcontra hma

#print axioms positive_opposite_at_two
#print axioms actual_first_entry_no_third_pivot
end Rank4CoordinatorR2.FirstStrongEntry
