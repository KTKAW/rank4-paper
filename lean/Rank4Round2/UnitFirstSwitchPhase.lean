import Rank4CoordinatorR2.ResidualUnitExcursion
import Rank4ReviewRound2.UnitPrefixMinimal

/-! Actual first outside-pair decomposition of a corrected residual unit
packet. Profile minimality leaves only two initial pair phases. No triangle
shape or later return pattern is inferred. -/
namespace Rank4Round2.UnitFirstSwitchPhase
open QuiverProofs Rank4Coordinator Rank4CoordinatorR2 Rank4Round2
open ResidualUnitExcursion Rank4ReviewRound2.UnitPrefixMinimal

theorem first_outside (i j : Fin 4) (w : List (Fin 4))
    (h : ∃ k∈w,k≠i ∧ k≠j) :
    ∃ pre k post,w=pre++k::post ∧ (∀ a∈pre,a=i ∨ a=j) ∧ k≠i ∧ k≠j := by
  induction w with
  | nil => simp at h
  | cons a w ih =>
    by_cases ha : a=i ∨ a=j
    · have ht : ∃ k∈w,k≠i ∧ k≠j := by
        obtain ⟨k,hk,hki,hkj⟩ := h
        rcases List.mem_cons.mp hk with rfl|hk
        · rcases ha with ha|ha
          · exact False.elim (hki ha)
          · exact False.elim (hkj ha)
        · exact ⟨k,hk,hki,hkj⟩
      obtain ⟨pre,k,post,he,hp,hki,hkj⟩ := ih ht
      refine ⟨a::pre,k,post,by simpa only [List.cons_append] using congrArg (List.cons a) he,?_,hki,hkj⟩
      intro b hb
      rcases List.mem_cons.mp hb with rfl|hb
      · exact ha
      · exact hp b hb
    · refine ⟨[],a,w,rfl,by simp,?_,?_⟩ <;> intro he
      · exact ha (Or.inl he)
      · exact ha (Or.inr he)

theorem proper_block_high (Q : Rank4Input) (H : Nat)
    (w lead : List (Fin 4)) (i j : Fin 4) (mid tail : List (Fin 4))
    (hp : Packet Q H w lead i j mid tail) (u v : List (Fin 4))
    (he : (i::j::mid)=u++v) (hu : u≠[]) (hv : v≠[]) :
    ¬HeightLe (applyWord (applyWord Q.val lead) u) H := by
  cases u with
  | nil => exact False.elim (hu rfl)
  | cons a u =>
    have ha : i=a := (List.cons.inj he).1
    subst a
    have ht : (j::mid)=u++v := (List.cons.inj he).2
    exact hp.properHigh u v ht hv

private theorem prefix_shape (i j k : Fin 4) (mid pre post : List (Fin 4))
    (he : (i::j::mid)=pre++k::post) (hki : k≠i) (hkj : k≠j)
    (hp : ∀ a∈pre,a=i ∨ a=j) (hl : pre.length≤3)
    (hn : ∀ u a v,pre≠u++a::a::v) : pre=[i,j] ∨ pre=[i,j,i] := by
  cases pre with
  | nil => exact False.elim (hki (List.cons.inj he).1.symm)
  | cons a pre =>
    have ha : a=i := (List.cons.inj he).1.symm
    subst a
    have ht : (j::mid)=pre++k::post := (List.cons.inj he).2
    cases pre with
    | nil => exact False.elim (hkj (List.cons.inj ht).1.symm)
    | cons b pre =>
      have hb : b=j := (List.cons.inj ht).1.symm
      subst b
      cases pre with
      | nil => exact Or.inl rfl
      | cons x pre =>
        have hpre : pre=[] := by
          apply List.length_eq_zero_iff.mp
          simp only [List.length_cons] at hl
          omega
        subst pre
        rcases hp x (by simp) with hx|hx
        · subst x;exact Or.inr rfl
        · subst x;exact False.elim (hn [i] j [] rfl)

theorem packet_first_switch_two_phases (Q : Rank4Input) (H : Nat)
    (w lead : List (Fin 4)) (i j : Fin 4) (mid tail : List (Fin 4))
    (hp : Packet Q H w lead i j mid tail) :
    ∃ pre k post,(i::j::mid)=pre++k::post ∧ k≠i ∧ k≠j ∧
      (pre=[i,j] ∨ pre=[i,j,i]) := by
  obtain ⟨pre,k,post,he,hAlphabet,hki,hkj⟩ := first_outside i j (i::j::mid) hp.thirdPivot
  have hw : w=lead++(pre++((k::post)++tail)) := by
    rw [hp.split,he,List.append_assoc]
  have hu : abs (applyWord Q.val lead i j)=1 := by
    have hh := hp.unit
    simp [mutate] at hh
    exact hh
  have hCount : ∀ v,Acyclic (applyWord Q.val v) → PrefixHeightLe Q.val v (H+1) →
      overCount Q.val w ((H+1)-1)≤overCount Q.val v ((H+1)-1) := by
    simpa only [Nat.add_sub_cancel] using hp.countMinimum
  have hHigh : ∀ u v,pre=u++v → u≠[] →
      ¬HeightLe (applyWord (applyWord Q.val lead) u) ((H+1)-1) := by
    intro u v huv hu
    simp only [Nat.add_sub_cancel]
    apply proper_block_high Q H w lead i j mid tail hp u (v++k::post)
    · rw [he,huv,List.append_assoc]
    · exact hu
    · simp
  have hl := high_constant_unit_block_length_le_three Q (H+1) w hp.acyclic hp.ceiling
    hCount lead pre ((k::post)++tail) i j hp.distinct hw hu hAlphabet hHigh
  have hn := PairWord.embedded_no_backtrack w lead pre ((k::post)++tail) hw hp.reduced
  exact ⟨pre,k,post,he,hki,hkj,prefix_shape i j k mid pre post he hki hkj hAlphabet hl hn⟩

#print axioms first_outside
#print axioms proper_block_high
#print axioms packet_first_switch_two_phases
end Rank4Round2.UnitFirstSwitchPhase
