import Rank4CoordinatorR2.UnitOrbit

/-! Whole-witness progress for arbitrary labeled constant-unit-pair blocks.
Actual endpoint and suffix frames are transported, with the same supplied
whole ceiling and a strict drop of the count above H. -/
namespace Rank4CoordinatorR2.UnitBlock
open QuiverProofs Rank4Coordinator Rank4Round2
open Census ProperObstructionSoundness Rank4ReviewRound2.PeakNormalization
open Rank4CoordinatorR2.UnitOrbit

theorem arbitrary_unit_pair_route (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4)
    (B : Matrix 4) (hs : SkewSymmetric B) (hma : MutationAcyclic B)
    (i j : Fin 4) (hij : i≠j) (hu : |B i j|=1) (H : Nat) (hB : HeightLe B H)
    (old : List (Fin 4)) (hp : ∀ k∈old,k=i ∨ k=j)
    (hend : HeightLe (applyWord B old) H) :
    ∃ (new : List (Fin 4)) (q : Relabeling 4), new.length≤3 ∧
      PrefixHeightLe B new H ∧ applyWord B new=relabel (applyWord B old) q := by
  let p := pivotFrame i j
  have hslots := pivotFrame_slots i j hij
  change p.toFun 0=i ∧ p.toFun 1=j at hslots
  have hi : p.invFun i=0 := by
    simpa only [p.left_inv] using (congrArg p.invFun hslots.1).symm
  have hj : p.invFun j=1 := by
    simpa only [p.left_inv] using (congrArg p.invFun hslots.2).symm
  let C := relabel B p
  have huC : |C 0 1|=1 := by
    change |B (p.toFun 0) (p.toFun 1)|=1
    simpa only [p,hslots.1,hslots.2] using hu
  have hpC : ∀ k∈old.map p.invFun,k=0 ∨ k=1 := by
    intro k hk
    obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hk
    rcases hp l hl with h|h
    · left; simpa only [h] using hi
    · right; simpa only [h] using hj
  have heC : applyWord C (old.map p.invFun)=relabel (applyWord B old) p := by
    dsimp only [C]
    rw [word_relabel,map_inverse_word]
  have hB_C : HeightLe C H := (heightLe_relabel_iff B p H).mpr hB
  have hE_C : HeightLe (applyWord C (old.map p.invFun)) H := by
    rw [heC,heightLe_relabel_iff]
    exact hend
  obtain ⟨new,q,hlen,hpre,he⟩ := unit_pair_bounded_route hExist hEnd C
    (relabel_skew B p hs) ((MA_relabel_iff B p).mpr hma) huC H hB_C
    (old.map p.invFun) hpC hE_C
  have hh := congrArg (fun X => relabel X p.symm) he
  have hendNew : applyWord B (new.map p.toFun)=
      relabel (applyWord B old) ((p.trans q).trans p.symm) := by
    rw [word_relabel,heC] at hh
    change relabel (relabel (applyWord B (new.map p.toFun)) p) p.symm=
      relabel (relabel (relabel (applyWord B old) p) q) p.symm at hh
    rw [relabel_inverse] at hh
    simpa only [Relabeling.symm,←relabel_trans] using hh
  refine ⟨new.map p.toFun,(p.trans q).trans p.symm,by simpa using hlen,?_,hendNew⟩
  exact (signedFrame_forward_prefix B p false new H).mp hpre

theorem unit_block_in_witness_progress (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4)
    (Q : Matrix 4) (hs : SkewSymmetric Q) (lead old tail : List (Fin 4))
    (i j : Fin 4) (hij : i≠j) (hu : |applyWord Q lead i j|=1)
    (hp : ∀ k∈old,k=i ∨ k=j) (H K : Nat) (hHK : H≤K)
    (hLeft : HeightLe (applyWord Q lead) H)
    (hRight : HeightLe (applyWord Q (lead++old)) H)
    (hPath : PrefixHeightLe Q (lead++(old++tail)) K)
    (ha : Acyclic (applyWord Q (lead++(old++tail))))
    (hover : 0<overCount (applyWord Q lead) old H) :
    ∃ (new : List (Fin 4)) (p : Relabeling 4), new.length≤3 ∧
      PrefixHeightLe Q (lead++(new++tail.map p.invFun)) K ∧
      Acyclic (applyWord Q (lead++(new++tail.map p.invFun))) ∧
      overCount Q (lead++(new++tail.map p.invFun)) H <
        overCount Q (lead++(old++tail)) H := by
  let B := applyWord Q lead
  change 0<overCount B old H at hover
  have hsB := word_preserves_skew Q lead hs
  have haLocal : Acyclic (applyWord B (old++tail)) := by
    rwa [applyWord_append] at ha
  have hmaB : MutationAcyclic B := ⟨old++tail,haLocal⟩
  have hR : HeightLe (applyWord B old) H := by
    rwa [applyWord_append] at hRight
  obtain ⟨new,p,hlen,hnew,he⟩ := arbitrary_unit_pair_route hExist hEnd B hsB hmaB
    i j hij hu H hLeft old hp hR
  obtain ⟨hlead,hlocal⟩ := (prefixHeight_append_iff Q lead (old++tail) K).mp hPath
  have ht := ((prefixHeight_append_iff B old tail K).mp hlocal).2
  have hpre := reroute_prefixHeight B old new tail p K he
    (prefixHeight_mono B new H K hHK hnew) ht
  have hacyc : Acyclic (applyWord B (new++tail.map p.invFun)) := by
    rw [reroute_endpoint B old new tail p he]
    exact (acyclic_relabel_iff _ p).mpr haLocal
  have hcount : overCount B (new++tail.map p.invFun) H + overCount B old H=
      overCount B (old++tail) H := by
    rw [overCount_append,he,overCount_relabel,overCount_eq_zero B new H hnew,
      overCount_append]
    omega
  refine ⟨new,p,hlen,prefixHeight_append Q lead _ K hlead hpre,?_,?_⟩
  · rw [applyWord_append]
    exact hacyc
  · rw [overCount_append Q lead (new++tail.map p.invFun) H,
      overCount_append Q lead (old++tail) H]
    change overCount Q lead H+overCount B (new++tail.map p.invFun) H <
      overCount Q lead H+overCount B (old++tail) H
    omega

#print axioms arbitrary_unit_pair_route
#print axioms unit_block_in_witness_progress
end Rank4CoordinatorR2.UnitBlock
