import Rank4StructureRound2.StableFirstSwitch
import Rank4StructureRound2.StableLaterSwitch

/-! Whole-word stable-cone trap. A reduced word beginning at the strong
forward pivot stays in its pair at every ceiling-bounded prefix. The first
forward state retains its zero-wall scalar exception; later states use
strict rows. This supplies a normalized arbitrary-word result, with actual
MA, proper scalar, and endpoint bridge premises explicit. -/
namespace QuiverProofs.Rank4StructureRound2.StableWordAssembly
open Census ProperOrder ProperWiggle ProperMutation ProperObstructionSoundness
open Rank4Coordinator Rank4Round2 Rank4ReviewRound2.StrongPairIncident
open TwoStateScalar MixedExitGeometry StableFirstSwitch StableLaterSwitch
set_option maxHeartbeats 4000000

def ReducedAfter (prev : Fin 4) : List (Fin 4) → Prop
  | [] => True
  | k::w => k≠prev ∧ ReducedAfter k w

theorem no_backtrack_reduced_after (i : Fin 4) (w : List (Fin 4))
    (hnr : ∀ u k v,(i::w)≠u++k::k::v) : ReducedAfter i w := by
  induction w generalizing i with
  | nil => trivial
  | cons k w ih =>
    refine ⟨?_,?_⟩
    · intro he
      subst k
      exact hnr [] i w rfl
    · apply ih k
      intro u l v he
      apply hnr (i::u) l v
      simpa only [List.cons_append] using congrArg (List.cons i) he

theorem strict_aligned_reduced_word_is_alternating (w : List (Fin 4))
    (B : Matrix 4) (hs : SkewSymmetric B) (i j : Fin 4)
    (hp : (i=0 ∧ j=1) ∨ (i=1 ∧ j=0)) (H : Nat)
    (ha : 2≤B i j) (hf : B 2 3=(H:Int)+1) (hc : Aligned B i j)
    (hstrict : ∀ l,l≠i → l≠j → B i l<0 ∧ 0<B j l)
    (hnr : ReducedAfter i w) (hceil : PrefixHeightLe B w (H+1)) :
    w=alternatingWord i j w.length := by
  induction w generalizing B i j with
  | nil => rfl
  | cons k w ih =>
    have hij : i≠j := by omega
    have hi2 : i≠2 := by omega
    have hi3 : i≠3 := by omega
    have hj2 : j≠2 := by omega
    have hj3 : j≠3 := by omega
    have h2 := hstrict 2 (Ne.symm hi2) (Ne.symm hj2)
    have h3 := hstrict 3 (Ne.symm hi3) (Ne.symm hj3)
    have hthird := strict_rows_opposite_ceiling_no_third B hs i j 2 3
      hi2 hi3 hj2 hj3 (by decide) H hf h2.1 h3.1 h2.2 h3.2
    have ht := ((prefixHeight_cons B k w (H+1)).mp hceil).2
    have hkceil : HeightLe (mutate B k) (H+1) := ht [] w rfl
    have hki : k≠i := hnr.1
    have hkj : k=j := by
      by_contra hkj
      have hk : k=2 ∨ k=3 := by omega
      rcases hk with rfl | rfl
      · exact hthird.1 hkceil
      · exact hthird.2 hkceil
    subst k
    have hs' := mutation_preserves_skew B j hs
    have ha' : 2≤mutate B j j i := by
      simp only [mutate,true_or,if_true,hs j i,Int.neg_neg]
      exact ha
    have hf' : mutate B j 2 3=(H:Int)+1 := by
      rw [aligned_opposite_step B hs i j 2 3 hij (Ne.symm hi2) (Ne.symm hj2)
        (Ne.symm hi3) (Ne.symm hj3) hc,hf]
    have hc' := aligned_step B hs i j hij ha hc
    have hstrict' := aligned_positive_step_strict B i j hij ha hc
      (fun l hli hlj => (hstrict l hli hlj).2)
    have he := ih (mutate B j) hs' j i (by omega) ha' hf' hc'
      (fun l hlj hli => hstrict' l hli hlj) hnr.2 ht
    exact congrArg (List.cons j) he

private theorem corr_positive (x y : Int) (hx : 0≤x) (hy : 0≤y) :
    correction x y=x*y := by
  simp only [correction,max_eq_left hx,max_eq_left hy,
    max_eq_right (show -x≤0 by omega),max_eq_right (show -y≤0 by omega)]
  ring

private theorem corr_nonpos_nonneg (x y : Int) (hx : x≤0) (hy : 0≤y) :
    correction x y=0 := by
  simp only [correction,max_eq_right hx,max_eq_left hy,
    max_eq_right (show -y≤0 by omega)]
  ring

theorem stable_first_reduced_word_is_alternating (a b c d E f : Int) (H : Nat)
    (ha : 2≤a) (hb : 0<b) (hc : 0<c) (hd : 0≤d) (hcE : c≤E)
    (hf : f=(H:Int)+1) (p : CyclicOrder) (hp : ProperClass (Q a b c d E f) p)
    (hM : orderMarkov (Q a b c d E f) p≤(H:Int)) (w : List (Fin 4))
    (hnr : ReducedAfter 1 w) (hceil : PrefixHeightLe (Q a b c d E f) (1::w) (H+1)) :
    (1::w)=alternatingWord 0 1 (w.length+1) := by
  have hE : 0≤E := by omega
  let B := mutate (Q a b c d E f) 1
  have hsB : SkewSymmetric B := mutation_preserves_skew _ _ (ofSix_skew _ _ _ _ _ _)
  have haB : 2≤B 1 0 := by change 2≤ -(-a); omega
  have hcB : Aligned B 1 0 := mixed_first_aligned a b c d E f ha (by omega) hd hE hcE
  have hfB : B 2 3=(H:Int)+1 := by
    change f+correction (-d) E=(H:Int)+1
    rw [corr_nonpos_nonneg _ _ (by omega) hE,Int.add_zero,hf]
  have hposB : ∀ l,l≠1 → l≠0 → 0<B 0 l := by
    intro l hl1 hl0
    have hl : l=2 ∨ l=3 := by omega
    rcases hl with rfl | rfl
    · change 0<b+correction a d
      rw [corr_positive _ _ (by omega) hd]
      have hm := mul_nonneg (show 0≤a by omega) hd
      omega
    · change 0< -c+correction a E
      rw [corr_positive _ _ (by omega) hE]
      have hm := mul_nonneg (show 0≤a-2 by omega) hE
      nlinarith
  have ht : PrefixHeightLe B w (H+1) :=
    ((prefixHeight_cons _ 1 w (H+1)).mp hceil).2
  cases w with
  | nil => rfl
  | cons k w =>
    have hki : k≠1 := hnr.1
    have htail := ((prefixHeight_cons B k w (H+1)).mp ht).2
    have hkceil : HeightLe (mutate B k) (H+1) := htail [] w rfl
    have hk0 : k=0 := by
      by_contra hk0
      have hk : k=2 ∨ k=3 := by omega
      exact stable_first_no_third a b c d E f H ha hb hc hd hcE hf p hp hM k hk hkceil
    subst k
    have hs' := mutation_preserves_skew B 0 hsB
    have ha' : 2≤mutate B 0 0 1 := by
      simp only [mutate,true_or,if_true,hsB 0 1,Int.neg_neg]
      exact haB
    have hf' : mutate B 0 2 3=(H:Int)+1 := by
      rw [aligned_opposite_step B hsB 1 0 2 3 (by decide) (by decide) (by decide)
        (by decide) (by decide) hcB,hfB]
    have hc' := aligned_step B hsB 1 0 (by decide) haB hcB
    have hstrict := aligned_positive_step_strict B 1 0 (by decide) haB hcB hposB
    have he := strict_aligned_reduced_word_is_alternating w (mutate B 0) hs' 0 1
      (by decide) H ha' hf' hc' (fun l hl0 hl1 => hstrict l hl1 hl0) hnr.2 htail
    simpa only [List.length_cons,alternatingWord] using congrArg (List.cons 1)
      (congrArg (List.cons 0) he)

theorem normalized_reduced_strong_excursion_impossible (hEnd : EndpointTopological4)
    (a b c d E f : Int) (H : Nat) (ha : 2≤a) (hb : 0<b) (hc : 0<c)
    (hf : f=(H:Int)+1) (h0 : HeightLe (mutate (Q a b c d E f) 0) H)
    (hma : MutationAcyclic (Q a b c d E f))
    (p : CyclicOrder) (hp : TotalProper (Q a b c d E f) p)
    (hM : orderMarkov (Q a b c d E f) p≤(H:Int)) (w : List (Fin 4))
    (hnr : ∀ u k v,(1::w)≠u++k::k::v)
    (hceil : PrefixHeightLe (Q a b c d E f) (1::w) (H+1))
    (hend : HeightLe (applyWord (Q a b c d E f) (1::w)) H) : False := by
  obtain ⟨hP,ht⟩ := (prefixHeight_cons _ 1 w (H+1)).mp hceil
  have h1 : HeightLe (mutate (Q a b c d E f) 1) (H+1) := ht [] w rfl
  obtain ⟨hd,hcE⟩ := HalfEntryStable.normalized_half_entry_forces_stable_chamber
    hEnd a b c d E f H ha hb hc hf hP h0 h1 hma p hp hM
  have he := stable_first_reduced_word_is_alternating a b c d E f H ha hb hc hd hcE
    hf p (totalProper_proper _ p hp) hM w (no_backtrack_reduced_after 1 w hnr) hceil
  rw [he] at hend
  have hl := mixed_bounded_exit_forces_c_gt_E a b c d E f H (w.length+1)
    ha (by omega) hd (by omega) hf hend
  omega

theorem normalized_reduced_forward_word_no_return (hEnd : EndpointTopological4)
    (a b c d E f : Int) (H : Nat) (ha : 2≤a) (hb : 0<b) (hc : 0<c)
    (hf : f=(H:Int)+1) (h0 : HeightLe (mutate (Q a b c d E f) 0) H)
    (hma : MutationAcyclic (Q a b c d E f))
    (p : CyclicOrder) (hp : TotalProper (Q a b c d E f) p)
    (hM : orderMarkov (Q a b c d E f) p≤(H:Int)) (w : List (Fin 4))
    (hfirst : ∀ k tail,w=k::tail → k=1)
    (hnr : ∀ u k v,w≠u++k::k::v)
    (hceil : PrefixHeightLe (Q a b c d E f) w (H+1))
    (hend : HeightLe (applyWord (Q a b c d E f) w) H) : False := by
  cases w with
  | nil =>
    have hl := (hend 2 3).2
    change f≤(H:Int) at hl
    omega
  | cons k w =>
    have hk := hfirst k w rfl
    subst k
    exact normalized_reduced_strong_excursion_impossible hEnd a b c d E f H
      ha hb hc hf h0 hma p hp hM w hnr hceil hend

#print axioms no_backtrack_reduced_after
#print axioms strict_aligned_reduced_word_is_alternating
#print axioms stable_first_reduced_word_is_alternating
#print axioms normalized_reduced_strong_excursion_impossible
#print axioms normalized_reduced_forward_word_no_return
end QuiverProofs.Rank4StructureRound2.StableWordAssembly
