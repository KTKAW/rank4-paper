import Rank4Round2.UnitFrameProgress

/-! Reversing an actual bounded mutation path remains bounded. In particular,
the strict unit peak admits the pentagon detour in either ordered direction.
-/
namespace Rank4Round2
open QuiverProofs Rank4Coordinator Census ProperObstructionSoundness

theorem prefixHeight_reverse_word (B : Matrix 4) (w : List (Fin 4)) (H : Nat)
    (h : PrefixHeightLe B w H) : PrefixHeightLe (applyWord B w) w.reverse H := by
  induction w generalizing B with
  | nil => exact h
  | cons k w ih =>
    obtain ⟨hb,ht⟩ := (prefixHeight_cons B k w H).mp h
    have hr := ih (mutate B k) ht
    simp only [applyWord,List.reverse_cons]
    apply prefixHeight_append _ _ _ H hr
    rw [applyWord_undo]
    apply (prefixHeight_cons _ k [] H).mpr
    refine ⟨ht [] w rfl,?_⟩
    rw [mutation_involutive,prefixHeight_nil]
    exact hb

theorem unitPeak_backward_endpoint (b c d e f : Int)
    (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e) :
    applyWord (mutate (unitPeak b c d e f) 1) [0,1,0] =
      relabel (mutate (unitPeak b c d e f) 0) Forks.swap01 := by
  have hundo := applyWord_undo (mutate (unitPeak b c d e f) 0) [1,0,1]
  rw [unitPeak_detour_endpoint b c d e f hb hc hd he,word_relabel] at hundo
  have h := congrArg (fun Q => relabel Q Forks.swap01.symm) hundo
  dsimp only at h
  rw [relabel_inverse] at h
  exact h

theorem unitPeak_backward_prefix (b c d e f : Int) (H : Nat)
    (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e)
    (h : PrefixHeightLe (mutate (unitPeak b c d e f) 0) [1,0,1] H) :
    PrefixHeightLe (mutate (unitPeak b c d e f) 1) [0,1,0] H := by
  have hr := prefixHeight_reverse_word _ [1,0,1] H h
  rw [unitPeak_detour_endpoint b c d e f hb hc hd he] at hr
  exact (prefixHeight_relabel_iff _ Forks.swap01 [0,1,0] H).mp hr

theorem unit_ma_backward_guard
    (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4)
    (b c d e f : Int) (H : Nat)
    (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e)
    (h0 : HeightLe (mutate (unitPeak b c d e f) 0) H)
    (h1 : HeightLe (mutate (unitPeak b c d e f) 1) H)
    (hf : (H:Int)<f) (hma : MutationAcyclic (unitPeak b c d e f)) :
    PrefixHeightLe (mutate (unitPeak b c d e f) 1) [0,1,0] H :=
  unitPeak_backward_prefix b c d e f H hb hc hd he
    (unit_ma_uniform_guard hExist hEnd b c d e f H hb hc hd he h0 h1 hf hma)

theorem unit_ma_backward_count_decrease
    (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4)
    (b c d e f : Int) (H : Nat)
    (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e)
    (h0 : HeightLe (mutate (unitPeak b c d e f) 0) H)
    (h1 : HeightLe (mutate (unitPeak b c d e f) 1) H)
    (hf : (H:Int)<f) (hma : MutationAcyclic (unitPeak b c d e f))
    (tail : List (Fin 4)) :
    overCount (mutate (unitPeak b c d e f) 1)
        ([0,1,0]++tail.map Forks.swap01.invFun) H + 1 =
      overCount (mutate (unitPeak b c d e f) 1) ([1,0]++tail) H := by
  apply strict_peak_overCount _ 1 0 [0,1,0] tail Forks.swap01 H _ h0
    (unitPeak_backward_endpoint b c d e f hb hc hd he)
    (unit_ma_backward_guard hExist hEnd b c d e f H hb hc hd he h0 h1 hf hma)
  intro hP
  have h := (hP 2 3).2
  change f≤(H:Int) at h
  omega

#print axioms prefixHeight_reverse_word
#print axioms unitPeak_backward_endpoint
#print axioms unit_ma_backward_count_decrease
end Rank4Round2
