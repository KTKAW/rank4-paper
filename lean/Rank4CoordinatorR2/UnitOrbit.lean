import Rank4CoordinatorR2.UnitCycle
import Rank4Round2.WordBounds

/-! Whole constant-unit-pair subwords can be replaced by a bounded actual
word of length at most three, up to an explicitly transported suffix frame.
This does not supply a decomposition of arbitrary pivot-switching blocks. -/
namespace Rank4CoordinatorR2.UnitOrbit
open QuiverProofs Rank4Coordinator Rank4Round2
open Census ProperObstructionSoundness Rank4CoordinatorR2.UnitCycle

def frame (B : Matrix 4) (r : Bool) : Matrix 4 :=
  if r then relabel B Forks.swap01 else B

def baseStep (v : Fin 5) (k : Bool) : Fin 5×Bool :=
  match v.val,k with
  | 0,false => (1,false) | 0,true => (4,true)
  | 1,false => (0,false) | 1,true => (2,false)
  | 2,false => (3,false) | 2,true => (1,false)
  | 3,false => (2,false) | 3,true => (4,false)
  | _,false => (0,true) | _,true => (3,false)

theorem transition (B : Matrix 4) (hs : SkewSymmetric B) (hu : |B 0 1|=1)
    (v : Fin 5) (r k : Bool) :
    mutate (frame (node B v) r) (if k then 1 else 0)=
      frame (node B (baseStep v (Bool.xor k r)).1)
        (Bool.xor r (baseStep v (Bool.xor k r)).2) := by
  have hb := backward_edge B hs hu
  have hc := forward_closing B hs hu
  have hb' : mutate B 1=relabel (mutate (mutate (mutate (mutate B 0) 1) 0) 1) Forks.swap01 := hb
  have hc' : mutate (mutate (mutate (mutate (mutate B 0) 1) 0) 1) 0=relabel B Forks.swap01 := hc
  have h0 : Forks.swap01.toFun 0=1 := rfl
  have h1 : Forks.swap01.toFun 1=0 := rfl
  have hv : v=0 ∨ v=1 ∨ v=2 ∨ v=3 ∨ v=4 := by omega
  rcases hv with rfl|rfl|rfl|rfl|rfl <;> cases r <;> cases k <;>
    simp [frame,baseStep,node,cyclePrefix,applyWord,mutate_relabel,h0,h1,
      mutation_involutive,hb',hc',swap_twice]

theorem orbit_word (B : Matrix 4) (hs : SkewSymmetric B) (hu : |B 0 1|=1)
    (w : List (Fin 4)) (hp : ∀ k∈w,k=0 ∨ k=1) :
    ∃ (v : Fin 5) (r : Bool), applyWord B w=frame (node B v) r := by
  have hall : ∀ (w : List (Fin 4)) (v : Fin 5) (r : Bool),
      (∀ k∈w,k=0 ∨ k=1) →
      ∃ (u : Fin 5) (s : Bool), applyWord (frame (node B v) r) w=frame (node B u) s := by
    intro w
    induction w with
    | nil => intro v r _; exact ⟨v,r,rfl⟩
    | cons k w ih =>
      intro v r h
      have hk := h k (by simp)
      have ht : ∀ l∈w,l=0 ∨ l=1 := fun l hl => h l (by simp [hl])
      rcases hk with rfl|rfl
      · have he := transition B hs hu v r false
        change mutate (frame (node B v) r) 0=_ at he
        change ∃ u s, applyWord (mutate (frame (node B v) r) 0) w=frame (node B u) s
        rw [he]
        exact ih _ _ ht
      · have he := transition B hs hu v r true
        change mutate (frame (node B v) r) 1=_ at he
        change ∃ u s, applyWord (mutate (frame (node B v) r) 1) w=frame (node B u) s
        rw [he]
        exact ih _ _ ht
  exact hall w 0 false hp

theorem frame_height (B : Matrix 4) (r : Bool) (H : Nat) :
    HeightLe (frame B r) H ↔ HeightLe B H := by
  cases r <;> simp [frame,heightLe_relabel_iff]

theorem unit_pair_bounded_route (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4)
    (B : Matrix 4) (hs : SkewSymmetric B) (hma : MutationAcyclic B)
    (hu : |B 0 1|=1) (H : Nat) (hB : HeightLe B H)
    (old : List (Fin 4)) (hp : ∀ k∈old,k=0 ∨ k=1)
    (hend : HeightLe (applyWord B old) H) :
    ∃ (new : List (Fin 4)) (p : Relabeling 4), new.length≤3 ∧
      PrefixHeightLe B new H ∧ applyWord B new=relabel (applyWord B old) p := by
  obtain ⟨v,r,he⟩ := orbit_word B hs hu old hp
  have hv : HeightLe (node B v) H := by
    rw [he] at hend
    exact (frame_height _ r H).mp hend
  obtain ⟨new,q,hlen,hpre,hnew⟩ := short_to_node hExist hEnd B hs hma hu H hB v hv
  let p : Relabeling 4 := if r then Forks.swap01 else .identity 4
  have hpe : applyWord B old=relabel (node B v) p := by
    rw [he]
    cases r <;> rfl
  refine ⟨new,p.symm.trans q,hlen,hpre,?_⟩
  rw [hpe,←relabel_trans,relabel_inverse]
  exact hnew

theorem unit_pair_suffix_progress (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4)
    (B : Matrix 4) (hs : SkewSymmetric B) (hma : MutationAcyclic B)
    (hu : |B 0 1|=1) (H K : Nat) (hHK : H≤K) (hB : HeightLe B H)
    (old tail : List (Fin 4)) (hp : ∀ k∈old,k=0 ∨ k=1)
    (hend : HeightLe (applyWord B old) H)
    (hpath : PrefixHeightLe B (old++tail) K)
    (ha : Acyclic (applyWord B (old++tail))) :
    ∃ (new : List (Fin 4)) (p : Relabeling 4), new.length≤3 ∧
      PrefixHeightLe B (new++tail.map p.invFun) K ∧
      Acyclic (applyWord B (new++tail.map p.invFun)) ∧
      overCount B (new++tail.map p.invFun) H + overCount B old H=
        overCount B (old++tail) H := by
  obtain ⟨new,p,hlen,hpre,he⟩ := unit_pair_bounded_route hExist hEnd B hs hma hu H hB old hp hend
  have ht := ((prefixHeight_append_iff B old tail K).mp hpath).2
  refine ⟨new,p,hlen,?_,?_,?_⟩
  · exact reroute_prefixHeight B old new tail p K he
      (prefixHeight_mono B new H K hHK hpre) ht
  · rw [reroute_endpoint B old new tail p he]
    exact (acyclic_relabel_iff _ p).mpr ha
  · rw [overCount_append,he,overCount_relabel,overCount_eq_zero B new H hpre,
      overCount_append]
    omega

#print axioms transition
#print axioms unit_pair_bounded_route
#print axioms unit_pair_suffix_progress
end Rank4CoordinatorR2.UnitOrbit
