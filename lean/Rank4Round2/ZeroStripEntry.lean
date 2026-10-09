import Rank4Round2.ZeroMAGuard
import QuiverProofs.UnitZeroStrip

/-! Actual mutation and frame identities from a zero-unit parent to the
ten-phase strip. Both entrance parents remain displayed; no safety of either
parent, complete exit cover, or zero-unit NMA conclusion is asserted here.
-/
namespace Rank4Round2.ZeroStripEntry
open QuiverProofs Rank4Coordinator Rank4Round2

private theorem four (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega

def swap23 : Relabeling 4 :=
  ⟨fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | _ => 2,
   fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | _ => 2,
   by decide,by decide⟩

def parameters (d e f u : Int) : UnitZeroStrip.Parameters :=
  ⟨u,d*f-e,d*(d*f-e)-f⟩

theorem reverse_mutate_two (c d e f : Int) (hd : 0<d) (hf : 0<f) :
    reverse (mutate (zeroPeak 1 c d e f) 2)=zeroPeak 1 (f-c) d (d*f-e) f := by
  funext i j
  rcases four i with rfl|rfl|rfl|rfl <;>
    rcases four j with rfl|rfl|rfl|rfl <;>
    simp [zeroPeak,reverse,mutate,correction,ofSix] <;> grind

theorem square_reverse_swap (c d e u v : Int)
    (hc : 0<c) (hd : 0<d) (he : 0<e) (hde : d*e=c+u+v) :
    reverse (applyWord (zeroPeak 1 c d e (c+u)) [0,1])=
      zeroPeak 1 c d e (c+v) := by
  change reverse (mutate (mutate (zeroPeak 1 c d e (c+u)) 0) 1)=_
  rw [zeroPeak_double 1 c d e (c+u) (by decide) hc hd he]
  funext i j
  rcases four i with rfl|rfl|rfl|rfl <;>
    rcases four j with rfl|rfl|rfl|rfl <;>
    simp [reverse,zeroPeak,ofSix] <;> omega

theorem parameters_domain (d e f u : Int)
    (hd : 2≤d) (hu : 2≤u) (he : 0<e) (hfe : e<f) (hfd : d<f) :
    UnitZeroStrip.Domain d (parameters d e f u).u
      (parameters d e f u).v (parameters d e f u).w := by
  have hf : 0<f := by omega
  have hdf := Int.mul_le_mul_of_nonneg_right hd (show 0≤f by omega)
  have hV : f<d*f-e := by omega
  have hdV := Int.mul_le_mul_of_nonneg_right hd (show 0≤d*f-e by omega)
  unfold UnitZeroStrip.Domain parameters
  dsimp
  exact ⟨hd,hu,by omega,by omega⟩

theorem mutate_one_entry (d e f u : Int) (hd : 0<d) (hV : 0<d*f-e) :
    relabel (mutate (zeroPeak 1 u d (d*f-e) f) 1) swap23=
      UnitZeroStrip.node d u (d*f-e) (d*(d*f-e)-f) 0 := by
  rw [zeroPeak_one 1 u d (d*f-e) f hd hV]
  funext i j
  rcases four i with rfl|rfl|rfl|rfl <;>
    rcases four j with rfl|rfl|rfl|rfl <;>
    simp [relabel,swap23,UnitZeroStrip.node,ofSix]

theorem original_word_entry (c d e f : Int)
    (hd : 0<d) (hf : 0<f) (hV : 0<d*f-e) :
    relabel (reverse (applyWord (zeroPeak 1 c d e f) [2,1])) swap23=
      UnitZeroStrip.strip d (parameters d e f (f-c)) 0 0 := by
  change relabel (reverse (mutate (mutate (zeroPeak 1 c d e f) 2) 1)) swap23=_
  rw [←mutate_reverse,reverse_mutate_two c d e f hd hf]
  exact mutate_one_entry d e f (f-c) hd hV

theorem parent_zero (d e f u : Int) (hd : 0<d) (hV : 0<d*f-e) :
    UnitZeroStrip.parent d (parameters d e f u) 0=
      relabel (zeroPeak 1 u d (d*f-e) f) swap23 := by
  change mutate (UnitZeroStrip.node d u (d*f-e) (d*(d*f-e)-f) 0) 1=_
  rw [←mutate_one_entry d e f u hd hV,mutate_relabel]
  change relabel (mutate (mutate (zeroPeak 1 u d (d*f-e) f) 1) 1) swap23=_
  rw [mutation_involutive]

theorem parent_one (d e f u : Int)
    (hd : 2≤d) (hu : 2≤u) (he : 0<e) (hfe : e<f) (hfd : d<f) :
    UnitZeroStrip.parent d (parameters d e f u) 1=
      relabel (mutate (zeroPeak 1 u d (d*f-e) f) 0) swap23 := by
  have hDom := parameters_domain d e f u hd hu he hfe hfd
  change UnitZeroStrip.Domain d u (d*f-e) (d*(d*f-e)-f) at hDom
  have hV : 0<d*f-e := by
    have hdf := Int.mul_le_mul_of_nonneg_right hd (show 0≤f by omega)
    omega
  change mutate (UnitZeroStrip.node d u (d*f-e) (d*(d*f-e)-f) 1) 1=_
  rw [UnitZeroStrip.parent_commutation _ _ _ _ hDom]
  have hp := parent_zero d e f u (by omega) hV
  change mutate (UnitZeroStrip.node d u (d*f-e) (d*(d*f-e)-f) 0) 1=_ at hp
  rw [hp,mutate_relabel]
  rfl

theorem both_parents (d e f u : Int)
    (hd : 2≤d) (hu : 2≤u) (he : 0<e) (hfe : e<f) (hfd : d<f)
    (j : Fin 2) :
    UnitZeroStrip.parent d (parameters d e f u) j =
      if j=0 then relabel (zeroPeak 1 u d (d*f-e) f) swap23
      else relabel (mutate (zeroPeak 1 u d (d*f-e) f) 0) swap23 := by
  have hj : j=0 ∨ j=1 := by omega
  rcases hj with rfl|rfl
  · simp only [if_pos rfl]
    apply parent_zero d e f u (by omega)
    have hdf := Int.mul_le_mul_of_nonneg_right hd (show 0≤f by omega)
    omega
  · simp only [show (1:Fin 2)≠0 by decide,if_false]
    exact parent_one d e f u hd hu he hfe hfd

#print axioms reverse_mutate_two
#print axioms original_word_entry
#print axioms both_parents
end Rank4Round2.ZeroStripEntry
