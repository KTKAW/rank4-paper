import Rank4ReviewRound2.ZeroUnitDominance
import Rank4Round2.ZeroBoundary
import Rank4Round2.ZeroWeakInterfaces

/-! The actual ten-phase central block below the usual strip domain.
Its special edges and cyclicity hold uniformly. The first outward root is
proved with its actual return vertex. Phase-four exits remain explicit gaps.
-/
namespace Rank4ReviewRound2.ZeroWeakBlock
open QuiverProofs Rank4Round2
set_option maxHeartbeats 4000000

private theorem four (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
private theorem ten (i : Fin 10) :
    i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 := by omega

theorem forward (d c e w : Int) (hd : 0<d) (hc : 0<c) (he : 0<e) (hw : 0<w)
    (i : Fin 10) :
    mutate (UnitZeroStrip.node d c e w i) (UnitZeroStrip.forwardVertex i)=
      UnitZeroStrip.node d c e w (UnitZeroStrip.nextPhase i) := by
  rcases ten i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    funext a b <;> rcases four a with rfl|rfl|rfl|rfl <;>
    rcases four b with rfl|rfl|rfl|rfl <;>
    simp [UnitZeroStrip.node,UnitZeroStrip.forwardVertex,UnitZeroStrip.nextPhase,
      mutate,correction,ofSix] <;> grind

private theorem cyclic_zero (d c e w : Int) (hd : 0<d) (he : 0<e) (hw : 0<w) :
    ¬Acyclic (UnitZeroStrip.node d c e w 0) := by
  rintro ⟨r,hr⟩
  have h1 := hr 1 2 (by simp [UnitZeroStrip.node,ofSix]; omega)
  have h2 := hr 2 3 (by simp [UnitZeroStrip.node,ofSix]; omega)
  have h3 := hr 3 1 (by simp [UnitZeroStrip.node,ofSix]; omega)
  omega

private theorem cyclic_one (d c e w : Int) (hd : 0<d) (he : 0<e)
    (hc : 0<c) (hw : 0<w) : ¬Acyclic (UnitZeroStrip.node d c e w 1) := by
  rintro ⟨r,hr⟩
  have h1 := hr 1 2 (by simp [UnitZeroStrip.node,ofSix]; omega)
  have h2 := hr 2 3 (by simp [UnitZeroStrip.node,ofSix]; omega)
  have h3 := hr 3 1 (by simp [UnitZeroStrip.node,ofSix]; omega)
  omega

private theorem cyclic_two (d c e w : Int) (hd : 0<d) (hc : 0<c) (hw : 0<w)
    (hE : e<d*(c+w)) : ¬Acyclic (UnitZeroStrip.node d c e w 2) := by
  rintro ⟨r,hr⟩
  have h1 := hr 1 3 (by simp [UnitZeroStrip.node,ofSix]; omega)
  have h2 := hr 3 2 (by simp [UnitZeroStrip.node,ofSix]; omega)
  have h3 := hr 2 1 (by simp [UnitZeroStrip.node,ofSix]; omega)
  omega

private theorem cyclic_three (d c e w : Int) (hd : 0<d) (hc : 0<c)
    (hE : e<d*(c+w)) : ¬Acyclic (UnitZeroStrip.node d c e w 3) := by
  rintro ⟨r,hr⟩
  have h1 := hr 1 3 (by simp [UnitZeroStrip.node,ofSix]; omega)
  have h2 := hr 3 2 (by simp [UnitZeroStrip.node,ofSix]; omega)
  have h3 := hr 2 1 (by simp [UnitZeroStrip.node,ofSix]; omega)
  omega

private theorem cyclic_four (d c e w : Int) (hd : 0<d) :
    ¬Acyclic (UnitZeroStrip.node d c e w 4) := by
  rintro ⟨r,hr⟩
  have h1 := hr 0 3 (by simp [UnitZeroStrip.node,ofSix])
  have h2 := hr 3 1 (by simp [UnitZeroStrip.node,ofSix]; omega)
  have h3 := hr 1 0 (by simp [UnitZeroStrip.node,ofSix]; omega)
  omega

theorem cyclic (d c e w : Int) (hd : 0<d) (hc : 0<c) (he : 0<e) (hw : 0<w)
    (hE : e<d*(c+w)) (i : Fin 10) : ¬Acyclic (UnitZeroStrip.node d c e w i) := by
  have hswap (j : Fin 10) (hj : ¬Acyclic (UnitZeroStrip.node d c e w j)) :
      ¬Acyclic (UnitZeroStrip.node d c e w (UnitZeroStrip.swapPhase j)) := by
    rw [UnitZeroStrip.swapped]
    exact fun h => hj ((acyclic_relabel_iff _ _).mp h)
  rcases ten i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact cyclic_zero d c e w hd he hw
  · exact cyclic_one d c e w hd he hc hw
  · exact cyclic_two d c e w hd hc hw hE
  · exact cyclic_three d c e w hd hc hE
  · exact cyclic_four d c e w hd
  · exact hswap 0 (cyclic_zero d c e w hd he hw)
  · exact hswap 1 (cyclic_one d c e w hd he hc hw)
  · exact hswap 2 (cyclic_two d c e w hd hc hw hE)
  · exact hswap 3 (cyclic_three d c e w hd hc hE)
  · exact hswap 4 (cyclic_four d c e w hd)

def frame2103 : Relabeling 4 :=
  ⟨fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | _ => 3,
   fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | _ => 3,by decide,by decide⟩

theorem phase_zero_root (d c e w : Int)
    (hc : 2≤c) (he : 2≤e) (hw : 2≤w) (hde : d<e) :
    Regions.IsRoot (mutate (UnitZeroStrip.node d c e w 0) 2) 2 := by
  have hce := Forks.product_add_dominates c e 0 hc he (by decide)
  simp only [zero_add] at hce
  have hew := Int.mul_le_mul_of_nonneg_right he (show 0≤w-1 by omega)
  have hwe := Int.mul_le_mul_of_nonneg_left hw (show 0≤e by omega)
  have heq : relabel (mutate (UnitZeroStrip.node d c e w 0) 2) frame2103=
      Regions.root e (c*e) (e*w-d) c w 1 := by
    funext a b
    rcases four a with rfl|rfl|rfl|rfl <;> rcases four b with rfl|rfl|rfl|rfl <;>
      simp [UnitZeroStrip.node,Regions.root,relabel,frame2103,mutate,correction,ofSix] <;> grind
  have hDom : Regions.Domain e (c*e) (e*w-d) c w := by
    unfold Regions.Domain
    refine ⟨he,hc,hw,hce.2,hce.1,?_,?_⟩ <;> nlinarith
  have hRoot : Regions.IsRoot
      (relabel (mutate (UnitZeroStrip.node d c e w 0) 2) frame2103) 0 := by
    rw [heq]
    exact Regions.IsRoot.basic _ _ _ _ _ _ hDom (Or.inr rfl)
  exact Regions.root_of_relabel frame2103 hRoot

#print axioms forward
#print axioms cyclic
#print axioms phase_zero_root
end Rank4ReviewRound2.ZeroWeakBlock
