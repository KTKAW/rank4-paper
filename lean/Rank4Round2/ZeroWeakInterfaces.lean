import Rank4Round2.ZeroStripEntry

/-! The two weak ten-phase blocks exchange their actual unswapped parents.
The phase-two/three exits enter genuine strips when the selected u is at
least two. No boundary-root/fork law for all weak phases is inferred.
-/
namespace Rank4Round2.ZeroWeakInterfaces
open QuiverProofs Rank4Round2

private theorem four (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega

theorem phase_zero_cross (c d e u v : Int) (hd : 0<d) (he : 0<e)
    (hde : d*e=c+u+v) :
    mutate (UnitZeroStrip.node d c e u 0) 1=
      reverse (UnitZeroStrip.node d c e v 1) := by
  funext i j
  rcases four i with rfl|rfl|rfl|rfl <;>
    rcases four j with rfl|rfl|rfl|rfl <;>
    simp [UnitZeroStrip.node,reverse,mutate,correction,ofSix] <;> grind

theorem phase_one_cross (c d e u v : Int) (hd : 0<d) (he : 0<e)
    (hde : d*e=c+u+v) :
    mutate (UnitZeroStrip.node d c e u 1) 1=
      reverse (UnitZeroStrip.node d c e v 0) := by
  funext i j
  rcases four i with rfl|rfl|rfl|rfl <;>
    rcases four j with rfl|rfl|rfl|rfl <;>
    simp [UnitZeroStrip.node,reverse,mutate,correction,ofSix] <;> grind

theorem phase_two_strip (c d e u : Int) (hd : 0<d) (hE : 0<d*(c+u)-e) :
    mutate (UnitZeroStrip.node d c e u 2) 1=
      UnitZeroStrip.strip d (ZeroStripEntry.parameters d e (c+u) u) 0 0 := by
  change mutate (UnitZeroStrip.node d c e u 2) 1=
    UnitZeroStrip.node d u (d*(c+u)-e) (d*(d*(c+u)-e)-(c+u)) 0
  funext i j
  rcases four i with rfl|rfl|rfl|rfl <;>
    rcases four j with rfl|rfl|rfl|rfl <;>
    simp [UnitZeroStrip.node,mutate,correction,ofSix] <;> grind

theorem phase_three_strip (c d e u : Int) (hd : 0<d) (hE : 0<d*(c+u)-e) :
    mutate (UnitZeroStrip.node d c e u 3) 1=
      UnitZeroStrip.strip d (ZeroStripEntry.parameters d e (c+u) u) 0 1 := by
  change mutate (UnitZeroStrip.node d c e u 3) 1=
    UnitZeroStrip.node d u (d*(c+u)-e) (d*(d*(c+u)-e)-(c+u)) 1
  funext i j
  rcases four i with rfl|rfl|rfl|rfl <;>
    rcases four j with rfl|rfl|rfl|rfl <;>
    simp [UnitZeroStrip.node,mutate,correction,ofSix] <;> grind

theorem strip_parents_are_weak_phases (c d e u : Int)
    (hd : 2≤d) (hu : 2≤u) (he : 0<e) (hfe : e<c+u) (hfd : d<c+u)
    (j : Fin 2) :
    UnitZeroStrip.parent d (ZeroStripEntry.parameters d e (c+u) u) j=
      UnitZeroStrip.node d c e u (if j=0 then 2 else 3) := by
  have hE : 0<d*(c+u)-e := by
    have hdf := Int.mul_le_mul_of_nonneg_right hd (show 0≤c+u by omega)
    omega
  have hj : j=0 ∨ j=1 := by omega
  rcases hj with rfl|rfl
  · change mutate (UnitZeroStrip.strip d (ZeroStripEntry.parameters d e (c+u) u) 0 0) 1=_
    rw [←phase_two_strip c d e u (by omega) hE,mutation_involutive]
    rfl
  · change mutate (UnitZeroStrip.strip d (ZeroStripEntry.parameters d e (c+u) u) 0 1) 1=_
    rw [←phase_three_strip c d e u (by omega) hE,mutation_involutive]
    rfl

#print axioms phase_zero_cross
#print axioms phase_one_cross
#print axioms strip_parents_are_weak_phases
end Rank4Round2.ZeroWeakInterfaces
