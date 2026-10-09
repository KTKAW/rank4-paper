import Rank4Round2.ZeroBoundary

/-! Actual weak-block spine and proved outward roots for phases zero through
three when both c and the selected residual u are at least two. Unit residual
walls and phase-four exits remain separate obligations.
-/
namespace Rank4Round2.ZeroWeakExits
open QuiverProofs Rank4Round2 Forks
set_option maxHeartbeats 4000000

private theorem four (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
private theorem ten (i : Fin 10) :
    i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 := by omega

def swap02 : Relabeling 4 :=
  ⟨fun i => match i.val with | 0=>2 | 1=>1 | 2=>0 | _=>3,
   fun i => match i.val with | 0=>2 | 1=>1 | 2=>0 | _=>3,by decide,by decide⟩
def frame2301 : Relabeling 4 :=
  ⟨fun i => match i.val with | 0=>2 | 1=>3 | 2=>0 | _=>1,
   fun i => match i.val with | 0=>2 | 1=>3 | 2=>0 | _=>1,by decide,by decide⟩

theorem weak_forward (c d e u : Int) (hc : 0<c) (hd : 0<d) (hu : 0<u)
    (hE : 0<d*(c+u)-e) (i : Fin 10) :
    mutate (UnitZeroStrip.node d c e u i) (UnitZeroStrip.forwardVertex i)=
      UnitZeroStrip.node d c e u (UnitZeroStrip.nextPhase i) := by
  rcases ten i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    funext a b <;> rcases four a with rfl|rfl|rfl|rfl <;>
    rcases four b with rfl|rfl|rfl|rfl <;>
    simp [UnitZeroStrip.node,UnitZeroStrip.forwardVertex,UnitZeroStrip.nextPhase,
      mutate,correction,ofSix] <;> grind

theorem phase_zero_shape (c d e u : Int) (hc : 0<c) (he : 0<e) (hu : 0<u) :
    relabel (mutate (UnitZeroStrip.node d c e u 0) 2) swap02=
      Regions.root e (c*e) (e*u-d) c u 1 := by
  funext i j
  rcases four i with rfl|rfl|rfl|rfl <;>
    rcases four j with rfl|rfl|rfl|rfl <;>
    simp [UnitZeroStrip.node,Regions.root,relabel,swap02,mutate,correction,ofSix] <;> grind

theorem phase_zero_root (c d e u : Int)
    (hc : 2≤c) (hd : 2≤d) (hu : 2≤u) (hed : d<e) :
    Regions.IsRoot (mutate (UnitZeroStrip.node d c e u 0) 2) 2 := by
  have he : 2≤e := by omega
  have hce := product_add_dominates c e 0 hc he (by decide)
  have heu := Int.mul_le_mul_of_nonneg_left hu (show 0≤e by omega)
  have he1u := Int.mul_le_mul_of_nonneg_right hu (show 0≤e-1 by omega)
  have hDom : Regions.Domain e (c*e) (e*u-d) c u := by
    unfold Regions.Domain
    refine ⟨he,hc,hu,by simpa using hce.2,by simpa using hce.1,by omega,?_⟩
    nlinarith
  have hr : Regions.IsRoot (relabel (mutate (UnitZeroStrip.node d c e u 0) 2) swap02) 0 := by
    rw [phase_zero_shape c d e u (by omega) (by omega) (by omega)]
    exact Regions.IsRoot.basic _ _ _ _ _ _ hDom (Or.inr rfl)
  exact Regions.root_of_relabel swap02 hr

theorem phase_one_shape (c d e u : Int) (hc : 0<c) (hd : 0<d)
    (he : 0<e) (hf : 0<c+u) :
    relabel (reverse (mutate (UnitZeroStrip.node d c e u 1) 2)) frame2301=
      Regions.root (c+u) (c*(c+u)-1) (e*(c+u)-d) c e 0 := by
  funext i j
  rcases four i with rfl|rfl|rfl|rfl <;>
    rcases four j with rfl|rfl|rfl|rfl <;>
    simp [UnitZeroStrip.node,Regions.root,relabel,reverse,frame2301,mutate,correction,ofSix] <;> grind

theorem phase_one_root (c d e u : Int)
    (hc : 2≤c) (hd : 0<d) (he : 2≤e) (hf : 2≤c+u) (hdf : d<c+u) :
    Regions.IsRoot (mutate (UnitZeroStrip.node d c e u 1) 2) 2 := by
  have hr : Regions.IsRoot (relabel (reverse (mutate (UnitZeroStrip.node d c e u 1) 2)) frame2301) 0 := by
    rw [phase_one_shape c d e u (by omega) hd (by omega) (by omega)]
    exact Regions.IsRoot.basic _ _ _ _ _ _
      (ZeroBoundary.zero_unit_three_root_domain c d e (c+u) hc he hf hdf) (Or.inl rfl)
  exact Regions.root_of_reverse (Regions.root_of_relabel frame2301 hr)

theorem phase_two_shape (c d e u : Int) (hd : 0<d) (hu : 0<u)
    (hf : 0<c+u) (hE : 0<d*(c+u)-e) :
    relabel (mutate (UnitZeroStrip.node d c e u 2) 2) frame2301=
      Regions.root (c+u) (u*(c+u)-1) ((d*(c+u)-e)*(c+u)-d) u (d*(c+u)-e) 0 := by
  funext i j
  rcases four i with rfl|rfl|rfl|rfl <;>
    rcases four j with rfl|rfl|rfl|rfl <;>
    simp [UnitZeroStrip.node,Regions.root,relabel,frame2301,mutate,correction,ofSix] <;> grind

theorem phase_two_root (c d e u : Int) (hd : 0<d) (hu : 2≤u)
    (hf : 2≤c+u) (hdf : d<c+u) (hE : 2≤d*(c+u)-e) :
    Regions.IsRoot (mutate (UnitZeroStrip.node d c e u 2) 2) 2 := by
  have hr : Regions.IsRoot (relabel (mutate (UnitZeroStrip.node d c e u 2) 2) frame2301) 0 := by
    rw [phase_two_shape c d e u hd (by omega) (by omega) (by omega)]
    exact Regions.IsRoot.basic _ _ _ _ _ _
      (ZeroBoundary.zero_unit_three_root_domain u d (d*(c+u)-e) (c+u) hu hE hf hdf) (Or.inl rfl)
  exact Regions.root_of_relabel frame2301 hr

theorem phase_three_shape (c d e u : Int) (hc : 0<c) (hu : 0<u)
    (hE : 0<d*(c+u)-e) :
    relabel (reverse (mutate (UnitZeroStrip.node d c e u 3) 2)) swap02=
      Regions.root (d*(c+u)-e) (u*(d*(c+u)-e)) ((d*(c+u)-e)*c-d) u c 1 := by
  funext i j
  rcases four i with rfl|rfl|rfl|rfl <;>
    rcases four j with rfl|rfl|rfl|rfl <;>
    simp [UnitZeroStrip.node,Regions.root,relabel,reverse,swap02,mutate,correction,ofSix] <;> grind

theorem phase_three_root (c d e u : Int) (hc : 2≤c) (hu : 2≤u)
    (hE : c<d*(c+u)-e) (hdE : d<d*(c+u)-e) :
    Regions.IsRoot (mutate (UnitZeroStrip.node d c e u 3) 2) 2 := by
  have hE2 : 2≤d*(c+u)-e := by omega
  have hprod := product_add_dominates u (d*(c+u)-e) 0 hu hE2 (by decide)
  have hsub := product_sub_dominates c (d*(c+u)-e) d hc hE hdE
  have hDom : Regions.Domain (d*(c+u)-e) (u*(d*(c+u)-e)) ((d*(c+u)-e)*c-d) u c := by
    unfold Regions.Domain
    refine ⟨hE2,hu,hc,by simpa using hprod.2,by simpa using hprod.1,?_,?_⟩
    · simpa only [Int.mul_comm] using hsub.2
    · simpa only [Int.mul_comm] using hsub.1
  have hr : Regions.IsRoot (relabel (reverse (mutate (UnitZeroStrip.node d c e u 3) 2)) swap02) 0 := by
    rw [phase_three_shape c d e u (by omega) (by omega) (by omega)]
    exact Regions.IsRoot.basic _ _ _ _ _ _ hDom (Or.inr rfl)
  exact Regions.root_of_reverse (Regions.root_of_relabel swap02 hr)

#print axioms weak_forward
#print axioms phase_zero_root
#print axioms phase_three_root
end Rank4Round2.ZeroWeakExits
