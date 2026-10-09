import Rank4Round2.ZeroStripEntry

/-! True local exits for the zero-unit central boundary. The proved root exit
keeps its actual last vertex. The other child matrices are displayed without
claiming a complete semantic safety cover.
-/
namespace Rank4Round2.ZeroBoundary
open QuiverProofs Rank4Round2

private theorem four (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega

def rootFrame : Relabeling 4 :=
  ⟨fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | _ => 1,
   fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | _ => 0,
   by decide,by decide⟩

theorem zero_unit_three (c d e f : Int)
    (hc : 0<c) (he : 0<e) (hf : 0<f) :
    mutate (zeroPeak 1 c d e f) 3=
      ofSix 0 (1-c*f) c (d-e*f) e (-f) := by
  funext i j
  rcases four i with rfl|rfl|rfl|rfl <;>
    rcases four j with rfl|rfl|rfl|rfl <;>
    simp [zeroPeak,mutate,correction,ofSix] <;> grind

theorem zero_unit_three_frame (c d e f : Int)
    (hc : 0<c) (he : 0<e) (hf : 0<f) :
    relabel (mutate (zeroPeak 1 c d e f) 3) rootFrame=
      Regions.root f (c*f-1) (e*f-d) c e 0 := by
  rw [zero_unit_three c d e f hc he hf]
  funext i j
  rcases four i with rfl|rfl|rfl|rfl <;>
    rcases four j with rfl|rfl|rfl|rfl <;>
    simp [relabel,rootFrame,Regions.root,ofSix]

theorem zero_unit_three_root_domain (c d e f : Int)
    (hc : 2≤c) (he : 2≤e) (hf : 2≤f) (hdf : d<f) :
    Regions.Domain f (c*f-1) (e*f-d) c e := by
  have hcf := Int.mul_le_mul_of_nonneg_right hc (show 0≤f by omega)
  have hfc := Int.mul_le_mul_of_nonneg_left hf (show 0≤c by omega)
  have hef := Int.mul_le_mul_of_nonneg_right he (show 0≤f by omega)
  have he1f := Int.mul_le_mul_of_nonneg_left hf (show 0≤e-1 by omega)
  unfold Regions.Domain
  refine ⟨hf,hc,he,by omega,by omega,by omega,?_⟩
  nlinarith

theorem zero_unit_three_root (c d e f : Int)
    (hc : 2≤c) (he : 2≤e) (hf : 2≤f) (hdf : d<f) :
    Regions.IsRoot (mutate (zeroPeak 1 c d e f) 3) 3 := by
  have hr : Regions.IsRoot (relabel (mutate (zeroPeak 1 c d e f) 3) rootFrame) 0 := by
    rw [zero_unit_three_frame c d e f (by omega) (by omega) (by omega)]
    exact Regions.IsRoot.basic _ _ _ _ _ _
      (zero_unit_three_root_domain c d e f hc he hf hdf) (Or.inl rfl)
  exact Regions.root_of_relabel rootFrame hr

theorem transformed_three_root (c d e f : Int)
    (hd : 2≤d) (he : 0<e) (hfe : e<f) (hfd : d<f) (hu : 2≤f-c) :
    Regions.IsRoot (mutate (reverse (mutate (zeroPeak 1 c d e f) 2)) 3) 3 := by
  have hf : 2≤f := by omega
  have hdf := Int.mul_le_mul_of_nonneg_right hd (show 0≤f by omega)
  rw [ZeroStripEntry.reverse_mutate_two c d e f (by omega) (by omega)]
  exact zero_unit_three_root (f-c) d (d*f-e) f hu (by omega) hf hfd

def leftChild (c d e u : Int) : Matrix 4 := ofSix 0 (-1) c d (-e) u

theorem left_mutate_two (c d e u : Int) (hd : 0<d) (hu : 0<u) :
    mutate (leftChild c d e u) 2=ofSix (-d) 1 c (-d) (d*u-e) (-u) := by
  funext i j
  rcases four i with rfl|rfl|rfl|rfl <;>
    rcases four j with rfl|rfl|rfl|rfl <;>
    simp [leftChild,mutate,correction,ofSix] <;> grind

theorem left_mutate_three (c d e u : Int)
    (hc : 0<c) (he : 0<e) (hu : 0<u) :
    mutate (leftChild c d e u) 3=ofSix (c*e) (-1) (-c) (d-e*u) e (-u) := by
  funext i j
  rcases four i with rfl|rfl|rfl|rfl <;>
    rcases four j with rfl|rfl|rfl|rfl <;>
    simp [leftChild,mutate,correction,ofSix] <;> grind

theorem original_left_child (c d e f : Int) (hc : 0<c) :
    mutate (zeroPeak 1 c d e f) 0=leftChild c d e (f-c) := by
  simpa only [leftChild,one_mul] using zeroPeak_zero 1 c d e f (by decide) hc

theorem transformed_left_child (c d e f : Int) (hu : 0<f-c) :
    mutate (zeroPeak 1 (f-c) d (d*f-e) f) 0=leftChild (f-c) d (d*f-e) c := by
  rw [zeroPeak_zero 1 (f-c) d (d*f-e) f (by decide) hu]
  unfold leftChild
  congr 1 <;> ring

#print axioms zero_unit_three_root
#print axioms transformed_three_root
#print axioms left_mutate_two
#print axioms left_mutate_three
end Rank4Round2.ZeroBoundary
