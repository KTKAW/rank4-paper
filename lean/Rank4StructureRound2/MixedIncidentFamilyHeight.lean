import Rank4Round2.WordBounds
import Mathlib.Tactic.Ring

/-! Two slope-dependent height guards for the other unit triangle phase.
R=(1,-1,-t,2,t-F,F-w). If t>w use [1,0,2,1,2]; if w>t use
[2,0,2,1,0]. Both stay below F-1. The equal slope wall is retained
explicitly. No MA, proper scalar, or universal shape premise is inferred. -/
namespace QuiverProofs.Rank4StructureRound2.MixedIncidentFamilyHeight
open Rank4Coordinator Rank4Round2
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

def R (t w F : Int) : Matrix 4 := ofSix 1 (-1) (-t) 2 (t-F) (F-w)
def A1 (t w F : Int) : Matrix 4 := ofSix (-1) 1 (-t) (-2) (F-t) (2*t-F-w)
def A2 (t w F : Int) : Matrix 4 := ofSix 1 (-1) t (-1) (F-t) (t-F-w)
def A3 (t w F : Int) : Matrix 4 := ofSix 1 1 (2*t-F-w) 1 (-w) (F+w-t)
def A4 (t w F : Int) : Matrix 4 := ofSix (-1) 2 (2*t-F-w) (-1) w (F-t)
def E (t w F : Int) : Matrix 4 := ofSix 1 (-2) (F-w) 1 w (t-F)
def B1 (t w F : Int) : Matrix 4 := ofSix (-1) 1 (-t) (-2) (F+t-2*w) (w-F)
def B2 (t w F : Int) : Matrix 4 := ofSix 1 (-1) t (-1) (F+t-2*w) (w-F-t)
def B3 (t w F : Int) : Matrix 4 := ofSix 1 1 (w-F) 1 (-w) (F+t-w)
def B4 (t w F : Int) : Matrix 4 := ofSix (-1) 2 (w-F) (-1) w (F+t-2*w)

private theorem four (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega

theorem matrices (t w F : Int) (ht : 1≤t) (hw : 1≤w)
    (htF : t≤F-1) (hwF : w≤F-1) :
    mutate (R t w F) 1=A1 t w F ∧ mutate (A1 t w F) 0=A2 t w F ∧
    mutate (A2 t w F) 2=A3 t w F ∧ mutate (A3 t w F) 1=A4 t w F ∧
    mutate (A4 t w F) 2=E t w F ∧
    mutate (R t w F) 2=B1 t w F ∧ mutate (B1 t w F) 0=B2 t w F ∧
    mutate (B2 t w F) 2=B3 t w F ∧ mutate (B3 t w F) 1=B4 t w F ∧
    mutate (B4 t w F) 0=E t w F := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> funext i j <;>
    rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
    simp [R,A1,A2,A3,A4,E,B1,B2,B3,B4,mutate,ofSix,correction,
      max_eq_left (show 0≤t by omega),max_eq_right (show -t≤0 by omega),
      max_eq_left (show 0≤w by omega),max_eq_right (show -w≤0 by omega),
      max_eq_left (show 0≤F-t by omega),max_eq_right (show t-F≤0 by omega),
      max_eq_left (show 0≤F-w by omega),max_eq_right (show w-F≤0 by omega),
      max_eq_left (show 0≤F+w-t by omega),max_eq_right (show t-F-w≤0 by omega),
      max_eq_left (show 0≤F+t-w by omega),max_eq_right (show w-F-t≤0 by omega)] <;> omega

theorem first_slope_below (t w : Int) (H : Nat) (hH : 2≤H)
    (ht : 1≤t) (hw : 1≤w) (htH : t≤(H:Int)) (hwH : w≤(H:Int))
    (hSlope : w<t) : PrefixHeightLe (R t w ((H:Int)+1)) [1,0,2,1,2] H := by
  obtain ⟨h1,h2,h3,h4,h5,_,_,_,_,_⟩:=matrices t w ((H:Int)+1) ht hw (by omega) (by omega)
  have hr : HeightLe (R t w ((H:Int)+1)) H := by
    intro i j
    rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
      simp only [R,ofSix] <;> omega
  have a1 : HeightLe (A1 t w ((H:Int)+1)) H := by
    intro i j
    rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
      simp only [A1,ofSix] <;> omega
  have a2 : HeightLe (A2 t w ((H:Int)+1)) H := by
    intro i j
    rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
      simp only [A2,ofSix] <;> omega
  have a3 : HeightLe (A3 t w ((H:Int)+1)) H := by
    intro i j
    rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
      simp only [A3,ofSix] <;> omega
  have a4 : HeightLe (A4 t w ((H:Int)+1)) H := by
    intro i j
    rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
      simp only [A4,ofSix] <;> omega
  have he : HeightLe (E t w ((H:Int)+1)) H := by
    intro i j
    rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
      simp only [E,ofSix] <;> omega
  simp only [prefixHeight_cons,prefixHeight_nil,h1,h2,h3,h4,h5]
  exact ⟨hr,a1,a2,a3,a4,he⟩

theorem second_slope_below (t w : Int) (H : Nat) (hH : 2≤H)
    (ht : 1≤t) (hw : 1≤w) (htH : t≤(H:Int)) (hwH : w≤(H:Int))
    (hSlope : t<w) : PrefixHeightLe (R t w ((H:Int)+1)) [2,0,2,1,0] H := by
  obtain ⟨_,_,_,_,_,h1,h2,h3,h4,h5⟩:=matrices t w ((H:Int)+1) ht hw (by omega) (by omega)
  have hr : HeightLe (R t w ((H:Int)+1)) H := by
    intro i j
    rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
      simp only [R,ofSix] <;> omega
  have a1 : HeightLe (B1 t w ((H:Int)+1)) H := by
    intro i j
    rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
      simp only [B1,ofSix] <;> omega
  have a2 : HeightLe (B2 t w ((H:Int)+1)) H := by
    intro i j
    rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
      simp only [B2,ofSix] <;> omega
  have a3 : HeightLe (B3 t w ((H:Int)+1)) H := by
    intro i j
    rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
      simp only [B3,ofSix] <;> omega
  have a4 : HeightLe (B4 t w ((H:Int)+1)) H := by
    intro i j
    rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
      simp only [B4,ofSix] <;> omega
  have he : HeightLe (E t w ((H:Int)+1)) H := by
    intro i j
    rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
      simp only [E,ofSix] <;> omega
  simp only [prefixHeight_cons,prefixHeight_nil,h1,h2,h3,h4,h5]
  exact ⟨hr,a1,a2,a3,a4,he⟩

#print axioms matrices
#print axioms first_slope_below
#print axioms second_slope_below
end QuiverProofs.Rank4StructureRound2.MixedIncidentFamilyHeight
