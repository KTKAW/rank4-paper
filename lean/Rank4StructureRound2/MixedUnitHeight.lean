import Rank4Round2.WordBounds
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Ring

/-! Height guard for a mixed unit reroute. The triangle is (1,-2,1).
The old five-letter path begins above H, stays at H+1, and ends below H.
The replacement [1,0,2] stays below H. Matrix endpoint covariance is a
separate exact relation; no MA or scalar premise is used in this guard. -/
namespace QuiverProofs.Rank4StructureRound2.MixedUnitHeight
open Rank4Coordinator Rank4Round2
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000

def pos (x : Int) : Int := max x 0
def neg (x : Int) : Int := max (-x) 0
def R (c e f : Int) : Matrix 4 := ofSix 1 (-2) c 1 e f
def O1 (c e f : Int) : Matrix 4 := ofSix (-1) 2 (-c) (-1)
  (e-neg c) (f+2*pos c)
def O2 (c e f : Int) : Matrix 4 :=
  let l:=e-neg c
  ofSix 1 1 (-c-neg l) 1 (-l) (f+2*pos c+pos l)
def O3 (c e f : Int) : Matrix 4 :=
  let l:=e-neg c; let n:=f+2*pos c+pos l
  ofSix 1 (-1) (-c-neg l+pos n) (-1) (-l+pos n) (-n)
def O4 (c e f : Int) : Matrix 4 :=
  let l:=e-neg c; let n:=f+2*pos c+pos l; let a:=-c-neg l+pos n
  ofSix (-1) 1 (-a) (-2) (-l+pos n-neg a) (-n+pos a)
def O5 (c e f : Int) : Matrix 4 :=
  let l:=e-neg c; let n:=f+2*pos c+pos l; let a:=-c-neg l+pos n
  let t:=-n+pos a
  ofSix 1 (-1) (-a+pos t) 2 (-l+pos n-neg a-2*neg t) (-t)
def N1 (c e f : Int) : Matrix 4 :=
  ofSix (-1) (-1) (c+pos e) (-1) (-e) (f-neg e)
def N2 (c e f : Int) : Matrix 4 :=
  let x:=c+pos e
  ofSix 1 1 (-x) (-1) (-e+pos x) (f-neg e+pos x)
def N3 (c e f : Int) : Matrix 4 :=
  let x:=c+pos e;let v:=f-neg e+pos x
  ofSix 2 (-1) (-x+pos v) 1 (-e+pos x-neg v) (-v)

private theorem four (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega

theorem matrices (c e f : Int) :
    mutate (R c e f) 0=O1 c e f ∧ mutate (O1 c e f) 1=O2 c e f ∧
    mutate (O2 c e f) 2=O3 c e f ∧ mutate (O3 c e f) 0=O4 c e f ∧
    mutate (O4 c e f) 2=O5 c e f ∧
    mutate (R c e f) 1=N1 c e f ∧ mutate (N1 c e f) 0=N2 c e f ∧
    mutate (N2 c e f) 2=N3 c e f := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> funext i j <;>
    rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
    simp [R,O1,O2,O3,O4,O5,N1,N2,N3,mutate,ofSix,correction,pos,neg] <;> ring

private theorem scalar_height_guard (c e f h : Int) (hh : 2≤h)
    (hc : -h≤c ∧ c≤h) (he : -h≤e ∧ e≤h) (hf : -h≤f ∧ f≤h)
    (hout : ¬(-h≤e-neg c ∧ e-neg c≤h ∧ -h≤f+2*pos c ∧ f+2*pos c≤h))
    (h1 : -(h+1)≤e-neg c ∧ e-neg c≤h+1 ∧
      -(h+1)≤f+2*pos c ∧ f+2*pos c≤h+1)
    (h2 : -(h+1)≤ -c-neg (e-neg c) ∧ -c-neg (e-neg c)≤h+1 ∧
      -(h+1)≤f+2*pos c+pos (e-neg c) ∧ f+2*pos c+pos (e-neg c)≤h+1)
    (hend : -h≤ -(-c-neg (e-neg c)+pos (f+2*pos c+pos (e-neg c)))+
        pos (-(f+2*pos c+pos (e-neg c))+pos (-c-neg (e-neg c)+pos (f+2*pos c+pos (e-neg c)))) ∧
      -(-c-neg (e-neg c)+pos (f+2*pos c+pos (e-neg c)))+
        pos (-(f+2*pos c+pos (e-neg c))+pos (-c-neg (e-neg c)+pos (f+2*pos c+pos (e-neg c))))≤h ∧
      -h≤ -(e-neg c)+pos (f+2*pos c+pos (e-neg c))-
        neg (-c-neg (e-neg c)+pos (f+2*pos c+pos (e-neg c)))-
        2*neg (-(f+2*pos c+pos (e-neg c))+pos (-c-neg (e-neg c)+pos (f+2*pos c+pos (e-neg c)))) ∧
      -(e-neg c)+pos (f+2*pos c+pos (e-neg c))-
        neg (-c-neg (e-neg c)+pos (f+2*pos c+pos (e-neg c)))-
        2*neg (-(f+2*pos c+pos (e-neg c))+pos (-c-neg (e-neg c)+pos (f+2*pos c+pos (e-neg c))))≤h ∧
      -h≤ -(f+2*pos c+pos (e-neg c))+pos (-c-neg (e-neg c)+pos (f+2*pos c+pos (e-neg c))) ∧
      -(f+2*pos c+pos (e-neg c))+pos (-c-neg (e-neg c)+pos (f+2*pos c+pos (e-neg c)))≤h) :
    (-h≤c+pos e ∧ c+pos e≤h) ∧ (-h≤f-neg e ∧ f-neg e≤h) ∧
    (-h≤ -e+pos (c+pos e) ∧ -e+pos (c+pos e)≤h) ∧
    (-h≤f-neg e+pos (c+pos e) ∧ f-neg e+pos (c+pos e)≤h) ∧
    (-h≤ -(c+pos e)+pos (f-neg e+pos (c+pos e)) ∧
      -(c+pos e)+pos (f-neg e+pos (c+pos e))≤h) ∧
    (-h≤ -e+pos (c+pos e)-neg (f-neg e+pos (c+pos e)) ∧
      -e+pos (c+pos e)-neg (f-neg e+pos (c+pos e))≤h) := by
  unfold pos neg at *
  omega

theorem guarded_new_prefix_below (c e f : Int) (H : Nat)
    (hR : HeightLe (R c e f) H)
    (hout : ¬HeightLe (mutate (R c e f) 0) H)
    (hceil : PrefixHeightLe (R c e f) [0,1,2,0,2] (H+1))
    (hend : HeightLe (applyWord (R c e f) [0,1,2,0,2]) H) :
    PrefixHeightLe (R c e f) [1,0,2] H := by
  obtain ⟨ho1,ho2,ho3,ho4,ho5,hn1,hn2,hn3⟩ := matrices c e f
  have h1 : HeightLe (O1 c e f) (H+1) := by
    simpa only [applyWord,ho1] using hceil [0] [1,2,0,2] rfl
  have h2 : HeightLe (O2 c e f) (H+1) := by
    simpa only [applyWord,ho1,ho2] using hceil [0,1] [2,0,2] rfl
  have h5 : HeightLe (O5 c e f) H := by
    simpa only [applyWord,ho1,ho2,ho3,ho4,ho5] using hend
  have hH := (hR 0 2).1
  change -(H:Int)≤ -2 at hH
  have hc := hR 0 3
  have he := hR 1 3
  have hf := hR 2 3
  change -(H:Int)≤c ∧ c≤(H:Int) at hc
  change -(H:Int)≤e ∧ e≤(H:Int) at he
  change -(H:Int)≤f ∧ f≤(H:Int) at hf
  have hout' : ¬(-(H:Int)≤e-neg c ∧ e-neg c≤(H:Int) ∧
      -(H:Int)≤f+2*pos c ∧ f+2*pos c≤(H:Int)) := by
    intro h
    apply hout
    rw [ho1]
    intro i j
    rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
      simp only [O1,ofSix] <;> omega
  have hh1 := h1 1 3
  have hh2 := h1 2 3
  have hh3 := h2 0 3
  have hh4 := h2 2 3
  have hh5 := h5 0 3
  have hh6 := h5 1 3
  have hh7 := h5 2 3
  simp only [O1,O2,O5,ofSix,Nat.cast_add,Nat.cast_one] at hh1 hh2 hh3 hh4 hh5 hh6 hh7
  have hguard := scalar_height_guard c e f (H:Int) (by omega) hc he hf hout'
    ⟨hh1.1,hh1.2,hh2.1,hh2.2⟩ ⟨hh3.1,hh3.2,hh4.1,hh4.2⟩
    ⟨hh5.1,hh5.2,hh6.1,hh6.2,by omega,by omega⟩
  have hb1 : HeightLe (N1 c e f) H := by
    intro i j
    rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
      simp only [N1,ofSix] <;> omega
  have hb2 : HeightLe (N2 c e f) H := by
    intro i j
    rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
      simp only [N2,ofSix] <;> omega
  have hb3 : HeightLe (N3 c e f) H := by
    intro i j
    rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
      simp only [N3,ofSix] <;> omega
  simp only [prefixHeight_cons,prefixHeight_nil,hn1,hn2,hn3]
  exact ⟨hR,hb1,hb2,hb3⟩

#print axioms matrices
#print axioms guarded_new_prefix_below
end QuiverProofs.Rank4StructureRound2.MixedUnitHeight
