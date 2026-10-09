import Rank4Round2.MixedUnitReverseRelation

/-! An exact sufficient and necessary local height inequality for the
second mixed triangle in a specified family. No MA membership or global
supplier of the parameter inequality is asserted. -/
namespace Rank4Round2.MixedUnitReverseFamily
open QuiverProofs Rank4Coordinator Rank4Round2 MixedUnitRelation
open MixedUnitReverseRelation

def R (H : Nat) (t f : Int) : Matrix 4 := R2 (-t) (t-((H:Int)+1)) f
def O1 (H : Nat) (t f : Int) : Matrix 4 := ofSix (-1) 1 t 1 (-((H:Int)+1)) f
def O2 (H : Nat) (t f : Int) : Matrix 4 := ofSix 1 1 (t-((H:Int)+1)) (-1) ((H:Int)+1) (f-((H:Int)+1))
def O3 (H : Nat) (t f : Int) : Matrix 4 := ofSix 2 (-1) (t-((H:Int)+1)) 1 f ((H:Int)+1-f)
def N1 (H : Nat) (t f : Int) : Matrix 4 := ofSix (-1) 1 (-t) (-2) ((H:Int)+1-t) (f+2*t-2*((H:Int)+1))
def N2 (H : Nat) (t f : Int) : Matrix 4 := ofSix 1 (-1) t (-1) ((H:Int)+1-t) (f+t-2*((H:Int)+1))
def N3 (H : Nat) (t f : Int) : Matrix 4 := ofSix 1 1 (f+2*t-2*((H:Int)+1)) 1 (f-((H:Int)+1)) (2*((H:Int)+1)-f-t)
def N4 (H : Nat) (t f : Int) : Matrix 4 := ofSix (-1) 2 (f+2*t-2*((H:Int)+1)) (-1) ((H:Int)+1-f) ((H:Int)+1-t)
def N5 (H : Nat) (t f : Int) : Matrix 4 := ofSix 1 (-2) f 1 ((H:Int)+1-f) (t-((H:Int)+1))

private theorem four (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega

theorem matrices (H : Nat) (t f : Int) (ht : 1≤t) (htH : t≤(H:Int))
    (hf : 1≤f) (hfH : f≤(H:Int)) :
    mutate (R H t f) 0=O1 H t f ∧ mutate (O1 H t f) 1=O2 H t f ∧
    mutate (O2 H t f) 2=O3 H t f ∧
    mutate (R H t f) 1=N1 H t f ∧ mutate (N1 H t f) 0=N2 H t f ∧
    mutate (N2 H t f) 2=N3 H t f ∧ mutate (N3 H t f) 1=N4 H t f ∧
    mutate (N4 H t f) 2=N5 H t f := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> funext i j <;>
    rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
    simp [R,R2,O1,O2,O3,N1,N2,N3,N4,N5,mutate,ofSix,correction] <;>
    first | omega | ring

theorem old_bounds (H : Nat) (t f : Int) (hH : 2≤H)
    (ht : 1≤t) (htH : t≤(H:Int)) (hf : 1≤f) (hfH : f≤(H:Int)) :
    HeightLe (R H t f) H ∧ HeightLe (O1 H t f) (H+1) ∧
    HeightLe (O2 H t f) (H+1) ∧ HeightLe (O3 H t f) H := by
  refine ⟨?_,?_,?_,?_⟩ <;> intro i j <;>
    rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
    simp only [R,R2,O1,O2,O3,ofSix,Nat.cast_add,Nat.cast_one] <;> omega

theorem new_bounds (H : Nat) (t f : Int) (hH : 2≤H)
    (ht : 1≤t) (htH : t≤(H:Int)) (hf : 1≤f) (hfH : f≤(H:Int))
    (hSum : (H:Int)+2≤f+t) :
    HeightLe (N1 H t f) H ∧ HeightLe (N2 H t f) H ∧
    HeightLe (N3 H t f) H ∧ HeightLe (N4 H t f) H ∧ HeightLe (N5 H t f) H := by
  refine ⟨?_,?_,?_,?_,?_⟩ <;> intro i j <;>
    rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
    simp only [N1,N2,N3,N4,N5,ofSix] <;> omega

theorem new_prefix_iff (H : Nat) (t f : Int) (hH : 2≤H)
    (ht : 1≤t) (htH : t≤(H:Int)) (hf : 1≤f) (hfH : f≤(H:Int)) :
    PrefixHeightLe (R H t f) long H ↔ (H:Int)+2≤f+t := by
  obtain ⟨_,_,_,hn1,hn2,hn3,hn4,hn5⟩ := matrices H t f ht htH hf hfH
  constructor
  · intro hn
    have hb := hn [1,0] [2,1,2] rfl
    have hh := (hb 2 3).1
    simp only [applyWord,hn1,hn2,N2,ofSix] at hh
    omega
  · intro hSum
    have hR := (old_bounds H t f hH ht htH hf hfH).1
    obtain ⟨h1,h2,h3,h4,h5⟩ := new_bounds H t f hH ht htH hf hfH hSum
    simp only [long,prefixHeight_cons,prefixHeight_nil,hn1,hn2,hn3,hn4,hn5]
    exact ⟨hR,h1,h2,h3,h4,h5⟩

theorem local_progress (H : Nat) (t f : Int) (hH : 2≤H)
    (ht : 1≤t) (htH : t≤(H:Int)) (hf : 1≤f) (hfH : f≤(H:Int))
    (hSum : (H:Int)+2≤f+t) :
    PrefixHeightLe (R H t f) short (H+1) ∧ PrefixHeightLe (R H t f) long H ∧
    overCount (R H t f) short H=2 ∧ overCount (R H t f) long H=0 := by
  obtain ⟨ho1,ho2,ho3,_,_,_,_,_⟩ := matrices H t f ht htH hf hfH
  obtain ⟨hR,h1,h2,h3⟩ := old_bounds H t f hH ht htH hf hfH
  have hn := (new_prefix_iff H t f hH ht htH hf hfH).mpr hSum
  have hh1 : ¬HeightLe (O1 H t f) H := by
    intro h;have hh := (h 1 3).1;change -(H:Int)≤ -((H:Int)+1) at hh;omega
  have hh2 : ¬HeightLe (O2 H t f) H := by
    intro h;have hh := (h 1 3).2;change (H:Int)+1≤(H:Int) at hh;omega
  refine ⟨?_,hn,?_,overCount_eq_zero _ _ _ hn⟩
  · simp only [short,prefixHeight_cons,prefixHeight_nil,ho1,ho2,ho3]
    exact ⟨heightLe_mono _ H (H+1) (by omega) hR,h1,h2,
      heightLe_mono _ H (H+1) (by omega) h3⟩
  · simp only [short,overCount,ho1,ho2,ho3,overBit,if_neg hh1,if_neg hh2,if_pos h3]

theorem tail_progress (H K : Nat) (t f : Int) (hH : 2≤H)
    (ht : 1≤t) (htH : t≤(H:Int)) (hf : 1≤f) (hfH : f≤(H:Int))
    (hSum : (H:Int)+2≤f+t) (hHK : H≤K) (tail : List (Fin 4))
    (hOld : PrefixHeightLe (R H t f) (short++tail) K)
    (ha : Acyclic (applyWord (R H t f) (short++tail))) :
    PrefixHeightLe (R H t f) (long++tail.map cycle.invFun) K ∧
    Acyclic (applyWord (R H t f) (long++tail.map cycle.invFun)) ∧
    overCount (R H t f) (long++tail.map cycle.invFun) H+2=
      overCount (R H t f) (short++tail) H := by
  obtain ⟨_,hn,hoCount,hnCount⟩ := local_progress H t f hH ht htH hf hfH hSum
  refine ⟨tail_prefix (-t) (t-((H:Int)+1)) f K tail
    (prefixHeight_mono _ _ H K hHK hn) hOld,
    tail_acyclic (-t) (t-((H:Int)+1)) f tail ha,?_⟩
  have hc := tail_count (-t) (t-((H:Int)+1)) f H tail
  change overCount (R H t f) (long++tail.map cycle.invFun) H+overCount (R H t f) short H=
    overCount (R H t f) (short++tail) H+overCount (R H t f) long H at hc
  rw [hoCount,hnCount,Nat.add_zero] at hc
  exact hc

#print axioms matrices
#print axioms new_prefix_iff
#print axioms local_progress
#print axioms tail_progress
end Rank4Round2.MixedUnitReverseFamily
