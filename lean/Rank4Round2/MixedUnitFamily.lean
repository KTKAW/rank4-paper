import Rank4Round2.MixedUnitFrame

/-! Uniform bounded progress for F=H+1, H>=2 and 1<=c<=H.
The old path has exactly four reached states above H; the three-letter
replacement stays below H. This is an explicit family, not a supplier
of membership for every mixed-unit first switch. -/
namespace Rank4Round2.MixedUnitFamily
open QuiverProofs Rank4Coordinator Rank4Round2 MixedUnitRelation

def R (H : Nat) (c : Int) : Matrix 4 := MixedUnitRelation.R c 0 ((H:Int)+1-2*c)
def O1 (H : Nat) (c : Int) : Matrix 4 := ofSix (-1) 2 (-c) (-1) 0 ((H:Int)+1)
def O2 (H : Nat) (c : Int) : Matrix 4 := ofSix 1 1 (-c) 1 0 ((H:Int)+1)
def O3 (H : Nat) (c : Int) : Matrix 4 := ofSix 1 (-1) ((H:Int)+1-c) (-1) ((H:Int)+1) (-((H:Int)+1))
def O4 (H : Nat) (c : Int) : Matrix 4 := ofSix (-1) 1 (c-((H:Int)+1)) (-2) ((H:Int)+1) (-c)
def O5 (H : Nat) (c : Int) : Matrix 4 := ofSix 1 (-1) (c-((H:Int)+1)) 2 ((H:Int)+1-2*c) c
def N1 (H : Nat) (c : Int) : Matrix 4 := ofSix (-1) (-1) c (-1) 0 ((H:Int)+1-2*c)
def N2 (H : Nat) (c : Int) : Matrix 4 := ofSix 1 1 (-c) (-1) c ((H:Int)+1-c)
def N3 (H : Nat) (c : Int) : Matrix 4 := ofSix 2 (-1) ((H:Int)+1-2*c) 1 c (c-((H:Int)+1))

private theorem four (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega

theorem matrices (H : Nat) (c : Int) (hc : 1≤c) (hCH : c≤(H:Int)) :
    mutate (R H c) 0=O1 H c ∧ mutate (O1 H c) 1=O2 H c ∧
    mutate (O2 H c) 2=O3 H c ∧ mutate (O3 H c) 0=O4 H c ∧
    mutate (O4 H c) 2=O5 H c ∧
    mutate (R H c) 1=N1 H c ∧ mutate (N1 H c) 0=N2 H c ∧
    mutate (N2 H c) 2=N3 H c := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> funext i j <;>
    rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
    simp [R,MixedUnitRelation.R,O1,O2,O3,O4,O5,N1,N2,N3,mutate,ofSix,correction] <;>
    first | omega | ring

theorem bounds (H : Nat) (c : Int) (hH : 2≤H) (hc : 1≤c) (hCH : c≤(H:Int)) :
    HeightLe (R H c) H ∧ HeightLe (O1 H c) (H+1) ∧
    HeightLe (O2 H c) (H+1) ∧ HeightLe (O3 H c) (H+1) ∧
    HeightLe (O4 H c) (H+1) ∧ HeightLe (O5 H c) H ∧
    HeightLe (N1 H c) H ∧ HeightLe (N2 H c) H ∧ HeightLe (N3 H c) H := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> intro i j <;>
    rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
    simp only [R,MixedUnitRelation.R,O1,O2,O3,O4,O5,N1,N2,N3,ofSix,
      Nat.cast_add,Nat.cast_one] <;> omega

theorem highs (H : Nat) (c : Int) :
    ¬HeightLe (O1 H c) H ∧ ¬HeightLe (O2 H c) H ∧
    ¬HeightLe (O3 H c) H ∧ ¬HeightLe (O4 H c) H := by
  refine ⟨?_,?_,?_,?_⟩
  · intro h;have hh := (h 2 3).2;change (H:Int)+1≤(H:Int) at hh;omega
  · intro h;have hh := (h 2 3).2;change (H:Int)+1≤(H:Int) at hh;omega
  · intro h;have hh := (h 1 3).2;change (H:Int)+1≤(H:Int) at hh;omega
  · intro h;have hh := (h 1 3).2;change (H:Int)+1≤(H:Int) at hh;omega

theorem local_progress (H : Nat) (c : Int) (hH : 2≤H) (hc : 1≤c) (hCH : c≤(H:Int)) :
    PrefixHeightLe (R H c) old (H+1) ∧ PrefixHeightLe (R H c) new H ∧
    overCount (R H c) old H=4 ∧ overCount (R H c) new H=0 := by
  obtain ⟨ho1,ho2,ho3,ho4,ho5,hn1,hn2,hn3⟩ := matrices H c hc hCH
  obtain ⟨hR,h1,h2,h3,h4,h5,hN1,hN2,hN3⟩ := bounds H c hH hc hCH
  obtain ⟨hh1,hh2,hh3,hh4⟩ := highs H c
  have hOld : PrefixHeightLe (R H c) old (H+1) := by
    simp only [old,prefixHeight_cons,prefixHeight_nil,ho1,ho2,ho3,ho4,ho5]
    exact ⟨heightLe_mono _ H (H+1) (by omega) hR,h1,h2,h3,h4,
      heightLe_mono _ H (H+1) (by omega) h5⟩
  have hNew : PrefixHeightLe (R H c) new H := by
    simp only [new,prefixHeight_cons,prefixHeight_nil,hn1,hn2,hn3]
    exact ⟨hR,hN1,hN2,hN3⟩
  refine ⟨hOld,hNew,?_,overCount_eq_zero _ _ _ hNew⟩
  simp only [old,overCount,ho1,ho2,ho3,ho4,ho5,overBit,
    if_neg hh1,if_neg hh2,if_neg hh3,if_neg hh4,if_pos h5]

theorem tail_progress (H K : Nat) (c : Int) (hH : 2≤H)
    (hc : 1≤c) (hCH : c≤(H:Int)) (hHK : H≤K) (tail : List (Fin 4))
    (hOld : PrefixHeightLe (R H c) (old++tail) K)
    (ha : Acyclic (applyWord (R H c) (old++tail))) :
    PrefixHeightLe (R H c) (new++tail.map cycle.invFun) K ∧
    Acyclic (applyWord (R H c) (new++tail.map cycle.invFun)) ∧
    overCount (R H c) (new++tail.map cycle.invFun) H+4=
      overCount (R H c) (old++tail) H := by
  obtain ⟨_,hNew,hOldCount,hNewCount⟩ := local_progress H c hH hc hCH
  refine ⟨literal_tail_prefix c 0 ((H:Int)+1-2*c) K tail
    (prefixHeight_mono _ _ H K hHK hNew) hOld,
    literal_tail_acyclic c 0 ((H:Int)+1-2*c) tail ha,?_⟩
  have h := literal_tail_count c 0 ((H:Int)+1-2*c) H tail
  change overCount (R H c) (new++tail.map cycle.invFun) H+overCount (R H c) old H=
    overCount (R H c) (old++tail) H+overCount (R H c) new H at h
  rw [hOldCount,hNewCount,Nat.add_zero] at h
  exact h

#print axioms matrices
#print axioms local_progress
#print axioms tail_progress
end Rank4Round2.MixedUnitFamily
