import QuiverProofs.PendantLanguage

/-! The two orientations of an abundant pendant root and their complete
unbounded recurrence. All base returns are explicit; both parent orientations
are retained. The proof reuses the exact pendant-square local identities. -/
namespace QuiverProofs.AbundantPendantStrip
open PendantSquare

structure Parameters where
  x : Int
  y : Int

def orbit (d : Int) (s : Parameters) : Nat → Parameters
  | 0 => s
  | n+1 => let t := orbit d s n; ⟨t.y,d*t.y-t.x⟩

def orientation (i : Fin 2) : Int := if i=0 then 1 else -1

def strip (c d : Int) (s : Parameters) (n : Nat) (i : Fin 2) : Matrix 4 :=
  state c d (orbit d s n).x (orbit d s n).y (orientation i)

def parent (c d : Int) (s : Parameters) (i : Fin 2) : Matrix 4 :=
  mutate (strip c d s 0 i) 1

theorem orbit_domain (c d : Int) (s : Parameters) (hs : Domain c d s.x s.y)
    (n : Nat) : Domain c d (orbit d s n).x (orbit d s n).y := by
  induction n with
  | zero => exact hs
  | succ n ih => exact child_domain c d _ _ ih

theorem orientation_sign (i : Fin 2) : Sign (orientation i) := by
  by_cases hi : i=0 <;> simp [orientation,Sign,hi]

theorem strip_skew (c d : Int) (s : Parameters) (n : Nat) (i : Fin 2) :
    SkewSymmetric (strip c d s n i) := ofSix_skew _ _ _ _ _ _

theorem strip_cyclic (c d : Int) (s : Parameters) (hs : Domain c d s.x s.y)
    (n : Nat) (i : Fin 2) : ¬Acyclic (strip c d s n i) :=
  cyclic c d _ _ _ (orbit_domain c d s hs n)

private theorem swap_twice (B : Matrix 4) : relabel (relabel B swap12) swap12 = B := by
  funext i j
  have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  have hj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
  rcases hi with rfl|rfl|rfl|rfl <;> rcases hj with rfl|rfl|rfl|rfl <;> rfl

theorem child_step (c d : Int) (s : Parameters) (hs : Domain c d s.x s.y)
    (n : Nat) (i : Fin 2) :
    mutate (strip c d s n i) 2 = relabel (strip c d s (n+1) i) swap12 := by
  have h := child_frame c d _ _ (orientation i) (orbit_domain c d s hs n)
  have hh := congrArg (fun B => relabel B swap12) h
  simpa only [swap_twice] using hh

theorem inward_step (c d : Int) (s : Parameters) (hs : Domain c d s.x s.y)
    (n : Nat) (i : Fin 2) :
    mutate (strip c d s (n+1) i) 1 = relabel (strip c d s n i) swap12 :=
  PendantLanguage.child_parent c d _ _ (orientation i) (orbit_domain c d s hs n)

/-- Every mutation is another strip state, one of the two actual base parents,
or a checked diamond root whose return is precisely the performed mutation. -/
theorem all_edges (c d : Int) (s : Parameters) (hs : Domain c d s.x s.y)
    (n : Nat) (i : Fin 2) (k : Fin 4) :
    (∃ (n' : Nat) (i' : Fin 2) (p : Relabeling 4),
      mutate (strip c d s n i) k = relabel (strip c d s n' i') p) ∨
    (∃ (i' : Fin 2) (p : Relabeling 4),
      mutate (strip c d s n i) k = relabel (parent c d s i') p) ∨
    Regions.IsRoot (mutate (strip c d s n i) k) k := by
  have hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
  rcases hk with rfl|rfl|rfl|rfl
  · left
    have hi : i=0 ∨ i=1 := by omega
    rcases hi with rfl|rfl
    · refine ⟨n,1,.identity 4,?_⟩
      exact leaf c d _ _ 1
    · refine ⟨n,0,.identity 4,?_⟩
      simpa only [show -(-1 : Int)=1 by decide] using leaf c d (orbit d s n).x (orbit d s n).y (-1)
  · cases n with
    | zero => exact Or.inr (Or.inl ⟨i,.identity 4,rfl⟩)
    | succ n => exact Or.inl ⟨n,i,swap12,inward_step c d s hs n i⟩
  · exact Or.inl ⟨n+1,i,swap12,child_step c d s hs n i⟩
  · exact Or.inr (Or.inr (junction_isRoot c d _ _ _ (orbit_domain c d s hs n) (orientation_sign i)))

end QuiverProofs.AbundantPendantStrip
