import QuiverProofs.E2Strip

namespace QuiverProofs.E2Strip
open TriangleRegions

theorem p_zero (a b c : Int) (h : Domain a b c) : mutate (P a b c) 0=R a b c := by
  rw [←r_zero a b c h,mutation_involutive]
theorem q_one (a b c : Int) (h : Domain a b c) : mutate (Q a b c) 1=P a b c := by
  rw [←p_one a b c h,mutation_involutive]
theorem s_two (a b c : Int) (h : Domain a b c) : mutate (S a b c) 2=P a b c := by
  rw [←p_two a b c h,mutation_involutive]
theorem t_one (a b c : Int) (h : Domain a b c) : mutate (T a b c) 1=S a b c := by
  rw [←s_one a b c h,mutation_involutive]
theorem v_zero (a b c : Int) (h : Domain a b c) : mutate (V a b c) 0=T a b c := by
  rw [←t_zero a b c h,mutation_involutive]
theorem r_forward_two (a b c : Int) (h : Domain a b c) :
    mutate (R (A a b c) (B a c) (C a b c)) 2=Q a b c := by
  rw [←q_two a b c h,mutation_involutive]
theorem r_forward_one (a b c : Int) (h : Domain a b c) :
    mutate (R (A a b c) (B a c) (C a b c)) 1=relabel (T a b c) frame0213 := by
  rw [←t_two a b c h,mutate_relabel]
  change relabel (mutate (mutate (T a b c) 2) 2) frame0213 = _
  rw [mutation_involutive]
theorem q_forward_zero (a b c : Int) (h : Domain a b c) :
    mutate (Q (A a b c) (B a c) (C a b c)) 0=relabel (V a b c) frame2013 := by
  rw [←v_two a b c h,mutate_relabel]
  change relabel (mutate (mutate (V a b c) 2) 2) frame2013 = _
  rw [mutation_involutive]

def form (a b c : Int) (s : Fin 6) : Matrix 4 := match s.val with
  | 0 => R a b c | 1 => P a b c | 2 => Q a b c
  | 3 => S a b c | 4 => T a b c | _ => V a b c

private theorem fin6 (s : Fin 6) : s=0 ∨ s=1 ∨ s=2 ∨ s=3 ∨ s=4 ∨ s=5 := by omega

theorem layer_triangles (a b c : Int) (h : Domain a b c) (hr : AllTrianglesMA (R a b c)) :
    ∀ s : Fin 6, AllTrianglesMA (form a b c s) := by
  have hp : AllTrianglesMA (P a b c) := by
    apply deletion_triangle_transfer _ 0 (p_deletion a b c h)
    rwa [p_zero a b c h]
  have hq : AllTrianglesMA (Q a b c) := by
    apply deletion_triangle_transfer _ 1 (q_deletion a b c h)
    rwa [q_one a b c h]
  have hs : AllTrianglesMA (S a b c) := by
    apply deletion_triangle_transfer _ 2 (s_deletion a b c h)
    rwa [s_two a b c h]
  have ht : AllTrianglesMA (T a b c) := by
    apply deletion_triangle_transfer _ 1 (t_deletion a b c h)
    rwa [t_one a b c h]
  have hv : AllTrianglesMA (V a b c) := by
    apply deletion_triangle_transfer _ 0 (v_deletion a b c h)
    rwa [v_zero a b c h]
  intro s
  rcases fin6 s with rfl|rfl|rfl|rfl|rfl|rfl
  · exact hr
  · exact hp
  · exact hq
  · exact hs
  · exact ht
  · exact hv

structure Parameters where
  a : Int
  b : Int
  c : Int

def parameters : Nat → Parameters
  | 0 => ⟨13,5,7⟩
  | n+1 => let t := parameters n; ⟨A t.a t.b t.c,B t.a t.c,C t.a t.b t.c⟩

def pa (n : Nat) := (parameters n).a
def pb (n : Nat) := (parameters n).b
def pc (n : Nat) := (parameters n).c

theorem pa_succ (n : Nat) : pa (n+1)=A (pa n) (pb n) (pc n) := rfl
theorem pb_succ (n : Nat) : pb (n+1)=B (pa n) (pc n) := rfl
theorem pc_succ (n : Nat) : pc (n+1)=C (pa n) (pb n) (pc n) := rfl

theorem parameters_domain (n : Nat) : Domain (pa n) (pb n) (pc n) := by
  induction n with
  | zero => unfold Domain pa pb pc parameters; decide
  | succ n ih => exact domain_forward (pa n) (pb n) (pc n) ih

def strip (n : Nat) (s : Fin 6) : Matrix 4 := form (pa n) (pb n) (pc n) s

theorem strip_skew (n : Nat) (s : Fin 6) : SkewSymmetric (strip n s) := by
  rcases fin6 s with rfl|rfl|rfl|rfl|rfl|rfl <;> exact ofSix_skew _ _ _ _ _ _

theorem strip_cyclic (n : Nat) (s : Fin 6) : ¬ Acyclic (strip n s) := by
  have h := parameters_domain n
  rcases fin6 s with rfl|rfl|rfl|rfl|rfl|rfl
  · exact r_cyclic _ _ _ h
  · exact p_cyclic _ _ _ h
  · exact q_cyclic _ _ _ h
  · exact s_cyclic _ _ _ h
  · exact t_cyclic _ _ _ h
  · exact v_cyclic _ _ _ h

/-- The separate retained-triangle descent through all six states and every index. -/
theorem strip_triangles (hr : AllTrianglesMA (strip 0 0)) (n : Nat) (s : Fin 6) :
    AllTrianglesMA (strip n s) := by
  have hx : ∀ n, AllTrianglesMA (strip n 0) := by
    intro n
    induction n with
    | zero => exact hr
    | succ n ih =>
      have hq := layer_triangles _ _ _ (parameters_domain n) ih 2
      apply deletion_triangle_transfer _ 2 (r_deletion _ _ _ (parameters_domain (n+1)))
      change AllTrianglesMA (mutate (R (A (pa n) (pb n) (pc n)) (B (pa n) (pc n))
        (C (pa n) (pb n) (pc n))) 2)
      rw [r_forward_two _ _ _ (parameters_domain n)]
      exact hq
  exact layer_triangles _ _ _ (parameters_domain n) (hx n) s

end QuiverProofs.E2Strip
