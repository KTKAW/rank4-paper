import QuiverProofs.UnitZeroStrip
import QuiverProofs.TriangleRegions

/-! Exact symbolic local rules of the unit-pendant continuation. The domain is
`d,x ≥ 2` and `y > max(d,x)`. Base parents are explicit interfaces, not
negative recursion indices. -/
namespace QuiverProofs.UnitPendantStrip
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def Domain (d x y : Int) : Prop := 2 ≤ d ∧ 2 ≤ x ∧ d < y ∧ x < y
def h (d x y : Int) : Int := x*y-d

def D0 (d x y : Int) : Matrix 4 := ofSix 0 0 1 d (-x) y
def D1 (d x y : Int) : Matrix 4 := ofSix 0 0 (-1) d (-x) y
def D2 (d x y : Int) : Matrix 4 := ofSix 0 (-y) 1 (-(h d x y)) x (-y)
def D3 (d x y : Int) : Matrix 4 := ofSix 0 y (-1) (-(h d x y)) x 0
def D4 (d x y : Int) : Matrix 4 := ofSix (-x) y 1 (-(h d x y)) (-x) 0

def sigma : Relabeling 4 :=
  ⟨fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | _ => 0,
   fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | _ => 0,
   by decide, by decide⟩
abbrev tau : Relabeling 4 := Regions.frame0213
def rho : Relabeling 4 :=
  ⟨fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | _ => 0,
   fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | _ => 0,
   by decide, by decide⟩

def phase (d x y : Int) (i : Fin 10) : Matrix 4 :=
  match i.val with
  | 0 => D0 d x y | 1 => D1 d x y | 2 => D2 d x y
  | 3 => D3 d x y | 4 => D4 d x y
  | 5 => relabel (D0 d x y) sigma | 6 => relabel (D1 d x y) sigma
  | 7 => relabel (D2 d x y) sigma | 8 => relabel (D3 d x y) sigma
  | _ => relabel (D4 d x y) sigma

private theorem fin4 (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
private theorem fin10 (i : Fin 10) :
    i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 := by omega

/-- Inequalities used in both recursive cones and the two zero-edge roots. -/
theorem parameter_bounds (d x y : Int) (hd : Domain d x y) :
    y < h d x y ∧ y < d*y-x ∧ d < d*y-x ∧
    x < x*h d x y-y ∧ h d x y < x*h d x y-y ∧
    y < y*h d x y-x ∧ h d x y < y*h d x y-x ∧
    x < x*x-1 ∧ y < y*y-1 := by
  obtain ⟨hd,hx,hdy,hxy⟩ := hd
  have hy : 2 ≤ y := by omega
  have hxy2 := Int.mul_le_mul_of_nonneg_right hx (show 0 ≤ y by omega)
  have hh : y < h d x y := by unfold h; omega
  have hdy2 := Int.mul_le_mul_of_nonneg_right hd (show 0 ≤ y by omega)
  have hxh := Forks.product_sub_dominates x (h d x y) y hx (by omega) hh
  have hyh := Forks.product_sub_dominates y (h d x y) x hy hh (by omega)
  have hxx := Int.mul_le_mul_of_nonneg_right hx (show 0 ≤ x by omega)
  have hyy := Int.mul_le_mul_of_nonneg_right hy (show 0 ≤ y by omega)
  omega

theorem child_domain (d x y : Int) (hd : Domain d x y) : Domain d y (d*y-x) := by
  have hb := parameter_bounds d x y hd
  unfold Domain at *
  omega

theorem attachment_cones (d x y : Int) (hd : Domain d x y) :
    (2 ≤ x ∧ 2 ≤ y ∧ x < h d x y ∧ h d x y < x*h d x y-y) ∧
    (2 ≤ y ∧ 2 ≤ x ∧ y < h d x y ∧ h d x y < y*h d x y-x) := by
  have hb := parameter_bounds d x y hd
  unfold Domain at hd
  omega

abbrev N0 (x u v w : Int) : Matrix 4 := UnitZeroStrip.node x u v w 0
abbrev N1 (x u v w : Int) : Matrix 4 := UnitZeroStrip.node x u v w 1

theorem D0_zero (d x y : Int) (hd : Domain d x y) :
    mutate (D0 d x y) 0 = D1 d x y := by
  have hb := parameter_bounds d x y hd
  unfold Domain h at *
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;>
    rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [D0,D1,D2,D3,D4,N0,N1,UnitZeroStrip.node,h,relabel,reverse,sigma,tau,Regions.frame0213,rho,
      mutate,correction,ofSix] <;> grind

theorem D1_three (d x y : Int) (hd : Domain d x y) :
    mutate (D1 d x y) 3 = D2 d x y := by
  have hb := parameter_bounds d x y hd
  unfold Domain h at *
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;>
    rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [D0,D1,D2,D3,D4,N0,N1,UnitZeroStrip.node,h,relabel,reverse,sigma,tau,Regions.frame0213,rho,
      mutate,correction,ofSix] <;> grind

theorem D2_zero (d x y : Int) (hd : Domain d x y) :
    mutate (D2 d x y) 0 = D3 d x y := by
  have hb := parameter_bounds d x y hd
  unfold Domain h at *
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;>
    rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [D0,D1,D2,D3,D4,N0,N1,UnitZeroStrip.node,h,relabel,reverse,sigma,tau,Regions.frame0213,rho,
      mutate,correction,ofSix] <;> grind

theorem D3_three (d x y : Int) (hd : Domain d x y) :
    mutate (D3 d x y) 3 = D4 d x y := by
  have hb := parameter_bounds d x y hd
  unfold Domain h at *
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;>
    rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [D0,D1,D2,D3,D4,N0,N1,UnitZeroStrip.node,h,relabel,reverse,sigma,tau,Regions.frame0213,rho,
      mutate,correction,ofSix] <;> grind

theorem D4_zero (d x y : Int) (hd : Domain d x y) :
    mutate (D4 d x y) 0 = relabel (D0 d x y) sigma := by
  have hb := parameter_bounds d x y hd
  unfold Domain h at *
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;>
    rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [D0,D1,D2,D3,D4,N0,N1,UnitZeroStrip.node,h,relabel,reverse,sigma,tau,Regions.frame0213,rho,
      mutate,correction,ofSix] <;> grind

theorem D0_two (d x y : Int) (hd : Domain d x y) :
    mutate (D0 d x y) 2 = relabel (D0 d y (d*y-x)) tau := by
  have hb := parameter_bounds d x y hd
  unfold Domain h at *
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;>
    rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [D0,D1,D2,D3,D4,N0,N1,UnitZeroStrip.node,h,relabel,reverse,sigma,tau,Regions.frame0213,rho,
      mutate,correction,ofSix] <;> grind

theorem D1_two (d x y : Int) (hd : Domain d x y) :
    mutate (D1 d x y) 2 = relabel (D1 d y (d*y-x)) tau := by
  have hb := parameter_bounds d x y hd
  unfold Domain h at *
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;>
    rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [D0,D1,D2,D3,D4,N0,N1,UnitZeroStrip.node,h,relabel,reverse,sigma,tau,Regions.frame0213,rho,
      mutate,correction,ofSix] <;> grind

theorem D2_one (d x y : Int) (hd : Domain d x y) :
    mutate (D2 d x y) 1 = N0 x y (h d x y) (x*h d x y-y) := by
  have hb := parameter_bounds d x y hd
  unfold Domain h at *
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;>
    rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [D0,D1,D2,D3,D4,N0,N1,UnitZeroStrip.node,h,relabel,reverse,sigma,tau,Regions.frame0213,rho,
      mutate,correction,ofSix] <;> grind

theorem D3_one (d x y : Int) (hd : Domain d x y) :
    mutate (D3 d x y) 1 = N1 x y (h d x y) (x*h d x y-y) := by
  have hb := parameter_bounds d x y hd
  unfold Domain h at *
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;>
    rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [D0,D1,D2,D3,D4,N0,N1,UnitZeroStrip.node,h,relabel,reverse,sigma,tau,Regions.frame0213,rho,
      mutate,correction,ofSix] <;> grind

theorem D3_two (d x y : Int) (hd : Domain d x y) :
    mutate (D3 d x y) 2 = reverse (relabel (N1 y x (h d x y) (y*h d x y-x)) rho) := by
  have hb := parameter_bounds d x y hd
  unfold Domain h at *
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;>
    rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [D0,D1,D2,D3,D4,N0,N1,UnitZeroStrip.node,h,relabel,reverse,sigma,tau,Regions.frame0213,rho,
      mutate,correction,ofSix] <;> grind

theorem D4_two (d x y : Int) (hd : Domain d x y) :
    mutate (D4 d x y) 2 = reverse (relabel (N0 y x (h d x y) (y*h d x y-x)) rho) := by
  have hb := parameter_bounds d x y hd
  unfold Domain h at *
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;>
    rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [D0,D1,D2,D3,D4,N0,N1,UnitZeroStrip.node,h,relabel,reverse,sigma,tau,Regions.frame0213,rho,
      mutate,correction,ofSix] <;> grind

theorem D2_two_matrix (d x y : Int) (hd : Domain d x y) :
    mutate (D2 d x y) 2 = ofSix 0 y (1-y*y) (h d x y) (x-h d x y*y) y := by
  have hb := parameter_bounds d x y hd
  unfold Domain h at *
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;>
    rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [D0,D1,D2,D3,D4,N0,N1,UnitZeroStrip.node,h,relabel,reverse,sigma,tau,Regions.frame0213,rho,
      mutate,correction,ofSix] <;> grind

theorem D4_one_matrix (d x y : Int) (hd : Domain d x y) :
    mutate (D4 d x y) 1 = ofSix x (y-x*h d x y) (1-x*x) (h d x y) x 0 := by
  have hb := parameter_bounds d x y hd
  unfold Domain h at *
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;>
    rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [D0,D1,D2,D3,D4,N0,N1,UnitZeroStrip.node,h,relabel,reverse,sigma,tau,Regions.frame0213,rho,
      mutate,correction,ofSix] <;> grind

theorem D0_one_matrix (d x y : Int) (hd : Domain d x y) :
    mutate (D0 d x y) 1 = ofSix 0 0 1 (-d) x (y-d*x) := by
  have hb := parameter_bounds d x y hd
  unfold Domain h at *
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;>
    rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [D0,D1,D2,D3,D4,N0,N1,UnitZeroStrip.node,h,relabel,reverse,sigma,tau,Regions.frame0213,rho,
      mutate,correction,ofSix] <;> grind

theorem D1_one_matrix (d x y : Int) (hd : Domain d x y) :
    mutate (D1 d x y) 1 = ofSix 0 0 (-1) (-d) x (y-d*x) := by
  have hb := parameter_bounds d x y hd
  unfold Domain h at *
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;>
    rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [D0,D1,D2,D3,D4,N0,N1,UnitZeroStrip.node,h,relabel,reverse,sigma,tau,Regions.frame0213,rho,
      mutate,correction,ofSix] <;> grind

private def frame2301 : Relabeling 4 :=
  ⟨fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | _ => 1,
   fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | _ => 1,
   by decide, by decide⟩

theorem D2_two_domain (d x y : Int) (hd : Domain d x y) :
    Regions.Domain y (y*y-1) (h d x y*y-x) y (h d x y) := by
  have hb := parameter_bounds d x y hd
  have he : h d x y*y = y*h d x y := by grind
  unfold Domain at hd
  unfold Regions.Domain
  omega

theorem D2_two_root (d x y : Int) (hd : Domain d x y) :
    Regions.IsRoot (mutate (D2 d x y) 2) 2 := by
  have he : relabel (mutate (D2 d x y) 2) frame2301 =
      Regions.root y (y*y-1) (h d x y*y-x) y (h d x y) 0 := by
    rw [D2_two_matrix d x y hd]
    funext i j
    rcases fin4 i with rfl|rfl|rfl|rfl <;>
      rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [relabel,frame2301,Regions.root,ofSix] <;> grind
  have hr : Regions.IsRoot (relabel (mutate (D2 d x y) 2) frame2301) 0 := by
    rw [he]
    exact .basic _ _ _ _ _ _ (D2_two_domain d x y hd) (Or.inl rfl)
  exact Regions.root_of_relabel frame2301 hr

theorem D4_one_domain (d x y : Int) (hd : Domain d x y) :
    Regions.Domain x (x*h d x y-y) (x*x-1) (h d x y) x := by
  have hb := parameter_bounds d x y hd
  unfold Domain at hd
  unfold Regions.Domain
  omega

theorem D4_one_root (d x y : Int) (hd : Domain d x y) :
    Regions.IsRoot (mutate (D4 d x y) 1) 1 := by
  have he : relabel (reverse (mutate (D4 d x y) 1)) Forks.swap01 =
      Regions.root x (x*h d x y-y) (x*x-1) (h d x y) x 0 := by
    rw [D4_one_matrix d x y hd]
    funext i j
    rcases fin4 i with rfl|rfl|rfl|rfl <;>
      rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [relabel,reverse,Forks.swap01,Regions.root,ofSix] <;> grind
  have hr : Regions.IsRoot (relabel (reverse (mutate (D4 d x y) 1)) Forks.swap01) 0 := by
    rw [he]
    exact .basic _ _ _ _ _ _ (D4_one_domain d x y hd) (Or.inl rfl)
  exact Regions.root_of_reverse (Regions.root_of_relabel Forks.swap01 hr)

theorem parent_commutation (d x y : Int) (hd : Domain d x y) :
    mutate (mutate (D0 d x y) 1) 0 = mutate (D1 d x y) 1 := by
  rw [D0_one_matrix d x y hd,D1_one_matrix d x y hd]
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;>
    rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [mutate,correction,ofSix] <;> grind

def forwardVertex (i : Fin 10) : Fin 4 := if i.val%2=0 then 0 else 3
def nextPhase (i : Fin 10) : Fin 10 := ⟨(i.val+1)%10, Nat.mod_lt _ (by decide)⟩
def previousPhase (i : Fin 10) : Fin 10 := ⟨(i.val+9)%10, Nat.mod_lt _ (by decide)⟩
def backwardVertex (i : Fin 10) : Fin 4 := if i.val%2=0 then 3 else 0
def swapPhase (i : Fin 10) : Fin 10 := ⟨(i.val+5)%10, Nat.mod_lt _ (by decide)⟩

theorem swapped (d x y : Int) (i : Fin 10) :
    phase d x y (swapPhase i) = relabel (phase d x y i) sigma := by
  rcases fin10 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    funext a b <;>
    rcases fin4 a with rfl|rfl|rfl|rfl <;>
    rcases fin4 b with rfl|rfl|rfl|rfl <;>
    simp [phase,swapPhase,relabel,sigma]

theorem special_5 (d x y : Int) (hd : Domain d x y) :
    mutate (phase d x y 5) 3 = phase d x y 6 := by
  have hb := parameter_bounds d x y hd
  unfold Domain h at *
  funext a b
  rcases fin4 a with rfl|rfl|rfl|rfl <;>
    rcases fin4 b with rfl|rfl|rfl|rfl <;>
    simp [phase,D0,D1,D2,D3,D4,h,relabel,sigma,mutate,correction,ofSix] <;> grind

theorem special_6 (d x y : Int) (hd : Domain d x y) :
    mutate (phase d x y 6) 0 = phase d x y 7 := by
  have hb := parameter_bounds d x y hd
  unfold Domain h at *
  funext a b
  rcases fin4 a with rfl|rfl|rfl|rfl <;>
    rcases fin4 b with rfl|rfl|rfl|rfl <;>
    simp [phase,D0,D1,D2,D3,D4,h,relabel,sigma,mutate,correction,ofSix] <;> grind

theorem special_7 (d x y : Int) (hd : Domain d x y) :
    mutate (phase d x y 7) 3 = phase d x y 8 := by
  have hb := parameter_bounds d x y hd
  unfold Domain h at *
  funext a b
  rcases fin4 a with rfl|rfl|rfl|rfl <;>
    rcases fin4 b with rfl|rfl|rfl|rfl <;>
    simp [phase,D0,D1,D2,D3,D4,h,relabel,sigma,mutate,correction,ofSix] <;> grind

theorem special_8 (d x y : Int) (hd : Domain d x y) :
    mutate (phase d x y 8) 0 = phase d x y 9 := by
  have hb := parameter_bounds d x y hd
  unfold Domain h at *
  funext a b
  rcases fin4 a with rfl|rfl|rfl|rfl <;>
    rcases fin4 b with rfl|rfl|rfl|rfl <;>
    simp [phase,D0,D1,D2,D3,D4,h,relabel,sigma,mutate,correction,ofSix] <;> grind

theorem special_9 (d x y : Int) (hd : Domain d x y) :
    mutate (phase d x y 9) 3 = phase d x y 0 := by
  have hb := parameter_bounds d x y hd
  unfold Domain h at *
  funext a b
  rcases fin4 a with rfl|rfl|rfl|rfl <;>
    rcases fin4 b with rfl|rfl|rfl|rfl <;>
    simp [phase,D0,D1,D2,D3,D4,h,relabel,sigma,mutate,correction,ofSix] <;> grind

theorem forward_step (d x y : Int) (hd : Domain d x y) (i : Fin 10) :
    mutate (phase d x y i) (forwardVertex i) = phase d x y (nextPhase i) := by
  rcases fin10 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact D0_zero d x y hd
  · exact D1_three d x y hd
  · exact D2_zero d x y hd
  · exact D3_three d x y hd
  · exact D4_zero d x y hd
  · exact special_5 d x y hd
  · exact special_6 d x y hd
  · exact special_7 d x y hd
  · exact special_8 d x y hd
  · exact special_9 d x y hd

theorem backward_step (d x y : Int) (hd : Domain d x y) (i : Fin 10) :
    mutate (phase d x y i) (backwardVertex i) = phase d x y (previousPhase i) := by
  have he := forward_step d x y hd (previousPhase i)
  have hn : nextPhase (previousPhase i)=i := by
    rcases fin10 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  have hv : forwardVertex (previousPhase i)=backwardVertex i := by
    rcases fin10 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  rw [hn,hv] at he
  rw [←he,mutation_involutive]

theorem phase_skew (d x y : Int) (i : Fin 10) : SkewSymmetric (phase d x y i) := by
  rcases fin10 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact ofSix_skew _ _ _ _ _ _ | exact relabel_skew _ _ (ofSix_skew _ _ _ _ _ _)

theorem D0_cyclic (d x y : Int) (hd : Domain d x y) : ¬Acyclic (D0 d x y) := by
  have hb := parameter_bounds d x y hd
  unfold Domain h at *
  rintro ⟨rank,hr⟩
  have h0 := hr 1 2 (by simp [D0,h,ofSix] <;> omega)
  have h1 := hr 2 3 (by simp [D0,h,ofSix] <;> omega)
  have h2 := hr 3 1 (by simp [D0,h,ofSix] <;> omega)
  omega

theorem D1_cyclic (d x y : Int) (hd : Domain d x y) : ¬Acyclic (D1 d x y) := by
  have hb := parameter_bounds d x y hd
  unfold Domain h at *
  rintro ⟨rank,hr⟩
  have h0 := hr 1 2 (by simp [D1,h,ofSix] <;> omega)
  have h1 := hr 2 3 (by simp [D1,h,ofSix] <;> omega)
  have h2 := hr 3 1 (by simp [D1,h,ofSix] <;> omega)
  omega

theorem D2_cyclic (d x y : Int) (hd : Domain d x y) : ¬Acyclic (D2 d x y) := by
  have hb := parameter_bounds d x y hd
  unfold Domain h at *
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by simp [D2,h,ofSix] <;> omega)
  have h1 := hr 3 2 (by simp [D2,h,ofSix] <;> omega)
  have h2 := hr 2 0 (by simp [D2,h,ofSix] <;> omega)
  omega

theorem D3_cyclic (d x y : Int) (hd : Domain d x y) : ¬Acyclic (D3 d x y) := by
  have hb := parameter_bounds d x y hd
  unfold Domain h at *
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (by simp [D3,h,ofSix] <;> omega)
  have h1 := hr 2 1 (by simp [D3,h,ofSix] <;> omega)
  have h2 := hr 1 3 (by simp [D3,h,ofSix] <;> omega)
  have h3 := hr 3 0 (by simp [D3,h,ofSix] <;> omega)
  omega

theorem D4_cyclic (d x y : Int) (hd : Domain d x y) : ¬Acyclic (D4 d x y) := by
  have hb := parameter_bounds d x y hd
  unfold Domain h at *
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (by simp [D4,h,ofSix] <;> omega)
  have h1 := hr 2 1 (by simp [D4,h,ofSix] <;> omega)
  have h2 := hr 1 0 (by simp [D4,h,ofSix] <;> omega)
  omega

theorem phase_cyclic (d x y : Int) (hd : Domain d x y) (i : Fin 10) :
    ¬Acyclic (phase d x y i) := by
  rcases fin10 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact D0_cyclic d x y hd
  · exact D1_cyclic d x y hd
  · exact D2_cyclic d x y hd
  · exact D3_cyclic d x y hd
  · exact D4_cyclic d x y hd
  · intro ha
    exact D0_cyclic d x y hd ((acyclic_relabel_iff _ sigma).mp ha)
  · intro ha
    exact D1_cyclic d x y hd ((acyclic_relabel_iff _ sigma).mp ha)
  · intro ha
    exact D2_cyclic d x y hd ((acyclic_relabel_iff _ sigma).mp ha)
  · intro ha
    exact D3_cyclic d x y hd ((acyclic_relabel_iff _ sigma).mp ha)
  · intro ha
    exact D4_cyclic d x y hd ((acyclic_relabel_iff _ sigma).mp ha)

/-- Both parents of the recursively attached pendant cell are old phases. -/
theorem child_D0_one (d x y : Int) (hd : Domain d x y) :
    mutate (D0 d y (d*y-x)) 1 = relabel (D0 d x y) tau := by
  rw [D0_one_matrix d y (d*y-x) (child_domain d x y hd)]
  funext a b
  rcases fin4 a with rfl|rfl|rfl|rfl <;>
    rcases fin4 b with rfl|rfl|rfl|rfl <;>
    simp [D0,relabel,tau,Regions.frame0213,ofSix] <;> grind

theorem child_D1_one (d x y : Int) (hd : Domain d x y) :
    mutate (D1 d y (d*y-x)) 1 = relabel (D1 d x y) tau := by
  rw [D1_one_matrix d y (d*y-x) (child_domain d x y hd)]
  funext a b
  rcases fin4 a with rfl|rfl|rfl|rfl <;>
    rcases fin4 b with rfl|rfl|rfl|rfl <;>
    simp [D1,relabel,tau,Regions.frame0213,ofSix] <;> grind

/-- The two unswapped parents of the first attached N strip. -/
theorem A0_one (d x y : Int) (hd : Domain d x y) :
    mutate (N0 x y (h d x y) (x*h d x y-y)) 1 = D2 d x y := by
  rw [←D2_one d x y hd,mutation_involutive]

theorem A1_one (d x y : Int) (hd : Domain d x y) :
    mutate (N1 x y (h d x y) (x*h d x y-y)) 1 = D3 d x y := by
  rw [←D3_one d x y hd,mutation_involutive]

theorem signed_rho_involutive (B : Matrix 4) :
    reverse (relabel (reverse (relabel B rho)) rho) = B := by
  funext a b
  rcases fin4 a with rfl|rfl|rfl|rfl <;>
    rcases fin4 b with rfl|rfl|rfl|rfl <;>
    simp [reverse,relabel,rho]

/-- The second attached N strip returns in the exact signed rho frame. -/
theorem B0_one (d x y : Int) (hd : Domain d x y) :
    mutate (N0 y x (h d x y) (y*h d x y-x)) 1 = reverse (relabel (D4 d x y) rho) := by
  have hm := congrArg (fun B => mutate B 2) (D4_two d x y hd)
  dsimp only at hm
  rw [mutation_involutive,mutate_reverse,mutate_relabel] at hm
  change D4 d x y = reverse (relabel (mutate (N0 y x (h d x y) (y*h d x y-x)) 1) rho) at hm
  have hr := congrArg (fun B => reverse (relabel B rho)) hm
  dsimp only at hr
  rw [signed_rho_involutive] at hr
  exact hr.symm

theorem B1_one (d x y : Int) (hd : Domain d x y) :
    mutate (N1 y x (h d x y) (y*h d x y-x)) 1 = reverse (relabel (D3 d x y) rho) := by
  have hm := congrArg (fun B => mutate B 2) (D3_two d x y hd)
  dsimp only at hm
  rw [mutation_involutive,mutate_reverse,mutate_relabel] at hm
  change D3 d x y = reverse (relabel (mutate (N1 y x (h d x y) (y*h d x y-x)) 1) rho) at hm
  have hr := congrArg (fun B => reverse (relabel B rho)) hm
  dsimp only at hr
  rw [signed_rho_involutive] at hr
  exact hr.symm

/-- Mutation 1 or 2 commutes with the special-label swap. This supplies
all swapped exterior and parent equations from the unswapped identities. -/
theorem swap_mutation (B : Matrix 4) (k : Fin 4) (hk : k=1 ∨ k=2) :
    mutate (relabel B sigma) k = relabel (mutate B k) sigma := by
  rw [mutate_relabel]
  rcases hk with rfl|rfl <;> rfl

open TriangleRegions

/-- Selected retained mutation. Phases 3 and 8 have all triangles acyclic
and therefore do not use the otherwise arbitrary value zero. -/
def inward (i : Fin 10) : Fin 4 := match i.val with
  | 0 | 1 | 5 | 6 => 1 | 2 | 9 => 3 | _ => 0

def level (i : Fin 10) : Nat := match i.val with
  | 2 | 4 | 7 | 9 => 1 | _ => 0

private def deletionRank (i : Fin 10) (v : Fin 4) : Nat :=
  match i.val,v.val with
  | 0,3 => 1 | 1,0 => 2 | 1,3 => 1
  | 2,0 => 1 | 2,1 => 1 | 4,1 => 1
  | 5,0 => 1 | 6,0 => 1 | 6,3 => 2
  | 7,1 => 1 | 7,3 => 1 | 9,1 => 1 | _,_ => 0

theorem phase_deletion (d x y : Int) (hd : Domain d x y) (i : Fin 10)
    (hi3 : i≠3) (hi8 : i≠8) : DeletionAcyclic (phase d x y i) (inward i) := by
  have hb := parameter_bounds d x y hd
  unfold Domain h at *
  refine ⟨deletionRank i,?_⟩
  intro a b ha hb' hab
  rcases fin10 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    rcases fin4 a with rfl|rfl|rfl|rfl <;>
    rcases fin4 b with rfl|rfl|rfl|rfl <;>
    simp_all [phase,D0,D1,D2,D3,D4,h,relabel,sigma,ofSix,inward,deletionRank] <;> omega

private def exceptionalRank (r v : Fin 4) : Nat := match r.val,v.val with
  | 0,1 => 1 | 0,3 => 2
  | 1,0 => 1 | 1,2 => 2
  | 2,3 => 1 | 2,0 => 2
  | 3,2 => 1 | 3,1 => 2
  | _,_ => 0

/-- The directed four-cycle D3 has an acyclic deletion at every vertex. -/
theorem D3_deletions (d x y : Int) (hd : Domain d x y) (r : Fin 4) :
    DeletionAcyclic (D3 d x y) r := by
  have hb := parameter_bounds d x y hd
  unfold Domain h at *
  refine ⟨exceptionalRank r,?_⟩
  intro a b ha hb' hab
  rcases fin4 r with rfl|rfl|rfl|rfl <;>
    rcases fin4 a with rfl|rfl|rfl|rfl <;>
    rcases fin4 b with rfl|rfl|rfl|rfl <;>
    simp_all [D3,h,ofSix,exceptionalRank] <;> omega

theorem D3_triangles (d x y : Int) (hd : Domain d x y) : AllTrianglesMA (D3 d x y) := by
  apply allTrianglesMA_of_deletions
  intro r
  obtain ⟨rank,hr⟩ := D3_deletions d x y hd r
  apply acyclic_is_mutationAcyclic
  refine ⟨rank ∘ deleteVertex r,?_⟩
  intro i j hij
  apply hr _ _ ?_ ?_ hij
  all_goals
    have hmiss : ∀ (r : Fin 4) (a : Fin 3), deleteVertex r a≠r := by decide
    apply hmiss

theorem exceptional_triangles (d x y : Int) (hd : Domain d x y) (i : Fin 10)
    (hi : i=3 ∨ i=8) : AllTrianglesMA (phase d x y i) := by
  rcases hi with rfl|rfl
  · exact D3_triangles d x y hd
  · exact triangles_relabel _ sigma (D3_triangles d x y hd)

/-- The four positive-level phases descend within the same decagon. -/
theorem inward_phase_descent (d x y : Int) (hd : Domain d x y) (i : Fin 10)
    (hi : i=2 ∨ i=4 ∨ i=7 ∨ i=9) :
    ∃ j : Fin 10, mutate (phase d x y i) (inward i) = phase d x y j ∧ level j < level i := by
  rcases hi with rfl|rfl|rfl|rfl
  · exact ⟨1,backward_step d x y hd 2,by decide⟩
  · exact ⟨5,forward_step d x y hd 4,by decide⟩
  · exact ⟨6,backward_step d x y hd 7,by decide⟩
  · exact ⟨0,forward_step d x y hd 9,by decide⟩

/-- Local triangle descent reaches the two actual supplied parents. -/
theorem phase_triangles (d x y : Int) (hd : Domain d x y)
    (h0 : AllTrianglesMA (mutate (D0 d x y) 1))
    (h1 : AllTrianglesMA (mutate (D1 d x y) 1)) (i : Fin 10) :
    AllTrianglesMA (phase d x y i) := by
  have ht0 : AllTrianglesMA (D0 d x y) :=
    deletion_triangle_transfer _ 1 (phase_deletion d x y hd 0 (by decide) (by decide)) h0
  have ht1 : AllTrianglesMA (D1 d x y) :=
    deletion_triangle_transfer _ 1 (phase_deletion d x y hd 1 (by decide) (by decide)) h1
  have ht2 : AllTrianglesMA (D2 d x y) := by
    apply deletion_triangle_transfer _ 3 (phase_deletion d x y hd 2 (by decide) (by decide))
    change AllTrianglesMA (mutate (phase d x y 2) (backwardVertex 2))
    rw [backward_step d x y hd 2]
    exact ht1
  have ht3 := D3_triangles d x y hd
  have ht4 : AllTrianglesMA (D4 d x y) := by
    apply deletion_triangle_transfer _ 0 (phase_deletion d x y hd 4 (by decide) (by decide))
    change AllTrianglesMA (mutate (D4 d x y) 0)
    rw [D4_zero d x y hd]
    exact triangles_relabel _ sigma ht0
  rcases fin10 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact ht0
  · exact ht1
  · exact ht2
  · exact ht3
  · exact ht4
  · exact triangles_relabel _ sigma ht0
  · exact triangles_relabel _ sigma ht1
  · exact triangles_relabel _ sigma ht2
  · exact triangles_relabel _ sigma ht3
  · exact triangles_relabel _ sigma ht4

structure Parameters where
  d : Int
  x : Int
  y : Int

def parameterDomain (p : Parameters) : Prop := Domain p.d p.x p.y
def node (p : Parameters) (i : Fin 10) : Matrix 4 := phase p.d p.x p.y i
def child (p : Parameters) : Parameters := ⟨p.d,p.y,p.d*p.y-p.x⟩
def parent (p : Parameters) (j : Fin 2) : Matrix 4 :=
  mutate (node p (if j=0 then 0 else 1)) 1

theorem child_parameterDomain (p : Parameters) (hp : parameterDomain p) :
    parameterDomain (child p) := child_domain p.d p.x p.y hp

theorem child_parent (p : Parameters) (hp : parameterDomain p) (j : Fin 2) :
    parent (child p) j = relabel (node p (if j=0 then 0 else 1)) tau := by
  have hj : j=0 ∨ j=1 := by omega
  rcases hj with rfl|rfl
  · exact child_D0_one p.d p.x p.y hp
  · exact child_D1_one p.d p.x p.y hp

theorem node_skew (p : Parameters) (i : Fin 10) : SkewSymmetric (node p i) :=
  phase_skew p.d p.x p.y i

theorem node_cyclic (p : Parameters) (hp : parameterDomain p) (i : Fin 10) :
    ¬Acyclic (node p i) := phase_cyclic p.d p.x p.y hp i

theorem parent_skew (p : Parameters) (j : Fin 2) : SkewSymmetric (parent p j) :=
  mutation_preserves_skew _ _ (node_skew p _)

theorem parent_triangles (p : Parameters) (hp : parameterDomain p)
    (ht : ∀ j, AllTrianglesMA (parent p j)) (i : Fin 10) : AllTrianglesMA (node p i) := by
  exact phase_triangles p.d p.x p.y hp (ht 0) (ht 1) i

/-- Exact seeds of the two attached unit-zero strips. -/
def AParameters (p : Parameters) : UnitZeroStrip.Parameters :=
  ⟨p.y,h p.d p.x p.y,p.x*h p.d p.x p.y-p.y⟩
def BParameters (p : Parameters) : UnitZeroStrip.Parameters :=
  ⟨p.x,h p.d p.x p.y,p.y*h p.d p.x p.y-p.x⟩

theorem A_domain (p : Parameters) (hp : parameterDomain p) :
    UnitZeroStrip.Domain p.x (AParameters p).u (AParameters p).v (AParameters p).w :=
  (attachment_cones p.d p.x p.y hp).1

theorem B_domain (p : Parameters) (hp : parameterDomain p) :
    UnitZeroStrip.Domain p.y (BParameters p).u (BParameters p).v (BParameters p).w :=
  (attachment_cones p.d p.x p.y hp).2

end QuiverProofs.UnitPendantStrip
