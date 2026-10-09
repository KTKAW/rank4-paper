import QuiverProofs.ExtendedWeakPairs

/-! The equal-box missing-edge ray and the pendant two-missing-edge ray.
These include zero internal weights, so the positive-u,v,w cone theorem
does not apply. Mutation identities and invariant domains are proved here
directly, without extrapolation from that cone. -/
namespace QuiverProofs.MissingEdgeRays

private theorem fin4 (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega

private def rowBound (B : Matrix 4) (i : Fin 4) : Int :=
  max (max (B i 0) (B i 1)) (max (B i 2) (B i 3))
private def matrixBound (B : Matrix 4) : Int :=
  max (max (rowBound B 0) (rowBound B 1)) (max (rowBound B 2) (rowBound B 3))
private def listBound : List (Matrix 4) → Int
  | [] => 0
  | B::bs => max (matrixBound B) (listBound bs)

private theorem entry_le_matrixBound (B : Matrix 4) (i j : Fin 4) :
    B i j ≤ matrixBound B := by
  have hrow : B i j ≤ rowBound B i := by
    rcases fin4 j with rfl|rfl|rfl|rfl
    · exact Int.le_trans (Int.le_max_left _ _) (Int.le_max_left _ _)
    · exact Int.le_trans (Int.le_max_right _ _) (Int.le_max_left _ _)
    · exact Int.le_trans (Int.le_max_left _ _) (Int.le_max_right _ _)
    · exact Int.le_trans (Int.le_max_right _ _) (Int.le_max_right _ _)
  rcases fin4 i with rfl|rfl|rfl|rfl
  · exact Int.le_trans hrow (Int.le_trans (Int.le_max_left _ _) (Int.le_max_left _ _))
  · exact Int.le_trans hrow (Int.le_trans (Int.le_max_right _ _) (Int.le_max_left _ _))
  · exact Int.le_trans hrow (Int.le_trans (Int.le_max_left _ _) (Int.le_max_right _ _))
  · exact Int.le_trans hrow (Int.le_trans (Int.le_max_right _ _) (Int.le_max_right _ _))

private theorem entry_le_listBound (bs : List (Matrix 4)) (B : Matrix 4)
    (hB : B∈bs) (i j : Fin 4) : B i j ≤ listBound bs := by
  induction bs with
  | nil => simp at hB
  | cons C cs ih =>
    rcases List.mem_cons.mp hB with rfl|hB
    · have hb := entry_le_matrixBound B i j
      simp only [listBound]; omega
    · have hb := ih hB
      simp only [listBound]; omega

/-- An unbounded coordinate rules out every finite collection even after
arbitrary reindexing functions, hence after vertex permutations. -/
theorem escapes_of_unbounded_entry (f : Nat → Matrix 4) (i j : Fin 4)
    (h : ∀ bound : Int, ∃ n, bound < f n i j) (candidates : List (Matrix 4)) :
    ∃ n, ∀ B∈candidates, ∀ p : Fin 4 → Fin 4, f n ≠ (fun a b => B (p a) (p b)) := by
  obtain ⟨n,hn⟩ := h (listBound candidates)
  refine ⟨n,?_⟩
  intro B hB p heq
  have hb := entry_le_listBound candidates B hB (p i) (p j)
  have he := congrArg (fun C : Matrix 4 => C i j) heq
  dsimp only at he
  omega

structure State where
  x : Int
  y : Int
  deriving DecidableEq, Repr

namespace EqualBox

def quiver (t : Int) (s : State) : Matrix 4 := ofSix (-t) 0 s.x (-t) s.y (-s.x)
def domain (s : State) : Prop := 0<s.x ∧ 0≤s.y
def step (t : Int) (s : State) : State :=
  ⟨(t*t-1)*s.x+t*s.y,t*(t*t-2)*s.x+(t*t-1)*s.y⟩
def word : Nat → List (Fin 4)
  | 0 => []
  | n+1 => word n ++ [0,1,2]
def orbit (t : Int) (s : State) : Nat → State
  | 0 => s
  | n+1 => step t (orbit t s n)
def phaseMatrix (t : Int) (s : State) (phase : Fin 3) : Matrix 4 :=
  match phase.val with
  | 0 => quiver t s
  | 1 => ofSix t 0 (-s.x) (-t) (s.y+t*s.x) (-s.x)
  | _ => ofSix (-t) 0 ((t*t-1)*s.x+t*s.y) t (-(s.y+t*s.x))
      (t*(s.y+t*s.x)-s.x)

theorem phase_one (t : Int) (s : State) (ht : 2≤t) (hs : domain s) :
    mutate (quiver t s) 0 = phaseMatrix t s 1 := by
  obtain ⟨hx,hy⟩ := hs
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [quiver,phaseMatrix,mutate,ofSix,correction] <;> grind

theorem phase_two (t : Int) (s : State) (ht : 2≤t) (hs : domain s) :
    mutate (phaseMatrix t s 1) 1 = phaseMatrix t s 2 := by
  obtain ⟨hx,hy⟩ := hs
  have htx := Int.mul_pos (show 0<t by omega) hx
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [phaseMatrix,mutate,ofSix,correction] <;> grind

theorem step_domain_and_growth (t : Int) (s : State) (ht : 2≤t) (hs : domain s) :
    domain (step t s) ∧ 3*s.x ≤ (step t s).x := by
  obtain ⟨hx,hy⟩ := hs
  have ht2 : 4≤t*t := by
    have h := Int.mul_le_mul_of_nonneg_left ht (show 0≤t by omega)
    omega
  have hxx := Int.mul_nonneg (show 0≤t*t-4 by omega) (show 0≤s.x by omega)
  have hty := Int.mul_nonneg (show 0≤t by omega) hy
  have hyy := Int.mul_nonneg (show 0≤t*t-1 by omega) hy
  have hyx := Int.mul_nonneg
    (Int.mul_nonneg (show 0≤t by omega) (show 0≤t*t-2 by omega)) (show 0≤s.x by omega)
  dsimp [domain,step]
  grind

theorem phase_three (t : Int) (s : State) (ht : 2≤t) (hs : domain s) :
    mutate (phaseMatrix t s 2) 2 = quiver t (step t s) := by
  obtain ⟨hx,hy⟩ := hs
  have hpos : 0 < t*(s.y+t*s.x)-s.x := by
    have hg := (step_domain_and_growth t s ht ⟨hx,hy⟩).2
    dsimp [step] at hg
    grind
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [quiver,phaseMatrix,step,mutate,ofSix,correction] <;> grind

theorem block (t : Int) (s : State) (ht : 2≤t) (hs : domain s) :
    applyWord (quiver t s) [0,1,2] = quiver t (step t s) := by
  simp only [applyWord]
  rw [phase_one t s ht hs,phase_two t s ht hs,phase_three t s ht hs]

theorem orbit_domain (t : Int) (s : State) (ht : 2≤t) (hs : domain s) (n : Nat) :
    domain (orbit t s n) := by
  induction n with
  | zero => exact hs
  | succ n ih => exact (step_domain_and_growth t _ ht ih).1

theorem orbit_as_mutations (t : Int) (s : State) (ht : 2≤t) (hs : domain s) (n : Nat) :
    applyWord (quiver t s) (word n) = quiver t (orbit t s n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [word,applyWord_append,ih]
    exact block t _ ht (orbit_domain t s ht hs n)

theorem phase_as_mutations (t : Int) (s : State) (ht : 2≤t) (hs : domain s)
    (n : Nat) (phase : Fin 3) :
    applyWord (quiver t s) (word n ++ ([0,1,2] : List (Fin 4)).take phase.val) =
      phaseMatrix t (orbit t s n) phase := by
  rw [applyWord_append,orbit_as_mutations t s ht hs n]
  have hp : phase=0 ∨ phase=1 ∨ phase=2 := by omega
  rcases hp with rfl|rfl|rfl
  · rfl
  · exact phase_one t _ ht (orbit_domain t s ht hs n)
  · simpa only [List.take,applyWord] using
      (by rw [phase_one t _ ht (orbit_domain t s ht hs n),
        phase_two t _ ht (orbit_domain t s ht hs n)] :
        mutate (mutate (quiver t (orbit t s n)) 0) 1 = phaseMatrix t (orbit t s n) 2)

theorem every_phase_missing_pair (t : Int) (s : State) (phase : Fin 3) :
    phaseMatrix t s phase 0 2 = 0 := by
  have hp : phase=0 ∨ phase=1 ∨ phase=2 := by omega
  rcases hp with rfl|rfl|rfl <;> rfl

theorem every_phase_nonfork (t : Int) (s : State) (ht : 2≤t) (hs : domain s)
    (n : Nat) (phase : Fin 3) (r : Fin 4) :
    ¬ ForkDefinition.GraphFork
      (applyWord (quiver t s) (word n ++ ([0,1,2] : List (Fin 4)).take phase.val)) r := by
  rw [phase_as_mutations t s ht hs n phase]
  intro hf
  have hb := hf.2.2.1 0 2 (by decide)
  rw [every_phase_missing_pair] at hb
  contradiction

theorem orbit_x_gap (t : Int) (s : State) (ht : 2≤t) (hs : domain s) (n : Nat) :
    s.x+(n : Int) ≤ (orbit t s n).x := by
  induction n with
  | zero => simp [orbit]
  | succ n ih =>
    have hg := (step_domain_and_growth t _ ht (orbit_domain t s ht hs n)).2
    have hx := (orbit_domain t s ht hs n).1
    change s.x+((n+1 : Nat) : Int) ≤ (step t (orbit t s n)).x
    omega

theorem orbit_x_unbounded (t : Int) (s : State) (ht : 2≤t) (hs : domain s)
    (bound : Int) : ∃ n, bound < (orbit t s n).x := by
  let n := (bound-s.x+1).toNat
  have hcast := Int.self_le_toNat (bound-s.x+1)
  have hgap := orbit_x_gap t s ht hs n
  exact ⟨n,by dsimp [n] at *; omega⟩

theorem escapes_finite_nonfork_core (t : Int) (s : State) (ht : 2≤t) (hs : domain s)
    (candidates : List (Matrix 4)) :
    ∃ n, (∀ B∈candidates, ∀ p : Relabeling 4,
      applyWord (quiver t s) (word n) ≠ relabel B p) ∧
      (∀ r, ¬ ForkDefinition.GraphFork (applyWord (quiver t s) (word n)) r) := by
  obtain ⟨n,hn⟩ := escapes_of_unbounded_entry (fun n => applyWord (quiver t s) (word n)) 0 3
    (by intro bound; obtain ⟨n,hn⟩ := orbit_x_unbounded t s ht hs bound
        exact ⟨n,by dsimp only; rw [orbit_as_mutations t s ht hs n]; exact hn⟩) candidates
  refine ⟨n,fun B hB p => hn B hB p.toFun,?_⟩
  intro r
  simpa only [List.take,List.append_nil] using every_phase_nonfork t s ht hs n 0 r

theorem printed_equal_box_initial (t : Int) :
    quiver t ⟨t,0⟩ = ofSix (-t) 0 t (-t) 0 (-t) := rfl

theorem boundary_t_one_leaves_domain : step 1 ⟨1,0⟩ = ⟨0,-1⟩ := by decide

end EqualBox

namespace Pendant

def quiver (c d : Int) (s : State) : Matrix 4 := ofSix 0 0 c d (-s.x) s.y
def domain (s : State) : Prop := 0<s.x ∧ s.x≤s.y
def step (d : Int) (s : State) : State :=
  ⟨d*s.y-s.x,(d*d-1)*s.y-d*s.x⟩
def word : Nat → List (Fin 4)
  | 0 => []
  | n+1 => word n ++ [2,1]
def orbit (d : Int) (s : State) : Nat → State
  | 0 => s
  | n+1 => step d (orbit d s n)
def phaseMatrix (c d : Int) (s : State) (phase : Fin 2) : Matrix 4 :=
  if phase=0 then quiver c d s else ofSix 0 0 c (-d) (d*s.y-s.x) (-s.y)

theorem step_domain_and_growth (d : Int) (s : State) (hd : 3≤d) (hs : domain s) :
    domain (step d s) ∧ 5*s.y ≤ (step d s).y := by
  obtain ⟨hx,hxy⟩ := hs
  have hy : 0<s.y := by omega
  have hd2 : 5≤d*d-d-1 := by
    have h := Int.mul_le_mul_of_nonneg_left (show 2≤d-1 by omega) (show 0≤d by omega)
    grind
  have hdx := Int.mul_nonneg (show 0≤d by omega) (show 0≤s.y-s.x by omega)
  have hdy := Int.mul_nonneg (show 0≤d-3 by omega) (show 0≤s.y by omega)
  have hyy := Int.mul_nonneg (show 0≤d*d-d-6 by omega) (show 0≤s.y by omega)
  have hdiff := Int.mul_nonneg
    (Int.mul_nonneg (show 0≤d by omega) (show 0≤d-2 by omega)) (show 0≤s.y by omega)
  have hdxy := Int.mul_nonneg (show 0≤d-1 by omega) (show 0≤s.y-s.x by omega)
  dsimp [domain,step]
  grind

theorem phase_one (c d : Int) (s : State) (hd : 3≤d) (hs : domain s) :
    mutate (quiver c d s) 2 = phaseMatrix c d s 1 := by
  obtain ⟨hx,hxy⟩ := hs
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [quiver,phaseMatrix,mutate,ofSix,correction] <;> grind

theorem phase_two (c d : Int) (s : State) (hd : 3≤d) (hs : domain s) :
    mutate (phaseMatrix c d s 1) 1 = quiver c d (step d s) := by
  have hx := (step_domain_and_growth d s hd hs).1.1
  dsimp [step] at hx
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [quiver,phaseMatrix,step,mutate,ofSix,correction] <;> grind

theorem block (c d : Int) (s : State) (hd : 3≤d) (hs : domain s) :
    applyWord (quiver c d s) [2,1] = quiver c d (step d s) := by
  simp only [applyWord]
  rw [phase_one c d s hd hs,phase_two c d s hd hs]

theorem orbit_domain (d : Int) (s : State) (hd : 3≤d) (hs : domain s) (n : Nat) :
    domain (orbit d s n) := by
  induction n with
  | zero => exact hs
  | succ n ih => exact (step_domain_and_growth d _ hd ih).1

theorem orbit_as_mutations (c d : Int) (s : State) (hd : 3≤d) (hs : domain s) (n : Nat) :
    applyWord (quiver c d s) (word n) = quiver c d (orbit d s n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [word,applyWord_append,ih]
    exact block c d _ hd (orbit_domain d s hd hs n)

theorem phase_as_mutations (c d : Int) (s : State) (hd : 3≤d) (hs : domain s)
    (n : Nat) (phase : Fin 2) :
    applyWord (quiver c d s) (word n ++ ([2,1] : List (Fin 4)).take phase.val) =
      phaseMatrix c d (orbit d s n) phase := by
  rw [applyWord_append,orbit_as_mutations c d s hd hs n]
  have hp : phase=0 ∨ phase=1 := by omega
  rcases hp with rfl|rfl
  · rfl
  · exact phase_one c d _ hd (orbit_domain d s hd hs n)

theorem phase_two_weak_pairs (c d : Int) (s : State) (phase : Fin 2) :
    ExtendedWeakPairs.TwoWeakPairs (phaseMatrix c d s phase) := by
  have hp : phase=0 ∨ phase=1 := by omega
  rcases hp with rfl|rfl <;>
    exact ⟨0,1,0,2,by simp [ExtendedWeakPairs.Weak,phaseMatrix,quiver,ofSix],
      by simp [ExtendedWeakPairs.Weak,phaseMatrix,quiver,ofSix],
      by simp [ExtendedWeakPairs.SamePair]⟩

theorem phase_cyclic (c d : Int) (s : State) (hd : 3≤d) (hs : domain s)
    (phase : Fin 2) : ¬ Acyclic (phaseMatrix c d s phase) := by
  obtain ⟨hx,hxy⟩ := hs
  have hp : phase=0 ∨ phase=1 := by omega
  rcases hp with rfl|rfl
  · rintro ⟨rank,hr⟩
    have h12 := hr 1 2 (by simp [phaseMatrix,quiver,ofSix]; omega)
    have h23 := hr 2 3 (by simp [phaseMatrix,quiver,ofSix]; omega)
    have h31 := hr 3 1 (by simp [phaseMatrix,quiver,ofSix]; omega)
    omega
  · have hx' := (step_domain_and_growth d s hd ⟨hx,hxy⟩).1.1
    dsimp [step] at hx'
    rintro ⟨rank,hr⟩
    have h21 := hr 2 1 (by simp [phaseMatrix,ofSix]; omega)
    have h13 := hr 1 3 (by simp [phaseMatrix,ofSix]; omega)
    have h32 := hr 3 2 (by simp [phaseMatrix,ofSix]; omega)
    omega

theorem orbit_y_gap (d : Int) (s : State) (hd : 3≤d) (hs : domain s) (n : Nat) :
    s.y+(n : Int) ≤ (orbit d s n).y := by
  induction n with
  | zero => simp [orbit]
  | succ n ih =>
    have hg := (step_domain_and_growth d _ hd (orbit_domain d s hd hs n)).2
    have hx := (orbit_domain d s hd hs n).1
    have hxy := (orbit_domain d s hd hs n).2
    change s.y+((n+1 : Nat) : Int) ≤ (step d (orbit d s n)).y
    omega

theorem orbit_y_unbounded (d : Int) (s : State) (hd : 3≤d) (hs : domain s)
    (bound : Int) : ∃ n, bound < (orbit d s n).y := by
  let n := (bound-s.y+1).toNat
  have hcast := Int.self_le_toNat (bound-s.y+1)
  have hgap := orbit_y_gap d s hd hs n
  exact ⟨n,by dsimp [n] at *; omega⟩

theorem escapes_finite_core_and_exterior (c d : Int) (s : State)
    (hd : 3≤d) (hs : domain s) (candidates : List (Matrix 4)) :
    ∃ n, (∀ B∈candidates, ∀ p : Relabeling 4,
      applyWord (quiver c d s) (word n) ≠ relabel B p) ∧
      ¬ ExtendedWeakPairs.Exterior (applyWord (quiver c d s) (word n)) := by
  obtain ⟨n,hn⟩ := escapes_of_unbounded_entry (fun n => applyWord (quiver c d s) (word n)) 2 3
    (by intro bound; obtain ⟨n,hn⟩ := orbit_y_unbounded d s hd hs bound
        exact ⟨n,by dsimp only; rw [orbit_as_mutations c d s hd hs n]; exact hn⟩) candidates
  refine ⟨n,fun B hB p => hn B hB p.toFun,?_⟩
  apply ExtendedWeakPairs.two_not_exterior
  rw [orbit_as_mutations c d s hd hs n]
  exact phase_two_weak_pairs c d _ 0

theorem no_finite_core_exterior_cover (c d : Int) (s : State)
    (hd : 3≤d) (hs : domain s) :
    ¬ ExtendedWeakPairs.FiniteCoreExteriorCover (quiver c d s) := by
  rintro ⟨candidates,hcover⟩
  obtain ⟨n,hfinite,hext⟩ := escapes_finite_core_and_exterior c d s hd hs candidates
  rcases hcover (word n) with ⟨B,hB,p,hp⟩ | he
  · exact hfinite B hB p hp
  · exact hext he

theorem printed_qs_no_finite_core_exterior_cover (s : Int) (hs : 2≤s) :
    ¬ ExtendedWeakPairs.FiniteCoreExteriorCover
      (ofSix 0 0 (s*s+s+1) (s*s+1) (-1) 1) := by
  have hsq := Int.mul_le_mul_of_nonneg_left hs (show 0≤s by omega)
  exact no_finite_core_exterior_cover (s*s+s+1) (s*s+1) ⟨1,1⟩
    (by omega) (by unfold domain; decide)

theorem boundary_d_two_does_not_grow : step 2 ⟨1,1⟩ = ⟨1,1⟩ := by decide

end Pendant

end QuiverProofs.MissingEdgeRays
