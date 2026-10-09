import QuiverProofs.Mutation

/-!
Arithmetic portion of `sequel_research/technical_note.tex`, Proposition
`prop:cone`. The recurrence and its invariant cone are proved over integers.
The three mutation phases are identified with the recurrence. The graph
definition of a fork and the mutation-graph distance corollary are not proved.
-/

namespace QuiverProofs.Cone

def nextA (u v w A H Z : Int) : Int :=
  (u*u + v*v + u*v*w - 1)*A + (u + v*w)*H - v*Z

def nextH (u v w A H Z : Int) : Int :=
  (w*v + u*w*w - u)*A + (w*w - 1)*H - w*Z

def nextZ (u v w A H Z : Int) : Int :=
  (v + u*w)*A + w*H - Z

def InCone (v A H Z : Int) : Prop :=
  0 < A ∧ 0 ≤ H ∧ 0 < Z ∧ Z ≤ v*A

def growth (u v w : Int) : Int := u*u + u*v*w - 1

private theorem fin_cases (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega

theorem mutation_phase_one (u v w A H Z : Int)
    (hu : 1 ≤ u) (hv : 1 ≤ v) (hA : 0 < A) :
    mutate (ofSix (-u) (-v) A (-w) H (-Z)) 0 =
      ofSix u v (-A) (-w) (H+u*A) (v*A-Z) := by
  funext i j
  rcases fin_cases i with rfl | rfl | rfl | rfl <;>
    rcases fin_cases j with rfl | rfl | rfl | rfl <;>
    simp [mutate, ofSix, correction] <;> grind

theorem mutation_phase_two (u v w A H Z : Int)
    (hu : 1 ≤ u) (hw : 1 ≤ w) (hA : 0 < A) (hH : 0 ≤ H) :
    mutate (ofSix u v (-A) (-w) (H+u*A) (v*A-Z)) 1 =
      ofSix (-u) v ((u*u-1)*A+u*H) w (-(H+u*A))
        ((v+u*w)*A+w*H-Z) := by
  have hp : 0 < u*A := Int.mul_pos (by omega) hA
  have hX : 0 ≤ H+u*A := by omega
  funext i j
  rcases fin_cases i with rfl | rfl | rfl | rfl <;>
    rcases fin_cases j with rfl | rfl | rfl | rfl <;>
    simp [mutate, ofSix, correction] <;> grind

theorem mutation_phase_three (u v w A H Z : Int)
    (hv : 1 ≤ v) (hw : 1 ≤ w)
    (hL : 0 < (v+u*w)*A+w*H-Z) :
    mutate (ofSix (-u) v ((u*u-1)*A+u*H) w (-(H+u*A))
        ((v+u*w)*A+w*H-Z)) 2 =
      ofSix (-u) (-v) (nextA u v w A H Z) (-w)
        (nextH u v w A H Z) (-(nextZ u v w A H Z)) := by
  funext i j
  rcases fin_cases i with rfl | rfl | rfl | rfl <;>
    rcases fin_cases j with rfl | rfl | rfl | rfl <;>
    simp [mutate, ofSix, correction, nextA, nextH, nextZ] <;> grind

theorem nextA_remainder (u v w A H Z : Int) :
    nextA u v w A H Z =
      growth u v w*A + (u + v*w)*H + v*(v*A-Z) := by
  unfold nextA growth
  grind

theorem nextH_remainder (u v w A H Z : Int) :
    nextH u v w A H Z =
      (w*w-1)*(u*A+H) + w*(v*A-Z) := by
  unfold nextH
  grind

theorem nextZ_remainder (u v w A H Z : Int) :
    nextZ u v w A H Z = u*w*A + w*H + (v*A-Z) := by
  unfold nextZ
  grind

theorem upper_remainder (u v w A H Z : Int) :
    v*nextA u v w A H Z - nextZ u v w A H Z =
      (v*(u*u-1) + u*w*(v*v-1))*A +
      (v*u + w*(v*v-1))*H + (v*v-1)*(v*A-Z) := by
  unfold nextA nextZ
  grind

private theorem square_ge_one (u : Int) (hu : 1 ≤ u) : 1 ≤ u*u := by
  have hp : 0 < u*u := Int.mul_pos (by omega) (by omega)
  omega

theorem growth_positive (u v w : Int) (hu : 1 ≤ u)
    (hv : 1 ≤ v) (hw : 1 ≤ w) : 1 ≤ growth u v w := by
  have hs := square_ge_one u hu
  have hp : 0 < u*v*w :=
    Int.mul_pos (Int.mul_pos (by omega) (by omega)) (by omega)
  unfold growth
  omega

theorem nextA_lower_bound (u v w A H Z : Int)
    (hu : 1 ≤ u) (hv : 1 ≤ v) (hw : 1 ≤ w)
    (hc : InCone v A H Z) :
    growth u v w*A ≤ nextA u v w A H Z := by
  obtain ⟨hA, hH, hZ, hZA⟩ := hc
  have hvw : 0 ≤ v*w := Int.mul_nonneg (by omega) (by omega)
  have h1 : 0 ≤ (u+v*w)*H := Int.mul_nonneg (by omega) hH
  have h2 : 0 ≤ v*(v*A-Z) := Int.mul_nonneg (by omega) (by omega)
  rw [nextA_remainder]
  omega

theorem preserves_cone (u v w A H Z : Int)
    (hu : 1 ≤ u) (hv : 1 ≤ v) (hw : 1 ≤ w)
    (hc : InCone v A H Z) :
    InCone v (nextA u v w A H Z) (nextH u v w A H Z)
      (nextZ u v w A H Z) := by
  have hlower := nextA_lower_bound u v w A H Z hu hv hw hc
  obtain ⟨hA, hH, hZ, hZA⟩ := hc
  have hu0 : 0 ≤ u := by omega
  have hv0 : 0 ≤ v := by omega
  have hw0 : 0 ≤ w := by omega
  have hA0 : 0 ≤ A := by omega
  have hR : 0 ≤ v*A-Z := by omega
  have hu2 : 0 ≤ u*u-1 := by have := square_ge_one u hu; omega
  have hv2 : 0 ≤ v*v-1 := by have := square_ge_one v hv; omega
  have hw2 : 0 ≤ w*w-1 := by have := square_ge_one w hw; omega
  have huw : 0 ≤ u*w := Int.mul_nonneg hu0 hw0
  have huA : 0 ≤ u*A := Int.mul_nonneg hu0 hA0
  have hfirst : 0 < growth u v w*A :=
    Int.mul_pos (by have := growth_positive u v w hu hv hw; omega) hA
  have hA' : 0 < nextA u v w A H Z := by omega
  have hH1 : 0 ≤ (w*w-1)*(u*A+H) := Int.mul_nonneg hw2 (by omega)
  have hH2 : 0 ≤ w*(v*A-Z) := Int.mul_nonneg hw0 hR
  have hH' : 0 ≤ nextH u v w A H Z := by rw [nextH_remainder]; omega
  have hZ1 : 0 < u*w*A :=
    Int.mul_pos (Int.mul_pos (by omega) (by omega)) hA
  have hZ2 : 0 ≤ w*H := Int.mul_nonneg hw0 hH
  have hZ' : 0 < nextZ u v w A H Z := by rw [nextZ_remainder]; omega
  have hc1 : 0 ≤ v*(u*u-1) := Int.mul_nonneg hv0 hu2
  have hc2 : 0 ≤ u*w*(v*v-1) := Int.mul_nonneg huw hv2
  have hc3 : 0 ≤ v*u := Int.mul_nonneg hv0 hu0
  have hc4 : 0 ≤ w*(v*v-1) := Int.mul_nonneg hw0 hv2
  have hU1 : 0 ≤ (v*(u*u-1)+u*w*(v*v-1))*A :=
    Int.mul_nonneg (by omega) hA0
  have hU2 : 0 ≤ (v*u+w*(v*v-1))*H := Int.mul_nonneg (by omega) hH
  have hU3 : 0 ≤ (v*v-1)*(v*A-Z) := Int.mul_nonneg hv2 hR
  have hU : 0 ≤ v*nextA u v w A H Z - nextZ u v w A H Z := by
    rw [upper_remainder]
    omega
  exact ⟨hA', hH', hZ', by omega⟩

/-- The invariant-cone recurrence is exactly the chronological mutation word
    (0,1,2), including the boundary Z=v*A. -/
theorem cone_word (u v w A H Z : Int)
    (hu : 1 ≤ u) (hv : 1 ≤ v) (hw : 1 ≤ w)
    (hc : InCone v A H Z) :
    applyWord (ofSix (-u) (-v) A (-w) H (-Z)) [0,1,2] =
      ofSix (-u) (-v) (nextA u v w A H Z) (-w)
        (nextH u v w A H Z) (-(nextZ u v w A H Z)) := by
  have hL : 0 < (v+u*w)*A+w*H-Z :=
    (preserves_cone u v w A H Z hu hv hw hc).2.2.1
  simp only [applyWord, mutation_phase_one u v w A H Z hu hv hc.1,
    mutation_phase_two u v w A H Z hu hw hc.1 hc.2.1,
    mutation_phase_three u v w A H Z hv hw hL]

theorem doubles_A (u v w A H Z : Int)
    (hu : 1 ≤ u) (hv : 1 ≤ v) (hw : 1 ≤ w)
    (hc : InCone v A H Z) (hg : 2 ≤ growth u v w) :
    2*A ≤ nextA u v w A H Z := by
  have hlower := nextA_lower_bound u v w A H Z hu hv hw hc
  have hA : 0 ≤ A := by have := hc.1; omega
  have hp : 0 ≤ (growth u v w-2)*A := Int.mul_nonneg (by omega) hA
  grind

theorem strictly_grows_A (u v w A H Z : Int)
    (hu : 1 ≤ u) (hv : 1 ≤ v) (hw : 1 ≤ w)
    (hc : InCone v A H Z) (hg : 2 ≤ growth u v w) :
    A < nextA u v w A H Z := by
  have := doubles_A u v w A H Z hu hv hw hc hg
  have := hc.1
  omega

structure State where
  A : Int
  H : Int
  Z : Int
  deriving DecidableEq, Repr

def step (u v w : Int) (s : State) : State :=
  ⟨nextA u v w s.A s.H s.Z, nextH u v w s.A s.H s.Z,
    nextZ u v w s.A s.H s.Z⟩

def orbit (u v w : Int) (s : State) : Nat → State
  | 0 => s
  | n+1 => step u v w (orbit u v w s n)

def quiver (u v w : Int) (s : State) : Matrix 4 :=
  ofSix (-u) (-v) s.A (-w) s.H (-s.Z)

def repeatedWord : Nat → List (Fin 4)
  | 0 => []
  | n+1 => repeatedWord n ++ [0,1,2]

theorem orbit_in_cone (u v w : Int) (s : State)
    (hu : 1 ≤ u) (hv : 1 ≤ v) (hw : 1 ≤ w)
    (hc : InCone v s.A s.H s.Z) (n : Nat) :
    InCone v (orbit u v w s n).A (orbit u v w s n).H
      (orbit u v w s n).Z := by
  induction n with
  | zero => exact hc
  | succ n ih =>
    exact preserves_cone u v w _ _ _ hu hv hw ih

theorem orbit_as_mutations (u v w : Int) (s : State)
    (hu : 1 ≤ u) (hv : 1 ≤ v) (hw : 1 ≤ w)
    (hc : InCone v s.A s.H s.Z) (n : Nat) :
    applyWord (quiver u v w s) (repeatedWord n) =
      quiver u v w (orbit u v w s n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [repeatedWord, applyWord_append, ih]
    exact cone_word u v w _ _ _ hu hv hw
      (orbit_in_cone u v w s hu hv hw hc n)

theorem orbit_A_step (u v w : Int) (s : State)
    (hu : 1 ≤ u) (hv : 1 ≤ v) (hw : 1 ≤ w)
    (hc : InCone v s.A s.H s.Z) (hg : 2 ≤ growth u v w)
    (n : Nat) : (orbit u v w s n).A < (orbit u v w s (n+1)).A := by
  exact strictly_grows_A u v w _ _ _ hu hv hw
    (orbit_in_cone u v w s hu hv hw hc n) hg

theorem orbit_A_gap (u v w : Int) (s : State)
    (hu : 1 ≤ u) (hv : 1 ≤ v) (hw : 1 ≤ w)
    (hc : InCone v s.A s.H s.Z) (hg : 2 ≤ growth u v w)
    (m n : Nat) :
    (orbit u v w s m).A + (n : Int) ≤ (orbit u v w s (m+n)).A := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep := orbit_A_step u v w s hu hv hw hc hg (m+n)
    have heq : m + (n+1) = (m+n)+1 := by omega
    rw [heq]
    omega

theorem orbit_A_unbounded (u v w : Int) (s : State)
    (hu : 1 ≤ u) (hv : 1 ≤ v) (hw : 1 ≤ w)
    (hc : InCone v s.A s.H s.Z) (hg : 2 ≤ growth u v w)
    (bound : Int) : ∃ n : Nat, bound < (orbit u v w s n).A := by
  let n := (bound-s.A+1).toNat
  have hcast := Int.self_le_toNat (bound-s.A+1)
  have hgap := orbit_A_gap u v w s hu hv hw hc hg 0 n
  simp only [orbit, Nat.zero_add] at hgap
  exact ⟨n, by dsimp [n] at *; omega⟩

theorem orbit_A_strictly_increasing (u v w : Int) (s : State)
    (hu : 1 ≤ u) (hv : 1 ≤ v) (hw : 1 ≤ w)
    (hc : InCone v s.A s.H s.Z) (hg : 2 ≤ growth u v w)
    (m n : Nat) (hmn : m < n) :
    (orbit u v w s m).A < (orbit u v w s n).A := by
  have hgap := orbit_A_gap u v w s hu hv hw hc hg m (n-m)
  have heq : m+(n-m) = n := by omega
  rw [heq] at hgap
  omega

/-- Distinct indices produce distinct integer states, for arbitrarily many
    iterations. This is a statement about the recurrence, not yet about
    isomorphism classes of quivers. -/
theorem orbit_injective (u v w : Int) (s : State)
    (hu : 1 ≤ u) (hv : 1 ≤ v) (hw : 1 ≤ w)
    (hc : InCone v s.A s.H s.Z) (hg : 2 ≤ growth u v w)
    (m n : Nat) (heq : orbit u v w s m = orbit u v w s n) : m = n := by
  have hA : (orbit u v w s m).A = (orbit u v w s n).A := congrArg State.A heq
  by_cases hmn : m < n
  · have := orbit_A_strictly_increasing u v w s hu hv hw hc hg m n hmn
    omega
  · by_cases hnm : n < m
    · have := orbit_A_strictly_increasing u v w s hu hv hw hc hg n m hnm
      omega
    · omega

/-- Different iterates are distinct labeled quivers reachable from the same
    input. Isomorphism-class and graph-distance conclusions are separate. -/
theorem mutation_orbit_injective (u v w : Int) (s : State)
    (hu : 1 ≤ u) (hv : 1 ≤ v) (hw : 1 ≤ w)
    (hc : InCone v s.A s.H s.Z) (hg : 2 ≤ growth u v w)
    (m n : Nat)
    (heq : applyWord (quiver u v w s) (repeatedWord m) =
      applyWord (quiver u v w s) (repeatedWord n)) : m = n := by
  rw [orbit_as_mutations u v w s hu hv hw hc m,
    orbit_as_mutations u v w s hu hv hw hc n] at heq
  have hA : (orbit u v w s m).A = (orbit u v w s n).A :=
    congrArg (fun B : Matrix 4 => B 0 3) heq
  by_cases hmn : m < n
  · have := orbit_A_strictly_increasing u v w s hu hv hw hc hg m n hmn
    omega
  · by_cases hnm : n < m
    · have := orbit_A_strictly_increasing u v w s hu hv hw hc hg n m hnm
      omega
    · omega

private def rowBound (B : Matrix 4) (i : Fin 4) : Int :=
  max (max (B i 0) (B i 1)) (max (B i 2) (B i 3))

private def matrixBound (B : Matrix 4) : Int :=
  max (max (rowBound B 0) (rowBound B 1))
    (max (rowBound B 2) (rowBound B 3))

private theorem entry_le_matrixBound (B : Matrix 4) (i j : Fin 4) :
    B i j ≤ matrixBound B := by
  have hrow : B i j ≤ rowBound B i := by
    rcases fin_cases j with rfl | rfl | rfl | rfl
    · exact Int.le_trans (Int.le_max_left _ _) (Int.le_max_left _ _)
    · exact Int.le_trans (Int.le_max_right _ _) (Int.le_max_left _ _)
    · exact Int.le_trans (Int.le_max_left _ _) (Int.le_max_right _ _)
    · exact Int.le_trans (Int.le_max_right _ _) (Int.le_max_right _ _)
  rcases fin_cases i with rfl | rfl | rfl | rfl
  · exact Int.le_trans hrow (Int.le_trans (Int.le_max_left _ _) (Int.le_max_left _ _))
  · exact Int.le_trans hrow (Int.le_trans (Int.le_max_right _ _) (Int.le_max_left _ _))
  · exact Int.le_trans hrow (Int.le_trans (Int.le_max_left _ _) (Int.le_max_right _ _))
  · exact Int.le_trans hrow (Int.le_trans (Int.le_max_right _ _) (Int.le_max_right _ _))

private def listBound : List (Matrix 4) → Int
  | [] => 0
  | B :: bs => max (matrixBound B) (listBound bs)

private theorem entry_le_listBound (bs : List (Matrix 4)) (B : Matrix 4)
    (hB : B ∈ bs) (i j : Fin 4) : B i j ≤ listBound bs := by
  induction bs with
  | nil => simp at hB
  | cons C cs ih =>
    simp only [List.mem_cons] at hB
    rcases hB with rfl | hB
    · have := entry_le_matrixBound B i j
      simp only [listBound]
      omega
    · have := ih hB
      simp only [listBound]
      omega

/-- No finite list of matrices covers this mutation orbit up to relabeling.
    We even rule out every reindexing function, so in particular every vertex
    permutation. This states infinitude of the isomorphism classes without
    relying on a separate quotient implementation. -/
theorem mutation_orbit_escapes_finite_relabelings (u v w : Int) (s : State)
    (hu : 1 ≤ u) (hv : 1 ≤ v) (hw : 1 ≤ w)
    (hc : InCone v s.A s.H s.Z) (hg : 2 ≤ growth u v w)
    (candidates : List (Matrix 4)) :
    ∃ n : Nat, ∀ B ∈ candidates, ∀ p : Fin 4 → Fin 4,
      applyWord (quiver u v w s) (repeatedWord n) ≠
        (fun i j => B (p i) (p j)) := by
  obtain ⟨n, hn⟩ := orbit_A_unbounded u v w s hu hv hw hc hg (listBound candidates)
  refine ⟨n, ?_⟩
  intro B hB p heq
  have hbound := entry_le_listBound candidates B hB (p 0) (p 3)
  rw [orbit_as_mutations u v w s hu hv hw hc n] at heq
  have hentry : (orbit u v w s n).A = B (p 0) (p 3) :=
    congrArg (fun C : Matrix 4 => C 0 3) heq
  omega

theorem mutation_orbit_unit_edge (u v w : Int) (s : State)
    (hu : 1 ≤ u) (hv : 1 ≤ v) (hw : 1 ≤ w)
    (hc : InCone v s.A s.H s.Z) (hunit : u=1 ∨ v=1 ∨ w=1)
    (n : Nat) :
    ∃ i j : Fin 4, i ≠ j ∧
      applyWord (quiver u v w s) (repeatedWord n) i j = -1 := by
  rw [orbit_as_mutations u v w s hu hv hw hc n]
  rcases hunit with rfl | rfl | rfl
  · exact ⟨0, 1, by decide, rfl⟩
  · exact ⟨0, 2, by decide, rfl⟩
  · exact ⟨1, 2, by decide, rfl⟩

def Abundant (B : Matrix 4) : Prop :=
  ∀ i j, i ≠ j → 2 ≤ (B i j).natAbs

/-- Forks must be abundant; this proves the required obstruction without
    importing or postulating the rest of the definition of a fork. -/
theorem mutation_orbit_not_abundant (u v w : Int) (s : State)
    (hu : 1 ≤ u) (hv : 1 ≤ v) (hw : 1 ≤ w)
    (hc : InCone v s.A s.H s.Z) (hunit : u=1 ∨ v=1 ∨ w=1)
    (n : Nat) :
    ¬ Abundant (applyWord (quiver u v w s) (repeatedWord n)) := by
  obtain ⟨i,j,hij,hentry⟩ := mutation_orbit_unit_edge u v w s hu hv hw hc hunit n
  intro h
  have hweight := h i j hij
  rw [hentry] at hweight
  contradiction

/-- The four cone-entry states and stated growth factors in `tab:cone`.
    Mutation words leading to these entries are a separate obligation. -/
theorem printed_entries :
    InCone 2 1 2 2 ∧ growth 2 2 1 = 7 ∧
    InCone 1 37 5 18 ∧ growth 2 1 1 = 5 ∧
    InCone 2 1 2 2 ∧ growth 1 2 1 = 2 ∧
    InCone 1 10 9 6 ∧ growth 2 1 2 = 7 := by
  unfold InCone growth
  decide

theorem E2_enters_cone :
    applyWord (ofSix (-2) (-1) 1 (-1) 1 (-2)) [0,1,2,0,1,2] =
      quiver 2 1 1 ⟨37,5,18⟩ := by
  funext i j
  rcases fin_cases i with rfl | rfl | rfl | rfl <;>
    rcases fin_cases j with rfl | rfl | rfl | rfl <;> decide

theorem E4_enters_cone :
    applyWord (ofSix (-2) (-1) 2 (-2) (-1) (-2)) [0,1,2] =
      quiver 2 1 2 ⟨10,9,6⟩ := by
  funext i j
  rcases fin_cases i with rfl | rfl | rfl | rfl <;>
    rcases fin_cases j with rfl | rfl | rfl | rfl <;> decide

def swap12 (i : Fin 4) : Fin 4 :=
  if i=1 then 2 else if i=2 then 1 else i

theorem swap12_involutive (i : Fin 4) : swap12 (swap12 i) = i := by
  rcases fin_cases i with rfl | rfl | rfl | rfl <;> decide

/-- The printed E3 is put into the cone coordinates by swapping labels 1,2. -/
theorem E3_relabels_into_cone :
    (fun i j => ofSix (-2) (-1) 1 1 (-2) 2 (swap12 i) (swap12 j)) =
      quiver 1 2 1 ⟨1,2,2⟩ := by
  funext i j
  rcases fin_cases i with rfl | rfl | rfl | rfl <;>
    rcases fin_cases j with rfl | rfl | rfl | rfl <;> decide

theorem E1_already_in_cone :
    ofSix (-2) (-2) 1 (-1) 2 (-2) = quiver 2 2 1 ⟨1,2,2⟩ := rfl

end QuiverProofs.Cone
