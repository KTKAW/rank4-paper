import QuiverProofs.Cone
import QuiverProofs.ClassSeparation
import QuiverProofs.Regions

/-! Symbolic components of the generic multiplicity strip.  The domain is
exactly `2 ≤ m < b < c < a`; no assertion about the three base returns, NMA,
or global triangle avoidance is inferred from the forward recurrence. -/
namespace QuiverProofs.GenericStrip

def Domain (m a b c : Int) : Prop := 2 ≤ m ∧ m < b ∧ b < c ∧ c < a
def nextA (m a b c : Int) : Int := m*(m+1)*a+(m+1)*b-m*c
def nextB (m a c : Int) : Int := m*a-c
def nextC (m a b c : Int) : Int := (m+1)*a+b-c
def root (m a b c : Int) : Matrix 4 := ofSix (-1) (-m) a (-1) b (-c)
def phaseP (m a b c : Int) : Matrix 4 :=
  ofSix 1 m (-a) (-1) (a+b) (nextB m a c)
def phaseQ (m a b c : Int) : Matrix 4 :=
  ofSix (-1) m b 1 (-a-b) (nextC m a b c)
def phaseS (m a b c : Int) : Matrix 4 :=
  ofSix (m+1) (-m) (m*nextB m a c-a) 1 (a+b) (-nextB m a c)
def phaseT (m a b c : Int) : Matrix 4 :=
  ofSix (-m-1) 1 (nextA m a b c) (-1) (-a-b) (-nextB m a c)
def phaseV (m a b c : Int) : Matrix 4 :=
  ofSix (m+1) (-1) (-nextA m a b c) m
    ((m+1)*nextA m a b c-a-b) (-nextB m a c)

theorem next_identities (m a b c : Int) :
    nextC m a b c = nextB m a c+a+b ∧
    nextA m a b c = m*nextC m a b c+b := by
  simp only [nextA,nextB,nextC]; constructor <;> grind

theorem preserves_domain (m a b c : Int) (h : Domain m a b c) :
    Domain m (nextA m a b c) (nextB m a c) (nextC m a b c) := by
  obtain ⟨hm,hmb,hbc,hca⟩ := h
  have hma := Int.mul_le_mul_of_nonneg_right hm (show 0 ≤ a by omega)
  have hB : a < nextB m a c := by unfold nextB; omega
  have ids := next_identities m a b c
  have hC : nextB m a c < nextC m a b c := by omega
  have hmC := Int.mul_le_mul_of_nonneg_right hm
    (show 0 ≤ nextC m a b c by omega)
  unfold Domain; omega

theorem growth (m a b c : Int) (h : Domain m a b c) :
    4*a < nextA m a b c := by
  obtain ⟨hm,hmb,hbc,hca⟩ := h
  have hsq : 0 ≤ m*m-4 := by
    have hmul := Int.mul_le_mul_of_nonneg_right hm (show 0 ≤ m by omega)
    omega
  have hp := Int.mul_nonneg hsq (show 0 ≤ a by omega)
  have hq := Int.mul_pos (show 0 < m by omega) (show 0 < a-c by omega)
  have hr := Int.mul_pos (show 0 < m+1 by omega) (show 0 < b by omega)
  unfold nextA; grind

theorem parameter_bounds (m a b c : Int) (h : Domain m a b c) :
    0 < a ∧ 0 < b ∧ 0 < c ∧ a < nextB m a c ∧
    a < m*nextB m a c-a ∧ 0 < (m+1)*nextA m a b c-a-b := by
  have hg := growth m a b c h
  obtain ⟨hm,hmb,hbc,hca⟩ := h
  have hma := Int.mul_le_mul_of_nonneg_right hm (show 0 ≤ a by omega)
  have hB : a < nextB m a c := by unfold nextB; omega
  have hmB := Int.mul_le_mul_of_nonneg_right hm
    (show 0 ≤ nextB m a c by omega)
  have hmA := Int.mul_le_mul_of_nonneg_right (show 1 ≤ m+1 by omega)
    (show 0 ≤ nextA m a b c by omega)
  omega

theorem inverse_step (m a b c : Int) :
    (m+1)*nextC m a b c-nextB m a c-nextA m a b c = a ∧
    nextA m a b c-m*nextC m a b c = b ∧
    m*(m+1)*nextC m a b c-(m+1)*nextB m a c-m*nextA m a b c = c := by
  simp only [nextA,nextB,nextC]; constructor
  · grind
  constructor <;> grind

private theorem fin4 (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega

theorem root_zero (m a b c : Int) (h : Domain m a b c) :
    mutate (root m a b c) 0 = phaseP m a b c := by
  have hp := parameter_bounds m a b c h
  obtain ⟨hm,hmb,hbc,hca⟩ := h
  simp only [nextA,nextB,nextC] at *
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;>
    rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [mutate,correction,ofSix,root,phaseP,nextB] <;> grind

theorem P_one (m a b c : Int) (h : Domain m a b c) :
    mutate (phaseP m a b c) 1 = phaseQ m a b c := by
  have hp := parameter_bounds m a b c h
  obtain ⟨hm,hmb,hbc,hca⟩ := h
  simp only [nextA,nextB,nextC] at *
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;>
    rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [mutate,correction,ofSix,phaseP,phaseQ,nextB,nextC] <;> grind

theorem Q_two (m a b c : Int) (h : Domain m a b c) :
    mutate (phaseQ m a b c) 2 =
      root m (nextA m a b c) (nextB m a c) (nextC m a b c) := by
  have hp := parameter_bounds m a b c h
  have hc := preserves_domain m a b c h
  unfold Domain nextA nextB nextC at hc
  obtain ⟨hm,hmb,hbc,hca⟩ := h
  simp only [nextA,nextB,nextC] at *
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;>
    rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [mutate,correction,ofSix,phaseQ,root,nextA,nextB,nextC] <;> grind

theorem recurrence (m a b c : Int) (h : Domain m a b c) :
    applyWord (root m a b c) [0,1,2] =
      root m (nextA m a b c) (nextB m a c) (nextC m a b c) := by
  simp only [applyWord,root_zero m a b c h,P_one m a b c h,Q_two m a b c h]

theorem P_two (m a b c : Int) (h : Domain m a b c) :
    mutate (phaseP m a b c) 2 = phaseS m a b c := by
  have hp := parameter_bounds m a b c h
  obtain ⟨hm,hmb,hbc,hca⟩ := h
  simp only [nextA,nextB,nextC] at *
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;>
    rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [mutate,correction,ofSix,phaseP,phaseS,nextA,nextB,nextC] <;> grind

theorem S_one (m a b c : Int) (h : Domain m a b c) :
    mutate (phaseS m a b c) 1 = phaseT m a b c := by
  have hp := parameter_bounds m a b c h
  obtain ⟨hm,hmb,hbc,hca⟩ := h
  simp only [nextA,nextB,nextC] at *
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;>
    rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [mutate,correction,ofSix,phaseS,phaseT,nextA,nextB] <;> grind

theorem T_zero (m a b c : Int) (h : Domain m a b c) :
    mutate (phaseT m a b c) 0 = phaseV m a b c := by
  have hp := parameter_bounds m a b c h
  have hg := growth m a b c h
  obtain ⟨hm,hmb,hbc,hca⟩ := h
  simp only [nextA,nextB,nextC] at *
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;>
    rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [mutate,correction,ofSix,phaseT,phaseV,nextA,nextB,nextC] <;> grind

theorem T_two (m a b c : Int) (h : Domain m a b c) :
    relabel (mutate (phaseT m a b c) 2) Regions.frame0213 =
      root m (nextA m a b c) (nextB m a c) (nextC m a b c) := by
  have hp := parameter_bounds m a b c h
  have ids := next_identities m a b c
  obtain ⟨hm,hmb,hbc,hca⟩ := h
  simp only [nextA,nextB,nextC] at *
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;>
    rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [relabel,Regions.frame0213,mutate,correction,ofSix,phaseT,root,nextA,nextB,nextC] <;> grind

theorem V_two (m a b c : Int) (h : Domain m a b c) :
    relabel (mutate (phaseV m a b c) 2) Regions.frame1203.symm =
      phaseQ m (nextA m a b c) (nextB m a c) (nextC m a b c) := by
  have hp := parameter_bounds m a b c h
  have hg := growth m a b c h
  have ids := next_identities m a b c
  obtain ⟨hm,hmb,hbc,hca⟩ := h
  simp only [nextA,nextB,nextC] at *
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;>
    rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [relabel,Regions.frame1203,Relabeling.symm,mutate,correction,ofSix,phaseV,phaseQ,nextA,nextB,nextC] <;> grind

theorem P_zero (m a b c : Int) (h : Domain m a b c) :
    mutate (phaseP m a b c) 0 = root m a b c := by
  rw [← root_zero m a b c h, mutation_involutive]

theorem Q_one (m a b c : Int) (h : Domain m a b c) :
    mutate (phaseQ m a b c) 1 = phaseP m a b c := by
  rw [← P_one m a b c h, mutation_involutive]

theorem S_two (m a b c : Int) (h : Domain m a b c) :
    mutate (phaseS m a b c) 2 = phaseP m a b c := by
  rw [← P_two m a b c h, mutation_involutive]

theorem T_one (m a b c : Int) (h : Domain m a b c) :
    mutate (phaseT m a b c) 1 = phaseS m a b c := by
  rw [← S_one m a b c h, mutation_involutive]

theorem V_zero (m a b c : Int) (h : Domain m a b c) :
    mutate (phaseV m a b c) 0 = phaseT m a b c := by
  rw [← T_zero m a b c h, mutation_involutive]

theorem next_root_two (m a b c : Int) (h : Domain m a b c) :
    mutate (root m (nextA m a b c) (nextB m a c) (nextC m a b c)) 2 =
      phaseQ m a b c := by
  rw [← Q_two m a b c h, mutation_involutive]

theorem next_root_one (m a b c : Int) (h : Domain m a b c) :
    mutate (root m (nextA m a b c) (nextB m a c) (nextC m a b c)) 1 =
      relabel (phaseT m a b c) Regions.frame0213 := by
  rw [← T_two m a b c h, mutate_relabel]
  change relabel (mutate (mutate (phaseT m a b c) 2) 2) _ = _
  rw [mutation_involutive]

theorem next_Q_zero (m a b c : Int) (h : Domain m a b c) :
    mutate (phaseQ m (nextA m a b c) (nextB m a c) (nextC m a b c)) 0 =
      relabel (phaseV m a b c) Regions.frame1203.symm := by
  rw [← V_two m a b c h, mutate_relabel]
  change relabel (mutate (mutate (phaseV m a b c) 2) 2) _ = _
  rw [mutation_involutive]

def phase (m a b c : Int) (i : Fin 6) : Matrix 4 :=
  match i.val with
  | 0 => root m a b c | 1 => phaseP m a b c | 2 => phaseQ m a b c
  | 3 => phaseS m a b c | 4 => phaseT m a b c | _ => phaseV m a b c

theorem phase_skew (m a b c : Int) (i : Fin 6) :
    SkewSymmetric (phase m a b c i) := by
  have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 := by omega
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;> exact ofSix_skew _ _ _ _ _ _

theorem phase_cyclic (m a b c : Int) (h : Domain m a b c) (i : Fin 6) :
    ¬ Acyclic (phase m a b c i) := by
  have hp := parameter_bounds m a b c h
  have hg := growth m a b c h
  obtain ⟨hm,hmb,hbc,hca⟩ := h
  have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 := by omega
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl
  · rintro ⟨rank,hr⟩
    have h1 := hr 0 3 (by simp [phase,root,ofSix]; omega)
    have h2 := hr 3 2 (by simp [phase,root,ofSix]; omega)
    have h3 := hr 2 0 (by simp [phase,root,ofSix]; omega)
    omega
  · rintro ⟨rank,hr⟩
    have h1 := hr 0 1 (by simp [phase,phaseP,ofSix])
    have h2 := hr 1 3 (by simp [phase,phaseP,ofSix]; omega)
    have h3 := hr 3 0 (by simp [phase,phaseP,ofSix]; omega)
    omega
  · rintro ⟨rank,hr⟩
    have h1 := hr 0 3 (by simp [phase,phaseQ,ofSix]; omega)
    have h2 := hr 3 1 (by simp [phase,phaseQ,ofSix]; omega)
    have h3 := hr 1 0 (by simp [phase,phaseQ,ofSix])
    omega
  · rintro ⟨rank,hr⟩
    have h1 := hr 0 3 (by simp [phase,phaseS,ofSix]; omega)
    have h2 := hr 3 2 (by simp [phase,phaseS,ofSix]; omega)
    have h3 := hr 2 0 (by simp [phase,phaseS,ofSix]; omega)
    omega
  · rintro ⟨rank,hr⟩
    have h1 := hr 0 2 (by simp [phase,phaseT,ofSix])
    have h2 := hr 2 1 (by simp [phase,phaseT,ofSix])
    have h3 := hr 1 0 (by simp [phase,phaseT,ofSix]; omega)
    omega
  · rintro ⟨rank,hr⟩
    have h1 := hr 0 1 (by simp [phase,phaseV,ofSix]; omega)
    have h2 := hr 1 2 (by simp [phase,phaseV,ofSix]; omega)
    have h3 := hr 2 0 (by simp [phase,phaseV,ofSix])
    omega

def step (m : Int) (s : Cone.State) : Cone.State :=
  ⟨nextA m s.A s.H s.Z, nextB m s.A s.Z, nextC m s.A s.H s.Z⟩

def orbit (m : Int) (s : Cone.State) : Nat → Cone.State
  | 0 => s | n+1 => step m (orbit m s n)

theorem orbit_domain (m : Int) (s : Cone.State) (h : Domain m s.A s.H s.Z)
    (n : Nat) : Domain m (orbit m s n).A (orbit m s n).H (orbit m s n).Z := by
  induction n with
  | zero => exact h
  | succ n ih => exact preserves_domain _ _ _ _ ih

theorem orbit_growth (m : Int) (s : Cone.State) (h : Domain m s.A s.H s.Z)
    (n : Nat) : 4*(orbit m s n).A < (orbit m s (n+1)).A :=
  growth _ _ _ _ (orbit_domain m s h n)

theorem orbit_as_mutations (m : Int) (s : Cone.State) (h : Domain m s.A s.H s.Z)
    (n : Nat) : applyWord (root m s.A s.H s.Z) (Cone.repeatedWord n) =
      root m (orbit m s n).A (orbit m s n).H (orbit m s n).Z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Cone.repeatedWord,applyWord_append,ih]
    exact recurrence _ _ _ _ (orbit_domain m s h n)

def familyG (n : Int) : Matrix 4 := root 2 (8*n+7) (8*n+3) (8*n+5)

theorem familyG_domain (n : Int) (hn : 1 ≤ n) : Domain 2 (8*n+7) (8*n+3) (8*n+5) := by
  unfold Domain; omega

theorem familyG_pfaffian (n : Int) : matrixPfaffian (familyG n) = 16*n+4 := by
  simp [matrixPfaffian,familyG,root,ofSix]; grind

/-- Reversal, permutation, and arbitrary mutation words cannot identify two
different members. This class-separation claim does not require NMA. -/
theorem familyG_distinct (s t : Int) (hs : 1 ≤ s) (ht : 1 ≤ t) (hst : s ≠ t)
    (word : List (Fin 4)) (p : Relabeling 4) (rev : Bool) :
    applyWord (familyG s) word ≠ relabel (if rev then reverse (familyG t) else familyG t) p := by
  intro he
  have hsk : SkewSymmetric (if rev then reverse (familyG t) else familyG t) := by
    cases rev
    · exact ofSix_skew _ _ _ _ _ _
    · exact reverse_skew _ (ofSix_skew _ _ _ _ _ _)
  have hi := pfaffian_square_word (familyG s) word (ofSix_skew _ _ _ _ _ _)
  rw [he,ClassSeparation.pfaffian_square_relabel _ hsk p] at hi
  have htpf : matrixPfaffian (if rev then reverse (familyG t) else familyG t) = 16*t+4 := by
    cases rev
    · exact familyG_pfaffian t
    · simp [matrixPfaffian,familyG,root,reverse,ofSix]; grind
  rw [htpf,familyG_pfaffian] at hi
  have hc := ClassSeparation.square_eq_cases (16*t+4) (16*s+4) hi
  omega

end QuiverProofs.GenericStrip
