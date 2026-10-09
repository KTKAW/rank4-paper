import QuiverProofs.Forks

/-! Universal integer transition identities for the diamond and unit-pentagon
region cells of rank4_general_research/technical_note.tex. All hypotheses are
unbounded integer inequalities; no sampled parameter check is used. -/
namespace QuiverProofs.Regions

/-- The exact normal-form parameter domain (R). -/
def Domain (A B C D E : Int) : Prop :=
  2 ≤ A ∧ 2 ≤ D ∧ 2 ≤ E ∧ A < B ∧ D < B ∧ A < C ∧ E < C

def H (A B D : Int) : Int := B*D-A
def J (A C E : Int) : Int := C*E-A
def L0 (A B C D E : Int) : Int := B*D+C*E-A
def L (A B C D E : Int) : Int := B*(D+E)+C*E-A

def root (A B C D E ε : Int) : Matrix 4 := ofSix A (-D) (-E) B C ε
def diamondW2 (A B C D E : Int) : Matrix 4 := ofSix (-(H A B D)) D (-E) (-B) C 0
def diamondW3 (A B C D E : Int) : Matrix 4 := ofSix (-(J A C E)) (-D) E B (-C) 0
def diamondT (A B C D E : Int) : Matrix 4 := ofSix (-(L0 A B C D E)) D E (-B) (-C) 0
def unitW (A B C D E : Int) : Matrix 4 := ofSix (-(H A B D)) D (-E) (-B) (B+C) (-1)
def unitT (A B C D E : Int) : Matrix 4 := ofSix (-(L A B C D E)) D E C (-B-C) 1
def unitTP (A B C D E : Int) : Matrix 4 := ofSix (-(L A B C D E)) (-D) (D+E) (-C) (-B) (-1)
def unitWP (A B C D E : Int) : Matrix 4 := ofSix (-(J A C E)) E (-D-E) (-C) B 1

private theorem fin4 (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega

/-- All four compound parameters are strictly positive and dominate the
coordinates needed to fix mutation signs. -/
theorem parameter_bounds (A B C D E : Int) (h : Domain A B C D E) :
    B < H A B D ∧ D < H A B D ∧ C < J A C E ∧ E < J A C E ∧
    B+C < L0 A B C D E ∧ D+E < L0 A B C D E ∧
    B+C < L A B C D E ∧ D+E < L A B C D E := by
  obtain ⟨hA,hD,hE,hAB,hDB,hAC,hEC⟩ := h
  have hH := Forks.product_sub_dominates D B A hD hDB hAB
  have hJ := Forks.product_sub_dominates E C A hE hEC hAC
  have hCE := Int.mul_le_mul_of_nonneg_left hE (show 0 ≤ C by omega)
  have hBD := Int.mul_le_mul_of_nonneg_left hD (show 0 ≤ B by omega)
  have hEC := Int.mul_le_mul_of_nonneg_left (show 2 ≤ C by omega) (show 0 ≤ E by omega)
  have hDB := Int.mul_le_mul_of_nonneg_left (show 2 ≤ B by omega) (show 0 ≤ D by omega)
  have hBE := Int.mul_nonneg (show 0 ≤ B by omega) (show 0 ≤ E by omega)
  unfold H J L0 L
  grind

theorem diamond_root_two (A B C D E : Int) (h : Domain A B C D E) :
    mutate (root A B C D E 0) 2 = diamondW2 A B C D E := by
  have hp := parameter_bounds A B C D E h
  obtain ⟨hA,hD,hE,hAB,hDB,hAC,hEC⟩ := h
  unfold H J L0 L at hp
  funext i j
  rcases fin4 i with rfl | rfl | rfl | rfl <;>
    rcases fin4 j with rfl | rfl | rfl | rfl <;>
    simp [mutate,ofSix,correction,root,diamondW2,H] <;> grind

theorem diamond_root_three (A B C D E : Int) (h : Domain A B C D E) :
    mutate (root A B C D E 0) 3 = diamondW3 A B C D E := by
  have hp := parameter_bounds A B C D E h
  obtain ⟨hA,hD,hE,hAB,hDB,hAC,hEC⟩ := h
  unfold H J L0 L at hp
  funext i j
  rcases fin4 i with rfl | rfl | rfl | rfl <;>
    rcases fin4 j with rfl | rfl | rfl | rfl <;>
    simp [mutate,ofSix,correction,root,diamondW3,J] <;> grind

theorem diamond_w2_three (A B C D E : Int) (h : Domain A B C D E) :
    mutate (diamondW2 A B C D E) 3 = diamondT A B C D E := by
  have hp := parameter_bounds A B C D E h
  obtain ⟨hA,hD,hE,hAB,hDB,hAC,hEC⟩ := h
  unfold H J L0 L at hp
  funext i j
  rcases fin4 i with rfl | rfl | rfl | rfl <;>
    rcases fin4 j with rfl | rfl | rfl | rfl <;>
    simp [mutate,ofSix,correction,diamondW2,diamondT,H,L0] <;> grind

theorem diamond_w3_two (A B C D E : Int) (h : Domain A B C D E) :
    mutate (diamondW3 A B C D E) 2 = diamondT A B C D E := by
  have hp := parameter_bounds A B C D E h
  obtain ⟨hA,hD,hE,hAB,hDB,hAC,hEC⟩ := h
  unfold H J L0 L at hp
  funext i j
  rcases fin4 i with rfl | rfl | rfl | rfl <;>
    rcases fin4 j with rfl | rfl | rfl | rfl <;>
    simp [mutate,ofSix,correction,diamondW3,diamondT,J,L0] <;> grind

theorem unit_root_two (A B C D E : Int) (h : Domain A B C D E) :
    mutate (root A B C D E 1) 2 = unitW A B C D E := by
  have hp := parameter_bounds A B C D E h
  obtain ⟨hA,hD,hE,hAB,hDB,hAC,hEC⟩ := h
  unfold H J L0 L at hp
  funext i j
  rcases fin4 i with rfl | rfl | rfl | rfl <;>
    rcases fin4 j with rfl | rfl | rfl | rfl <;>
    simp [mutate,ofSix,correction,root,unitW,H] <;> grind

theorem unit_w_three (A B C D E : Int) (h : Domain A B C D E) :
    mutate (unitW A B C D E) 3 = unitT A B C D E := by
  have hp := parameter_bounds A B C D E h
  obtain ⟨hA,hD,hE,hAB,hDB,hAC,hEC⟩ := h
  unfold H J L0 L at hp
  funext i j
  rcases fin4 i with rfl | rfl | rfl | rfl <;>
    rcases fin4 j with rfl | rfl | rfl | rfl <;>
    simp [mutate,ofSix,correction,unitW,unitT,H,L] <;> grind

theorem unit_t_two (A B C D E : Int) (h : Domain A B C D E) :
    mutate (unitT A B C D E) 2 = unitTP A B C D E := by
  have hp := parameter_bounds A B C D E h
  obtain ⟨hA,hD,hE,hAB,hDB,hAC,hEC⟩ := h
  unfold H J L0 L at hp
  funext i j
  rcases fin4 i with rfl | rfl | rfl | rfl <;>
    rcases fin4 j with rfl | rfl | rfl | rfl <;>
    simp [mutate,ofSix,correction,unitT,unitTP,L,L] <;> grind

theorem unit_tp_three (A B C D E : Int) (h : Domain A B C D E) :
    mutate (unitTP A B C D E) 3 = unitWP A B C D E := by
  have hp := parameter_bounds A B C D E h
  obtain ⟨hA,hD,hE,hAB,hDB,hAC,hEC⟩ := h
  unfold H J L0 L at hp
  funext i j
  rcases fin4 i with rfl | rfl | rfl | rfl <;>
    rcases fin4 j with rfl | rfl | rfl | rfl <;>
    simp [mutate,ofSix,correction,unitTP,unitWP,L,J] <;> grind

theorem unit_wp_two (A B C D E : Int) (h : Domain A B C D E) :
    mutate (unitWP A B C D E) 2 = root A C B E D (-1) := by
  have hp := parameter_bounds A B C D E h
  obtain ⟨hA,hD,hE,hAB,hDB,hAC,hEC⟩ := h
  unfold H J L0 L at hp
  funext i j
  rcases fin4 i with rfl | rfl | rfl | rfl <;>
    rcases fin4 j with rfl | rfl | rfl | rfl <;>
    simp [mutate,ofSix,correction,root,unitWP,J] <;> grind

theorem root_one (A B C D E ε : Int) (h : Domain A B C D E) :
    mutate (root A B C D E ε) 1 = ofSix (-A) (A*B-D) (A*C-E) (-B) (-C) ε := by
  have hp := parameter_bounds A B C D E h
  obtain ⟨hA,hD,hE,hAB,hDB,hAC,hEC⟩ := h
  unfold H J L0 L at hp
  funext i j
  rcases fin4 i with rfl | rfl | rfl | rfl <;>
    rcases fin4 j with rfl | rfl | rfl | rfl <;>
    simp [mutate,ofSix,correction,root] <;> grind

theorem diamond_w2_zero (A B C D E : Int) (h : Domain A B C D E) :
    mutate (diamondW2 A B C D E) 0 = ofSix (H A B D) (-D) E ((H A B D)*D-B) C (-D*E) := by
  have hp := parameter_bounds A B C D E h
  obtain ⟨hA,hD,hE,hAB,hDB,hAC,hEC⟩ := h
  unfold H J L0 L at hp
  funext i j
  rcases fin4 i with rfl | rfl | rfl | rfl <;>
    rcases fin4 j with rfl | rfl | rfl | rfl <;>
    simp [mutate,ofSix,correction,diamondW2,H] <;> grind

theorem diamond_w2_one (A B C D E : Int) (h : Domain A B C D E) :
    mutate (diamondW2 A B C D E) 1 = ofSix (H A B D) (D-(H A B D)*B) (-E) B (-C) (B*C) := by
  have hp := parameter_bounds A B C D E h
  obtain ⟨hA,hD,hE,hAB,hDB,hAC,hEC⟩ := h
  unfold H J L0 L at hp
  funext i j
  rcases fin4 i with rfl | rfl | rfl | rfl <;>
    rcases fin4 j with rfl | rfl | rfl | rfl <;>
    simp [mutate,ofSix,correction,diamondW2,H] <;> grind

theorem diamond_w3_zero (A B C D E : Int) (h : Domain A B C D E) :
    mutate (diamondW3 A B C D E) 0 = ofSix (J A C E) D (-E) B ((J A C E)*E-C) (D*E) := by
  have hp := parameter_bounds A B C D E h
  obtain ⟨hA,hD,hE,hAB,hDB,hAC,hEC⟩ := h
  unfold H J L0 L at hp
  funext i j
  rcases fin4 i with rfl | rfl | rfl | rfl <;>
    rcases fin4 j with rfl | rfl | rfl | rfl <;>
    simp [mutate,ofSix,correction,diamondW3,J] <;> grind

theorem diamond_w3_one (A B C D E : Int) (h : Domain A B C D E) :
    mutate (diamondW3 A B C D E) 1 = ofSix (J A C E) (-D) (E-(J A C E)*C) (-B) C (-B*C) := by
  have hp := parameter_bounds A B C D E h
  obtain ⟨hA,hD,hE,hAB,hDB,hAC,hEC⟩ := h
  unfold H J L0 L at hp
  funext i j
  rcases fin4 i with rfl | rfl | rfl | rfl <;>
    rcases fin4 j with rfl | rfl | rfl | rfl <;>
    simp [mutate,ofSix,correction,diamondW3,J] <;> grind

theorem diamond_t_zero (A B C D E : Int) (h : Domain A B C D E) :
    mutate (diamondT A B C D E) 0 = ofSix (L0 A B C D E) (-D) (-E) ((L0 A B C D E)*D-B) ((L0 A B C D E)*E-C) 0 := by
  have hp := parameter_bounds A B C D E h
  obtain ⟨hA,hD,hE,hAB,hDB,hAC,hEC⟩ := h
  unfold H J L0 L at hp
  funext i j
  rcases fin4 i with rfl | rfl | rfl | rfl <;>
    rcases fin4 j with rfl | rfl | rfl | rfl <;>
    simp [mutate,ofSix,correction,diamondT,L0] <;> grind

theorem diamond_t_one (A B C D E : Int) (h : Domain A B C D E) :
    mutate (diamondT A B C D E) 1 = ofSix (L0 A B C D E) (D-(L0 A B C D E)*B) (E-(L0 A B C D E)*C) B C 0 := by
  have hp := parameter_bounds A B C D E h
  obtain ⟨hA,hD,hE,hAB,hDB,hAC,hEC⟩ := h
  unfold H J L0 L at hp
  funext i j
  rcases fin4 i with rfl | rfl | rfl | rfl <;>
    rcases fin4 j with rfl | rfl | rfl | rfl <;>
    simp [mutate,ofSix,correction,diamondT,L0] <;> grind

theorem unit_w_zero (A B C D E : Int) (h : Domain A B C D E) :
    mutate (unitW A B C D E) 0 = ofSix (H A B D) (-D) E ((H A B D)*D-B) (B+C) (-1-D*E) := by
  have hp := parameter_bounds A B C D E h
  obtain ⟨hA,hD,hE,hAB,hDB,hAC,hEC⟩ := h
  unfold H J L0 L at hp
  funext i j
  rcases fin4 i with rfl | rfl | rfl | rfl <;>
    rcases fin4 j with rfl | rfl | rfl | rfl <;>
    simp [mutate,ofSix,correction,unitW,H] <;> grind

theorem unit_w_one (A B C D E : Int) (h : Domain A B C D E) :
    mutate (unitW A B C D E) 1 = ofSix (H A B D) (D-(H A B D)*B) (-E) B (-B-C) (B*(B+C)-1) := by
  have hp := parameter_bounds A B C D E h
  obtain ⟨hA,hD,hE,hAB,hDB,hAC,hEC⟩ := h
  unfold H J L0 L at hp
  funext i j
  rcases fin4 i with rfl | rfl | rfl | rfl <;>
    rcases fin4 j with rfl | rfl | rfl | rfl <;>
    simp [mutate,ofSix,correction,unitW,H] <;> grind

theorem unit_t_zero (A B C D E : Int) (h : Domain A B C D E) :
    mutate (unitT A B C D E) 0 = ofSix (L A B C D E) (-D) (-E) ((L A B C D E)*D+C) ((L A B C D E)*E-B-C) 1 := by
  have hp := parameter_bounds A B C D E h
  obtain ⟨hA,hD,hE,hAB,hDB,hAC,hEC⟩ := h
  unfold H J L0 L at hp
  funext i j
  rcases fin4 i with rfl | rfl | rfl | rfl <;>
    rcases fin4 j with rfl | rfl | rfl | rfl <;>
    simp [mutate,ofSix,correction,unitT,L] <;> grind

theorem unit_t_one (A B C D E : Int) (h : Domain A B C D E) :
    mutate (unitT A B C D E) 1 = ofSix (L A B C D E) D (E-(L A B C D E)*(B+C)) (-C) (B+C) (1-C*(B+C)) := by
  have hp := parameter_bounds A B C D E h
  obtain ⟨hA,hD,hE,hAB,hDB,hAC,hEC⟩ := h
  unfold H J L0 L at hp
  funext i j
  rcases fin4 i with rfl | rfl | rfl | rfl <;>
    rcases fin4 j with rfl | rfl | rfl | rfl <;>
    simp [mutate,ofSix,correction,unitT,L] <;> grind

theorem unit_tp_zero (A B C D E : Int) (h : Domain A B C D E) :
    mutate (unitTP A B C D E) 0 = ofSix (L A B C D E) D (-D-E) (-C) ((L A B C D E)*(D+E)-B) (D*(D+E)-1) := by
  have hp := parameter_bounds A B C D E h
  obtain ⟨hA,hD,hE,hAB,hDB,hAC,hEC⟩ := h
  unfold H J L0 L at hp
  funext i j
  rcases fin4 i with rfl | rfl | rfl | rfl <;>
    rcases fin4 j with rfl | rfl | rfl | rfl <;>
    simp [mutate,ofSix,correction,unitTP,L] <;> grind

theorem unit_tp_one (A B C D E : Int) (h : Domain A B C D E) :
    mutate (unitTP A B C D E) 1 = ofSix (L A B C D E) (-D-(L A B C D E)*C) (D+E-(L A B C D E)*B) C B (-1) := by
  have hp := parameter_bounds A B C D E h
  obtain ⟨hA,hD,hE,hAB,hDB,hAC,hEC⟩ := h
  unfold H J L0 L at hp
  funext i j
  rcases fin4 i with rfl | rfl | rfl | rfl <;>
    rcases fin4 j with rfl | rfl | rfl | rfl <;>
    simp [mutate,ofSix,correction,unitTP,L] <;> grind

theorem unit_wp_zero (A B C D E : Int) (h : Domain A B C D E) :
    mutate (unitWP A B C D E) 0 = ofSix (J A C E) (-E) (D+E) ((J A C E)*E-C) B (1-E*(D+E)) := by
  have hp := parameter_bounds A B C D E h
  obtain ⟨hA,hD,hE,hAB,hDB,hAC,hEC⟩ := h
  unfold H J L0 L at hp
  funext i j
  rcases fin4 i with rfl | rfl | rfl | rfl <;>
    rcases fin4 j with rfl | rfl | rfl | rfl <;>
    simp [mutate,ofSix,correction,unitWP,J] <;> grind

theorem unit_wp_one (A B C D E : Int) (h : Domain A B C D E) :
    mutate (unitWP A B C D E) 1 = ofSix (J A C E) (E-(J A C E)*C) (-D-E) C (-B) (1+B*C) := by
  have hp := parameter_bounds A B C D E h
  obtain ⟨hA,hD,hE,hAB,hDB,hAC,hEC⟩ := h
  unfold H J L0 L at hp
  funext i j
  rcases fin4 i with rfl | rfl | rfl | rfl <;>
    rcases fin4 j with rfl | rfl | rfl | rfl <;>
    simp [mutate,ofSix,correction,unitWP,J] <;> grind

def frame0213 : Relabeling 4 :=
  ⟨fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | _ => 3,
   fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | _ => 3, by decide, by decide⟩

def frame1203 : Relabeling 4 :=
  ⟨fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 0 | _ => 3,
   fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 1 | _ => 3, by decide, by decide⟩

def frame0312 : Relabeling 4 :=
  ⟨fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | _ => 2,
   fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | _ => 1, by decide, by decide⟩

def frame1302 : Relabeling 4 :=
  ⟨fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 0 | _ => 2,
   fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 3 | _ => 1, by decide, by decide⟩

def frame1320 : Relabeling 4 :=
  ⟨fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | _ => 0,
   fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | _ => 1, by decide, by decide⟩

def frame0321 : Relabeling 4 :=
  ⟨fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | _ => 1,
   fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | _ => 1, by decide, by decide⟩

def frame0132 : Relabeling 4 :=
  ⟨fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | _ => 2,
   fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | _ => 2, by decide, by decide⟩

/-- A framed zero-edge or unit-edge pre-fork root. -/
inductive IsRoot : Matrix 4 → Fin 4 → Prop
  | basic (A B C D E ε : Int) : Domain A B C D E → (ε=0 ∨ ε=1) →
      IsRoot (root A B C D E ε) 0
  | relabelled {Q : Matrix 4} {r : Fin 4} : IsRoot Q r → (p : Relabeling 4) →
      IsRoot (relabel Q p) (p.invFun r)
  | reversed {Q : Matrix 4} {r : Fin 4} : IsRoot Q r → IsRoot (reverse Q) r

theorem root_of_relabel {Q : Matrix 4} (p : Relabeling 4) {r : Fin 4}
    (h : IsRoot (relabel Q p) r) : IsRoot Q (p.toFun r) := by
  have h' := IsRoot.relabelled h p.symm
  change IsRoot (relabel (relabel Q p) p.symm) (p.toFun r) at h'
  rw [relabel_inverse] at h'
  exact h'

theorem root_of_reverse {Q : Matrix 4} {r : Fin 4}
    (h : IsRoot (reverse Q) r) : IsRoot Q r := by
  simpa only [reverse_involutive] using IsRoot.reversed h

theorem diamond_w2_zero_domain (A B C D E : Int) (h : Domain A B C D E) :
    Forks.Domain (D) (H A B D) (E) ((H A B D)*D-B) (D*E) (C) := by
  have hp := parameter_bounds A B C D E h
  obtain ⟨hA,hD,hE,hAB,hDB,hAC,hEC⟩ := h
  have hh0 := Forks.product_sub_dominates D (H A B D) B (by omega) (by omega) (by omega)
  have hh1 := Forks.product_add_dominates D E 0 (by omega) (by omega) (by omega)
  unfold Forks.Domain
  grind

theorem diamond_w2_zero_fork (A B C D E : Int) (h : Domain A B C D E) :
    Forks.IsFork (mutate (diamondW2 A B C D E) 0) 0 := by
  have heq : relabel (mutate (diamondW2 A B C D E) 0) frame0213 = Forks.template (D) (H A B D) (E) ((H A B D)*D-B) (D*E) (C) := by
    rw [diamond_w2_zero A B C D E h]
    funext i j
    rcases fin4 i with rfl | rfl | rfl | rfl <;>
      rcases fin4 j with rfl | rfl | rfl | rfl <;>
      simp [relabel,frame0213,Forks.template,ofSix] <;> grind
  have hf : Forks.IsFork (relabel (mutate (diamondW2 A B C D E) 0) frame0213) 0 := by
    rw [heq]
    exact Forks.IsFork.basic _ _ _ _ _ _ (diamond_w2_zero_domain A B C D E h)
  exact Forks.fork_of_relabel frame0213 hf

theorem diamond_w2_one_domain (A B C D E : Int) (h : Domain A B C D E) :
    Forks.Domain (B) (H A B D) (C) ((H A B D)*B-D) (B*C) (E) := by
  have hp := parameter_bounds A B C D E h
  obtain ⟨hA,hD,hE,hAB,hDB,hAC,hEC⟩ := h
  have hh0 := Forks.product_sub_dominates B (H A B D) D (by omega) (by omega) (by omega)
  have hh1 := Forks.product_add_dominates B C 0 (by omega) (by omega) (by omega)
  unfold Forks.Domain
  grind

theorem diamond_w2_one_fork (A B C D E : Int) (h : Domain A B C D E) :
    Forks.IsFork (mutate (diamondW2 A B C D E) 1) 1 := by
  have heq : relabel (reverse (mutate (diamondW2 A B C D E) 1)) frame1203 = Forks.template (B) (H A B D) (C) ((H A B D)*B-D) (B*C) (E) := by
    rw [diamond_w2_one A B C D E h]
    funext i j
    rcases fin4 i with rfl | rfl | rfl | rfl <;>
      rcases fin4 j with rfl | rfl | rfl | rfl <;>
      simp [relabel,reverse,frame1203,Forks.template,ofSix] <;> grind
  have hf : Forks.IsFork (relabel (reverse (mutate (diamondW2 A B C D E) 1)) frame1203) 0 := by
    rw [heq]
    exact Forks.IsFork.basic _ _ _ _ _ _ (diamond_w2_one_domain A B C D E h)
  exact Forks.fork_of_reverse (Forks.fork_of_relabel frame1203 hf)

theorem diamond_w3_zero_domain (A B C D E : Int) (h : Domain A B C D E) :
    Forks.Domain (E) (J A C E) (D) ((J A C E)*E-C) (D*E) (B) := by
  have hp := parameter_bounds A B C D E h
  obtain ⟨hA,hD,hE,hAB,hDB,hAC,hEC⟩ := h
  have hh0 := Forks.product_sub_dominates E (J A C E) C (by omega) (by omega) (by omega)
  have hh1 := Forks.product_add_dominates D E 0 (by omega) (by omega) (by omega)
  unfold Forks.Domain
  grind

theorem diamond_w3_zero_fork (A B C D E : Int) (h : Domain A B C D E) :
    Forks.IsFork (mutate (diamondW3 A B C D E) 0) 0 := by
  have heq : relabel (mutate (diamondW3 A B C D E) 0) frame0312 = Forks.template (E) (J A C E) (D) ((J A C E)*E-C) (D*E) (B) := by
    rw [diamond_w3_zero A B C D E h]
    funext i j
    rcases fin4 i with rfl | rfl | rfl | rfl <;>
      rcases fin4 j with rfl | rfl | rfl | rfl <;>
      simp [relabel,frame0312,Forks.template,ofSix] <;> grind
  have hf : Forks.IsFork (relabel (mutate (diamondW3 A B C D E) 0) frame0312) 0 := by
    rw [heq]
    exact Forks.IsFork.basic _ _ _ _ _ _ (diamond_w3_zero_domain A B C D E h)
  exact Forks.fork_of_relabel frame0312 hf

theorem diamond_w3_one_domain (A B C D E : Int) (h : Domain A B C D E) :
    Forks.Domain (C) (J A C E) (B) ((J A C E)*C-E) (B*C) (D) := by
  have hp := parameter_bounds A B C D E h
  obtain ⟨hA,hD,hE,hAB,hDB,hAC,hEC⟩ := h
  have hh0 := Forks.product_sub_dominates C (J A C E) E (by omega) (by omega) (by omega)
  have hh1 := Forks.product_add_dominates B C 0 (by omega) (by omega) (by omega)
  unfold Forks.Domain
  grind

theorem diamond_w3_one_fork (A B C D E : Int) (h : Domain A B C D E) :
    Forks.IsFork (mutate (diamondW3 A B C D E) 1) 1 := by
  have heq : relabel (reverse (mutate (diamondW3 A B C D E) 1)) frame1302 = Forks.template (C) (J A C E) (B) ((J A C E)*C-E) (B*C) (D) := by
    rw [diamond_w3_one A B C D E h]
    funext i j
    rcases fin4 i with rfl | rfl | rfl | rfl <;>
      rcases fin4 j with rfl | rfl | rfl | rfl <;>
      simp [relabel,reverse,frame1302,Forks.template,ofSix] <;> grind
  have hf : Forks.IsFork (relabel (reverse (mutate (diamondW3 A B C D E) 1)) frame1302) 0 := by
    rw [heq]
    exact Forks.IsFork.basic _ _ _ _ _ _ (diamond_w3_one_domain A B C D E h)
  exact Forks.fork_of_reverse (Forks.fork_of_relabel frame1302 hf)

theorem unit_w_zero_domain (A B C D E : Int) (h : Domain A B C D E) :
    Forks.Domain (D) (H A B D) (E) ((H A B D)*D-B) (1+D*E) (B+C) := by
  have hp := parameter_bounds A B C D E h
  obtain ⟨hA,hD,hE,hAB,hDB,hAC,hEC⟩ := h
  have hh0 := Forks.product_sub_dominates D (H A B D) B (by omega) (by omega) (by omega)
  have hh1 := Forks.product_add_dominates D E 1 (by omega) (by omega) (by omega)
  unfold Forks.Domain
  grind

theorem unit_w_zero_fork (A B C D E : Int) (h : Domain A B C D E) :
    Forks.IsFork (mutate (unitW A B C D E) 0) 0 := by
  have heq : relabel (mutate (unitW A B C D E) 0) frame0213 = Forks.template (D) (H A B D) (E) ((H A B D)*D-B) (1+D*E) (B+C) := by
    rw [unit_w_zero A B C D E h]
    funext i j
    rcases fin4 i with rfl | rfl | rfl | rfl <;>
      rcases fin4 j with rfl | rfl | rfl | rfl <;>
      simp [relabel,frame0213,Forks.template,ofSix] <;> grind
  have hf : Forks.IsFork (relabel (mutate (unitW A B C D E) 0) frame0213) 0 := by
    rw [heq]
    exact Forks.IsFork.basic _ _ _ _ _ _ (unit_w_zero_domain A B C D E h)
  exact Forks.fork_of_relabel frame0213 hf

theorem unit_w_one_domain (A B C D E : Int) (h : Domain A B C D E) :
    Forks.Domain (B) (H A B D) (B+C) ((H A B D)*B-D) (B*(B+C)-1) (E) := by
  have hp := parameter_bounds A B C D E h
  obtain ⟨hA,hD,hE,hAB,hDB,hAC,hEC⟩ := h
  have hh0 := Forks.product_sub_dominates B (H A B D) D (by omega) (by omega) (by omega)
  have hh1 := Forks.product_sub_dominates B (B+C) 1 (by omega) (by omega) (by omega)
  unfold Forks.Domain
  grind

theorem unit_w_one_fork (A B C D E : Int) (h : Domain A B C D E) :
    Forks.IsFork (mutate (unitW A B C D E) 1) 1 := by
  have heq : relabel (reverse (mutate (unitW A B C D E) 1)) frame1203 = Forks.template (B) (H A B D) (B+C) ((H A B D)*B-D) (B*(B+C)-1) (E) := by
    rw [unit_w_one A B C D E h]
    funext i j
    rcases fin4 i with rfl | rfl | rfl | rfl <;>
      rcases fin4 j with rfl | rfl | rfl | rfl <;>
      simp [relabel,reverse,frame1203,Forks.template,ofSix] <;> grind
  have hf : Forks.IsFork (relabel (reverse (mutate (unitW A B C D E) 1)) frame1203) 0 := by
    rw [heq]
    exact Forks.IsFork.basic _ _ _ _ _ _ (unit_w_one_domain A B C D E h)
  exact Forks.fork_of_reverse (Forks.fork_of_relabel frame1203 hf)

theorem unit_t_one_domain (A B C D E : Int) (h : Domain A B C D E) :
    Forks.Domain (B+C) (C) (L A B C D E) (C*(B+C)-1) ((L A B C D E)*(B+C)-E) (D) := by
  have hp := parameter_bounds A B C D E h
  obtain ⟨hA,hD,hE,hAB,hDB,hAC,hEC⟩ := h
  have hh0 := Forks.product_sub_dominates C (B+C) 1 (by omega) (by omega) (by omega)
  have hh1 := Forks.product_sub_dominates (B+C) (L A B C D E) E (by omega) (by omega) (by omega)
  unfold Forks.Domain
  grind

theorem unit_t_one_fork (A B C D E : Int) (h : Domain A B C D E) :
    Forks.IsFork (mutate (unitT A B C D E) 1) 1 := by
  have heq : relabel (reverse (mutate (unitT A B C D E) 1)) frame1320 = Forks.template (B+C) (C) (L A B C D E) (C*(B+C)-1) ((L A B C D E)*(B+C)-E) (D) := by
    rw [unit_t_one A B C D E h]
    funext i j
    rcases fin4 i with rfl | rfl | rfl | rfl <;>
      rcases fin4 j with rfl | rfl | rfl | rfl <;>
      simp [relabel,reverse,frame1320,Forks.template,ofSix] <;> grind
  have hf : Forks.IsFork (relabel (reverse (mutate (unitT A B C D E) 1)) frame1320) 0 := by
    rw [heq]
    exact Forks.IsFork.basic _ _ _ _ _ _ (unit_t_one_domain A B C D E h)
  exact Forks.fork_of_reverse (Forks.fork_of_relabel frame1320 hf)

theorem unit_tp_zero_domain (A B C D E : Int) (h : Domain A B C D E) :
    Forks.Domain (D+E) (D) (L A B C D E) (D*(D+E)-1) ((L A B C D E)*(D+E)-B) (C) := by
  have hp := parameter_bounds A B C D E h
  obtain ⟨hA,hD,hE,hAB,hDB,hAC,hEC⟩ := h
  have hh0 := Forks.product_sub_dominates D (D+E) 1 (by omega) (by omega) (by omega)
  have hh1 := Forks.product_sub_dominates (D+E) (L A B C D E) B (by omega) (by omega) (by omega)
  unfold Forks.Domain
  grind

theorem unit_tp_zero_fork (A B C D E : Int) (h : Domain A B C D E) :
    Forks.IsFork (mutate (unitTP A B C D E) 0) 0 := by
  have heq : relabel (mutate (unitTP A B C D E) 0) frame0321 = Forks.template (D+E) (D) (L A B C D E) (D*(D+E)-1) ((L A B C D E)*(D+E)-B) (C) := by
    rw [unit_tp_zero A B C D E h]
    funext i j
    rcases fin4 i with rfl | rfl | rfl | rfl <;>
      rcases fin4 j with rfl | rfl | rfl | rfl <;>
      simp [relabel,frame0321,Forks.template,ofSix] <;> grind
  have hf : Forks.IsFork (relabel (mutate (unitTP A B C D E) 0) frame0321) 0 := by
    rw [heq]
    exact Forks.IsFork.basic _ _ _ _ _ _ (unit_tp_zero_domain A B C D E h)
  exact Forks.fork_of_relabel frame0321 hf

theorem unit_wp_zero_domain (A B C D E : Int) (h : Domain A B C D E) :
    Forks.Domain (E) (J A C E) (D+E) ((J A C E)*E-C) (E*(D+E)-1) (B) := by
  have hp := parameter_bounds A B C D E h
  obtain ⟨hA,hD,hE,hAB,hDB,hAC,hEC⟩ := h
  have hh0 := Forks.product_sub_dominates E (J A C E) C (by omega) (by omega) (by omega)
  have hh1 := Forks.product_sub_dominates E (D+E) 1 (by omega) (by omega) (by omega)
  unfold Forks.Domain
  grind

theorem unit_wp_zero_fork (A B C D E : Int) (h : Domain A B C D E) :
    Forks.IsFork (mutate (unitWP A B C D E) 0) 0 := by
  have heq : relabel (mutate (unitWP A B C D E) 0) frame0213 = Forks.template (E) (J A C E) (D+E) ((J A C E)*E-C) (E*(D+E)-1) (B) := by
    rw [unit_wp_zero A B C D E h]
    funext i j
    rcases fin4 i with rfl | rfl | rfl | rfl <;>
      rcases fin4 j with rfl | rfl | rfl | rfl <;>
      simp [relabel,frame0213,Forks.template,ofSix] <;> grind
  have hf : Forks.IsFork (relabel (mutate (unitWP A B C D E) 0) frame0213) 0 := by
    rw [heq]
    exact Forks.IsFork.basic _ _ _ _ _ _ (unit_wp_zero_domain A B C D E h)
  exact Forks.fork_of_relabel frame0213 hf

theorem unit_wp_one_domain (A B C D E : Int) (h : Domain A B C D E) :
    Forks.Domain (C) (J A C E) (B) ((J A C E)*C-E) (1+B*C) (D+E) := by
  have hp := parameter_bounds A B C D E h
  obtain ⟨hA,hD,hE,hAB,hDB,hAC,hEC⟩ := h
  have hh0 := Forks.product_sub_dominates C (J A C E) E (by omega) (by omega) (by omega)
  have hh1 := Forks.product_add_dominates B C 1 (by omega) (by omega) (by omega)
  unfold Forks.Domain
  grind

theorem unit_wp_one_fork (A B C D E : Int) (h : Domain A B C D E) :
    Forks.IsFork (mutate (unitWP A B C D E) 1) 1 := by
  have heq : relabel (reverse (mutate (unitWP A B C D E) 1)) frame1203 = Forks.template (C) (J A C E) (B) ((J A C E)*C-E) (1+B*C) (D+E) := by
    rw [unit_wp_one A B C D E h]
    funext i j
    rcases fin4 i with rfl | rfl | rfl | rfl <;>
      rcases fin4 j with rfl | rfl | rfl | rfl <;>
      simp [relabel,reverse,frame1203,Forks.template,ofSix] <;> grind
  have hf : Forks.IsFork (relabel (reverse (mutate (unitWP A B C D E) 1)) frame1203) 0 := by
    rw [heq]
    exact Forks.IsFork.basic _ _ _ _ _ _ (unit_wp_one_domain A B C D E h)
  exact Forks.fork_of_reverse (Forks.fork_of_relabel frame1203 hf)

theorem root_one_root_domain (A B C D E : Int) (h : Domain A B C D E) :
    Domain (A) (A*B-D) (A*C-E) (B) (C) := by
  have hp := parameter_bounds A B C D E h
  obtain ⟨hA,hD,hE,hAB,hDB,hAC,hEC⟩ := h
  have hh0 := Forks.product_sub_dominates A B D (by omega) (by omega) (by omega)
  have hh1 := Forks.product_sub_dominates A C E (by omega) (by omega) (by omega)
  unfold Domain
  grind

theorem root_one_root (A B C D E ε : Int) (h : Domain A B C D E) (hε : ε=0 ∨ ε=1) :
    IsRoot (mutate (root A B C D E ε) 1) 1 := by
  have heq : relabel (mutate (root A B C D E ε) 1) Forks.swap01 = root (A) (A*B-D) (A*C-E) (B) (C) (ε) := by
    rw [root_one A B C D E ε h]
    funext i j
    rcases fin4 i with rfl | rfl | rfl | rfl <;>
      rcases fin4 j with rfl | rfl | rfl | rfl <;>
      simp [relabel,Forks.swap01,root,ofSix] <;> grind
  have hr : IsRoot (relabel (mutate (root A B C D E ε) 1) Forks.swap01) 0 := by
    rw [heq]
    exact IsRoot.basic _ _ _ _ _ _ (root_one_root_domain A B C D E h) hε
  exact root_of_relabel Forks.swap01 hr

theorem diamond_t_zero_root_domain (A B C D E : Int) (h : Domain A B C D E) :
    Domain (L0 A B C D E) ((L0 A B C D E)*D-B) ((L0 A B C D E)*E-C) (D) (E) := by
  have hp := parameter_bounds A B C D E h
  obtain ⟨hA,hD,hE,hAB,hDB,hAC,hEC⟩ := h
  have hh0 := Forks.product_sub_dominates D (L0 A B C D E) B (by omega) (by omega) (by omega)
  have hh1 := Forks.product_sub_dominates E (L0 A B C D E) C (by omega) (by omega) (by omega)
  unfold Domain
  grind

theorem diamond_t_zero_root (A B C D E : Int) (h : Domain A B C D E) :
    IsRoot (mutate (diamondT A B C D E) 0) 0 := by
  have heq : mutate (diamondT A B C D E) 0 = root (L0 A B C D E) ((L0 A B C D E)*D-B) ((L0 A B C D E)*E-C) (D) (E) (0) := by
    rw [diamond_t_zero A B C D E h]
    funext i j
    rcases fin4 i with rfl | rfl | rfl | rfl <;>
      rcases fin4 j with rfl | rfl | rfl | rfl <;>
      simp [root,ofSix] <;> grind
  have hr : IsRoot (mutate (diamondT A B C D E) 0) 0 := by
    rw [heq]
    exact IsRoot.basic _ _ _ _ _ _ (diamond_t_zero_root_domain A B C D E h) (by decide)
  exact hr

theorem diamond_t_one_root_domain (A B C D E : Int) (h : Domain A B C D E) :
    Domain (L0 A B C D E) ((L0 A B C D E)*B-D) ((L0 A B C D E)*C-E) (B) (C) := by
  have hp := parameter_bounds A B C D E h
  obtain ⟨hA,hD,hE,hAB,hDB,hAC,hEC⟩ := h
  have hh0 := Forks.product_sub_dominates B (L0 A B C D E) D (by omega) (by omega) (by omega)
  have hh1 := Forks.product_sub_dominates C (L0 A B C D E) E (by omega) (by omega) (by omega)
  unfold Domain
  grind

theorem diamond_t_one_root (A B C D E : Int) (h : Domain A B C D E) :
    IsRoot (mutate (diamondT A B C D E) 1) 1 := by
  have heq : relabel (reverse (mutate (diamondT A B C D E) 1)) Forks.swap01 = root (L0 A B C D E) ((L0 A B C D E)*B-D) ((L0 A B C D E)*C-E) (B) (C) (0) := by
    rw [diamond_t_one A B C D E h]
    funext i j
    rcases fin4 i with rfl | rfl | rfl | rfl <;>
      rcases fin4 j with rfl | rfl | rfl | rfl <;>
      simp [relabel,Forks.swap01,reverse,root,ofSix] <;> grind
  have hr : IsRoot (relabel (reverse (mutate (diamondT A B C D E) 1)) Forks.swap01) 0 := by
    rw [heq]
    exact IsRoot.basic _ _ _ _ _ _ (diamond_t_one_root_domain A B C D E h) (by decide)
  exact root_of_reverse (root_of_relabel Forks.swap01 hr)

theorem unit_t_zero_root_domain (A B C D E : Int) (h : Domain A B C D E) :
    Domain (L A B C D E) ((L A B C D E)*D+C) ((L A B C D E)*E-B-C) (D) (E) := by
  have hp := parameter_bounds A B C D E h
  obtain ⟨hA,hD,hE,hAB,hDB,hAC,hEC⟩ := h
  have hh0 := Forks.product_add_dominates D (L A B C D E) C (by omega) (by omega) (by omega)
  have hh1 := Forks.product_sub_dominates E (L A B C D E) (B+C) (by omega) (by omega) (by omega)
  unfold Domain
  grind

theorem unit_t_zero_root (A B C D E : Int) (h : Domain A B C D E) :
    IsRoot (mutate (unitT A B C D E) 0) 0 := by
  have heq : mutate (unitT A B C D E) 0 = root (L A B C D E) ((L A B C D E)*D+C) ((L A B C D E)*E-B-C) (D) (E) (1) := by
    rw [unit_t_zero A B C D E h]
    funext i j
    rcases fin4 i with rfl | rfl | rfl | rfl <;>
      rcases fin4 j with rfl | rfl | rfl | rfl <;>
      simp [root,ofSix] <;> grind
  have hr : IsRoot (mutate (unitT A B C D E) 0) 0 := by
    rw [heq]
    exact IsRoot.basic _ _ _ _ _ _ (unit_t_zero_root_domain A B C D E h) (by decide)
  exact hr

theorem unit_tp_one_root_domain (A B C D E : Int) (h : Domain A B C D E) :
    Domain (L A B C D E) (D+(L A B C D E)*C) ((L A B C D E)*B-D-E) (C) (B) := by
  have hp := parameter_bounds A B C D E h
  obtain ⟨hA,hD,hE,hAB,hDB,hAC,hEC⟩ := h
  have hh0 := Forks.product_add_dominates C (L A B C D E) D (by omega) (by omega) (by omega)
  have hh1 := Forks.product_sub_dominates B (L A B C D E) (D+E) (by omega) (by omega) (by omega)
  unfold Domain
  grind

theorem unit_tp_one_root (A B C D E : Int) (h : Domain A B C D E) :
    IsRoot (mutate (unitTP A B C D E) 1) 1 := by
  have heq : relabel (reverse (mutate (unitTP A B C D E) 1)) Forks.swap01 = root (L A B C D E) (D+(L A B C D E)*C) ((L A B C D E)*B-D-E) (C) (B) (1) := by
    rw [unit_tp_one A B C D E h]
    funext i j
    rcases fin4 i with rfl | rfl | rfl | rfl <;>
      rcases fin4 j with rfl | rfl | rfl | rfl <;>
      simp [relabel,Forks.swap01,reverse,root,ofSix] <;> grind
  have hr : IsRoot (relabel (reverse (mutate (unitTP A B C D E) 1)) Forks.swap01) 0 := by
    rw [heq]
    exact IsRoot.basic _ _ _ _ _ _ (unit_tp_one_root_domain A B C D E h) (by decide)
  exact root_of_reverse (root_of_relabel Forks.swap01 hr)

theorem root_cyclic (A B C D E ε : Int) (h : Domain A B C D E) :
    ¬ Acyclic (root A B C D E ε) := by
  have hp := parameter_bounds A B C D E h
  obtain ⟨hA,hD,hE,hAB,hDB,hAC,hEC⟩ := h
  unfold H J L0 L at hp
  rintro ⟨rank, hr⟩
  have h1 := hr 0 1 (by simp [root,ofSix]; omega)
  have h2 := hr 1 2 (by simp [root,ofSix]; omega)
  have h3 := hr 2 0 (by simp [root,ofSix]; omega)
  omega

theorem diamond_w2_cyclic (A B C D E : Int) (h : Domain A B C D E) :
    ¬ Acyclic (diamondW2 A B C D E) := by
  have hp := parameter_bounds A B C D E h
  obtain ⟨hA,hD,hE,hAB,hDB,hAC,hEC⟩ := h
  unfold H J L0 L at hp
  rintro ⟨rank, hr⟩
  have h1 := hr 1 0 (by simp [diamondW2,H,ofSix]; omega)
  have h2 := hr 0 2 (by simp [diamondW2,ofSix]; omega)
  have h3 := hr 2 1 (by simp [diamondW2,ofSix]; omega)
  omega

theorem diamond_w3_cyclic (A B C D E : Int) (h : Domain A B C D E) :
    ¬ Acyclic (diamondW3 A B C D E) := by
  have hp := parameter_bounds A B C D E h
  obtain ⟨hA,hD,hE,hAB,hDB,hAC,hEC⟩ := h
  unfold H J L0 L at hp
  rintro ⟨rank, hr⟩
  have h1 := hr 1 0 (by simp [diamondW3,J,ofSix]; omega)
  have h2 := hr 0 3 (by simp [diamondW3,ofSix]; omega)
  have h3 := hr 3 1 (by simp [diamondW3,ofSix]; omega)
  omega

theorem diamond_t_cyclic (A B C D E : Int) (h : Domain A B C D E) :
    ¬ Acyclic (diamondT A B C D E) := by
  have hp := parameter_bounds A B C D E h
  obtain ⟨hA,hD,hE,hAB,hDB,hAC,hEC⟩ := h
  unfold H J L0 L at hp
  rintro ⟨rank, hr⟩
  have h1 := hr 1 0 (by simp [diamondT,L0,ofSix]; omega)
  have h2 := hr 0 2 (by simp [diamondT,ofSix]; omega)
  have h3 := hr 2 1 (by simp [diamondT,ofSix]; omega)
  omega

theorem unit_w_cyclic (A B C D E : Int) (h : Domain A B C D E) :
    ¬ Acyclic (unitW A B C D E) := by
  have hp := parameter_bounds A B C D E h
  obtain ⟨hA,hD,hE,hAB,hDB,hAC,hEC⟩ := h
  unfold H J L0 L at hp
  rintro ⟨rank, hr⟩
  have h1 := hr 1 0 (by simp [unitW,H,ofSix]; omega)
  have h2 := hr 0 2 (by simp [unitW,ofSix]; omega)
  have h3 := hr 2 1 (by simp [unitW,ofSix]; omega)
  omega

theorem unit_t_cyclic (A B C D E : Int) (h : Domain A B C D E) :
    ¬ Acyclic (unitT A B C D E) := by
  have hp := parameter_bounds A B C D E h
  obtain ⟨hA,hD,hE,hAB,hDB,hAC,hEC⟩ := h
  unfold H J L0 L at hp
  rintro ⟨rank, hr⟩
  have h1 := hr 1 0 (by simp [unitT,L,ofSix]; omega)
  have h2 := hr 0 3 (by simp [unitT,ofSix]; omega)
  have h3 := hr 3 1 (by simp [unitT,ofSix]; omega)
  omega

theorem unit_tp_cyclic (A B C D E : Int) (h : Domain A B C D E) :
    ¬ Acyclic (unitTP A B C D E) := by
  have hp := parameter_bounds A B C D E h
  obtain ⟨hA,hD,hE,hAB,hDB,hAC,hEC⟩ := h
  unfold H J L0 L at hp
  rintro ⟨rank, hr⟩
  have h1 := hr 1 0 (by simp [unitTP,L,ofSix]; omega)
  have h2 := hr 0 3 (by simp [unitTP,ofSix]; omega)
  have h3 := hr 3 1 (by simp [unitTP,ofSix]; omega)
  omega

theorem unit_wp_cyclic (A B C D E : Int) (h : Domain A B C D E) :
    ¬ Acyclic (unitWP A B C D E) := by
  have hp := parameter_bounds A B C D E h
  obtain ⟨hA,hD,hE,hAB,hDB,hAC,hEC⟩ := h
  unfold H J L0 L at hp
  rintro ⟨rank, hr⟩
  have h1 := hr 1 0 (by simp [unitWP,J,ofSix]; omega)
  have h2 := hr 0 2 (by simp [unitWP,ofSix]; omega)
  have h3 := hr 2 1 (by simp [unitWP,ofSix]; omega)
  omega

theorem isRoot_skew {Q : Matrix 4} {r : Fin 4} (h : IsRoot Q r) : SkewSymmetric Q := by
  induction h with
  | basic A B C D E ε _ _ => exact ofSix_skew A (-D) (-E) B C ε
  | relabelled _ p ih => exact relabel_skew _ p ih
  | reversed _ ih => exact reverse_skew _ ih

theorem isRoot_cyclic {Q : Matrix 4} {r : Fin 4} (h : IsRoot Q r) : ¬ Acyclic Q := by
  induction h with
  | basic A B C D E ε h _ => exact root_cyclic A B C D E ε h
  | relabelled _ p ih => exact fun ha => ih ((acyclic_relabel_iff _ p).mp ha)
  | reversed h ih => exact fun ha => ih ((acyclic_reverse_iff _ (isRoot_skew h)).mp ha)

theorem diamond_w2_two (A B C D E : Int) (h : Domain A B C D E) :
    mutate (diamondW2 A B C D E) 2 = root A B C D E 0 := by
  rw [← diamond_root_two A B C D E h, mutation_involutive]

theorem diamond_w3_three (A B C D E : Int) (h : Domain A B C D E) :
    mutate (diamondW3 A B C D E) 3 = root A B C D E 0 := by
  rw [← diamond_root_three A B C D E h, mutation_involutive]

theorem diamond_t_two (A B C D E : Int) (h : Domain A B C D E) :
    mutate (diamondT A B C D E) 2 = diamondW3 A B C D E := by
  rw [← diamond_w3_two A B C D E h, mutation_involutive]

theorem diamond_t_three (A B C D E : Int) (h : Domain A B C D E) :
    mutate (diamondT A B C D E) 3 = diamondW2 A B C D E := by
  rw [← diamond_w2_three A B C D E h, mutation_involutive]

theorem unit_w_two (A B C D E : Int) (h : Domain A B C D E) :
    mutate (unitW A B C D E) 2 = root A B C D E 1 := by
  rw [← unit_root_two A B C D E h, mutation_involutive]

theorem unit_t_three (A B C D E : Int) (h : Domain A B C D E) :
    mutate (unitT A B C D E) 3 = unitW A B C D E := by
  rw [← unit_w_three A B C D E h, mutation_involutive]

theorem unit_tp_two (A B C D E : Int) (h : Domain A B C D E) :
    mutate (unitTP A B C D E) 2 = unitT A B C D E := by
  rw [← unit_t_two A B C D E h, mutation_involutive]

theorem unit_wp_three (A B C D E : Int) (h : Domain A B C D E) :
    mutate (unitWP A B C D E) 3 = unitTP A B C D E := by
  rw [← unit_tp_three A B C D E h, mutation_involutive]

theorem root_special_swap (A B C D E : Int) :
    relabel (root A B C D E 1) frame0132 = root A C B E D (-1) := by
  funext i j
  rcases fin4 i with rfl | rfl | rfl | rfl <;>
    rcases fin4 j with rfl | rfl | rfl | rfl <;>
    simp [relabel,frame0132,root,ofSix]

theorem unit_root_three (A B C D E : Int) (h : Domain A B C D E) :
    mutate (root A B C D E 1) 3 = relabel (unitWP A B C D E) frame0132 := by
  obtain ⟨hA,hD,hE,hAB,hDB,hAC,hEC⟩ := h
  funext i j
  rcases fin4 i with rfl | rfl | rfl | rfl <;>
    rcases fin4 j with rfl | rfl | rfl | rfl <;>
    simp [mutate,correction,relabel,frame0132,root,unitWP,J,ofSix] <;> grind

/-- Five alternating special mutations give the exact special swap,
including the sign of the unit edge. -/
theorem pentagon_special_swap (A B C D E : Int) (h : Domain A B C D E) :
    applyWord (root A B C D E 1) [2,3,2,3,2] =
      relabel (root A B C D E 1) frame0132 := by
  simp only [applyWord,unit_root_two A B C D E h,unit_w_three A B C D E h,
    unit_t_two A B C D E h,unit_tp_three A B C D E h,unit_wp_two A B C D E h]
  exact (root_special_swap A B C D E).symm

end QuiverProofs.Regions
