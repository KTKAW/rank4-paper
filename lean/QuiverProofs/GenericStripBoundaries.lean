import QuiverProofs.GenericStrip

/-! All eight exterior transitions of the generic multiplicity strip.
The parameter domain is unbounded. These are the inherited strict fork and
unit-root predicates, with the entering vertex as the return. -/
namespace QuiverProofs.GenericStripBoundaries
open GenericStrip

private theorem fin4 (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega

def sideD (m a c : Int) : Int := m*nextB m a c-a
def sideE (m a b c : Int) : Int := (m+1)*nextA m a b c-a-b

private theorem bounds (m a b c : Int) (h : Domain m a b c) :
    2 ≤ m ∧ m+1 < a ∧ 2 ≤ b ∧ 2 ≤ c ∧
    a < nextB m a c ∧ nextB m a c < sideD m a c ∧
    a+b < nextA m a b c ∧ nextA m a b c < sideE m a b c ∧
    2 ≤ nextC m a b c := by
  have hp := parameter_bounds m a b c h
  have hg := growth m a b c h
  have hn := preserves_domain m a b c h
  obtain ⟨hm,hmb,hbc,hca⟩ := h
  have hD := Int.mul_le_mul_of_nonneg_right hm
    (show 0 ≤ nextB m a c by omega)
  have hE := Int.mul_le_mul_of_nonneg_right (show 3 ≤ m+1 by omega)
    (show 0 ≤ nextA m a b c by omega)
  unfold sideD sideE Domain at *
  omega

private theorem product_sub (x y z : Int) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (_hzx : z < x) (hzy : z < y) : x < x*y-z ∧ y < x*y-z := by
  have h1 := Int.mul_le_mul_of_nonneg_left hy (show 0 ≤ x by omega)
  have h2 := Int.mul_le_mul_of_nonneg_right hx (show 0 ≤ y by omega)
  constructor <;> omega

private def frame3201 : Relabeling 4 :=
  ⟨fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | _ => 1,
   fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | _ => 0, by decide, by decide⟩

private def frame3012 : Relabeling 4 :=
  ⟨fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | _ => 2,
   fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | _ => 0, by decide, by decide⟩

private def frame3102 : Relabeling 4 :=
  ⟨fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 0 | _ => 2,
   fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 3 | _ => 0, by decide, by decide⟩

private def frame0231 : Relabeling 4 :=
  ⟨fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | _ => 1,
   fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | _ => 2, by decide, by decide⟩

private def frame3021 : Relabeling 4 :=
  ⟨fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | _ => 1,
   fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | _ => 0, by decide, by decide⟩

private def frame1023 : Relabeling 4 :=
  ⟨fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | _ => 3,
   fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | _ => 3, by decide, by decide⟩

private def frame3120 : Relabeling 4 :=
  ⟨fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | _ => 0,
   fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | _ => 0, by decide, by decide⟩

theorem root_three_domain (m a b c : Int) (h : Domain m a b c) :
    Regions.Domain (c) (a*c-m) (b*c-1) (a) (b) := by
  have hb := bounds m a b c h
  have hd := h
  unfold Domain at hd
  have hp0 := product_sub (a) (c) (m) (by omega) (by omega) (by omega) (by omega)
  have hp1 := product_sub (b) (c) (1) (by omega) (by omega) (by omega) (by omega)
  unfold Regions.Domain
  omega

theorem root_three (m a b c : Int) (h : Domain m a b c) :
    Regions.IsRoot (mutate (root m a b c) 3) 3 := by
  have hb := bounds m a b c h
  have hp := parameter_bounds m a b c h
  have hd := h
  unfold Domain at hd
  have heq : relabel (reverse (mutate (root m a b c) 3)) frame3201 =
      Regions.root (c) (a*c-m) (b*c-1) (a) (b) (1) := by
    funext i j
    rcases fin4 i with rfl|rfl|rfl|rfl <;>
      rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [relabel, reverse, frame3201, Regions.root, root, mutate, correction, ofSix] <;> grind
  have hf : Regions.IsRoot (relabel (reverse (mutate (root m a b c) 3)) frame3201) 0 := by
    rw [heq]
    exact Regions.IsRoot.basic _ _ _ _ _ _ (root_three_domain m a b c h) (Or.inr rfl)
  exact Regions.root_of_reverse (Regions.root_of_relabel frame3201 hf)

theorem P_three_domain (m a b c : Int) (h : Domain m a b c) :
    Regions.Domain (a) (a*(a+b)-1) (a*nextB m a c-m) (a+b) (nextB m a c) := by
  have hb := bounds m a b c h
  have hd := h
  unfold Domain at hd
  have hp0 := product_sub (a) (a+b) (1) (by omega) (by omega) (by omega) (by omega)
  have hp1 := product_sub (a) (nextB m a c) (m) (by omega) (by omega) (by omega) (by omega)
  unfold Regions.Domain
  omega

theorem P_three (m a b c : Int) (h : Domain m a b c) :
    Regions.IsRoot (mutate (phaseP m a b c) 3) 3 := by
  have hb := bounds m a b c h
  have hp := parameter_bounds m a b c h
  have hd := h
  unfold Domain at hd
  have heq : relabel (reverse (mutate (phaseP m a b c) 3)) frame3012 =
      Regions.root (a) (a*(a+b)-1) (a*nextB m a c-m) (a+b) (nextB m a c) (1) := by
    funext i j
    rcases fin4 i with rfl|rfl|rfl|rfl <;>
      rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [relabel, reverse, frame3012, Regions.root, phaseP, mutate, correction, ofSix] <;> grind
  have hf : Regions.IsRoot (relabel (reverse (mutate (phaseP m a b c) 3)) frame3012) 0 := by
    rw [heq]
    exact Regions.IsRoot.basic _ _ _ _ _ _ (P_three_domain m a b c h) (Or.inr rfl)
  exact Regions.root_of_reverse (Regions.root_of_relabel frame3012 hf)

theorem Q_three_domain (m a b c : Int) (h : Domain m a b c) :
    Forks.Domain (a+b) (b) (nextC m a b c) (b*(a+b)-1) (nextC m a b c*(a+b)-1) (m) := by
  have hb := bounds m a b c h
  have hd := h
  unfold Domain at hd
  have hp0 := product_sub (b) (a+b) (1) (by omega) (by omega) (by omega) (by omega)
  have hp1 := product_sub (nextC m a b c) (a+b) (1) (by omega) (by omega) (by omega) (by omega)
  unfold Forks.Domain
  omega

theorem Q_three (m a b c : Int) (h : Domain m a b c) :
    Forks.IsFork (mutate (phaseQ m a b c) 3) 3 := by
  have hb := bounds m a b c h
  have hp := parameter_bounds m a b c h
  have hd := h
  unfold Domain at hd
  have heq : relabel (mutate (phaseQ m a b c) 3) frame3102 =
      Forks.template (a+b) (b) (nextC m a b c) (b*(a+b)-1) (nextC m a b c*(a+b)-1) (m) := by
    funext i j
    rcases fin4 i with rfl|rfl|rfl|rfl <;>
      rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [relabel, frame3102, Forks.template, phaseQ, mutate, correction, ofSix] <;> grind
  have hf : Forks.IsFork (relabel (mutate (phaseQ m a b c) 3) frame3102) 0 := by
    rw [heq]
    exact Forks.IsFork.basic _ _ _ _ _ _ (Q_three_domain m a b c h)
  exact Forks.fork_of_relabel frame3102 hf

theorem S_zero_domain (m a b c : Int) (h : Domain m a b c) :
    Forks.Domain (m) (sideD m a c) (m+1) (m*sideD m a c-nextB m a c) (m*(m+1)-1) (a+b) := by
  have hb := bounds m a b c h
  have hd := h
  unfold Domain at hd
  have hp0 := Forks.product_sub_dominates (m) (sideD m a c) (nextB m a c) (by omega) (by omega) (by omega)
  have hp1 := product_sub (m) (m+1) (1) (by omega) (by omega) (by omega) (by omega)
  unfold Forks.Domain
  omega

theorem S_zero (m a b c : Int) (h : Domain m a b c) :
    Forks.IsFork (mutate (phaseS m a b c) 0) 0 := by
  have hb := bounds m a b c h
  have hp := parameter_bounds m a b c h
  have hd := h
  unfold Domain at hd
  have heq : relabel (reverse (mutate (phaseS m a b c) 0)) frame0231 =
      Forks.template (m) (sideD m a c) (m+1) (m*sideD m a c-nextB m a c) (m*(m+1)-1) (a+b) := by
    funext i j
    rcases fin4 i with rfl|rfl|rfl|rfl <;>
      rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [relabel, reverse, frame0231, Forks.template, phaseS, sideD, mutate, correction, ofSix] <;> grind
  have hf : Forks.IsFork (relabel (reverse (mutate (phaseS m a b c) 0)) frame0231) 0 := by
    rw [heq]
    exact Forks.IsFork.basic _ _ _ _ _ _ (S_zero_domain m a b c h)
  exact Forks.fork_of_reverse (Forks.fork_of_relabel frame0231 hf)

theorem S_three_domain (m a b c : Int) (h : Domain m a b c) :
    Forks.Domain (nextB m a c) (sideD m a c) (a+b) (sideD m a c*nextB m a c-m) (1+(a+b)*nextB m a c) (m+1) := by
  have hb := bounds m a b c h
  have hd := h
  unfold Domain at hd
  have hp0 := product_sub (sideD m a c) (nextB m a c) (m) (by omega) (by omega) (by omega) (by omega)
  have hp1 := product_sub (a+b) (nextB m a c) (-1) (by omega) (by omega) (by omega) (by omega)
  unfold Forks.Domain
  omega

theorem S_three (m a b c : Int) (h : Domain m a b c) :
    Forks.IsFork (mutate (phaseS m a b c) 3) 3 := by
  have hb := bounds m a b c h
  have hp := parameter_bounds m a b c h
  have hd := h
  unfold Domain at hd
  have heq : relabel (mutate (phaseS m a b c) 3) frame3201 =
      Forks.template (nextB m a c) (sideD m a c) (a+b) (sideD m a c*nextB m a c-m) (1+(a+b)*nextB m a c) (m+1) := by
    funext i j
    rcases fin4 i with rfl|rfl|rfl|rfl <;>
      rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [relabel, frame3201, Forks.template, phaseS, sideD, mutate, correction, ofSix] <;> grind
  have hf : Forks.IsFork (relabel (mutate (phaseS m a b c) 3) frame3201) 0 := by
    rw [heq]
    exact Forks.IsFork.basic _ _ _ _ _ _ (S_three_domain m a b c h)
  exact Forks.fork_of_relabel frame3201 hf

theorem T_three_domain (m a b c : Int) (h : Domain m a b c) :
    Regions.Domain (nextA m a b c) (1+nextA m a b c*nextB m a c) (nextA m a b c*(a+b)-m-1) (nextB m a c) (a+b) := by
  have hb := bounds m a b c h
  have hd := h
  unfold Domain at hd
  have hp0 := product_sub (nextA m a b c) (nextB m a c) (-1) (by omega) (by omega) (by omega) (by omega)
  have hp1 := product_sub (nextA m a b c) (a+b) (m+1) (by omega) (by omega) (by omega) (by omega)
  unfold Regions.Domain
  omega

theorem T_three (m a b c : Int) (h : Domain m a b c) :
    Regions.IsRoot (mutate (phaseT m a b c) 3) 3 := by
  have hb := bounds m a b c h
  have hp := parameter_bounds m a b c h
  have hd := h
  unfold Domain at hd
  have heq : relabel (mutate (phaseT m a b c) 3) frame3021 =
      Regions.root (nextA m a b c) (1+nextA m a b c*nextB m a c) (nextA m a b c*(a+b)-m-1) (nextB m a c) (a+b) (1) := by
    funext i j
    rcases fin4 i with rfl|rfl|rfl|rfl <;>
      rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [relabel, frame3021, Regions.root, phaseT, mutate, correction, ofSix] <;> grind
  have hf : Regions.IsRoot (relabel (mutate (phaseT m a b c) 3) frame3021) 0 := by
    rw [heq]
    exact Regions.IsRoot.basic _ _ _ _ _ _ (T_three_domain m a b c h) (Or.inr rfl)
  exact Regions.root_of_relabel frame3021 hf

theorem V_one_domain (m a b c : Int) (h : Domain m a b c) :
    Forks.Domain (m+1) (m) (sideE m a b c) (m*(m+1)-1) ((m+1)*sideE m a b c-nextA m a b c) (nextB m a c) := by
  have hb := bounds m a b c h
  have hd := h
  unfold Domain at hd
  have hp0 := product_sub (m) (m+1) (1) (by omega) (by omega) (by omega) (by omega)
  have hp1 := Forks.product_sub_dominates (m+1) (sideE m a b c) (nextA m a b c) (by omega) (by omega) (by omega)
  unfold Forks.Domain
  omega

theorem V_one (m a b c : Int) (h : Domain m a b c) :
    Forks.IsFork (mutate (phaseV m a b c) 1) 1 := by
  have hb := bounds m a b c h
  have hp := parameter_bounds m a b c h
  have hd := h
  unfold Domain at hd
  have heq : relabel (reverse (mutate (phaseV m a b c) 1)) frame1023 =
      Forks.template (m+1) (m) (sideE m a b c) (m*(m+1)-1) ((m+1)*sideE m a b c-nextA m a b c) (nextB m a c) := by
    funext i j
    rcases fin4 i with rfl|rfl|rfl|rfl <;>
      rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [relabel, reverse, frame1023, Forks.template, phaseV, sideE, mutate, correction, ofSix] <;> grind
  have hf : Forks.IsFork (relabel (reverse (mutate (phaseV m a b c) 1)) frame1023) 0 := by
    rw [heq]
    exact Forks.IsFork.basic _ _ _ _ _ _ (V_one_domain m a b c h)
  exact Forks.fork_of_reverse (Forks.fork_of_relabel frame1023 hf)

theorem V_three_domain (m a b c : Int) (h : Domain m a b c) :
    Regions.Domain (sideE m a b c) (m+nextB m a c*sideE m a b c) (nextA m a b c*sideE m a b c-m-1) (nextB m a c) (nextA m a b c) := by
  have hb := bounds m a b c h
  have hd := h
  unfold Domain at hd
  have hp0 := product_sub (nextB m a c) (sideE m a b c) (-m) (by omega) (by omega) (by omega) (by omega)
  have hp1 := product_sub (nextA m a b c) (sideE m a b c) (m+1) (by omega) (by omega) (by omega) (by omega)
  unfold Regions.Domain
  omega

theorem V_three (m a b c : Int) (h : Domain m a b c) :
    Regions.IsRoot (mutate (phaseV m a b c) 3) 3 := by
  have hb := bounds m a b c h
  have hp := parameter_bounds m a b c h
  have hd := h
  unfold Domain at hd
  have heq : relabel (mutate (phaseV m a b c) 3) frame3120 =
      Regions.root (sideE m a b c) (m+nextB m a c*sideE m a b c) (nextA m a b c*sideE m a b c-m-1) (nextB m a c) (nextA m a b c) (1) := by
    funext i j
    rcases fin4 i with rfl|rfl|rfl|rfl <;>
      rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [relabel, frame3120, Regions.root, phaseV, sideE, mutate, correction, ofSix] <;> grind
  have hf : Regions.IsRoot (relabel (mutate (phaseV m a b c) 3) frame3120) 0 := by
    rw [heq]
    exact Regions.IsRoot.basic _ _ _ _ _ _ (V_three_domain m a b c h) (Or.inr rfl)
  exact Regions.root_of_relabel frame3120 hf

end QuiverProofs.GenericStripBoundaries
