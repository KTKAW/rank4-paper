import QuiverProofs.Symmetry

namespace QuiverProofs.Forks

/-- A normalized rank-four fork with return vertex 0, incoming side {1},
outgoing side {2,3}, and the edge 2→3. Relabeling and reversal supply all frames. -/
def template (a b c d e f : Int) : Matrix 4 := ofSix (-a) b c (-d) (-e) f

def Domain (a b c d e f : Int) : Prop :=
  2 ≤ a ∧ 2 ≤ b ∧ 2 ≤ c ∧ a < d ∧ b < d ∧ a < e ∧ c < e ∧ 2 ≤ f

private theorem fin4 (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega

def swap01 : Relabeling 4 :=
  ⟨fun i => match i.val with | 0 => 1 | 1 => 0 | _ => i,
   fun i => match i.val with | 0 => 1 | 1 => 0 | _ => i,
   by decide, by decide⟩

def rotate2013 : Relabeling 4 :=
  ⟨fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 1 | _ => 3,
   fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 0 | _ => 3,
   by decide, by decide⟩

def rotate3102 : Relabeling 4 :=
  ⟨fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 0 | _ => 2,
   fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 3 | _ => 0,
   by decide, by decide⟩

theorem template_cyclic (a b c d e f : Int) (h : Domain a b c d e f) :
    ¬ Acyclic (template a b c d e f) := by
  rintro ⟨rank, hr⟩
  obtain ⟨ha,hb,hc,had,hbd,hae,hce,hf⟩ := h
  have h10 := hr 1 0 (by simp [template,ofSix]; omega)
  have h02 := hr 0 2 (by simp [template,ofSix]; omega)
  have h21 := hr 2 1 (by simp [template,ofSix]; omega)
  omega

theorem mutate_one (a b c d e f : Int) (h : Domain a b c d e f) :
    relabel (mutate (template a b c d e f) 1) swap01 =
      template a d e (a*d-b) (a*e-c) f := by
  obtain ⟨ha,hb,hc,had,hbd,hae,hce,hf⟩ := h
  funext i j
  rcases fin4 i with rfl | rfl | rfl | rfl <;>
    rcases fin4 j with rfl | rfl | rfl | rfl <;>
    simp [relabel,swap01,template,mutate,ofSix,correction] <;> grind

theorem mutate_two (a b c d e f : Int) (h : Domain a b c d e f) :
    relabel (reverse (mutate (template a b c d e f) 2)) rotate2013 =
      template b d f (b*d-a) (c+b*f) e := by
  obtain ⟨ha,hb,hc,had,hbd,hae,hce,hf⟩ := h
  funext i j
  rcases fin4 i with rfl | rfl | rfl | rfl <;>
    rcases fin4 j with rfl | rfl | rfl | rfl <;>
    simp [relabel,reverse,rotate2013,template,mutate,ofSix,correction] <;> grind

theorem mutate_three (a b c d e f : Int) (h : Domain a b c d e f) :
    relabel (mutate (template a b c d e f) 3) rotate3102 =
      template e c f (c*e-a) (d+e*f) b := by
  obtain ⟨ha,hb,hc,had,hbd,hae,hce,hf⟩ := h
  funext i j
  rcases fin4 i with rfl | rfl | rfl | rfl <;>
    rcases fin4 j with rfl | rfl | rfl | rfl <;>
    simp [relabel,rotate3102,template,mutate,ofSix,correction] <;> grind

theorem product_sub_dominates (x y z : Int) (hx : 2 ≤ x)
    (hxy : x < y) (hzy : z < y) : x < x*y-z ∧ y < x*y-z := by
  have hprod := Int.mul_le_mul_of_nonneg_right hx (show 0 ≤ y by omega)
  constructor <;> omega

theorem product_add_dominates (x y z : Int) (hx : 2 ≤ x)
    (hy : 2 ≤ y) (hz : 0 ≤ z) : x < z+x*y ∧ y < z+x*y := by
  have hxprod := Int.mul_le_mul_of_nonneg_left hy (show 0 ≤ x by omega)
  have hyprod := Int.mul_le_mul_of_nonneg_right hx (show 0 ≤ y by omega)
  constructor <;> omega

theorem domain_one (a b c d e f : Int) (h : Domain a b c d e f) :
    Domain a d e (a*d-b) (a*e-c) f := by
  obtain ⟨ha,hb,hc,had,hbd,hae,hce,hf⟩ := h
  have hd := product_sub_dominates a d b ha had hbd
  have he := product_sub_dominates a e c ha hae hce
  unfold Domain; omega

theorem domain_two (a b c d e f : Int) (h : Domain a b c d e f) :
    Domain b d f (b*d-a) (c+b*f) e := by
  obtain ⟨ha,hb,hc,had,hbd,hae,hce,hf⟩ := h
  have hd := product_sub_dominates b d a hb hbd had
  have he := product_add_dominates b f c hb hf (by omega)
  unfold Domain; omega

theorem domain_three (a b c d e f : Int) (h : Domain a b c d e f) :
    Domain e c f (c*e-a) (d+e*f) b := by
  obtain ⟨ha,hb,hc,had,hbd,hae,hce,hf⟩ := h
  have hd := product_sub_dominates c e a hc hce hae
  have he := product_add_dominates e f d (by omega) hf (by omega)
  unfold Domain; omega

/-- Explicit framed fork witnesses. Every witness is built from the displayed
inequalities and actual vertex permutations; no external continuation axiom. -/
inductive IsFork : Matrix 4 → Fin 4 → Prop
  | basic (a b c d e f : Int) : Domain a b c d e f → IsFork (template a b c d e f) 0
  | relabelled {B : Matrix 4} {r : Fin 4} : IsFork B r → (p : Relabeling 4) →
      IsFork (relabel B p) (p.invFun r)
  | reversed {B : Matrix 4} {r : Fin 4} : IsFork B r → IsFork (reverse B) r

theorem fork_skew {B : Matrix 4} {r : Fin 4} (h : IsFork B r) : SkewSymmetric B := by
  induction h with
  | basic a b c d e f _ => exact ofSix_skew (-a) b c (-d) (-e) f
  | relabelled _ p ih => exact relabel_skew _ p ih
  | reversed _ ih => exact reverse_skew _ ih

theorem fork_cyclic {B : Matrix 4} {r : Fin 4} (h : IsFork B r) : ¬ Acyclic B := by
  induction h with
  | basic a b c d e f h => exact template_cyclic a b c d e f h
  | relabelled _ p ih => exact fun ha => ih ((acyclic_relabel_iff _ p).mp ha)
  | reversed h ih => exact fun ha => ih ((acyclic_reverse_iff _ (fork_skew h)).mp ha)

theorem fork_of_relabel {B : Matrix 4} (p : Relabeling 4) {r : Fin 4}
    (h : IsFork (relabel B p) r) : IsFork B (p.toFun r) := by
  have h' := IsFork.relabelled h p.symm
  rw [relabel_inverse] at h'
  exact h'

theorem fork_of_reverse {B : Matrix 4} {r : Fin 4}
    (h : IsFork (reverse B) r) : IsFork B r := by
  simpa only [reverse_involutive] using IsFork.reversed h

/-- The rank-four fork continuation theorem, proved for every framed witness. -/
theorem fork_continuation {B : Matrix 4} {r : Fin 4} (h : IsFork B r)
    (k : Fin 4) (hk : k ≠ r) : IsFork (mutate B k) k := by
  induction h generalizing k with
  | basic a b c d e f h =>
    rcases fin4 k with rfl | rfl | rfl | rfl
    · exact False.elim (hk rfl)
    · have ht : IsFork (relabel (mutate (template a b c d e f) 1) swap01) 0 := by
        rw [mutate_one a b c d e f h]
        exact IsFork.basic _ _ _ _ _ _ (domain_one a b c d e f h)
      exact fork_of_relabel swap01 ht
    · have ht : IsFork (relabel (reverse (mutate (template a b c d e f) 2)) rotate2013) 0 := by
        rw [mutate_two a b c d e f h]
        exact IsFork.basic _ _ _ _ _ _ (domain_two a b c d e f h)
      exact fork_of_reverse (fork_of_relabel rotate2013 ht)
    · have ht : IsFork (relabel (mutate (template a b c d e f) 3) rotate3102) 0 := by
        rw [mutate_three a b c d e f h]
        exact IsFork.basic _ _ _ _ _ _ (domain_three a b c d e f h)
      exact fork_of_relabel rotate3102 ht
  | @relabelled B r h p ih =>
    have hpk : p.toFun k ≠ r := by
      intro heq
      have := congrArg p.invFun heq
      simp only [p.left_inv] at this
      exact hk this
    have hnew := IsFork.relabelled (ih (p.toFun k) hpk) p
    simpa only [p.left_inv, mutate_relabel] using hnew
  | @reversed B r h ih =>
    simpa only [mutate_reverse] using IsFork.reversed (ih k hk)

/-- A cyclic core together with arbitrarily many justified fork attachments. -/
inductive Shield (core : Matrix 4 → Prop) : Matrix 4 → Prop
  | central {B : Matrix 4} : core B → Shield core B
  | branch {B : Matrix 4} (r : Fin 4) : Shield core B → IsFork (mutate B r) r →
      Shield core (mutate B r)

theorem shield_cyclic (core : Matrix 4 → Prop)
    (hc : ∀ B, core B → ¬ Acyclic B) {B : Matrix 4} (h : Shield core B) :
    ¬ Acyclic B := by
  cases h with
  | central h => exact hc _ h
  | branch _ _ hfork => exact fork_cyclic hfork

theorem shield_closed (core : Matrix 4 → Prop)
    (hedge : ∀ B, core B → ∀ k, core (mutate B k) ∨ IsFork (mutate B k) k)
    {B : Matrix 4} (h : Shield core B) (k : Fin 4) : Shield core (mutate B k) := by
  induction h with
  | central h =>
    rcases hedge _ h k with hc | hf
    · exact Shield.central hc
    · exact Shield.branch k (Shield.central h) hf
  | @branch B r h hf ih =>
    by_cases hk : k = r
    · subst k
      simpa only [mutation_involutive] using h
    · exact Shield.branch k (Shield.branch r h hf) (fork_continuation hf k hk)

/-- Soundness of every cyclic-core/fork-boundary certificate, including infinite
mutation words' finite prefixes and all possible returns. -/
theorem fork_shield_NMA (core : Matrix 4 → Prop)
    (hc : ∀ B, core B → ¬ Acyclic B)
    (hedge : ∀ B, core B → ∀ k, core (mutate B k) ∨ IsFork (mutate B k) k)
    (B : Matrix 4) (hB : core B) : ¬ MutationAcyclic B := by
  have allWords : ∀ word, ∀ C, Shield core C → Shield core (applyWord C word) := by
    intro word
    induction word with
    | nil => intro C h; exact h
    | cons k ks ih =>
      intro C h
      exact ih (mutate C k) (shield_closed core hedge h k)
  rintro ⟨word, ha⟩
  exact shield_cyclic core hc (allWords word B (Shield.central hB)) ha

def FramedCore {m : Nat} (node : Fin m → Matrix 4) (B : Matrix 4) : Prop :=
  ∃ i : Fin m, ∃ p : Relabeling 4, B = relabel (node i) p

theorem framed_relabel {m : Nat} (node : Fin m → Matrix 4) {B : Matrix 4}
    (h : FramedCore node B) (p : Relabeling 4) : FramedCore node (relabel B p) := by
  obtain ⟨i,q,rfl⟩ := h
  exact ⟨i,q.trans p,rfl⟩

/-- A finite core need only list one frame of each node. The proof covers all
vertex permutations and all infinite fork continuations automatically. -/
theorem framed_core_NMA {m : Nat} (node : Fin m → Matrix 4)
    (hc : ∀ i, ¬ Acyclic (node i))
    (he : ∀ i k, FramedCore node (mutate (node i) k) ∨ IsFork (mutate (node i) k) k)
    (i : Fin m) : ¬ MutationAcyclic (node i) := by
  apply fork_shield_NMA (FramedCore node)
  · intro B h
    obtain ⟨j,p,rfl⟩ := h
    exact fun ha => hc j ((acyclic_relabel_iff _ p).mp ha)
  · intro B h k
    obtain ⟨j,p,rfl⟩ := h
    rw [mutate_relabel]
    rcases he j (p.toFun k) with hcore | hfork
    · exact Or.inl (framed_relabel node hcore p)
    · have hnew := IsFork.relabelled hfork p
      exact Or.inr (by simpa only [p.left_inv] using hnew)
  · exact ⟨i,.identity 4,rfl⟩

end QuiverProofs.Forks
