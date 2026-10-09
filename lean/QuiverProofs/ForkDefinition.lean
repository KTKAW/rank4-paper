import QuiverProofs.FiniteLogic
import QuiverProofs.Greedy

set_option maxHeartbeats 2000000
namespace QuiverProofs.ForkDefinition

/-- A topological ranking on the subquiver induced by a vertex predicate. -/
def AcyclicOn (B : Matrix 4) (vertices : Fin 4 → Prop) : Prop :=
  ∃ rank : Fin 4 → Nat, ∀ i j, vertices i → vertices j → 0 < B i j → rank i < rank j

/-- Warkentin's graph-theoretic fork definition at a specified return vertex:
cyclic, abundant, acyclic incoming/outgoing subquivers, and both strict
cross-edge inequalities. Skew symmetry records the ambient exchange-matrix domain. -/
def GraphFork (B : Matrix 4) (r : Fin 4) : Prop :=
  SkewSymmetric B ∧ ¬ Acyclic B ∧ Cone.Abundant B ∧
  AcyclicOn B (fun i => 0 < B i r) ∧ AcyclicOn B (fun i => 0 < B r i) ∧
  ∀ i j, 0 < B i r → 0 < B r j → B i r < B j i ∧ B r j < B j i

private theorem fin4 (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega

theorem acyclicOn_reverse (B : Matrix 4) (vertices : Fin 4 → Prop)
    (hs : SkewSymmetric B) (h : AcyclicOn B vertices) : AcyclicOn (reverse B) vertices := by
  rcases h with ⟨rank,hr⟩
  obtain ⟨bound,hb⟩ := finite_rank_bound 4 rank
  refine ⟨fun i => bound-rank i,?_⟩
  intro i j hi hj hij
  have hji : 0 < B j i := by have := hs i j; simp only [reverse] at hij; omega
  have hrji := hr j i hj hi hji
  have hbi := hb i
  have hbj := hb j
  dsimp
  omega

theorem graphFork_relabel (B : Matrix 4) (r : Fin 4) (h : GraphFork B r) (p : Relabeling 4) :
    GraphFork (relabel B p) (p.invFun r) := by
  rcases h with ⟨hs,hc,ha,⟨rin,hin⟩,⟨rout,hout⟩,hx⟩
  refine ⟨relabel_skew _ _ hs,fun h => hc ((acyclic_relabel_iff _ p).mp h),?_,?_,?_,?_⟩
  · intro i j hij
    exact ha _ _ (fun hh => hij (p.injective hh))
  · refine ⟨rin ∘ p.toFun,?_⟩
    intro i j hi hj hij
    simp only [relabel,p.right_inv] at hi hj hij
    exact hin _ _ hi hj hij
  · refine ⟨rout ∘ p.toFun,?_⟩
    intro i j hi hj hij
    simp only [relabel,p.right_inv] at hi hj hij
    exact hout _ _ hi hj hij
  · intro i j hi hj
    simp only [relabel,p.right_inv] at hi hj ⊢
    exact hx _ _ hi hj

theorem graphFork_reverse (B : Matrix 4) (r : Fin 4) (h : GraphFork B r) :
    GraphFork (reverse B) r := by
  rcases h with ⟨hs,hc,ha,hin,hout,hx⟩
  refine ⟨reverse_skew _ hs,fun h => hc ((acyclic_reverse_iff _ hs).mp h),?_,?_,?_,?_⟩
  · intro i j hij
    simpa [reverse] using ha i j hij
  · rcases acyclicOn_reverse B (fun i => 0 < B r i) hs hout with ⟨rank,hr⟩
    refine ⟨rank,?_⟩
    intro i j hi hj hij
    have hi' : 0 < B r i := by have := hs i r; simp only [reverse] at hi; omega
    have hj' : 0 < B r j := by have := hs j r; simp only [reverse] at hj; omega
    exact hr i j hi' hj' hij
  · rcases acyclicOn_reverse B (fun i => 0 < B i r) hs hin with ⟨rank,hr⟩
    refine ⟨rank,?_⟩
    intro i j hi hj hij
    have hi' : 0 < B i r := by have := hs i r; simp only [reverse] at hi; omega
    have hj' : 0 < B j r := by have := hs j r; simp only [reverse] at hj; omega
    exact hr i j hi' hj' hij
  · intro i j hi hj
    have hi' : 0 < B r i := by have := hs i r; simp only [reverse] at hi; omega
    have hj' : 0 < B j r := by have := hs j r; simp only [reverse] at hj; omega
    have hh := hx j i hj' hi'
    have hsj := hs j r
    have hsi := hs r i
    have hsij := hs i j
    simp only [reverse]
    omega

theorem template_graphFork (a b c d e f : Int) (h : Forks.Domain a b c d e f) :
    GraphFork (Forks.template a b c d e f) 0 := by
  have hf := Forks.IsFork.basic a b c d e f h
  refine ⟨Forks.fork_skew hf,Forks.fork_cyclic hf,FiniteLogic.fork_abundant hf,?_,?_,?_⟩
  all_goals rcases h with ⟨ha,hb,hc,had,hbd,hae,hce,hf⟩
  · refine ⟨fun _ => 0,?_⟩
    intro i j hi hj hij
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [Forks.template,ofSix] at * <;> omega
  · refine ⟨fun i => i.val,?_⟩
    intro i j hi hj hij
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [Forks.template,ofSix] at * <;> omega
  · intro i j hi hj
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [Forks.template,ofSix] at * <;> omega

theorem framed_fork_is_graphFork {B : Matrix 4} {r : Fin 4} (h : Forks.IsFork B r) : GraphFork B r := by
  induction h with
  | basic a b c d e f h => exact template_graphFork a b c d e f h
  | relabelled _ p ih => exact graphFork_relabel _ _ ih p
  | reversed _ ih => exact graphFork_reverse _ _ ih

private theorem large_natAbs_cases (x : Int) (h : 2 ≤ x.natAbs) : 2 ≤ x ∨ x ≤ -2 := by
  by_cases hx : 0 ≤ x
  · have := Int.natAbs_of_nonneg hx
    left
    omega
  · have := Int.ofNat_natAbs_of_nonpos (show x ≤ 0 by omega)
    right
    omega


private def frame0 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | _ => 3),(fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | _ => 3),by decide,by decide⟩

private def frame1 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | _ => 2),(fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | _ => 2),by decide,by decide⟩

private def frame2 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | _ => 3),(fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | _ => 3),by decide,by decide⟩

private def frame3 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | _ => 1),(fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | _ => 2),by decide,by decide⟩

private def frame4 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | _ => 2),(fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | _ => 1),by decide,by decide⟩

private def frame5 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | _ => 1),(fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | _ => 1),by decide,by decide⟩

/-- The finite orientation analysis needed to normalize any rank-four fork.
All magnitudes remain arbitrary integers. -/
theorem graphFork_normalize_zero (a b c d e f : Int)
    (h : GraphFork (ofSix a b c d e f) 0) : Forks.IsFork (ofSix a b c d e f) 0 := by
  rcases h with ⟨hs,hcyc,habund,⟨rin,hin⟩,⟨rout,hout⟩,hcross⟩
  have ha := large_natAbs_cases a (by simpa [ofSix] using habund 0 1 (by decide))
  have hb := large_natAbs_cases b (by simpa [ofSix] using habund 0 2 (by decide))
  have hc := large_natAbs_cases c (by simpa [ofSix] using habund 0 3 (by decide))
  have hd := large_natAbs_cases d (by simpa [ofSix] using habund 1 2 (by decide))
  have he := large_natAbs_cases e (by simpa [ofSix] using habund 1 3 (by decide))
  have hf := large_natAbs_cases f (by simpa [ofSix] using habund 2 3 (by decide))
  rcases ha with ha|ha <;> rcases hb with hb|hb <;> rcases hc with hc|hc <;>
    rcases hd with hd|hd <;> rcases he with he|he <;> rcases hf with hf|hf
  · exfalso
    apply hcyc
    refine ⟨(fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | _ => 3),?_⟩
    intro i j hij
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [ofSix] at hij ⊢ <;> omega
  · exfalso
    apply hcyc
    refine ⟨(fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | _ => 2),?_⟩
    intro i j hij
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [ofSix] at hij ⊢ <;> omega
  · exfalso
    have ht0 := hout 1 2 (by simp [ofSix]; omega) (by simp [ofSix]; omega) (by simp [ofSix]; omega)
    have ht1 := hout 2 3 (by simp [ofSix]; omega) (by simp [ofSix]; omega) (by simp [ofSix]; omega)
    have ht2 := hout 3 1 (by simp [ofSix]; omega) (by simp [ofSix]; omega) (by simp [ofSix]; omega)
    omega
  · exfalso
    apply hcyc
    refine ⟨(fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | _ => 1),?_⟩
    intro i j hij
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [ofSix] at hij ⊢ <;> omega
  · exfalso
    apply hcyc
    refine ⟨(fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | _ => 3),?_⟩
    intro i j hij
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [ofSix] at hij ⊢ <;> omega
  · exfalso
    have ht0 := hout 1 3 (by simp [ofSix]; omega) (by simp [ofSix]; omega) (by simp [ofSix]; omega)
    have ht1 := hout 3 2 (by simp [ofSix]; omega) (by simp [ofSix]; omega) (by simp [ofSix]; omega)
    have ht2 := hout 2 1 (by simp [ofSix]; omega) (by simp [ofSix]; omega) (by simp [ofSix]; omega)
    omega
  · exfalso
    apply hcyc
    refine ⟨(fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | _ => 2),?_⟩
    intro i j hij
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [ofSix] at hij ⊢ <;> omega
  · exfalso
    apply hcyc
    refine ⟨(fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | _ => 1),?_⟩
    intro i j hij
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [ofSix] at hij ⊢ <;> omega
  · have hc0 := hcross 3 1 (by simp [ofSix]; omega) (by simp [ofSix]; omega)
    have hc1 := hcross 3 2 (by simp [ofSix]; omega) (by simp [ofSix]; omega)
    simp [ofSix] at hc0 hc1
    have hdom : Forks.Domain (-c) a b e f d := by unfold Forks.Domain; omega
    have heq : relabel (ofSix a b c d e f) frame4 = Forks.template (-c) a b e f d := by
      funext i j
      rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
        simp [relabel,frame4,Forks.template,ofSix]
    have ht : Forks.IsFork (relabel (ofSix a b c d e f) frame4) 0 := by
      rw [heq]
      exact Forks.IsFork.basic _ _ _ _ _ _ hdom
    exact Forks.fork_of_relabel frame4 ht
  · have hh := hcross 3 2 (by simp [ofSix]; omega) (by simp [ofSix]; omega)
    simp [ofSix] at hh
    omega
  · have hh := hcross 3 1 (by simp [ofSix]; omega) (by simp [ofSix]; omega)
    simp [ofSix] at hh
    omega
  · exfalso
    apply hcyc
    refine ⟨(fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | _ => 0),?_⟩
    intro i j hij
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [ofSix] at hij ⊢ <;> omega
  · have hc0 := hcross 3 2 (by simp [ofSix]; omega) (by simp [ofSix]; omega)
    have hc1 := hcross 3 1 (by simp [ofSix]; omega) (by simp [ofSix]; omega)
    simp [ofSix] at hc0 hc1
    have hdom : Forks.Domain (-c) b a f e (-d) := by unfold Forks.Domain; omega
    have heq : relabel (ofSix a b c d e f) frame5 = Forks.template (-c) b a f e (-d) := by
      funext i j
      rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
        simp [relabel,frame5,Forks.template,ofSix]
    have ht : Forks.IsFork (relabel (ofSix a b c d e f) frame5) 0 := by
      rw [heq]
      exact Forks.IsFork.basic _ _ _ _ _ _ hdom
    exact Forks.fork_of_relabel frame5 ht
  · have hh := hcross 3 2 (by simp [ofSix]; omega) (by simp [ofSix]; omega)
    simp [ofSix] at hh
    omega
  · have hh := hcross 3 1 (by simp [ofSix]; omega) (by simp [ofSix]; omega)
    simp [ofSix] at hh
    omega
  · exfalso
    apply hcyc
    refine ⟨(fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | _ => 0),?_⟩
    intro i j hij
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [ofSix] at hij ⊢ <;> omega
  · have hh := hcross 2 3 (by simp [ofSix]; omega) (by simp [ofSix]; omega)
    simp [ofSix] at hh
    omega
  · have hc0 := hcross 2 1 (by simp [ofSix]; omega) (by simp [ofSix]; omega)
    have hc1 := hcross 2 3 (by simp [ofSix]; omega) (by simp [ofSix]; omega)
    simp [ofSix] at hc0 hc1
    have hdom : Forks.Domain (-b) a c d (-f) e := by unfold Forks.Domain; omega
    have heq : relabel (ofSix a b c d e f) frame2 = Forks.template (-b) a c d (-f) e := by
      funext i j
      rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
        simp [relabel,frame2,Forks.template,ofSix]
    have ht : Forks.IsFork (relabel (ofSix a b c d e f) frame2) 0 := by
      rw [heq]
      exact Forks.IsFork.basic _ _ _ _ _ _ hdom
    exact Forks.fork_of_relabel frame2 ht
  · have hh := hcross 2 3 (by simp [ofSix]; omega) (by simp [ofSix]; omega)
    simp [ofSix] at hh
    omega
  · have hc0 := hcross 2 3 (by simp [ofSix]; omega) (by simp [ofSix]; omega)
    have hc1 := hcross 2 1 (by simp [ofSix]; omega) (by simp [ofSix]; omega)
    simp [ofSix] at hc0 hc1
    have hdom : Forks.Domain (-b) c a (-f) d (-e) := by unfold Forks.Domain; omega
    have heq : relabel (ofSix a b c d e f) frame3 = Forks.template (-b) c a (-f) d (-e) := by
      funext i j
      rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
        simp [relabel,frame3,Forks.template,ofSix]
    have ht : Forks.IsFork (relabel (ofSix a b c d e f) frame3) 0 := by
      rw [heq]
      exact Forks.IsFork.basic _ _ _ _ _ _ hdom
    exact Forks.fork_of_relabel frame3 ht
  · exfalso
    apply hcyc
    refine ⟨(fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 0 | _ => 3),?_⟩
    intro i j hij
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [ofSix] at hij ⊢ <;> omega
  · have hh := hcross 2 1 (by simp [ofSix]; omega) (by simp [ofSix]; omega)
    simp [ofSix] at hh
    omega
  · exfalso
    apply hcyc
    refine ⟨(fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 0 | _ => 2),?_⟩
    intro i j hij
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [ofSix] at hij ⊢ <;> omega
  · have hh := hcross 2 1 (by simp [ofSix]; omega) (by simp [ofSix]; omega)
    simp [ofSix] at hh
    omega
  · have hc0 := hcross 3 1 (by simp [ofSix]; omega) (by simp [ofSix]; omega)
    have hc1 := hcross 2 1 (by simp [ofSix]; omega) (by simp [ofSix]; omega)
    simp [ofSix] at hc0 hc1
    have hdom : Forks.Domain a (-c) (-b) e d f := by unfold Forks.Domain; omega
    have heq : relabel (reverse (ofSix a b c d e f)) frame1 = Forks.template a (-c) (-b) e d f := by
      funext i j
      rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
        simp [relabel,frame1,Forks.template,ofSix,reverse]
    have ht : Forks.IsFork (relabel (reverse (ofSix a b c d e f)) frame1) 0 := by
      rw [heq]
      exact Forks.IsFork.basic _ _ _ _ _ _ hdom
    exact Forks.fork_of_reverse (Forks.fork_of_relabel frame1 ht)
  · have hc0 := hcross 2 1 (by simp [ofSix]; omega) (by simp [ofSix]; omega)
    have hc1 := hcross 3 1 (by simp [ofSix]; omega) (by simp [ofSix]; omega)
    simp [ofSix] at hc0 hc1
    have hdom : Forks.Domain a (-b) (-c) d e (-f) := by unfold Forks.Domain; omega
    have heq : relabel (reverse (ofSix a b c d e f)) frame0 = Forks.template a (-b) (-c) d e (-f) := by
      funext i j
      rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
        simp [relabel,frame0,Forks.template,ofSix,reverse]
    have ht : Forks.IsFork (relabel (reverse (ofSix a b c d e f)) frame0) 0 := by
      rw [heq]
      exact Forks.IsFork.basic _ _ _ _ _ _ hdom
    exact Forks.fork_of_reverse (Forks.fork_of_relabel frame0 ht)
  · have hh := hcross 3 1 (by simp [ofSix]; omega) (by simp [ofSix]; omega)
    simp [ofSix] at hh
    omega
  · have hh := hcross 3 1 (by simp [ofSix]; omega) (by simp [ofSix]; omega)
    simp [ofSix] at hh
    omega
  · have hh := hcross 2 1 (by simp [ofSix]; omega) (by simp [ofSix]; omega)
    simp [ofSix] at hh
    omega
  · have hh := hcross 2 1 (by simp [ofSix]; omega) (by simp [ofSix]; omega)
    simp [ofSix] at hh
    omega
  · exfalso
    apply hcyc
    refine ⟨(fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | _ => 1),?_⟩
    intro i j hij
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [ofSix] at hij ⊢ <;> omega
  · exfalso
    apply hcyc
    refine ⟨(fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | _ => 0),?_⟩
    intro i j hij
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [ofSix] at hij ⊢ <;> omega
  · exfalso
    apply hcyc
    refine ⟨(fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | _ => 3),?_⟩
    intro i j hij
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [ofSix] at hij ⊢ <;> omega
  · exfalso
    apply hcyc
    refine ⟨(fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | _ => 2),?_⟩
    intro i j hij
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [ofSix] at hij ⊢ <;> omega
  · have hh := hcross 1 2 (by simp [ofSix]; omega) (by simp [ofSix]; omega)
    simp [ofSix] at hh
    omega
  · have hh := hcross 1 2 (by simp [ofSix]; omega) (by simp [ofSix]; omega)
    simp [ofSix] at hh
    omega
  · have hh := hcross 1 3 (by simp [ofSix]; omega) (by simp [ofSix]; omega)
    simp [ofSix] at hh
    omega
  · have hh := hcross 1 3 (by simp [ofSix]; omega) (by simp [ofSix]; omega)
    simp [ofSix] at hh
    omega
  · have hc0 := hcross 1 2 (by simp [ofSix]; omega) (by simp [ofSix]; omega)
    have hc1 := hcross 1 3 (by simp [ofSix]; omega) (by simp [ofSix]; omega)
    simp [ofSix] at hc0 hc1
    have hdom : Forks.Domain (-a) b c (-d) (-e) f := by unfold Forks.Domain; omega
    have heq : relabel (ofSix a b c d e f) frame0 = Forks.template (-a) b c (-d) (-e) f := by
      funext i j
      rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
        simp [relabel,frame0,Forks.template,ofSix]
    have ht : Forks.IsFork (relabel (ofSix a b c d e f) frame0) 0 := by
      rw [heq]
      exact Forks.IsFork.basic _ _ _ _ _ _ hdom
    exact Forks.fork_of_relabel frame0 ht
  · have hc0 := hcross 1 3 (by simp [ofSix]; omega) (by simp [ofSix]; omega)
    have hc1 := hcross 1 2 (by simp [ofSix]; omega) (by simp [ofSix]; omega)
    simp [ofSix] at hc0 hc1
    have hdom : Forks.Domain (-a) c b (-e) (-d) (-f) := by unfold Forks.Domain; omega
    have heq : relabel (ofSix a b c d e f) frame1 = Forks.template (-a) c b (-e) (-d) (-f) := by
      funext i j
      rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
        simp [relabel,frame1,Forks.template,ofSix]
    have ht : Forks.IsFork (relabel (ofSix a b c d e f) frame1) 0 := by
      rw [heq]
      exact Forks.IsFork.basic _ _ _ _ _ _ hdom
    exact Forks.fork_of_relabel frame1 ht
  · have hh := hcross 1 2 (by simp [ofSix]; omega) (by simp [ofSix]; omega)
    simp [ofSix] at hh
    omega
  · exfalso
    apply hcyc
    refine ⟨(fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 3 | _ => 1),?_⟩
    intro i j hij
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [ofSix] at hij ⊢ <;> omega
  · have hh := hcross 1 2 (by simp [ofSix]; omega) (by simp [ofSix]; omega)
    simp [ofSix] at hh
    omega
  · exfalso
    apply hcyc
    refine ⟨(fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 3 | _ => 0),?_⟩
    intro i j hij
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [ofSix] at hij ⊢ <;> omega
  · have hc0 := hcross 3 2 (by simp [ofSix]; omega) (by simp [ofSix]; omega)
    have hc1 := hcross 1 2 (by simp [ofSix]; omega) (by simp [ofSix]; omega)
    simp [ofSix] at hc0 hc1
    have hdom : Forks.Domain b (-c) (-a) f (-d) e := by unfold Forks.Domain; omega
    have heq : relabel (reverse (ofSix a b c d e f)) frame3 = Forks.template b (-c) (-a) f (-d) e := by
      funext i j
      rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
        simp [relabel,frame3,Forks.template,ofSix,reverse]
    have ht : Forks.IsFork (relabel (reverse (ofSix a b c d e f)) frame3) 0 := by
      rw [heq]
      exact Forks.IsFork.basic _ _ _ _ _ _ hdom
    exact Forks.fork_of_reverse (Forks.fork_of_relabel frame3 ht)
  · have hh := hcross 3 2 (by simp [ofSix]; omega) (by simp [ofSix]; omega)
    simp [ofSix] at hh
    omega
  · have hc0 := hcross 1 2 (by simp [ofSix]; omega) (by simp [ofSix]; omega)
    have hc1 := hcross 3 2 (by simp [ofSix]; omega) (by simp [ofSix]; omega)
    simp [ofSix] at hc0 hc1
    have hdom : Forks.Domain b (-a) (-c) (-d) f (-e) := by unfold Forks.Domain; omega
    have heq : relabel (reverse (ofSix a b c d e f)) frame2 = Forks.template b (-a) (-c) (-d) f (-e) := by
      funext i j
      rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
        simp [relabel,frame2,Forks.template,ofSix,reverse]
    have ht : Forks.IsFork (relabel (reverse (ofSix a b c d e f)) frame2) 0 := by
      rw [heq]
      exact Forks.IsFork.basic _ _ _ _ _ _ hdom
    exact Forks.fork_of_reverse (Forks.fork_of_relabel frame2 ht)
  · have hh := hcross 3 2 (by simp [ofSix]; omega) (by simp [ofSix]; omega)
    simp [ofSix] at hh
    omega
  · exfalso
    apply hcyc
    refine ⟨(fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 1 | _ => 3),?_⟩
    intro i j hij
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [ofSix] at hij ⊢ <;> omega
  · have hh := hcross 1 3 (by simp [ofSix]; omega) (by simp [ofSix]; omega)
    simp [ofSix] at hh
    omega
  · have hh := hcross 2 3 (by simp [ofSix]; omega) (by simp [ofSix]; omega)
    simp [ofSix] at hh
    omega
  · have hc0 := hcross 2 3 (by simp [ofSix]; omega) (by simp [ofSix]; omega)
    have hc1 := hcross 1 3 (by simp [ofSix]; omega) (by simp [ofSix]; omega)
    simp [ofSix] at hc0 hc1
    have hdom : Forks.Domain c (-b) (-a) (-f) (-e) d := by unfold Forks.Domain; omega
    have heq : relabel (reverse (ofSix a b c d e f)) frame5 = Forks.template c (-b) (-a) (-f) (-e) d := by
      funext i j
      rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
        simp [relabel,frame5,Forks.template,ofSix,reverse]
    have ht : Forks.IsFork (relabel (reverse (ofSix a b c d e f)) frame5) 0 := by
      rw [heq]
      exact Forks.IsFork.basic _ _ _ _ _ _ hdom
    exact Forks.fork_of_reverse (Forks.fork_of_relabel frame5 ht)
  · exfalso
    apply hcyc
    refine ⟨(fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | _ => 3),?_⟩
    intro i j hij
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [ofSix] at hij ⊢ <;> omega
  · have hh := hcross 1 3 (by simp [ofSix]; omega) (by simp [ofSix]; omega)
    simp [ofSix] at hh
    omega
  · have hh := hcross 2 3 (by simp [ofSix]; omega) (by simp [ofSix]; omega)
    simp [ofSix] at hh
    omega
  · have hc0 := hcross 1 3 (by simp [ofSix]; omega) (by simp [ofSix]; omega)
    have hc1 := hcross 2 3 (by simp [ofSix]; omega) (by simp [ofSix]; omega)
    simp [ofSix] at hc0 hc1
    have hdom : Forks.Domain c (-a) (-b) (-e) (-f) (-d) := by unfold Forks.Domain; omega
    have heq : relabel (reverse (ofSix a b c d e f)) frame4 = Forks.template c (-a) (-b) (-e) (-f) (-d) := by
      funext i j
      rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
        simp [relabel,frame4,Forks.template,ofSix,reverse]
    have ht : Forks.IsFork (relabel (reverse (ofSix a b c d e f)) frame4) 0 := by
      rw [heq]
      exact Forks.IsFork.basic _ _ _ _ _ _ hdom
    exact Forks.fork_of_reverse (Forks.fork_of_relabel frame4 ht)
  · exfalso
    apply hcyc
    refine ⟨(fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | _ => 2),?_⟩
    intro i j hij
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [ofSix] at hij ⊢ <;> omega
  · exfalso
    apply hcyc
    refine ⟨(fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | _ => 1),?_⟩
    intro i j hij
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [ofSix] at hij ⊢ <;> omega
  · exfalso
    have ht0 := hin 1 2 (by simp [ofSix]; omega) (by simp [ofSix]; omega) (by simp [ofSix]; omega)
    have ht1 := hin 2 3 (by simp [ofSix]; omega) (by simp [ofSix]; omega) (by simp [ofSix]; omega)
    have ht2 := hin 3 1 (by simp [ofSix]; omega) (by simp [ofSix]; omega) (by simp [ofSix]; omega)
    omega
  · exfalso
    apply hcyc
    refine ⟨(fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | _ => 0),?_⟩
    intro i j hij
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [ofSix] at hij ⊢ <;> omega
  · exfalso
    apply hcyc
    refine ⟨(fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 0 | _ => 2),?_⟩
    intro i j hij
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [ofSix] at hij ⊢ <;> omega
  · exfalso
    have ht0 := hin 1 3 (by simp [ofSix]; omega) (by simp [ofSix]; omega) (by simp [ofSix]; omega)
    have ht1 := hin 3 2 (by simp [ofSix]; omega) (by simp [ofSix]; omega) (by simp [ofSix]; omega)
    have ht2 := hin 2 1 (by simp [ofSix]; omega) (by simp [ofSix]; omega) (by simp [ofSix]; omega)
    omega
  · exfalso
    apply hcyc
    refine ⟨(fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | _ => 1),?_⟩
    intro i j hij
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [ofSix] at hij ⊢ <;> omega
  · exfalso
    apply hcyc
    refine ⟨(fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | _ => 0),?_⟩
    intro i j hij
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [ofSix] at hij ⊢ <;> omega


theorem graphFork_to_framed_zero (B : Matrix 4) (h : GraphFork B 0) : Forks.IsFork B 0 := by
  have he := ofSix_reconstruct B h.1
  rw [← he] at h ⊢
  exact graphFork_normalize_zero _ _ _ _ _ _ h

private def swap02 : Relabeling 4 :=
  ⟨(fun i => match i.val with | 0 => 2 | 2 => 0 | _ => i),
   (fun i => match i.val with | 0 => 2 | 2 => 0 | _ => i),by decide,by decide⟩

private def swap03 : Relabeling 4 :=
  ⟨(fun i => match i.val with | 0 => 3 | 3 => 0 | _ => i),
   (fun i => match i.val with | 0 => 3 | 3 => 0 | _ => i),by decide,by decide⟩

theorem graphFork_to_framed (B : Matrix 4) (r : Fin 4) (h : GraphFork B r) : Forks.IsFork B r := by
  rcases fin4 r with rfl|rfl|rfl|rfl
  · exact graphFork_to_framed_zero B h
  · have hh := graphFork_relabel B 1 h Forks.swap01
    exact Forks.fork_of_relabel Forks.swap01 (graphFork_to_framed_zero _ hh)
  · have hh := graphFork_relabel B 2 h swap02
    exact Forks.fork_of_relabel swap02 (graphFork_to_framed_zero _ hh)
  · have hh := graphFork_relabel B 3 h swap03
    exact Forks.fork_of_relabel swap03 (graphFork_to_framed_zero _ hh)

/-- The normalized schema captures exactly all rank-four forks in the cited
graph-theoretic definition, at their actual return labels. -/
theorem framed_fork_iff_graphFork (B : Matrix 4) (r : Fin 4) :
    Forks.IsFork B r ↔ GraphFork B r :=
  ⟨framed_fork_is_graphFork,graphFork_to_framed B r⟩

theorem graphFork_continuation (B : Matrix 4) (r k : Fin 4)
    (h : GraphFork B r) (hk : k ≠ r) : GraphFork (mutate B k) k :=
  framed_fork_is_graphFork (Forks.fork_continuation (graphFork_to_framed B r h) k hk)

theorem framed_return_unique {B : Matrix 4} {r : Fin 4} (h : Forks.IsFork B r)
    (s : Fin 4) (hs : GraphFork B s) : r = s := by
  induction h generalizing s with
  | basic a b c d e f hd =>
    rcases hd with ⟨ha,hb,hc,had,hbd,hae,hce,hf⟩
    rcases hs with ⟨_,_,_,_,_,hx⟩
    rcases fin4 s with rfl|rfl|rfl|rfl
    · rfl
    · have hh := hx 2 0 (by simp [Forks.template,ofSix];omega) (by simp [Forks.template,ofSix];omega)
      simp [Forks.template,ofSix] at hh
      omega
    · have hh := hx 0 1 (by simp [Forks.template,ofSix];omega) (by simp [Forks.template,ofSix];omega)
      simp [Forks.template,ofSix] at hh
      omega
    · have hh := hx 0 1 (by simp [Forks.template,ofSix];omega) (by simp [Forks.template,ofSix];omega)
      simp [Forks.template,ofSix] at hh
      omega
  | @relabelled B r h p ih =>
    have hh := graphFork_relabel _ s hs p.symm
    rw [relabel_inverse] at hh
    have he := congrArg p.invFun (ih (p.toFun s) hh)
    simpa only [p.left_inv] using he
  | @reversed B r h ih =>
    have hh := graphFork_reverse _ s hs
    rw [reverse_involutive] at hh
    exact ih s hh

theorem graphFork_return_unique (B : Matrix 4) (r s : Fin 4)
    (hr : GraphFork B r) (hs : GraphFork B s) : r=s :=
  framed_return_unique (graphFork_to_framed B r hr) s hs


private theorem magnitude_neg (x : Int) : Greedy.magnitude (-x) = Greedy.magnitude x := by
  simp [Greedy.magnitude,Int.max_comm]

theorem totalWeight_reverse (B : Matrix 4) : Greedy.totalWeight (reverse B) = Greedy.totalWeight B := by
  simp only [Greedy.totalWeight,reverse,magnitude_neg]

theorem totalWeight_relabel (B : Matrix 4) (hB : SkewSymmetric B) (p : Relabeling 4) :
    Greedy.totalWeight (relabel B p) = Greedy.totalWeight B := by
  rw [← ofSix_reconstruct B hB]
  have h01 : p.toFun 0 ≠ p.toFun 1 := fun h => (by decide : (0 : Fin 4) ≠ 1) (p.injective h)
  have h02 : p.toFun 0 ≠ p.toFun 2 := fun h => (by decide : (0 : Fin 4) ≠ 2) (p.injective h)
  have h03 : p.toFun 0 ≠ p.toFun 3 := fun h => (by decide : (0 : Fin 4) ≠ 3) (p.injective h)
  have h12 : p.toFun 1 ≠ p.toFun 2 := fun h => (by decide : (1 : Fin 4) ≠ 2) (p.injective h)
  have h13 : p.toFun 1 ≠ p.toFun 3 := fun h => (by decide : (1 : Fin 4) ≠ 3) (p.injective h)
  have h23 : p.toFun 2 ≠ p.toFun 3 := fun h => (by decide : (2 : Fin 4) ≠ 3) (p.injective h)
  rcases fin4 (p.toFun 0) with h0|h0|h0|h0 <;>
    rcases fin4 (p.toFun 1) with h1|h1|h1|h1 <;>
    rcases fin4 (p.toFun 2) with h2|h2|h2|h2 <;>
    rcases fin4 (p.toFun 3) with h3|h3|h3|h3 <;>
    simp_all [Greedy.totalWeight,relabel,ofSix,magnitude_neg] <;> omega

theorem template_weight (a b c d e f : Int) (h : Forks.Domain a b c d e f) :
    Greedy.totalWeight (Forks.template a b c d e f) = a+b+c+d+e+f := by
  rcases h with ⟨ha,hb,hc,had,hbd,hae,hce,hf⟩
  simp [Greedy.totalWeight,Greedy.magnitude,Forks.template,ofSix]
  omega

theorem template_mutation_increases_weight (a b c d e f : Int) (h : Forks.Domain a b c d e f)
    (k : Fin 4) (hk : k ≠ 0) :
    Greedy.totalWeight (Forks.template a b c d e f) < Greedy.totalWeight (mutate (Forks.template a b c d e f) k) := by
  have hs := Forks.fork_skew (Forks.IsFork.basic a b c d e f h)
  have hdom := h
  rcases h with ⟨ha,hb,hc,had,hbd,hae,hce,hf⟩
  rcases fin4 k with rfl|rfl|rfl|rfl
  · exact False.elim (hk rfl)
  · have he := totalWeight_relabel _ (mutation_preserves_skew _ 1 hs) Forks.swap01
    rw [Forks.mutate_one a b c d e f hdom] at he
    rw [← he,template_weight _ _ _ _ _ _ (Forks.domain_one a b c d e f hdom),template_weight _ _ _ _ _ _ hdom]
    have hd := Forks.product_sub_dominates a d b ha had hbd
    have he := Forks.product_sub_dominates a e c ha hae hce
    omega
  · have he := totalWeight_relabel _ (reverse_skew _ (mutation_preserves_skew _ 2 hs)) Forks.rotate2013
    rw [Forks.mutate_two a b c d e f hdom,totalWeight_reverse] at he
    rw [← he,template_weight _ _ _ _ _ _ (Forks.domain_two a b c d e f hdom),template_weight _ _ _ _ _ _ hdom]
    have hd := Forks.product_sub_dominates b d a hb hbd had
    have he := Forks.product_add_dominates b f c hb hf (by omega)
    have hp := Int.mul_pos (show 0<b by omega) (show 0<f by omega)
    omega
  · have he := totalWeight_relabel _ (mutation_preserves_skew _ 3 hs) Forks.rotate3102
    rw [Forks.mutate_three a b c d e f hdom] at he
    rw [← he,template_weight _ _ _ _ _ _ (Forks.domain_three a b c d e f hdom),template_weight _ _ _ _ _ _ hdom]
    have hd := Forks.product_sub_dominates c e a hc hce hae
    have he := Forks.product_add_dominates e f d (by omega) hf (by omega)
    have hp := Int.mul_pos (show 0<e by omega) (show 0<f by omega)
    omega

theorem framed_mutation_increases_weight {B : Matrix 4} {r : Fin 4} (h : Forks.IsFork B r)
    (k : Fin 4) (hk : k ≠ r) : Greedy.totalWeight B < Greedy.totalWeight (mutate B k) := by
  induction h generalizing k with
  | basic a b c d e f h => exact template_mutation_increases_weight a b c d e f h k hk
  | @relabelled B r h p ih =>
    have hp : p.toFun k ≠ r := by
      intro hh
      have he := congrArg p.invFun hh
      simp only [p.left_inv] at he
      exact hk he
    rw [totalWeight_relabel B (Forks.fork_skew h) p,mutate_relabel,
      totalWeight_relabel _ (mutation_preserves_skew _ _ (Forks.fork_skew h)) p]
    exact ih (p.toFun k) hp
  | @reversed B r h ih =>
    rw [totalWeight_reverse,mutate_reverse,totalWeight_reverse]
    exact ih k hk

/-- Both continuation and strict total-arrow growth, for the full rank-four
graph-theoretic fork predicate, with no external fork lemma assumption. -/
theorem graphFork_continuation_and_growth (B : Matrix 4) (r k : Fin 4)
    (h : GraphFork B r) (hk : k ≠ r) :
    GraphFork (mutate B k) k ∧ Greedy.totalWeight B < Greedy.totalWeight (mutate B k) :=
  ⟨graphFork_continuation B r k h hk,
   framed_mutation_increases_weight (graphFork_to_framed B r h) k hk⟩

end QuiverProofs.ForkDefinition
