import Rank4Round2.KleinGeometry
import Rank4Round2.MultiRegionInterfaces

/-! Unconditional NMA for the cross-guarded six-parameter deep region.
The cyclic core is closed under both domain-preserving returns; each actual
fork retains its central predecessor. No scalar/properness premise is used.
-/
namespace Rank4Round2.KleinRegion
open QuiverProofs Forks RecursiveRegions MultiRegionInterfaces
set_option maxHeartbeats 4000000

private theorem three (i : Fin 3) : i=0 ∨ i=1 ∨ i=2 := by omega
private theorem four (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega

theorem derived_bounds (s : Parameters) (hs : Domain s) :
    b s<s.B ∧ e s<s.E ∧ b s<f s ∧ e s<f s ∧
    s.a<f s ∧ s.c<f s ∧ s.d<f s ∧ 2≤f s ∧ 2≤S s ∧ 2≤T s := by
  have hb := bounds s hs
  have had := Int.mul_pos (show 0<s.a by omega) (show 0<s.d by omega)
  have hac := Int.mul_pos (show 0<s.a by omega) (show 0<s.c by omega)
  have hbB : b s<s.B := by unfold b; omega
  have heE : e s<s.E := by unfold e; omega
  exact ⟨hbB,heE,by omega,by omega,by omega,by omega,by omega,
    by omega,by omega,by omega⟩

theorem fork02 (s : Parameters) (hs : Domain s) : IsFork (mutate (node s 0) 2) 2 := by
  have hb := bounds s hs
  have hf := derived_bounds s hs
  have hd := product_sub_dominates (b s) (f s) s.c (by omega) (by omega) (by omega)
  have he := product_sub_dominates s.d (f s) (e s) (by omega) (by omega) (by omega)
  have hn : IsFork (relabel (mutate (node s 0) 2) frame2301) 0 := by
    rw [shape02 s hs]
    exact IsFork.basic _ _ _ _ _ _ ⟨by omega,by omega,by omega,
      hd.2,hd.1,he.2,he.1,by omega⟩
  exact fork_of_relabel frame2301 hn

theorem fork03 (s : Parameters) (hs : Domain s) : IsFork (mutate (node s 0) 3) 3 := by
  have hb := bounds s hs
  have hf := derived_bounds s hs
  have hd := product_sub_dominates (e s) (f s) s.d (by omega) (by omega) (by omega)
  have he := product_sub_dominates s.c (f s) (b s) (by omega) (by omega) (by omega)
  have hn : IsFork (relabel (reverse (mutate (node s 0) 3)) frame3210) 0 := by
    rw [shape03 s hs]
    exact IsFork.basic _ _ _ _ _ _ ⟨by omega,by omega,by omega,
      hd.2,hd.1,he.2,he.1,by omega⟩
  exact fork_of_reverse (fork_of_relabel frame3210 hn)

theorem fork12 (s : Parameters) (hs : Domain s) : IsFork (mutate (node s 1) 2) 2 := by
  have hb := bounds s hs
  have hf := derived_bounds s hs
  have hd := product_sub_dominates s.d (S s) s.E (by omega) (by omega) (by omega)
  have he := product_add_dominates (b s) s.d s.a (by omega) (by omega) (by omega)
  have hn : IsFork (relabel (reverse (mutate (node s 1) 2)) frame2130) 0 := by
    rw [shape12 s hs]
    exact IsFork.basic _ _ _ _ _ _ ⟨by omega,by omega,by omega,
      hd.1,hd.2,he.2,he.1,by omega⟩
  exact fork_of_reverse (fork_of_relabel frame2130 hn)

theorem fork13 (s : Parameters) (hs : Domain s) : IsFork (mutate (node s 1) 3) 3 := by
  have hb := bounds s hs
  have hf := derived_bounds s hs
  have hd := product_sub_dominates s.E (S s) s.d (by omega) (by omega) (by omega)
  have he := product_sub_dominates s.c s.E s.a (by omega) (by omega) (by omega)
  have hn : IsFork (relabel (mutate (node s 1) 3) frame3120) 0 := by
    rw [shape13 s hs]
    exact IsFork.basic _ _ _ _ _ _ ⟨by omega,by omega,by omega,
      hd.1,hd.2,he.2,he.1,by omega⟩
  exact fork_of_relabel frame3120 hn

theorem fork22 (s : Parameters) (hs : Domain s) : IsFork (mutate (node s 2) 2) 2 := by
  have hb := bounds s hs
  have hf := derived_bounds s hs
  have hd := product_sub_dominates s.B (T s) s.c (by omega) (by omega) (by omega)
  have he := product_sub_dominates s.d s.B s.a (by omega) (by omega) (by omega)
  have hn : IsFork (relabel (reverse (mutate (node s 2) 2)) frame2031) 0 := by
    rw [shape22 s hs]
    exact IsFork.basic _ _ _ _ _ _ ⟨by omega,by omega,by omega,
      hd.1,hd.2,he.2,he.1,by omega⟩
  exact fork_of_reverse (fork_of_relabel frame2031 hn)

theorem fork23 (s : Parameters) (hs : Domain s) : IsFork (mutate (node s 2) 3) 3 := by
  have hb := bounds s hs
  have hf := derived_bounds s hs
  have hd := product_sub_dominates s.c (T s) s.B (by omega) (by omega) (by omega)
  have he := product_add_dominates s.c (e s) s.a (by omega) (by omega) (by omega)
  have hn : IsFork (relabel (mutate (node s 2) 3) frame3021) 0 := by
    rw [shape23 s hs]
    exact IsFork.basic _ _ _ _ _ _ ⟨by omega,by omega,by omega,
      hd.1,hd.2,he.1,he.2,by omega⟩
  exact fork_of_relabel frame3021 hn

def Core (B : Matrix 4) : Prop := ∃ s : Parameters, Domain s ∧ ∃ i : Fin 3, B=node s i
abbrev SafeCore := Safe data Core

theorem node_safe (s : Parameters) (hs : Domain s) (i : Fin 3) : SafeCore (node s i) :=
  Safe.central ⟨s,hs,i,rfl⟩

theorem node_skew (s : Parameters) (i : Fin 3) : SkewSymmetric (node s i) := by
  rcases three i with rfl|rfl|rfl <;> exact ofSix_skew _ _ _ _ _ _

theorem node_cyclic (s : Parameters) (hs : Domain s) (i : Fin 3) : ¬Acyclic (node s i) := by
  have hb := bounds s hs
  have hf := derived_bounds s hs
  rcases three i with rfl|rfl|rfl
  · rintro ⟨rank,hr⟩
    have h0 := hr 0 2 (show 0<node s 0 0 2 by change 0<b s; omega)
    have h1 := hr 2 3 (show 0<node s 0 2 3 by change 0<f s; omega)
    have h2 := hr 3 0 (show 0<node s 0 3 0 by simp only [node,ofSix,Int.neg_neg]; omega)
    omega
  · rintro ⟨rank,hr⟩
    have h0 := hr 0 3 (show 0<node s 1 0 3 by change 0<s.c; omega)
    have h1 := hr 3 1 (show 0<node s 1 3 1 by simp only [node,ofSix,Int.neg_neg]; omega)
    have h2 := hr 1 0 (show 0<node s 1 1 0 by simp only [node,ofSix,Int.neg_neg]; omega)
    omega
  · rintro ⟨rank,hr⟩
    have h0 := hr 0 2 (show 0<node s 2 0 2 by change 0<s.B; omega)
    have h1 := hr 2 1 (show 0<node s 2 2 1 by simp only [node,ofSix,Int.neg_neg]; omega)
    have h2 := hr 1 0 (show 0<node s 2 1 0 by simp only [node,ofSix,Int.neg_neg]; omega)
    omega

theorem node_edges (s : Parameters) (hs : Domain s) (i : Fin 3) (k : Fin 4) :
    SafeCore (mutate (node s i) k) := by
  rcases three i with rfl|rfl|rfl <;> rcases four k with rfl|rfl|rfl|rfl
  · rw [node_zero s hs]; exact node_safe s hs 1
  · rw [node_one s hs]; exact node_safe s hs 2
  · exact Safe.fork 2 (node_safe s hs 0) (fork02 s hs)
  · exact Safe.fork 3 (node_safe s hs 0) (fork03 s hs)
  · rw [←node_zero s hs,mutation_involutive]; exact node_safe s hs 0
  · rw [tau_return s hs]
    exact Safe.reversed (Safe.framed (node_safe (tau s) (tau_domain s hs) 1) swap02)
  · exact Safe.fork 2 (node_safe s hs 1) (fork12 s hs)
  · exact Safe.fork 3 (node_safe s hs 1) (fork13 s hs)
  · rw [sigma_return s hs]
    exact Safe.reversed (Safe.framed (node_safe (sigma s) (sigma_domain s hs) 2) swap13)
  · rw [←node_one s hs,mutation_involutive]; exact node_safe s hs 0
  · exact Safe.fork 2 (node_safe s hs 2) (fork22 s hs)
  · exact Safe.fork 3 (node_safe s hs 2) (fork23 s hs)

theorem core_NMA (s : Parameters) (hs : Domain s) : ¬MutationAcyclic (node s 0) := by
  apply safe_NMA data rules Core
  · rintro B ⟨p,_,i,rfl⟩; exact node_skew p i
  · rintro B ⟨p,hp,i,rfl⟩; exact node_cyclic p hp i
  · rintro B ⟨p,hp,i,rfl⟩ k; exact node_edges p hp i k
  · exact node_safe s hs 0

theorem all_NMA (a c d h E B : Int)
    (ha : 2≤a) (hc : 2≤c) (hd : 2≤d) (hh : 2≤h)
    (he : 2≤E-a*c) (he' : 2≤E-d*h) (hb : 2≤B-a*d) (hb' : 2≤B-c*h) :
    ¬MutationAcyclic (ofSix a (B-a*d) (-c) d (-(E-a*c)) ((B-a*d)*c+d*E-h)) := by
  exact core_NMA ⟨a,c,d,h,E,B⟩ ⟨ha,hc,hd,hh,he,he',hb,hb'⟩

#print axioms node_edges
#print axioms all_NMA
end Rank4Round2.KleinRegion
