import QuiverProofs.PendantSquare

/-! Graph-to-normal-form bridge for pendant squares. All side and edge
conditions are expressed on the induced three-vertex deletion. -/
namespace QuiverProofs.PendantNormalization
open TriangleRegions Pendant PendantSquare

/-- The graph-theoretic rank-three fork conditions on the deletion of `ell`.
Acyclic side conditions are retained explicitly as in the manuscript definition. -/
def DeletionFork (Q : Matrix 4) (ell r : Fin 4) : Prop :=
  ¬ DeletionAcyclic Q ell ∧
  (∀ i j, i≠ell → j≠ell → i≠j → 2 ≤ (Q i j).natAbs) ∧
  (∃ rank : Fin 4 → Nat, ∀ i j, i≠ell → j≠ell →
    0 < Q i r → 0 < Q j r → 0 < Q i j → rank i < rank j) ∧
  (∃ rank : Fin 4 → Nat, ∀ i j, i≠ell → j≠ell →
    0 < Q r i → 0 < Q r j → 0 < Q i j → rank i < rank j) ∧
  (∀ i j, i≠ell → j≠ell → 0 < Q i r → 0 < Q r j →
    Q i r < Q j i ∧ Q r j < Q j i)

def GraphPendant (Q : Matrix 4) (ell j r : Fin 4) : Prop :=
  SkewSymmetric Q ∧ At Q ell j ∧ 2 ≤ (Q ell j).natAbs ∧
  r≠ell ∧ r≠j ∧ DeletionFork Q ell r

private theorem fin4 (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega

private theorem large_natAbs_cases (x : Int) (h : 2 ≤ x.natAbs) : 2 ≤ x ∨ x ≤ -2 := by
  by_cases hx : 0 ≤ x
  · have := Int.natAbs_of_nonneg hx
    left
    omega
  · have := Int.ofNat_natAbs_of_nonpos (show x ≤ 0 by omega)
    right
    omega

private theorem deletion_zero_from_triangle (Q : Matrix 4)
    (h : Acyclic (restrict Q (deleteVertex 0))) : DeletionAcyclic Q 0 := by
  obtain ⟨rank,hr⟩ := h
  refine ⟨fun i => if i=1 then rank 0 else if i=2 then rank 1 else rank 2,?_⟩
  intro i j hi hj hij
  rcases fin4 i with rfl|rfl|rfl|rfl <;>
    rcases fin4 j with rfl|rfl|rfl|rfl
  all_goals simp_all only [Fin.isValue,ne_eq,not_true_eq_false]
  all_goals first
    | simpa using hr 0 0 hij
    | simpa using hr 0 1 hij
    | simpa using hr 0 2 hij
    | simpa using hr 1 0 hij
    | simpa using hr 1 1 hij
    | simpa using hr 1 2 hij
    | simpa using hr 2 0 hij
    | simpa using hr 2 1 hij
    | simpa using hr 2 2 hij

private theorem zero_deletion_eq (Q : Matrix 4) (hs : SkewSymmetric Q) :
    restrict Q (deleteVertex 0) = cycleThree (Q 1 2) (Q 2 3) (Q 3 1) := by
  funext i j
  have hi : i=0 ∨ i=1 ∨ i=2 := by omega
  have hj : j=0 ∨ j=1 ∨ j=2 := by omega
  have h11 := hs 1 1; have h22 := hs 2 2; have h33 := hs 3 3
  have h21 := hs 2 1; have h13 := hs 1 3; have h32 := hs 3 2
  rcases hi with rfl|rfl|rfl <;> rcases hj with rfl|rfl|rfl <;>
    simp [restrict,deleteVertex,cycleThree] <;> omega

theorem graphPendant_reverse (Q : Matrix 4) (ell j r : Fin 4)
    (h : GraphPendant Q ell j r) : GraphPendant (reverse Q) ell j r := by
  obtain ⟨hs,⟨helj,hn,hzero⟩,hab,hrl,hrj,hcyc,ha,hin,hout,hcross⟩ := h
  refine ⟨reverse_skew _ hs,⟨helj,?_,?_⟩,?_,hrl,hrj,?_,?_,?_,?_,?_⟩
  · simpa [reverse] using hn
  · intro i hi; simp [reverse,hzero i hi]
  · simpa [reverse] using hab
  · intro hd
    have hh := deletion_reverse (reverse Q) ell (reverse_skew Q hs) hd
    rw [reverse_involutive] at hh
    exact hcyc hh
  · intro i j hi hj hij
    simpa [reverse] using ha i j hi hj hij
  · obtain ⟨rank,hrank⟩ := hout
    obtain ⟨bound,hb⟩ := finite_rank_bound 4 rank
    refine ⟨fun i => bound-rank i,?_⟩
    intro i j hi hj hir hjr hij
    have hri : 0 < Q r i := by have := hs i r; simp [reverse] at hir; omega
    have hrj : 0 < Q r j := by have := hs j r; simp [reverse] at hjr; omega
    have hji : 0 < Q j i := by have := hs i j; simp [reverse] at hij; omega
    have hh := hrank j i hj hi hrj hri hji
    have hbi := hb i; have hbj := hb j
    change bound-rank i < bound-rank j
    omega
  · obtain ⟨rank,hrank⟩ := hin
    obtain ⟨bound,hb⟩ := finite_rank_bound 4 rank
    refine ⟨fun i => bound-rank i,?_⟩
    intro i j hi hj hri hrj hij
    have hir : 0 < Q i r := by have := hs r i; simp [reverse] at hri; omega
    have hjr : 0 < Q j r := by have := hs r j; simp [reverse] at hrj; omega
    have hji : 0 < Q j i := by have := hs i j; simp [reverse] at hij; omega
    have hh := hrank j i hj hi hjr hir hji
    have hbi := hb i; have hbj := hb j
    change bound-rank i < bound-rank j
    omega
  · intro i j hi hj hir hrj
    have hri : 0 < Q r i := by have := hs i r; simp [reverse] at hir; omega
    have hjr : 0 < Q j r := by have := hs r j; simp [reverse] at hrj; omega
    have hh := hcross j i hj hi hjr hri
    have := hs i r; have := hs r j; have := hs i j
    simp only [reverse]
    omega

private theorem positive_normalization (Q : Matrix 4) (h : GraphPendant Q 0 3 1)
    (hp : 0 < Q 1 2 ∧ 0 < Q 2 3 ∧ 0 < Q 3 1) :
    ∃ c d x y ε : Int, Domain c d x y ∧ Sign ε ∧ Q = state c d x y ε := by
  obtain ⟨hs,⟨_,_,hz⟩,hab,_,_,_,ha,_,_,hcross⟩ := h
  have hd := large_natAbs_cases _ (ha 1 2 (by decide) (by decide) (by decide))
  have hx := large_natAbs_cases _ (ha 3 1 (by decide) (by decide) (by decide))
  have hclose := hcross 3 2 (by decide) (by decide) hp.2.2 hp.1
  have h01 := hz 1 (by decide); have h02 := hz 2 (by decide)
  have hnorm : Q = ofSix 0 0 (Q 0 3) (Q 1 2) (-(Q 3 1)) (Q 2 3) := by
    calc
      Q = ofSix (Q 0 1) (Q 0 2) (Q 0 3) (Q 1 2) (Q 1 3) (Q 2 3) :=
        (ofSix_reconstruct Q hs).symm
      _ = _ := by rw [h01,h02,hs 1 3]
  rcases large_natAbs_cases _ hab with hc|hc
  · refine ⟨Q 0 3,Q 1 2,Q 3 1,Q 2 3,1,?_,Or.inl rfl,?_⟩
    · unfold Domain; omega
    · simpa [state] using hnorm
  · refine ⟨-(Q 0 3),Q 1 2,Q 3 1,Q 2 3,-1,?_,Or.inr rfl,?_⟩
    · unfold Domain; omega
    · simpa [state] using hnorm

/-- No geometric cases are omitted in the displayed normalization: every
pendant fork in the labels leaf=0, junction=3, return=1 has that form,
up to simultaneous reversal. -/
theorem graph_normalization (Q : Matrix 4) (h : GraphPendant Q 0 3 1) :
    ∃ c d x y ε : Int, Domain c d x y ∧ Sign ε ∧
      (Q = state c d x y ε ∨ Q = reverse (state c d x y ε)) := by
  have hs := h.1
  have hcyc := h.2.2.2.2.2.1
  by_cases hp : 0 < Q 1 2 ∧ 0 < Q 2 3 ∧ 0 < Q 3 1
  · obtain ⟨c,d,x,y,ε,hd,hε,heq⟩ := positive_normalization Q h hp
    exact ⟨c,d,x,y,ε,hd,hε,Or.inl heq⟩
  · have hn : Q 1 2 < 0 ∧ Q 2 3 < 0 ∧ Q 3 1 < 0 := by
      by_cases hn : Q 1 2 < 0 ∧ Q 2 3 < 0 ∧ Q 3 1 < 0
      · exact hn
      · have ha := cycleThree_mixed_acyclic _ _ _ hp hn
        rw [←zero_deletion_eq Q hs] at ha
        exact False.elim (hcyc (deletion_zero_from_triangle Q ha))
    obtain ⟨c,d,x,y,ε,hd,hε,heq⟩ := positive_normalization (reverse Q)
      (graphPendant_reverse Q 0 3 1 h) (by simp [reverse]; omega)
    refine ⟨c,d,x,y,ε,hd,hε,Or.inr ?_⟩
    have hh := congrArg reverse heq
    simpa only [reverse_involutive] using hh

/-- Graph predicates transport along actual new-to-old vertex permutations. -/
theorem graphPendant_relabel (Q : Matrix 4) (ell j r : Fin 4)
    (h : GraphPendant Q ell j r) (p : Relabeling 4) :
    GraphPendant (relabel Q p) (p.invFun ell) (p.invFun j) (p.invFun r) := by
  obtain ⟨hs,⟨helj,hn,hzero⟩,hab,hrl,hrj,hcyc,ha,hin,hout,hcross⟩ := h
  have hne : ∀ a b : Fin 4, a≠b → p.invFun a≠p.invFun b := by
    intro a b hab heq
    have := congrArg p.toFun heq
    exact hab (by simpa only [p.right_inv] using this)
  have hne' : ∀ a b : Fin 4, a≠p.invFun b → p.toFun a≠b := by
    intro a b hab heq
    have := congrArg p.invFun heq
    simp only [p.left_inv] at this
    exact hab this
  refine ⟨relabel_skew _ p hs,⟨hne _ _ helj,?_,?_⟩,?_,hne _ _ hrl,hne _ _ hrj,
    ?_,?_,?_,?_,?_⟩
  · simpa only [relabel,p.right_inv] using hn
  · intro i hi
    simp only [relabel,p.right_inv]
    exact hzero _ (hne' i j hi)
  · simpa only [relabel,p.right_inv] using hab
  · intro hd
    have hh := deletion_relabel (relabel Q p) (p.invFun ell) p.symm hd
    have heq : p.symm.invFun (p.invFun ell) = ell := p.right_inv ell
    rw [relabel_inverse,heq] at hh
    exact hcyc hh
  · intro i j hi hj hij
    exact ha _ _ (hne' i ell hi) (hne' j ell hj) (fun he => hij (p.injective he))
  · obtain ⟨rank,hrank⟩ := hin
    refine ⟨rank ∘ p.toFun,?_⟩
    intro i j hi hj hir hjr hij
    simp only [relabel,p.right_inv] at hir hjr hij
    exact hrank _ _ (hne' i ell hi) (hne' j ell hj) hir hjr hij
  · obtain ⟨rank,hrank⟩ := hout
    refine ⟨rank ∘ p.toFun,?_⟩
    intro i j hi hj hri hrj hij
    simp only [relabel,p.right_inv] at hri hrj hij
    exact hrank _ _ (hne' i ell hi) (hne' j ell hj) hri hrj hij
  · intro i j hi hj hir hrj
    simp only [relabel,p.right_inv] at hir hrj ⊢
    exact hcross _ _ (hne' i ell hi) (hne' j ell hj) hir hrj

/-- Build the labeled frame from the four distinct vertices. -/
def frame (a b c d : Fin 4) (h01 : a≠b) (h02 : a≠c) (h03 : a≠d)
    (h12 : b≠c) (h13 : b≠d) (h23 : c≠d) : Relabeling 4 where
  toFun i := match i.val with | 0 => a | 1 => b | 2 => c | _ => d
  invFun i := if i=a then 0 else if i=b then 1 else if i=c then 2 else 3
  left_inv := by
    intro i
    rcases fin4 i with rfl|rfl|rfl|rfl <;> simp_all [Ne.symm h01,Ne.symm h02,Ne.symm h03,Ne.symm h12,Ne.symm h13,Ne.symm h23]
  right_inv := by
    intro i
    by_cases hia : i=a
    · simp [hia]
    by_cases hib : i=b
    · simp [hib,Ne.symm h01]
    by_cases hic : i=c
    · simp [hic,Ne.symm h02,Ne.symm h12]
    have hid : i=d := by omega
    simp [hid,Ne.symm h03,Ne.symm h13,Ne.symm h23]

/-- Exact graph-to-normal-form coverage for every labeled pendant fork.
The displayed frame sends leaf, return and junction to 0,1,3 respectively. -/
theorem labeled_graph_normalization (Q : Matrix 4) (ell j r : Fin 4)
    (h : GraphPendant Q ell j r) :
    ∃ p : Relabeling 4, ∃ c d x y ε : Int,
      p.toFun 0=ell ∧ p.toFun 1=r ∧ p.toFun 3=j ∧
      Domain c d x y ∧ Sign ε ∧
      (relabel Q p = state c d x y ε ∨ relabel Q p = reverse (state c d x y ε)) := by
  have hlj := h.2.1.1
  have hrl := h.2.2.2.1
  have hrj := h.2.2.2.2.1
  have hfourth : ∀ a b c : Fin 4, a≠b → c≠a → c≠b →
      ∃ t : Fin 4, t≠a ∧ t≠b ∧ t≠c := by decide
  obtain ⟨t,htl,htj,htr⟩ := hfourth ell j r hlj hrl hrj
  let p := frame ell r t j (Ne.symm hrl) (Ne.symm htl) hlj (Ne.symm htr) hrj htj
  have hp0 : p.toFun 0=ell := rfl
  have hp1 : p.toFun 1=r := rfl
  have hp3 : p.toFun 3=j := rfl
  have h0 : p.invFun ell=0 := by rw [←hp0,p.left_inv]
  have h1 : p.invFun r=1 := by rw [←hp1,p.left_inv]
  have h3 : p.invFun j=3 := by rw [←hp3,p.left_inv]
  have hg := graphPendant_relabel Q ell j r h p
  rw [h0,h1,h3] at hg
  obtain ⟨c,d,x,y,ε,hd,hε,heq⟩ := graph_normalization (relabel Q p) hg
  exact ⟨p,c,d,x,y,ε,hp0,hp1,hp3,hd,hε,heq⟩

/-- Every point of the cone satisfies the original graph definition. -/
theorem state_graphPendant (c d x y ε : Int) (h : Domain c d x y) (hε : Sign ε) :
    GraphPendant (state c d x y ε) 0 3 1 := by
  have hp := pendant_at c d x y ε h hε
  obtain ⟨hc,hd,hx,hdy,hxy⟩ := h
  refine ⟨ofSix_skew _ _ _ _ _ _,hp,?_,by decide,by decide,?_,?_,?_,?_,?_⟩
  · rcases hε with rfl|rfl <;> simp [state,ofSix]
    all_goals have := Int.natAbs_of_nonneg (show 0 ≤ c by omega); omega
  · rintro ⟨rank,hr⟩
    have h12 := hr 1 2 (by decide) (by decide) (by simp [state,ofSix]; omega)
    have h23 := hr 2 3 (by decide) (by decide) (by simp [state,ofSix]; omega)
    have h31 := hr 3 1 (by decide) (by decide) (by simp [state,ofSix]; omega)
    omega
  · intro i j hi hj hij
    have hdn := Int.natAbs_of_nonneg (show 0 ≤ d by omega)
    have hxn := Int.natAbs_of_nonneg (show 0 ≤ x by omega)
    have hyn := Int.natAbs_of_nonneg (show 0 ≤ y by omega)
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp_all [state,ofSix] <;> omega
  · refine ⟨fun _ => 0,?_⟩
    intro i j hi hj hir hjr hij
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp_all [state,ofSix] <;> omega
  · refine ⟨fun _ => 0,?_⟩
    intro i j hi hj hri hrj hij
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp_all [state,ofSix] <;> omega
  · intro i j hi hj hir hrj
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp_all [state,ofSix] <;> omega

/-- Exact parameterization equivalence in the normalized labels. -/
theorem graph_normalization_iff (Q : Matrix 4) : GraphPendant Q 0 3 1 ↔
    ∃ c d x y ε : Int, Domain c d x y ∧ Sign ε ∧
      (Q = state c d x y ε ∨ Q = reverse (state c d x y ε)) := by
  constructor
  · exact graph_normalization Q
  · rintro ⟨c,d,x,y,ε,hd,hε,heq⟩
    rcases heq with rfl|rfl
    · exact state_graphPendant c d x y ε hd hε
    · exact graphPendant_reverse _ 0 3 1 (state_graphPendant c d x y ε hd hε)

end QuiverProofs.PendantNormalization
