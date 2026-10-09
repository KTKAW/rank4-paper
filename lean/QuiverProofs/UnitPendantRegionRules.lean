import QuiverProofs.UnitRegionData

/-! Complete local attachment and retained-triangle rules for D. Each recursive
D/N child has both parents explicitly wired to the current ten-state cell. -/
namespace QuiverProofs.UnitPendantRegionRules
open RecursiveRegions UnitRegionData UnitPendantStrip TriangleRegions

private theorem fin4 (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
private theorem fin10 (i : Fin 10) :
    i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 := by omega

abbrev current (p : Parameters) (hp : parameterDomain p) : Region := .d p hp
abbrev childD (p : Parameters) (hp : parameterDomain p) : Region :=
  .d (child p) (child_parameterDomain p hp)
abbrev childA (p : Parameters) (hp : parameterDomain p) : Region :=
  .n p.x (AParameters p) (A_domain p hp)
abbrev childB (p : Parameters) (hp : parameterDomain p) : Region :=
  .n p.y (BParameters p) (B_domain p hp)

theorem childD_parents (p : Parameters) (hp : parameterDomain p) (j : Fin 2) :
    LocalAddress data (current p hp) (fun _ => True) (data.parent (childD p hp) j) := by
  change LocalAddress data (current p hp) (fun _ => True) (UnitPendantStrip.parent (child p) j)
  rw [child_parent p hp j]
  exact .framed (LocalAddress.node (D:=data) (r:=current p hp) (if j=0 then 0 else 1) True.intro) tau

theorem childA_parents (p : Parameters) (hp : parameterDomain p) (j : Fin 2) :
    LocalAddress data (current p hp) (fun _ => True) (data.parent (childA p hp) j) := by
  have hj : j=0 ∨ j=1 := by omega
  rcases hj with rfl|rfl
  · change LocalAddress data (current p hp) (fun _ => True)
      (mutate (N0 p.x p.y (h p.d p.x p.y) (p.x*h p.d p.x p.y-p.y)) 1)
    rw [A0_one p.d p.x p.y hp]
    exact LocalAddress.node (D:=data) (r:=current p hp) 2 True.intro
  · change LocalAddress data (current p hp) (fun _ => True)
      (mutate (N1 p.x p.y (h p.d p.x p.y) (p.x*h p.d p.x p.y-p.y)) 1)
    rw [A1_one p.d p.x p.y hp]
    exact LocalAddress.node (D:=data) (r:=current p hp) 3 True.intro

theorem childB_parents (p : Parameters) (hp : parameterDomain p) (j : Fin 2) :
    LocalAddress data (current p hp) (fun _ => True) (data.parent (childB p hp) j) := by
  have hj : j=0 ∨ j=1 := by omega
  rcases hj with rfl|rfl
  · change LocalAddress data (current p hp) (fun _ => True)
      (mutate (N0 p.y p.x (h p.d p.x p.y) (p.y*h p.d p.x p.y-p.x)) 1)
    rw [B0_one p.d p.x p.y hp]
    exact .reversed (.framed (LocalAddress.node (D:=data) (r:=current p hp) 4 True.intro) rho)
  · change LocalAddress data (current p hp) (fun _ => True)
      (mutate (N1 p.y p.x (h p.d p.x p.y) (p.y*h p.d p.x p.y-p.x)) 1)
    rw [B1_one p.d p.x p.y hp]
    exact .reversed (.framed (LocalAddress.node (D:=data) (r:=current p hp) 3 True.intro) rho)

private theorem local_step (p : Parameters) (hp : parameterDomain p) (i j : Fin 10) (k : Fin 4)
    (he : mutate (phase p.d p.x p.y i) k = phase p.d p.x p.y j) :
    LocalEdge data (current p hp) (mutate (data.state (current p hp) i) k) k := by
  change LocalEdge data (current p hp) (mutate (phase p.d p.x p.y i) k) k
  rw [he]
  exact Or.inl (LocalAddress.node (D:=data) (r:=current p hp) j True.intro)

theorem node0_edges (p : Parameters) (hp : parameterDomain p) (k : Fin 4) :
    LocalEdge data (current p hp) (mutate (data.state (current p hp) 0) k) k := by
  rcases fin4 k with rfl|rfl|rfl|rfl
  · exact local_step p hp 0 1 0 (D0_zero p.d p.x p.y hp)
  · exact Or.inl (.parent 0)
  · right; right; right
    refine ⟨childD p hp,?_,childD_parents p hp⟩
    change LocalAddress data (childD p hp) _ (mutate (D0 p.d p.x p.y) 2)
    rw [D0_two p.d p.x p.y hp]
    exact .framed (LocalAddress.node (D:=data) (r:=childD p hp) 0 True.intro) tau
  · exact local_step p hp 0 9 3 (backward_step p.d p.x p.y hp 0)

theorem node1_edges (p : Parameters) (hp : parameterDomain p) (k : Fin 4) :
    LocalEdge data (current p hp) (mutate (data.state (current p hp) 1) k) k := by
  rcases fin4 k with rfl|rfl|rfl|rfl
  · exact local_step p hp 1 0 0 (backward_step p.d p.x p.y hp 1)
  · exact Or.inl (.parent 1)
  · right; right; right
    refine ⟨childD p hp,?_,childD_parents p hp⟩
    change LocalAddress data (childD p hp) _ (mutate (D1 p.d p.x p.y) 2)
    rw [D1_two p.d p.x p.y hp]
    exact .framed (LocalAddress.node (D:=data) (r:=childD p hp) 1 True.intro) tau
  · exact local_step p hp 1 2 3 (D1_three p.d p.x p.y hp)

theorem node2_edges (p : Parameters) (hp : parameterDomain p) (k : Fin 4) :
    LocalEdge data (current p hp) (mutate (data.state (current p hp) 2) k) k := by
  rcases fin4 k with rfl|rfl|rfl|rfl
  · exact local_step p hp 2 3 0 (D2_zero p.d p.x p.y hp)
  · right; right; right
    refine ⟨childA p hp,?_,childA_parents p hp⟩
    change LocalAddress data (childA p hp) _ (mutate (D2 p.d p.x p.y) 1)
    rw [D2_one p.d p.x p.y hp]
    exact LocalAddress.node (D:=data) (r:=childA p hp) (0,0) True.intro
  · right; right; left
    exact D2_two_root p.d p.x p.y hp
  · exact local_step p hp 2 1 3 (backward_step p.d p.x p.y hp 2)

theorem node3_edges (p : Parameters) (hp : parameterDomain p) (k : Fin 4) :
    LocalEdge data (current p hp) (mutate (data.state (current p hp) 3) k) k := by
  rcases fin4 k with rfl|rfl|rfl|rfl
  · exact local_step p hp 3 2 0 (backward_step p.d p.x p.y hp 3)
  · right; right; right
    refine ⟨childA p hp,?_,childA_parents p hp⟩
    change LocalAddress data (childA p hp) _ (mutate (D3 p.d p.x p.y) 1)
    rw [D3_one p.d p.x p.y hp]
    exact LocalAddress.node (D:=data) (r:=childA p hp) (0,1) True.intro
  · right; right; right
    refine ⟨childB p hp,?_,childB_parents p hp⟩
    change LocalAddress data (childB p hp) _ (mutate (D3 p.d p.x p.y) 2)
    rw [D3_two p.d p.x p.y hp]
    exact .reversed (.framed (LocalAddress.node (D:=data) (r:=childB p hp) (0,1) True.intro) rho)
  · exact local_step p hp 3 4 3 (D3_three p.d p.x p.y hp)

theorem node4_edges (p : Parameters) (hp : parameterDomain p) (k : Fin 4) :
    LocalEdge data (current p hp) (mutate (data.state (current p hp) 4) k) k := by
  rcases fin4 k with rfl|rfl|rfl|rfl
  · exact local_step p hp 4 5 0 (D4_zero p.d p.x p.y hp)
  · right; right; left
    exact D4_one_root p.d p.x p.y hp
  · right; right; right
    refine ⟨childB p hp,?_,childB_parents p hp⟩
    change LocalAddress data (childB p hp) _ (mutate (D4 p.d p.x p.y) 2)
    rw [D4_two p.d p.x p.y hp]
    exact .reversed (.framed (LocalAddress.node (D:=data) (r:=childB p hp) (0,0) True.intro) rho)
  · exact local_step p hp 4 3 3 (backward_step p.d p.x p.y hp 4)

private theorem edge_relabel (r : Region) (Q : Matrix 4) (f : Relabeling 4)
    (k : Fin 4) (he : LocalEdge data r (mutate Q (f.toFun k)) (f.toFun k)) :
    LocalEdge data r (mutate (relabel Q f) k) k := by
  rw [mutate_relabel]
  rcases he with ha|hf|hr|⟨c,ha,hp⟩
  · exact Or.inl (.framed ha f)
  · right; left
    simpa only [f.left_inv] using Forks.IsFork.relabelled hf f
  · right; right; left
    simpa only [f.left_inv] using Regions.IsRoot.relabelled hr f
  · right; right; right
    exact ⟨c,.framed ha f,hp⟩

theorem all_edges (p : Parameters) (hp : parameterDomain p) (i : Fin 10) (k : Fin 4) :
    LocalEdge data (.d p hp) (mutate (data.state (.d p hp) i) k) k := by
  rcases fin10 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact node0_edges p hp k
  · exact node1_edges p hp k
  · exact node2_edges p hp k
  · exact node3_edges p hp k
  · exact node4_edges p hp k
  · exact edge_relabel (current p hp) (D0 p.d p.x p.y) sigma k (node0_edges p hp (sigma.toFun k))
  · exact edge_relabel (current p hp) (D1 p.d p.x p.y) sigma k (node1_edges p hp (sigma.toFun k))
  · exact edge_relabel (current p hp) (D2 p.d p.x p.y) sigma k (node2_edges p hp (sigma.toFun k))
  · exact edge_relabel (current p hp) (D3 p.d p.x p.y) sigma k (node3_edges p hp (sigma.toFun k))
  · exact edge_relabel (current p hp) (D4 p.d p.x p.y) sigma k (node4_edges p hp (sigma.toFun k))

private theorem deletionMA (p : Parameters) (hp : parameterDomain p) (i : Fin 10)
    (hi3 : i≠3) (hi8 : i≠8) : Pendant.DeletionMA (phase p.d p.x p.y i) (inward i) := by
  obtain ⟨rank,hr⟩ := phase_deletion p.d p.x p.y hp i hi3 hi8
  intro e _ he
  apply acyclic_is_mutationAcyclic
  exact ⟨rank ∘ e,fun a b hab => hr _ _ (he a) (he b) hab⟩

theorem triangle_descent (p : Parameters) (hp : parameterDomain p) (i : Fin 10) :
    AllTrianglesMA (data.state (.d p hp) i) ∨
    ∃ k, Pendant.DeletionMA (data.state (.d p hp) i) k ∧
      LocalAddress data (.d p hp) (fun j => level j < level i)
        (mutate (data.state (.d p hp) i) k) := by
  by_cases hexc : i=3 ∨ i=8
  · exact Or.inl (exceptional_triangles p.d p.x p.y hp i hexc)
  right
  refine ⟨inward i,deletionMA p hp i (by omega) (by omega),?_⟩
  change LocalAddress data (.d p hp) (fun j => level j < level i)
    (mutate (phase p.d p.x p.y i) (inward i))
  by_cases hi : i=2 ∨ i=4 ∨ i=7 ∨ i=9
  · obtain ⟨j,hj,hl⟩ := inward_phase_descent p.d p.x p.y hp i hi
    rw [hj]
    exact LocalAddress.node (D:=data) (r:=Region.d p hp) j hl
  have hbase : i=0 ∨ i=1 ∨ i=5 ∨ i=6 := by omega
  rcases hbase with rfl|rfl|rfl|rfl
  · exact .parent 0
  · exact .parent 1
  · change LocalAddress data (.d p hp) _ (mutate (relabel (D0 p.d p.x p.y) sigma) 1)
    rw [swap_mutation _ 1 (Or.inl rfl)]
    exact .framed (.parent 0) sigma
  · change LocalAddress data (.d p hp) _ (mutate (relabel (D1 p.d p.x p.y) sigma) 1)
    rw [swap_mutation _ 1 (Or.inl rfl)]
    exact .framed (.parent 1) sigma

end QuiverProofs.UnitPendantRegionRules
