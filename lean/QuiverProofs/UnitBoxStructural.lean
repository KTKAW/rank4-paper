import QuiverProofs.UnitRegionRules
import QuiverProofs.L0Exclusion
import QuiverProofs.UnitBoxFamily

/-! A uniform three-state core for the unit-box family. Its two outward
choices enter the proved unit-pendant continuation with both parents
identified in the core. This bypasses any proper-order existence bridge. -/
namespace QuiverProofs.UnitBoxStructural
open RecursiveRegions TriangleRegions GlobalFamilies
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

private theorem fin4 (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
private theorem fin3 (i : Fin 3) : i=0 ∨ i=1 ∨ i=2 := by omega

def node (b : Int) (i : Fin 3) : Matrix 4 := match i.val with
  | 0 => ofSix (-1) 0 b (-b) 0 (-1)
  | 1 => ofSix 1 0 (-b) (-b) b (-1)
  | _ => ofSix (-1) 0 0 b (-b) (b*b-1)

def attached (b : Int) : UnitPendantStrip.Parameters := ⟨b*b-1,b,b*(b*b-1)-b⟩

theorem parameter_bounds (b : Int) (hb : 2≤b) :
    3≤b*b-1 ∧ b<b*b-1 ∧ b*b-1<b*(b*b-1)-b ∧ b<b*(b*b-1)-b := by
  have hsq := Int.mul_le_mul_of_nonneg_right hb (show 0≤b by omega)
  have hm := Int.mul_le_mul_of_nonneg_right hb (show 0≤b*b-1 by omega)
  omega

theorem attached_domain (b : Int) (hb : 2≤b) : UnitPendantStrip.parameterDomain (attached b) := by
  have hh := parameter_bounds b hb
  change 2≤b*b-1 ∧ 2≤b ∧ b*b-1<b*(b*b-1)-b ∧ b<b*(b*b-1)-b
  omega

def region (b : Int) (hb : 2≤b) : UnitRegionData.Region :=
  .d (attached b) (attached_domain b hb)

def Core (b : Int) (Q : Matrix 4) : Prop := ∃ i, Q=node b i
abbrev SafeCore (b : Int) := Safe UnitRegionData.data (Core b)

theorem node_skew (b : Int) (i : Fin 3) : SkewSymmetric (node b i) := by
  rcases fin3 i with rfl|rfl|rfl <;> exact ofSix_skew _ _ _ _ _ _

theorem node_cyclic (b : Int) (hb : 2≤b) (i : Fin 3) : ¬ Acyclic (node b i) := by
  have hh := parameter_bounds b hb
  rcases fin3 i with rfl|rfl|rfl <;> rintro ⟨rank,hr⟩
  · have h0 := hr 0 3 (by simp [node,ofSix];omega)
    have h1 := hr 3 2 (by simp [node,ofSix])
    have h2 := hr 2 1 (by simp [node,ofSix];omega)
    have h3 := hr 1 0 (by simp [node,ofSix])
    omega
  · have h0 := hr 0 1 (by simp [node,ofSix])
    have h1 := hr 1 3 (by simp [node,ofSix];omega)
    have h2 := hr 3 0 (by simp [node,ofSix];omega)
    omega
  · have h0 := hr 1 2 (by simp [node,ofSix];omega)
    have h1 := hr 2 3 (by simp [node,ofSix];omega)
    have h2 := hr 3 1 (by simp [node,ofSix];omega)
    omega

theorem node_triangles (b : Int) (hb : 2≤b) (i : Fin 3) : AllTrianglesMA (node b i) := by
  have hh := parameter_bounds b hb
  rcases fin3 i with rfl|rfl|rfl
  · change AllTrianglesMA (ofSix (-1) 0 b (-b) 0 (-1))
    apply ofSix_allTrianglesMA <;> apply weak_triangle_MA <;> omega
  · change AllTrianglesMA (ofSix 1 0 (-b) (-b) b (-1))
    apply ofSix_allTrianglesMA <;> apply weak_triangle_MA <;> omega
  · change AllTrianglesMA (ofSix (-1) 0 0 b (-b) (b*b-1))
    apply ofSix_allTrianglesMA
    · apply rankThree_cycle_MA_of_not_region b (b*b-1) (- -b) (by omega) (by omega) (by omega)
      intro hreg
      have hc := hreg.2.2.2
      have hid : triangleMarkov b (b*b-1) (- -b)=b*b+1 := by unfold triangleMarkov;grind
      rw [hid] at hc
      omega
    all_goals apply weak_triangle_MA <;> omega

theorem node_safe (b : Int) (i : Fin 3) : SafeCore b (node b i) :=
  Safe.central ⟨i,rfl⟩

def frame0123 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | _ => 3),(fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | _ => 3),by decide,by decide⟩

def frame1032 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | _ => 2),(fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | _ => 2),by decide,by decide⟩

def frame2301 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | _ => 1),(fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | _ => 1),by decide,by decide⟩

def frame0132 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | _ => 2),(fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | _ => 2),by decide,by decide⟩

def frame0231 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | _ => 1),(fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | _ => 2),by decide,by decide⟩

def frame0321 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | _ => 1),(fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | _ => 1),by decide,by decide⟩

theorem edge_0_0 (b : Int) (hb : 2≤b) :
    mutate (node b 0) 0=relabel (node b 1) frame0123.symm := by
  have hh := parameter_bounds b hb
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [node,frame0123,Relabeling.symm,relabel,reverse,mutate,correction,ofSix] <;> grind

theorem edge_0_1 (b : Int) (hb : 2≤b) :
    mutate (node b 0) 1=reverse (relabel (node b 1) frame1032.symm) := by
  have hh := parameter_bounds b hb
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [node,frame1032,Relabeling.symm,relabel,reverse,mutate,correction,ofSix] <;> grind

theorem edge_0_2 (b : Int) (hb : 2≤b) :
    mutate (node b 0) 2=reverse (relabel (node b 1) frame0123.symm) := by
  have hh := parameter_bounds b hb
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [node,frame0123,Relabeling.symm,relabel,reverse,mutate,correction,ofSix] <;> grind

theorem edge_0_3 (b : Int) (hb : 2≤b) :
    mutate (node b 0) 3=relabel (node b 1) frame1032.symm := by
  have hh := parameter_bounds b hb
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [node,frame1032,Relabeling.symm,relabel,reverse,mutate,correction,ofSix] <;> grind

theorem edge_1_0 (b : Int) (hb : 2≤b) :
    mutate (node b 1) 0=relabel (node b 0) frame0123.symm := by
  have hh := parameter_bounds b hb
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [node,frame0123,Relabeling.symm,relabel,reverse,mutate,correction,ofSix] <;> grind

theorem edge_1_1 (b : Int) (hb : 2≤b) :
    mutate (node b 1) 1=relabel (node b 2) frame0123.symm := by
  have hh := parameter_bounds b hb
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [node,frame0123,Relabeling.symm,relabel,reverse,mutate,correction,ofSix] <;> grind

theorem edge_1_2 (b : Int) (hb : 2≤b) :
    mutate (node b 1) 2=reverse (relabel (node b 0) frame0123.symm) := by
  have hh := parameter_bounds b hb
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [node,frame0123,Relabeling.symm,relabel,reverse,mutate,correction,ofSix] <;> grind

theorem edge_1_3 (b : Int) (hb : 2≤b) :
    mutate (node b 1) 3=reverse (relabel (node b 2) frame2301.symm) := by
  have hh := parameter_bounds b hb
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [node,frame2301,Relabeling.symm,relabel,reverse,mutate,correction,ofSix] <;> grind

theorem edge_2_0 (b : Int) (hb : 2≤b) :
    mutate (node b 2) 0=reverse (relabel (node b 2) frame0132.symm) := by
  have hh := parameter_bounds b hb
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [node,frame0132,Relabeling.symm,relabel,reverse,mutate,correction,ofSix] <;> grind

theorem edge_2_1 (b : Int) (hb : 2≤b) :
    mutate (node b 2) 1=relabel (node b 1) frame0123.symm := by
  have hh := parameter_bounds b hb
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [node,frame0123,Relabeling.symm,relabel,reverse,mutate,correction,ofSix] <;> grind

theorem parent_0 (b : Int) (hb : 2≤b) :
    UnitPendantStrip.parent (attached b) 0=reverse (relabel (node b 2) frame0231) := by
  have hh := parameter_bounds b hb
  have hdom := attached_domain b hb
  funext i k
  rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 k with rfl|rfl|rfl|rfl <;>
    simp [UnitPendantStrip.parent,UnitPendantStrip.node,UnitPendantStrip.phase,
      UnitPendantStrip.D0,UnitPendantStrip.D1,attached,node,frame0231,relabel,reverse,mutate,correction,ofSix] <;> grind

theorem parent_1 (b : Int) (hb : 2≤b) :
    UnitPendantStrip.parent (attached b) 1=relabel (node b 2) frame0321 := by
  have hh := parameter_bounds b hb
  have hdom := attached_domain b hb
  funext i k
  rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 k with rfl|rfl|rfl|rfl <;>
    simp [UnitPendantStrip.parent,UnitPendantStrip.node,UnitPendantStrip.phase,
      UnitPendantStrip.D0,UnitPendantStrip.D1,attached,node,frame0321,relabel,reverse,mutate,correction,ofSix] <;> grind

theorem region_edge_2 (b : Int) (hb : 2≤b) :
    mutate (node b 2) 2=reverse (relabel (UnitPendantStrip.node (attached b) 0) frame0231.symm) := by
  have hh := parameter_bounds b hb
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [UnitPendantStrip.node,UnitPendantStrip.phase,UnitPendantStrip.D0,UnitPendantStrip.D1,
      attached,node,frame0231,Relabeling.symm,relabel,reverse,mutate,correction,ofSix] <;> grind

theorem region_edge_3 (b : Int) (hb : 2≤b) :
    mutate (node b 2) 3=relabel (UnitPendantStrip.node (attached b) 1) frame0321.symm := by
  have hh := parameter_bounds b hb
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [UnitPendantStrip.node,UnitPendantStrip.phase,UnitPendantStrip.D0,UnitPendantStrip.D1,
      attached,node,frame0321,Relabeling.symm,relabel,reverse,mutate,correction,ofSix] <;> grind

theorem parents_safe (b : Int) (hb : 2≤b) (j : Fin 2) :
    SafeCore b (UnitRegionData.data.parent (region b hb) j) := by
  have hj : j=0 ∨ j=1 := by omega
  rcases hj with rfl|rfl
  · change SafeCore b (UnitPendantStrip.parent (attached b) 0)
    rw [parent_0 b hb]
    exact Safe.reversed (Safe.framed (node_safe b 2) frame0231)
  · change SafeCore b (UnitPendantStrip.parent (attached b) 1)
    rw [parent_1 b hb]
    exact Safe.framed (node_safe b 2) frame0321

theorem region_safe (b : Int) (hb : 2≤b) (i : Fin 10) :
    SafeCore b (UnitPendantStrip.node (attached b) i) :=
  Safe.region (D:=UnitRegionData.data) (core:=Core b) (region b hb) (parents_safe b hb) i

theorem node_edges (b : Int) (hb : 2≤b) (i : Fin 3) (k : Fin 4) :
    SafeCore b (mutate (node b i) k) := by
  rcases fin3 i with rfl|rfl|rfl <;> rcases fin4 k with rfl|rfl|rfl|rfl
  · rw [edge_0_0 b hb]; exact Safe.framed (node_safe b 1) frame0123.symm
  · rw [edge_0_1 b hb]; exact Safe.reversed (Safe.framed (node_safe b 1) frame1032.symm)
  · rw [edge_0_2 b hb]; exact Safe.reversed (Safe.framed (node_safe b 1) frame0123.symm)
  · rw [edge_0_3 b hb]; exact Safe.framed (node_safe b 1) frame1032.symm
  · rw [edge_1_0 b hb]; exact Safe.framed (node_safe b 0) frame0123.symm
  · rw [edge_1_1 b hb]; exact Safe.framed (node_safe b 2) frame0123.symm
  · rw [edge_1_2 b hb]; exact Safe.reversed (Safe.framed (node_safe b 0) frame0123.symm)
  · rw [edge_1_3 b hb]; exact Safe.reversed (Safe.framed (node_safe b 2) frame2301.symm)
  · rw [edge_2_0 b hb]; exact Safe.reversed (Safe.framed (node_safe b 2) frame0132.symm)
  · rw [edge_2_1 b hb]; exact Safe.framed (node_safe b 1) frame0123.symm
  · rw [region_edge_2 b hb]; exact Safe.reversed (Safe.framed (region_safe b hb 0) frame0231.symm)
  · rw [region_edge_3 b hb]; exact Safe.framed (region_safe b hb 1) frame0321.symm

theorem core_skew (b : Int) (Q : Matrix 4) (hQ : Core b Q) : SkewSymmetric Q := by
  obtain ⟨i,rfl⟩ := hQ
  exact node_skew b i

theorem core_cyclic (b : Int) (hb : 2≤b) (Q : Matrix 4) (hQ : Core b Q) : ¬ Acyclic Q := by
  obtain ⟨i,rfl⟩ := hQ
  exact node_cyclic b hb i

theorem core_triangles (b : Int) (hb : 2≤b) (Q : Matrix 4) (hQ : Core b Q) : AllTrianglesMA Q := by
  obtain ⟨i,rfl⟩ := hQ
  exact node_triangles b hb i

theorem core_edges (b : Int) (hb : 2≤b) (Q : Matrix 4) (hQ : Core b Q) (k : Fin 4) :
    SafeCore b (mutate Q k) := by
  obtain ⟨i,rfl⟩ := hQ
  exact node_edges b hb i k

/-- Unconditional NMA of every unit box in the exact source range. -/
theorem NMA (b : Int) (hb : 2≤b) : ¬ MutationAcyclic (UnitBoxFamily.quiver b) := by
  change ¬ MutationAcyclic (node b 0)
  exact safe_NMA UnitRegionData.data UnitRegionRules.rules (Core b)
    (core_skew b) (core_cyclic b hb) (core_edges b hb) (node_safe b 0)

/-- A new consequence of the complete N/D rules: every descendant triangle
of every unit box is MA. The source's earlier unresolved avoidance question
is settled by the separate retained-triangle argument. -/
theorem global_triangle_avoidance (b : Int) (hb : 2≤b) (word : List (Fin 4)) :
    AllTrianglesMA (applyWord (UnitBoxFamily.quiver b) word) := by
  change AllTrianglesMA (applyWord (node b 0) word)
  exact safe_global_triangle_avoidance UnitRegionData.data UnitRegionRules.rules
    UnitRegionRules.triangleRules (Core b) (core_skew b) (core_triangles b hb)
    (core_edges b hb) (node_safe b 0) word

theorem no_L0_certificate (b : Int) (hb : 2≤b) (c : CertificateSearch.RegionCertificate) :
    CertificateSearch.acceptCertificate (UnitBoxFamily.quiver b) c ≠ true := by
  intro h
  exact UnitBoxFamily.no_finite_core_exterior_cover b hb
    (L0Exclusion.accepted_implies_finite_cover _ c h)

/-- The complete unit-box NMA assertion, strengthened by global avoidance
and actual old-language certificate exclusion. The b=1 endpoint remains MA. -/
theorem unit_box_family (b : Int) (hb : 2≤b) :
    ¬ MutationAcyclic (UnitBoxFamily.quiver b) ∧
    (∀ word : List (Fin 4), AllTrianglesMA (applyWord (UnitBoxFamily.quiver b) word)) ∧
    (∀ c : CertificateSearch.RegionCertificate,
      CertificateSearch.acceptCertificate (UnitBoxFamily.quiver b) c ≠ true) :=
  ⟨NMA b hb,global_triangle_avoidance b hb,no_L0_certificate b hb⟩

/-- The exact source q577 frame: new labels read old vertices (3,0,1,2). -/
def boundedFrame : Relabeling 4 :=
  ⟨fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | _ => 2,
   fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | _ => 0,
   by decide,by decide⟩

theorem q577_identification :
    relabel (UnitBoxFamily.quiver 2) boundedFrame = ofSix (-2) 0 1 (-1) 0 (-2) := by
  funext i j
  revert i j
  decide

/-- A new unconditional bounded negative parent, for the exact saved q577. -/
theorem nma_q577 : ¬ MutationAcyclic (ofSix (-2) 0 1 (-1) 0 (-2)) := by
  rw [←q577_identification]
  intro h
  exact NMA 2 (by decide) ((MA_relabel_iff _ boundedFrame).mp h)

def boundedFrame517 : Relabeling 4 :=
  ⟨fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | _ => 1,
   fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | _ => 0,
   by decide,by decide⟩

theorem q517_identification :
    reverse (relabel (node 2 1) boundedFrame517) = ofSix (-2) (-1) 2 0 (-1) (-2) := by
  funext i j
  revert i j
  decide

theorem nma_q517 : ¬ MutationAcyclic (ofSix (-2) (-1) 2 0 (-1) (-2)) := by
  have hn : ¬ MutationAcyclic (node 2 1) :=
    safe_NMA UnitRegionData.data UnitRegionRules.rules (Core 2)
      (core_skew 2) (core_cyclic 2 (by decide)) (core_edges 2 (by decide)) (node_safe 2 1)
  rw [←q517_identification]
  intro h
  exact hn ((MA_relabel_iff _ boundedFrame517).mp
    ((MA_reverse_iff _ (relabel_skew _ boundedFrame517 (node_skew 2 1))).mp h))

end QuiverProofs.UnitBoxStructural
