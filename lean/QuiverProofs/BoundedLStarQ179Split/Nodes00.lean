import QuiverProofs.BoundedLStarQ179Split.Prefix11
namespace QuiverProofs.BoundedLStarChecks
open LStar CertificateSearch
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 4096

theorem q179_reachable0 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 0).word) (BoundedLStarData.q179.node 0) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) []) (ofSix (-2) (-2) (1) (-1) (-2) (1))
  rw [q179_prefix0]
  intro u v; rfl

theorem q179_cyclic0 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 0) := by decide +kernel

theorem q179_edge0_0 :
    EdgeChecks BoundedLStarData.q179 0 0 ((BoundedLStarData.q179.core 0).edges 0) := by decide +kernel

theorem q179_edge0_1 :
    EdgeChecks BoundedLStarData.q179 0 1 ((BoundedLStarData.q179.core 0).edges 1) := by decide +kernel

theorem q179_edge0_2 :
    EdgeChecks BoundedLStarData.q179 0 2 ((BoundedLStarData.q179.core 0).edges 2) := by decide +kernel

theorem q179_edge0_3 :
    EdgeChecks BoundedLStarData.q179 0 3 ((BoundedLStarData.q179.core 0).edges 3) := by decide +kernel

theorem q179_triangles0 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 0) = true := by decide +kernel

theorem q179_descent0 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 0) = true := by
  change allTriangleDescentsCheck (ofSix (-2) (-2) (1) (-1) (-2) (1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable1 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 1).word) (BoundedLStarData.q179.node 1) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [0]) (ofSix (2) (2) (-1) (-1) (0) (3))
  rw [q179_prefix1]
  intro u v; rfl

theorem q179_cyclic1 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 1) := by decide +kernel

theorem q179_edge1_0 :
    EdgeChecks BoundedLStarData.q179 1 0 ((BoundedLStarData.q179.core 1).edges 0) := by decide +kernel

theorem q179_edge1_1 :
    EdgeChecks BoundedLStarData.q179 1 1 ((BoundedLStarData.q179.core 1).edges 1) := by decide +kernel

theorem q179_edge1_2 :
    EdgeChecks BoundedLStarData.q179 1 2 ((BoundedLStarData.q179.core 1).edges 2) := by decide +kernel

theorem q179_edge1_3 :
    EdgeChecks BoundedLStarData.q179 1 3 ((BoundedLStarData.q179.core 1).edges 3) := by decide +kernel

theorem q179_triangles1 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 1) = true := by decide +kernel

theorem q179_descent1 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 1) = true := by
  change allTriangleDescentsCheck (ofSix (2) (2) (-1) (-1) (0) (3)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable2 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 2).word) (BoundedLStarData.q179.node 2) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [1]) (ofSix (2) (-4) (-3) (1) (2) (1))
  rw [q179_prefix2]
  intro u v; rfl

theorem q179_cyclic2 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 2) := by decide +kernel

theorem q179_edge2_0 :
    EdgeChecks BoundedLStarData.q179 2 0 ((BoundedLStarData.q179.core 2).edges 0) := by decide +kernel

theorem q179_edge2_1 :
    EdgeChecks BoundedLStarData.q179 2 1 ((BoundedLStarData.q179.core 2).edges 1) := by decide +kernel

theorem q179_edge2_2 :
    EdgeChecks BoundedLStarData.q179 2 2 ((BoundedLStarData.q179.core 2).edges 2) := by decide +kernel

theorem q179_edge2_3 :
    EdgeChecks BoundedLStarData.q179 2 3 ((BoundedLStarData.q179.core 2).edges 3) := by decide +kernel

theorem q179_triangles2 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 2) = true := by decide +kernel

theorem q179_descent2 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 2) = true := by
  change allTriangleDescentsCheck (ofSix (2) (-4) (-3) (1) (2) (1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable3 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 3).word) (BoundedLStarData.q179.node 3) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [2]) (ofSix (-2) (2) (1) (1) (-2) (-1))
  rw [q179_prefix3]
  intro u v; rfl

theorem q179_cyclic3 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 3) := by decide +kernel

theorem q179_edge3_0 :
    EdgeChecks BoundedLStarData.q179 3 0 ((BoundedLStarData.q179.core 3).edges 0) := by decide +kernel

theorem q179_edge3_1 :
    EdgeChecks BoundedLStarData.q179 3 1 ((BoundedLStarData.q179.core 3).edges 1) := by decide +kernel

theorem q179_edge3_2 :
    EdgeChecks BoundedLStarData.q179 3 2 ((BoundedLStarData.q179.core 3).edges 2) := by decide +kernel

theorem q179_edge3_3 :
    EdgeChecks BoundedLStarData.q179 3 3 ((BoundedLStarData.q179.core 3).edges 3) := by decide +kernel

theorem q179_triangles3 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 3) = true := by decide +kernel

theorem q179_descent3 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 3) = true := by
  change allTriangleDescentsCheck (ofSix (-2) (2) (1) (1) (-2) (-1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

end QuiverProofs.BoundedLStarChecks
