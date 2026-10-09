import QuiverProofs.BoundedLStarQ179Split.Prefix11
namespace QuiverProofs.BoundedLStarChecks
open LStar CertificateSearch
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 4096

theorem q179_reachable56 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 56).word) (BoundedLStarData.q179.node 56) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [3,0,2,1,0]) (ofSix (6) (-16) (-1) (93) (7) (-2))
  rw [q179_prefix56]
  intro u v; rfl

theorem q179_cyclic56 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 56) := by decide +kernel

theorem q179_edge56_0 :
    EdgeChecks BoundedLStarData.q179 56 0 ((BoundedLStarData.q179.core 56).edges 0) := by decide +kernel

theorem q179_edge56_1 :
    EdgeChecks BoundedLStarData.q179 56 1 ((BoundedLStarData.q179.core 56).edges 1) := by decide +kernel

theorem q179_edge56_2 :
    EdgeChecks BoundedLStarData.q179 56 2 ((BoundedLStarData.q179.core 56).edges 2) := by decide +kernel

theorem q179_edge56_3 :
    EdgeChecks BoundedLStarData.q179 56 3 ((BoundedLStarData.q179.core 56).edges 3) := by decide +kernel

theorem q179_triangles56 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 56) = true := by decide +kernel

theorem q179_descent56 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 56) = true := by
  change allTriangleDescentsCheck (ofSix (6) (-16) (-1) (93) (7) (-2)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable57 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 57).word) (BoundedLStarData.q179.node 57) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [3,0,2,1,3]) (ofSix (-6) (18) (-1) (-1) (-1) (2))
  rw [q179_prefix57]
  intro u v; rfl

theorem q179_cyclic57 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 57) := by decide +kernel

theorem q179_edge57_0 :
    EdgeChecks BoundedLStarData.q179 57 0 ((BoundedLStarData.q179.core 57).edges 0) := by decide +kernel

theorem q179_edge57_1 :
    EdgeChecks BoundedLStarData.q179 57 1 ((BoundedLStarData.q179.core 57).edges 1) := by decide +kernel

theorem q179_edge57_2 :
    EdgeChecks BoundedLStarData.q179 57 2 ((BoundedLStarData.q179.core 57).edges 2) := by decide +kernel

theorem q179_edge57_3 :
    EdgeChecks BoundedLStarData.q179 57 3 ((BoundedLStarData.q179.core 57).edges 3) := by decide +kernel

theorem q179_triangles57 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 57) = true := by decide +kernel

theorem q179_descent57 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 57) = true := by
  change allTriangleDescentsCheck (ofSix (-6) (18) (-1) (-1) (-1) (2)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable58 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 58).word) (BoundedLStarData.q179.node 58) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [3,2,0,1,3]) (ofSix (0) (22) (-3) (5) (-1) (8))
  rw [q179_prefix58]
  intro u v; rfl

theorem q179_cyclic58 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 58) := by decide +kernel

theorem q179_edge58_0 :
    EdgeChecks BoundedLStarData.q179 58 0 ((BoundedLStarData.q179.core 58).edges 0) := by decide +kernel

theorem q179_edge58_1 :
    EdgeChecks BoundedLStarData.q179 58 1 ((BoundedLStarData.q179.core 58).edges 1) := by decide +kernel

theorem q179_edge58_2 :
    EdgeChecks BoundedLStarData.q179 58 2 ((BoundedLStarData.q179.core 58).edges 2) := by decide +kernel

theorem q179_edge58_3 :
    EdgeChecks BoundedLStarData.q179 58 3 ((BoundedLStarData.q179.core 58).edges 3) := by decide +kernel

theorem q179_triangles58 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 58) = true := by decide +kernel

theorem q179_descent58 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 58) = true := by
  change allTriangleDescentsCheck (ofSix (0) (22) (-3) (5) (-1) (8)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable59 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 59).word) (BoundedLStarData.q179.node 59) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [3,2,0,3,1]) (ofSix (-3) (22) (0) (-3) (-1) (5))
  rw [q179_prefix59]
  intro u v; rfl

theorem q179_cyclic59 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 59) := by decide +kernel

theorem q179_edge59_0 :
    EdgeChecks BoundedLStarData.q179 59 0 ((BoundedLStarData.q179.core 59).edges 0) := by decide +kernel

theorem q179_edge59_1 :
    EdgeChecks BoundedLStarData.q179 59 1 ((BoundedLStarData.q179.core 59).edges 1) := by decide +kernel

theorem q179_edge59_2 :
    EdgeChecks BoundedLStarData.q179 59 2 ((BoundedLStarData.q179.core 59).edges 2) := by decide +kernel

theorem q179_edge59_3 :
    EdgeChecks BoundedLStarData.q179 59 3 ((BoundedLStarData.q179.core 59).edges 3) := by decide +kernel

theorem q179_triangles59 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 59) = true := by decide +kernel

theorem q179_descent59 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 59) = true := by
  change allTriangleDescentsCheck (ofSix (-3) (22) (0) (-3) (-1) (5)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

end QuiverProofs.BoundedLStarChecks
