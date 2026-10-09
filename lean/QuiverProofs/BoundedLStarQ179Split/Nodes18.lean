import QuiverProofs.BoundedLStarQ179Split.Prefix11
namespace QuiverProofs.BoundedLStarChecks
open LStar CertificateSearch
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 4096

theorem q179_reachable72 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 72).word) (BoundedLStarData.q179.node 72) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [3,0,2,1,3,0]) (ofSix (6) (-18) (1) (107) (-1) (-16))
  rw [q179_prefix72]
  intro u v; rfl

theorem q179_cyclic72 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 72) := by decide +kernel

theorem q179_edge72_0 :
    EdgeChecks BoundedLStarData.q179 72 0 ((BoundedLStarData.q179.core 72).edges 0) := by decide +kernel

theorem q179_edge72_1 :
    EdgeChecks BoundedLStarData.q179 72 1 ((BoundedLStarData.q179.core 72).edges 1) := by decide +kernel

theorem q179_edge72_2 :
    EdgeChecks BoundedLStarData.q179 72 2 ((BoundedLStarData.q179.core 72).edges 2) := by decide +kernel

theorem q179_edge72_3 :
    EdgeChecks BoundedLStarData.q179 72 3 ((BoundedLStarData.q179.core 72).edges 3) := by decide +kernel

theorem q179_triangles72 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 72) = true := by decide +kernel

theorem q179_descent72 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 72) = true := by
  change allTriangleDescentsCheck (ofSix (6) (-18) (1) (107) (-1) (-16)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable73 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 73).word) (BoundedLStarData.q179.node 73) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [3,0,2,1,3,2]) (ofSix (12) (-18) (35) (1) (-1) (-2))
  rw [q179_prefix73]
  intro u v; rfl

theorem q179_cyclic73 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 73) := by decide +kernel

theorem q179_edge73_0 :
    EdgeChecks BoundedLStarData.q179 73 0 ((BoundedLStarData.q179.core 73).edges 0) := by decide +kernel

theorem q179_edge73_1 :
    EdgeChecks BoundedLStarData.q179 73 1 ((BoundedLStarData.q179.core 73).edges 1) := by decide +kernel

theorem q179_edge73_2 :
    EdgeChecks BoundedLStarData.q179 73 2 ((BoundedLStarData.q179.core 73).edges 2) := by decide +kernel

theorem q179_edge73_3 :
    EdgeChecks BoundedLStarData.q179 73 3 ((BoundedLStarData.q179.core 73).edges 3) := by decide +kernel

theorem q179_triangles73 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 73) = true := by decide +kernel

theorem q179_descent73 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 73) = true := by
  change allTriangleDescentsCheck (ofSix (12) (-18) (35) (1) (-1) (-2)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable74 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 74).word) (BoundedLStarData.q179.node 74) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [0,1,0,1,0,2,0]) (ofSix (86) (-8) (1) (677) (13) (-9))
  rw [q179_prefix74]
  intro u v; rfl

theorem q179_cyclic74 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 74) := by decide +kernel

theorem q179_edge74_0 :
    EdgeChecks BoundedLStarData.q179 74 0 ((BoundedLStarData.q179.core 74).edges 0) := by decide +kernel

theorem q179_edge74_1 :
    EdgeChecks BoundedLStarData.q179 74 1 ((BoundedLStarData.q179.core 74).edges 1) := by decide +kernel

theorem q179_edge74_2 :
    EdgeChecks BoundedLStarData.q179 74 2 ((BoundedLStarData.q179.core 74).edges 2) := by decide +kernel

theorem q179_edge74_3 :
    EdgeChecks BoundedLStarData.q179 74 3 ((BoundedLStarData.q179.core 74).edges 3) := by decide +kernel

theorem q179_triangles74 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 74) = true := by decide +kernel

theorem q179_descent74 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 74) = true := by
  change allTriangleDescentsCheck (ofSix (86) (-8) (1) (677) (13) (-9)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable75 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 75).word) (BoundedLStarData.q179.node 75) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [0,1,0,1,0,2,3]) (ofSix (-99) (8) (1) (2) (-13) (1))
  rw [q179_prefix75]
  intro u v; rfl

theorem q179_cyclic75 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 75) := by decide +kernel

theorem q179_edge75_0 :
    EdgeChecks BoundedLStarData.q179 75 0 ((BoundedLStarData.q179.core 75).edges 0) := by decide +kernel

theorem q179_edge75_1 :
    EdgeChecks BoundedLStarData.q179 75 1 ((BoundedLStarData.q179.core 75).edges 1) := by decide +kernel

theorem q179_edge75_2 :
    EdgeChecks BoundedLStarData.q179 75 2 ((BoundedLStarData.q179.core 75).edges 2) := by decide +kernel

theorem q179_edge75_3 :
    EdgeChecks BoundedLStarData.q179 75 3 ((BoundedLStarData.q179.core 75).edges 3) := by decide +kernel

theorem q179_triangles75 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 75) = true := by decide +kernel

theorem q179_descent75 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 75) = true := by
  change allTriangleDescentsCheck (ofSix (-99) (8) (1) (2) (-13) (1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

end QuiverProofs.BoundedLStarChecks
