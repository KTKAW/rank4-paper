import QuiverProofs.BoundedLStarQ179Split.Prefix11
namespace QuiverProofs.BoundedLStarChecks
open LStar CertificateSearch
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 4096

theorem q179_reachable20 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 20).word) (BoundedLStarData.q179.node 20) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [1,2,3]) (ofSix (-11) (4) (3) (2) (-3) (1))
  rw [q179_prefix20]
  intro u v; rfl

theorem q179_cyclic20 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 20) := by decide +kernel

theorem q179_edge20_0 :
    EdgeChecks BoundedLStarData.q179 20 0 ((BoundedLStarData.q179.core 20).edges 0) := by decide +kernel

theorem q179_edge20_1 :
    EdgeChecks BoundedLStarData.q179 20 1 ((BoundedLStarData.q179.core 20).edges 1) := by decide +kernel

theorem q179_edge20_2 :
    EdgeChecks BoundedLStarData.q179 20 2 ((BoundedLStarData.q179.core 20).edges 2) := by decide +kernel

theorem q179_edge20_3 :
    EdgeChecks BoundedLStarData.q179 20 3 ((BoundedLStarData.q179.core 20).edges 3) := by decide +kernel

theorem q179_triangles20 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 20) = true := by decide +kernel

theorem q179_descent20 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 20) = true := by
  change allTriangleDescentsCheck (ofSix (-11) (4) (3) (2) (-3) (1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable21 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 21).word) (BoundedLStarData.q179.node 21) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [1,3,1]) (ofSix (4) (-7) (-5) (-1) (2) (-3))
  rw [q179_prefix21]
  intro u v; rfl

theorem q179_cyclic21 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 21) := by decide +kernel

theorem q179_edge21_0 :
    EdgeChecks BoundedLStarData.q179 21 0 ((BoundedLStarData.q179.core 21).edges 0) := by decide +kernel

theorem q179_edge21_1 :
    EdgeChecks BoundedLStarData.q179 21 1 ((BoundedLStarData.q179.core 21).edges 1) := by decide +kernel

theorem q179_edge21_2 :
    EdgeChecks BoundedLStarData.q179 21 2 ((BoundedLStarData.q179.core 21).edges 2) := by decide +kernel

theorem q179_edge21_3 :
    EdgeChecks BoundedLStarData.q179 21 3 ((BoundedLStarData.q179.core 21).edges 3) := by decide +kernel

theorem q179_triangles21 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 21) = true := by decide +kernel

theorem q179_descent21 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 21) = true := by
  change allTriangleDescentsCheck (ofSix (4) (-7) (-5) (-1) (2) (-3)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable22 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 22).word) (BoundedLStarData.q179.node 22) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [1,3,2]) (ofSix (-11) (7) (-4) (-1) (-2) (1))
  rw [q179_prefix22]
  intro u v; rfl

theorem q179_cyclic22 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 22) := by decide +kernel

theorem q179_edge22_0 :
    EdgeChecks BoundedLStarData.q179 22 0 ((BoundedLStarData.q179.core 22).edges 0) := by decide +kernel

theorem q179_edge22_1 :
    EdgeChecks BoundedLStarData.q179 22 1 ((BoundedLStarData.q179.core 22).edges 1) := by decide +kernel

theorem q179_edge22_2 :
    EdgeChecks BoundedLStarData.q179 22 2 ((BoundedLStarData.q179.core 22).edges 2) := by decide +kernel

theorem q179_edge22_3 :
    EdgeChecks BoundedLStarData.q179 22 3 ((BoundedLStarData.q179.core 22).edges 3) := by decide +kernel

theorem q179_triangles22 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 22) = true := by decide +kernel

theorem q179_descent22 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 22) = true := by
  change allTriangleDescentsCheck (ofSix (-11) (7) (-4) (-1) (-2) (1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable23 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 23).word) (BoundedLStarData.q179.node 23) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [2,0,1]) (ofSix (-2) (8) (-1) (-5) (0) (-1))
  rw [q179_prefix23]
  intro u v; rfl

theorem q179_cyclic23 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 23) := by decide +kernel

theorem q179_edge23_0 :
    EdgeChecks BoundedLStarData.q179 23 0 ((BoundedLStarData.q179.core 23).edges 0) := by decide +kernel

theorem q179_edge23_1 :
    EdgeChecks BoundedLStarData.q179 23 1 ((BoundedLStarData.q179.core 23).edges 1) := by decide +kernel

theorem q179_edge23_2 :
    EdgeChecks BoundedLStarData.q179 23 2 ((BoundedLStarData.q179.core 23).edges 2) := by decide +kernel

theorem q179_edge23_3 :
    EdgeChecks BoundedLStarData.q179 23 3 ((BoundedLStarData.q179.core 23).edges 3) := by decide +kernel

theorem q179_triangles23 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 23) = true := by decide +kernel

theorem q179_descent23 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 23) = true := by
  change allTriangleDescentsCheck (ofSix (-2) (8) (-1) (-5) (0) (-1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

end QuiverProofs.BoundedLStarChecks
