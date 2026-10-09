import QuiverProofs.BoundedLStarQ179Split.Prefix11
namespace QuiverProofs.BoundedLStarChecks
open LStar CertificateSearch
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 4096

theorem q179_reachable4 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 4).word) (BoundedLStarData.q179.node 4) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [3]) (ofSix (0) (-2) (-1) (-3) (2) (-1))
  rw [q179_prefix4]
  intro u v; rfl

theorem q179_cyclic4 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 4) := by decide +kernel

theorem q179_edge4_0 :
    EdgeChecks BoundedLStarData.q179 4 0 ((BoundedLStarData.q179.core 4).edges 0) := by decide +kernel

theorem q179_edge4_1 :
    EdgeChecks BoundedLStarData.q179 4 1 ((BoundedLStarData.q179.core 4).edges 1) := by decide +kernel

theorem q179_edge4_2 :
    EdgeChecks BoundedLStarData.q179 4 2 ((BoundedLStarData.q179.core 4).edges 2) := by decide +kernel

theorem q179_edge4_3 :
    EdgeChecks BoundedLStarData.q179 4 3 ((BoundedLStarData.q179.core 4).edges 3) := by decide +kernel

theorem q179_triangles4 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 4) = true := by decide +kernel

theorem q179_descent4 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 4) = true := by
  change allTriangleDescentsCheck (ofSix (0) (-2) (-1) (-3) (2) (-1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable5 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 5).word) (BoundedLStarData.q179.node 5) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [0,1]) (ofSix (-2) (2) (-1) (1) (0) (3))
  rw [q179_prefix5]
  intro u v; rfl

theorem q179_cyclic5 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 5) := by decide +kernel

theorem q179_edge5_0 :
    EdgeChecks BoundedLStarData.q179 5 0 ((BoundedLStarData.q179.core 5).edges 0) := by decide +kernel

theorem q179_edge5_1 :
    EdgeChecks BoundedLStarData.q179 5 1 ((BoundedLStarData.q179.core 5).edges 1) := by decide +kernel

theorem q179_edge5_2 :
    EdgeChecks BoundedLStarData.q179 5 2 ((BoundedLStarData.q179.core 5).edges 2) := by decide +kernel

theorem q179_edge5_3 :
    EdgeChecks BoundedLStarData.q179 5 3 ((BoundedLStarData.q179.core 5).edges 3) := by decide +kernel

theorem q179_triangles5 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 5) = true := by decide +kernel

theorem q179_descent5 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 5) = true := by
  change allTriangleDescentsCheck (ofSix (-2) (2) (-1) (1) (0) (3)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable6 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 6).word) (BoundedLStarData.q179.node 6) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [0,2]) (ofSix (4) (-2) (5) (1) (0) (-3))
  rw [q179_prefix6]
  intro u v; rfl

theorem q179_cyclic6 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 6) := by decide +kernel

theorem q179_edge6_0 :
    EdgeChecks BoundedLStarData.q179 6 0 ((BoundedLStarData.q179.core 6).edges 0) := by decide +kernel

theorem q179_edge6_1 :
    EdgeChecks BoundedLStarData.q179 6 1 ((BoundedLStarData.q179.core 6).edges 1) := by decide +kernel

theorem q179_edge6_2 :
    EdgeChecks BoundedLStarData.q179 6 2 ((BoundedLStarData.q179.core 6).edges 2) := by decide +kernel

theorem q179_edge6_3 :
    EdgeChecks BoundedLStarData.q179 6 3 ((BoundedLStarData.q179.core 6).edges 3) := by decide +kernel

theorem q179_triangles6 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 6) = true := by decide +kernel

theorem q179_descent6 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 6) = true := by
  change allTriangleDescentsCheck (ofSix (4) (-2) (5) (1) (0) (-3)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable7 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 7).word) (BoundedLStarData.q179.node 7) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [0,3]) (ofSix (2) (-1) (1) (-1) (0) (-3))
  rw [q179_prefix7]
  intro u v; rfl

theorem q179_cyclic7 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 7) := by decide +kernel

theorem q179_edge7_0 :
    EdgeChecks BoundedLStarData.q179 7 0 ((BoundedLStarData.q179.core 7).edges 0) := by decide +kernel

theorem q179_edge7_1 :
    EdgeChecks BoundedLStarData.q179 7 1 ((BoundedLStarData.q179.core 7).edges 1) := by decide +kernel

theorem q179_edge7_2 :
    EdgeChecks BoundedLStarData.q179 7 2 ((BoundedLStarData.q179.core 7).edges 2) := by decide +kernel

theorem q179_edge7_3 :
    EdgeChecks BoundedLStarData.q179 7 3 ((BoundedLStarData.q179.core 7).edges 3) := by decide +kernel

theorem q179_triangles7 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 7) = true := by decide +kernel

theorem q179_descent7 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 7) = true := by
  change allTriangleDescentsCheck (ofSix (2) (-1) (1) (-1) (0) (-3)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

end QuiverProofs.BoundedLStarChecks
