import QuiverProofs.BoundedLStarQ179Split.Prefix11
namespace QuiverProofs.BoundedLStarChecks
open LStar CertificateSearch
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 4096

theorem q179_reachable16 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 16).word) (BoundedLStarData.q179.node 16) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [0,1,0]) (ofSix (2) (-2) (1) (5) (0) (1))
  rw [q179_prefix16]
  intro u v; rfl

theorem q179_cyclic16 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 16) := by decide +kernel

theorem q179_edge16_0 :
    EdgeChecks BoundedLStarData.q179 16 0 ((BoundedLStarData.q179.core 16).edges 0) := by decide +kernel

theorem q179_edge16_1 :
    EdgeChecks BoundedLStarData.q179 16 1 ((BoundedLStarData.q179.core 16).edges 1) := by decide +kernel

theorem q179_edge16_2 :
    EdgeChecks BoundedLStarData.q179 16 2 ((BoundedLStarData.q179.core 16).edges 2) := by decide +kernel

theorem q179_edge16_3 :
    EdgeChecks BoundedLStarData.q179 16 3 ((BoundedLStarData.q179.core 16).edges 3) := by decide +kernel

theorem q179_triangles16 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 16) = true := by decide +kernel

theorem q179_descent16 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 16) = true := by
  change allTriangleDescentsCheck (ofSix (2) (-2) (1) (5) (0) (1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable17 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 17).word) (BoundedLStarData.q179.node 17) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [0,1,2]) (ofSix (-2) (-2) (5) (-1) (3) (-3))
  rw [q179_prefix17]
  intro u v; rfl

theorem q179_cyclic17 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 17) := by decide +kernel

theorem q179_edge17_0 :
    EdgeChecks BoundedLStarData.q179 17 0 ((BoundedLStarData.q179.core 17).edges 0) := by decide +kernel

theorem q179_edge17_1 :
    EdgeChecks BoundedLStarData.q179 17 1 ((BoundedLStarData.q179.core 17).edges 1) := by decide +kernel

theorem q179_edge17_2 :
    EdgeChecks BoundedLStarData.q179 17 2 ((BoundedLStarData.q179.core 17).edges 2) := by decide +kernel

theorem q179_edge17_3 :
    EdgeChecks BoundedLStarData.q179 17 3 ((BoundedLStarData.q179.core 17).edges 3) := by decide +kernel

theorem q179_triangles17 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 17) = true := by decide +kernel

theorem q179_descent17 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 17) = true := by
  change allTriangleDescentsCheck (ofSix (-2) (-2) (5) (-1) (3) (-3)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable18 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 18).word) (BoundedLStarData.q179.node 18) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [0,2,1]) (ofSix (-4) (2) (5) (-1) (0) (-3))
  rw [q179_prefix18]
  intro u v; rfl

theorem q179_cyclic18 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 18) := by decide +kernel

theorem q179_edge18_0 :
    EdgeChecks BoundedLStarData.q179 18 0 ((BoundedLStarData.q179.core 18).edges 0) := by decide +kernel

theorem q179_edge18_1 :
    EdgeChecks BoundedLStarData.q179 18 1 ((BoundedLStarData.q179.core 18).edges 1) := by decide +kernel

theorem q179_edge18_2 :
    EdgeChecks BoundedLStarData.q179 18 2 ((BoundedLStarData.q179.core 18).edges 2) := by decide +kernel

theorem q179_edge18_3 :
    EdgeChecks BoundedLStarData.q179 18 3 ((BoundedLStarData.q179.core 18).edges 3) := by decide +kernel

theorem q179_triangles18 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 18) = true := by decide +kernel

theorem q179_descent18 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 18) = true := by
  change allTriangleDescentsCheck (ofSix (-4) (2) (5) (-1) (0) (-3)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable19 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 19).word) (BoundedLStarData.q179.node 19) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [0,3,2]) (ofSix (2) (1) (-2) (1) (-3) (3))
  rw [q179_prefix19]
  intro u v; rfl

theorem q179_cyclic19 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 19) := by decide +kernel

theorem q179_edge19_0 :
    EdgeChecks BoundedLStarData.q179 19 0 ((BoundedLStarData.q179.core 19).edges 0) := by decide +kernel

theorem q179_edge19_1 :
    EdgeChecks BoundedLStarData.q179 19 1 ((BoundedLStarData.q179.core 19).edges 1) := by decide +kernel

theorem q179_edge19_2 :
    EdgeChecks BoundedLStarData.q179 19 2 ((BoundedLStarData.q179.core 19).edges 2) := by decide +kernel

theorem q179_edge19_3 :
    EdgeChecks BoundedLStarData.q179 19 3 ((BoundedLStarData.q179.core 19).edges 3) := by decide +kernel

theorem q179_triangles19 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 19) = true := by decide +kernel

theorem q179_descent19 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 19) = true := by
  change allTriangleDescentsCheck (ofSix (2) (1) (-2) (1) (-3) (3)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

end QuiverProofs.BoundedLStarChecks
