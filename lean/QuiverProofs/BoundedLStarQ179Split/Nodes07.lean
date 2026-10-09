import QuiverProofs.BoundedLStarQ179Split.Prefix11
namespace QuiverProofs.BoundedLStarChecks
open LStar CertificateSearch
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 4096

theorem q179_reachable28 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 28).word) (BoundedLStarData.q179.node 28) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [3,2,0]) (ofSix (0) (-2) (3) (3) (-1) (-5))
  rw [q179_prefix28]
  intro u v; rfl

theorem q179_cyclic28 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 28) := by decide +kernel

theorem q179_edge28_0 :
    EdgeChecks BoundedLStarData.q179 28 0 ((BoundedLStarData.q179.core 28).edges 0) := by decide +kernel

theorem q179_edge28_1 :
    EdgeChecks BoundedLStarData.q179 28 1 ((BoundedLStarData.q179.core 28).edges 1) := by decide +kernel

theorem q179_edge28_2 :
    EdgeChecks BoundedLStarData.q179 28 2 ((BoundedLStarData.q179.core 28).edges 2) := by decide +kernel

theorem q179_edge28_3 :
    EdgeChecks BoundedLStarData.q179 28 3 ((BoundedLStarData.q179.core 28).edges 3) := by decide +kernel

theorem q179_triangles28 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 28) = true := by decide +kernel

theorem q179_descent28 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 28) = true := by
  change allTriangleDescentsCheck (ofSix (0) (-2) (3) (3) (-1) (-5)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable29 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 29).word) (BoundedLStarData.q179.node 29) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [3,2,1]) (ofSix (0) (2) (-3) (-3) (1) (-2))
  rw [q179_prefix29]
  intro u v; rfl

theorem q179_cyclic29 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 29) := by decide +kernel

theorem q179_edge29_0 :
    EdgeChecks BoundedLStarData.q179 29 0 ((BoundedLStarData.q179.core 29).edges 0) := by decide +kernel

theorem q179_edge29_1 :
    EdgeChecks BoundedLStarData.q179 29 1 ((BoundedLStarData.q179.core 29).edges 1) := by decide +kernel

theorem q179_edge29_2 :
    EdgeChecks BoundedLStarData.q179 29 2 ((BoundedLStarData.q179.core 29).edges 2) := by decide +kernel

theorem q179_edge29_3 :
    EdgeChecks BoundedLStarData.q179 29 3 ((BoundedLStarData.q179.core 29).edges 3) := by decide +kernel

theorem q179_triangles29 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 29) = true := by decide +kernel

theorem q179_descent29 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 29) = true := by
  change allTriangleDescentsCheck (ofSix (0) (2) (-3) (-3) (1) (-2)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable30 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 30).word) (BoundedLStarData.q179.node 30) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [0,1,0,1]) (ofSix (-2) (8) (1) (-5) (0) (1))
  rw [q179_prefix30]
  intro u v; rfl

theorem q179_cyclic30 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 30) := by decide +kernel

theorem q179_edge30_0 :
    EdgeChecks BoundedLStarData.q179 30 0 ((BoundedLStarData.q179.core 30).edges 0) := by decide +kernel

theorem q179_edge30_1 :
    EdgeChecks BoundedLStarData.q179 30 1 ((BoundedLStarData.q179.core 30).edges 1) := by decide +kernel

theorem q179_edge30_2 :
    EdgeChecks BoundedLStarData.q179 30 2 ((BoundedLStarData.q179.core 30).edges 2) := by decide +kernel

theorem q179_edge30_3 :
    EdgeChecks BoundedLStarData.q179 30 3 ((BoundedLStarData.q179.core 30).edges 3) := by decide +kernel

theorem q179_triangles30 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 30) = true := by decide +kernel

theorem q179_descent30 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 30) = true := by
  change allTriangleDescentsCheck (ofSix (-2) (8) (1) (-5) (0) (1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable31 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 31).word) (BoundedLStarData.q179.node 31) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [0,1,0,2]) (ofSix (-8) (2) (1) (-5) (5) (-1))
  rw [q179_prefix31]
  intro u v; rfl

theorem q179_cyclic31 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 31) := by decide +kernel

theorem q179_edge31_0 :
    EdgeChecks BoundedLStarData.q179 31 0 ((BoundedLStarData.q179.core 31).edges 0) := by decide +kernel

theorem q179_edge31_1 :
    EdgeChecks BoundedLStarData.q179 31 1 ((BoundedLStarData.q179.core 31).edges 1) := by decide +kernel

theorem q179_edge31_2 :
    EdgeChecks BoundedLStarData.q179 31 2 ((BoundedLStarData.q179.core 31).edges 2) := by decide +kernel

theorem q179_edge31_3 :
    EdgeChecks BoundedLStarData.q179 31 3 ((BoundedLStarData.q179.core 31).edges 3) := by decide +kernel

theorem q179_triangles31 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 31) = true := by decide +kernel

theorem q179_descent31 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 31) = true := by
  change allTriangleDescentsCheck (ofSix (-8) (2) (1) (-5) (5) (-1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

end QuiverProofs.BoundedLStarChecks
