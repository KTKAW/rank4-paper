import QuiverProofs.BoundedLStarQ179Split.Prefix11
namespace QuiverProofs.BoundedLStarChecks
open LStar CertificateSearch
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 4096

theorem q179_reachable44 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 44).word) (BoundedLStarData.q179.node 44) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [0,1,0,1,0]) (ofSix (2) (-8) (-1) (11) (2) (1))
  rw [q179_prefix44]
  intro u v; rfl

theorem q179_cyclic44 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 44) := by decide +kernel

theorem q179_edge44_0 :
    EdgeChecks BoundedLStarData.q179 44 0 ((BoundedLStarData.q179.core 44).edges 0) := by decide +kernel

theorem q179_edge44_1 :
    EdgeChecks BoundedLStarData.q179 44 1 ((BoundedLStarData.q179.core 44).edges 1) := by decide +kernel

theorem q179_edge44_2 :
    EdgeChecks BoundedLStarData.q179 44 2 ((BoundedLStarData.q179.core 44).edges 2) := by decide +kernel

theorem q179_edge44_3 :
    EdgeChecks BoundedLStarData.q179 44 3 ((BoundedLStarData.q179.core 44).edges 3) := by decide +kernel

theorem q179_triangles44 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 44) = true := by decide +kernel

theorem q179_descent44 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 44) = true := by
  change allTriangleDescentsCheck (ofSix (2) (-8) (-1) (11) (2) (1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable45 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 45).word) (BoundedLStarData.q179.node 45) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [0,1,0,1,2]) (ofSix (38) (-8) (9) (5) (0) (-1))
  rw [q179_prefix45]
  intro u v; rfl

theorem q179_cyclic45 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 45) := by decide +kernel

theorem q179_edge45_0 :
    EdgeChecks BoundedLStarData.q179 45 0 ((BoundedLStarData.q179.core 45).edges 0) := by decide +kernel

theorem q179_edge45_1 :
    EdgeChecks BoundedLStarData.q179 45 1 ((BoundedLStarData.q179.core 45).edges 1) := by decide +kernel

theorem q179_edge45_2 :
    EdgeChecks BoundedLStarData.q179 45 2 ((BoundedLStarData.q179.core 45).edges 2) := by decide +kernel

theorem q179_edge45_3 :
    EdgeChecks BoundedLStarData.q179 45 3 ((BoundedLStarData.q179.core 45).edges 3) := by decide +kernel

theorem q179_triangles45 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 45) = true := by decide +kernel

theorem q179_descent45 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 45) = true := by
  change allTriangleDescentsCheck (ofSix (38) (-8) (9) (5) (0) (-1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable46 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 46).word) (BoundedLStarData.q179.node 46) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [0,1,0,2,0]) (ofSix (8) (-2) (-1) (11) (13) (-1))
  rw [q179_prefix46]
  intro u v; rfl

theorem q179_cyclic46 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 46) := by decide +kernel

theorem q179_edge46_0 :
    EdgeChecks BoundedLStarData.q179 46 0 ((BoundedLStarData.q179.core 46).edges 0) := by decide +kernel

theorem q179_edge46_1 :
    EdgeChecks BoundedLStarData.q179 46 1 ((BoundedLStarData.q179.core 46).edges 1) := by decide +kernel

theorem q179_edge46_2 :
    EdgeChecks BoundedLStarData.q179 46 2 ((BoundedLStarData.q179.core 46).edges 2) := by decide +kernel

theorem q179_edge46_3 :
    EdgeChecks BoundedLStarData.q179 46 3 ((BoundedLStarData.q179.core 46).edges 3) := by decide +kernel

theorem q179_triangles46 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 46) = true := by decide +kernel

theorem q179_descent46 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 46) = true := by
  change allTriangleDescentsCheck (ofSix (8) (-2) (-1) (11) (13) (-1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable47 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 47).word) (BoundedLStarData.q179.node 47) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [0,3,2,0,1]) (ofSix (2) (-1) (-12) (-1) (7) (-6))
  rw [q179_prefix47]
  intro u v; rfl

theorem q179_cyclic47 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 47) := by decide +kernel

theorem q179_edge47_0 :
    EdgeChecks BoundedLStarData.q179 47 0 ((BoundedLStarData.q179.core 47).edges 0) := by decide +kernel

theorem q179_edge47_1 :
    EdgeChecks BoundedLStarData.q179 47 1 ((BoundedLStarData.q179.core 47).edges 1) := by decide +kernel

theorem q179_edge47_2 :
    EdgeChecks BoundedLStarData.q179 47 2 ((BoundedLStarData.q179.core 47).edges 2) := by decide +kernel

theorem q179_edge47_3 :
    EdgeChecks BoundedLStarData.q179 47 3 ((BoundedLStarData.q179.core 47).edges 3) := by decide +kernel

theorem q179_triangles47 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 47) = true := by decide +kernel

theorem q179_descent47 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 47) = true := by
  change allTriangleDescentsCheck (ofSix (2) (-1) (-12) (-1) (7) (-6)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

end QuiverProofs.BoundedLStarChecks
