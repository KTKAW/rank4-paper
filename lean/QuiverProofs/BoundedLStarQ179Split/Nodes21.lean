import QuiverProofs.BoundedLStarQ179Split.Prefix11
namespace QuiverProofs.BoundedLStarChecks
open LStar CertificateSearch
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 4096

theorem q179_reachable84 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 84).word) (BoundedLStarData.q179.node 84) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [0,1,0,1,0,2,0,3]) (ofSix (86) (1) (-1) (794) (-13) (9))
  rw [q179_prefix85]
  intro u v; rfl

theorem q179_cyclic84 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 84) := by decide +kernel

theorem q179_edge84_0 :
    EdgeChecks BoundedLStarData.q179 84 0 ((BoundedLStarData.q179.core 84).edges 0) := by decide +kernel

theorem q179_edge84_1 :
    EdgeChecks BoundedLStarData.q179 84 1 ((BoundedLStarData.q179.core 84).edges 1) := by decide +kernel

theorem q179_edge84_2 :
    EdgeChecks BoundedLStarData.q179 84 2 ((BoundedLStarData.q179.core 84).edges 2) := by decide +kernel

theorem q179_edge84_3 :
    EdgeChecks BoundedLStarData.q179 84 3 ((BoundedLStarData.q179.core 84).edges 3) := by decide +kernel

theorem q179_triangles84 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 84) = true := by decide +kernel

theorem q179_descent84 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 84) = true := by
  change allTriangleDescentsCheck (ofSix (86) (1) (-1) (794) (-13) (9)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable85 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 85).word) (BoundedLStarData.q179.node 85) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [0,1,0,1,0,2,3,0]) (ofSix (99) (-8) (-1) (794) (86) (1))
  rw [q179_prefix86]
  intro u v; rfl

theorem q179_cyclic85 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 85) := by decide +kernel

theorem q179_edge85_0 :
    EdgeChecks BoundedLStarData.q179 85 0 ((BoundedLStarData.q179.core 85).edges 0) := by decide +kernel

theorem q179_edge85_1 :
    EdgeChecks BoundedLStarData.q179 85 1 ((BoundedLStarData.q179.core 85).edges 1) := by decide +kernel

theorem q179_edge85_2 :
    EdgeChecks BoundedLStarData.q179 85 2 ((BoundedLStarData.q179.core 85).edges 2) := by decide +kernel

theorem q179_edge85_3 :
    EdgeChecks BoundedLStarData.q179 85 3 ((BoundedLStarData.q179.core 85).edges 3) := by decide +kernel

theorem q179_triangles85 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 85) = true := by decide +kernel

theorem q179_descent85 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 85) = true := by
  change allTriangleDescentsCheck (ofSix (99) (-8) (-1) (794) (86) (1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable86 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 86).word) (BoundedLStarData.q179.node 86) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [0,1,0,2,0,2,3,0]) (ofSix (53) (1) (-3) (-11) (146) (2))
  rw [q179_prefix87]
  intro u v; rfl

theorem q179_cyclic86 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 86) := by decide +kernel

theorem q179_edge86_0 :
    EdgeChecks BoundedLStarData.q179 86 0 ((BoundedLStarData.q179.core 86).edges 0) := by decide +kernel

theorem q179_edge86_1 :
    EdgeChecks BoundedLStarData.q179 86 1 ((BoundedLStarData.q179.core 86).edges 1) := by decide +kernel

theorem q179_edge86_2 :
    EdgeChecks BoundedLStarData.q179 86 2 ((BoundedLStarData.q179.core 86).edges 2) := by decide +kernel

theorem q179_edge86_3 :
    EdgeChecks BoundedLStarData.q179 86 3 ((BoundedLStarData.q179.core 86).edges 3) := by decide +kernel

theorem q179_triangles86 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 86) = true := by decide +kernel

theorem q179_descent86 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 86) = true := by
  change allTriangleDescentsCheck (ofSix (53) (1) (-3) (-11) (146) (2)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable87 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 87).word) (BoundedLStarData.q179.node 87) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [2,0,1,2,0,2,3,0]) (ofSix (-2741) (-1) (9) (299) (-24626) (-8))
  rw [q179_prefix89]
  intro u v; rfl

theorem q179_cyclic87 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 87) := by decide +kernel

theorem q179_edge87_0 :
    EdgeChecks BoundedLStarData.q179 87 0 ((BoundedLStarData.q179.core 87).edges 0) := by decide +kernel

theorem q179_edge87_1 :
    EdgeChecks BoundedLStarData.q179 87 1 ((BoundedLStarData.q179.core 87).edges 1) := by decide +kernel

theorem q179_edge87_2 :
    EdgeChecks BoundedLStarData.q179 87 2 ((BoundedLStarData.q179.core 87).edges 2) := by decide +kernel

theorem q179_edge87_3 :
    EdgeChecks BoundedLStarData.q179 87 3 ((BoundedLStarData.q179.core 87).edges 3) := by decide +kernel

theorem q179_triangles87 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 87) = true := by decide +kernel

theorem q179_descent87 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 87) = true := by
  change allTriangleDescentsCheck (ofSix (-2741) (-1) (9) (299) (-24626) (-8)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

end QuiverProofs.BoundedLStarChecks
