import QuiverProofs.BoundedLStarQ179Split.Prefix11
namespace QuiverProofs.BoundedLStarChecks
open LStar CertificateSearch
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 4096

theorem q179_reachable48 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 48).word) (BoundedLStarData.q179.node 48) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [0,3,2,0,3]) (ofSix (12) (-1) (-2) (-6) (7) (-1))
  rw [q179_prefix48]
  intro u v; rfl

theorem q179_cyclic48 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 48) := by decide +kernel

theorem q179_edge48_0 :
    EdgeChecks BoundedLStarData.q179 48 0 ((BoundedLStarData.q179.core 48).edges 0) := by decide +kernel

theorem q179_edge48_1 :
    EdgeChecks BoundedLStarData.q179 48 1 ((BoundedLStarData.q179.core 48).edges 1) := by decide +kernel

theorem q179_edge48_2 :
    EdgeChecks BoundedLStarData.q179 48 2 ((BoundedLStarData.q179.core 48).edges 2) := by decide +kernel

theorem q179_edge48_3 :
    EdgeChecks BoundedLStarData.q179 48 3 ((BoundedLStarData.q179.core 48).edges 3) := by decide +kernel

theorem q179_triangles48 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 48) = true := by decide +kernel

theorem q179_descent48 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 48) = true := by
  change allTriangleDescentsCheck (ofSix (12) (-1) (-2) (-6) (7) (-1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable49 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 49).word) (BoundedLStarData.q179.node 49) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [1,3,1,2,3]) (ofSix (4) (-71) (26) (-2) (1) (-3))
  rw [q179_prefix49]
  intro u v; rfl

theorem q179_cyclic49 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 49) := by decide +kernel

theorem q179_edge49_0 :
    EdgeChecks BoundedLStarData.q179 49 0 ((BoundedLStarData.q179.core 49).edges 0) := by decide +kernel

theorem q179_edge49_1 :
    EdgeChecks BoundedLStarData.q179 49 1 ((BoundedLStarData.q179.core 49).edges 1) := by decide +kernel

theorem q179_edge49_2 :
    EdgeChecks BoundedLStarData.q179 49 2 ((BoundedLStarData.q179.core 49).edges 2) := by decide +kernel

theorem q179_edge49_3 :
    EdgeChecks BoundedLStarData.q179 49 3 ((BoundedLStarData.q179.core 49).edges 3) := by decide +kernel

theorem q179_triangles49 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 49) = true := by decide +kernel

theorem q179_descent49 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 49) = true := by
  change allTriangleDescentsCheck (ofSix (4) (-71) (26) (-2) (1) (-3)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable50 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 50).word) (BoundedLStarData.q179.node 50) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [2,0,1,0,3]) (ofSix (2) (1) (-1) (11) (0) (9))
  rw [q179_prefix50]
  intro u v; rfl

theorem q179_cyclic50 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 50) := by decide +kernel

theorem q179_edge50_0 :
    EdgeChecks BoundedLStarData.q179 50 0 ((BoundedLStarData.q179.core 50).edges 0) := by decide +kernel

theorem q179_edge50_1 :
    EdgeChecks BoundedLStarData.q179 50 1 ((BoundedLStarData.q179.core 50).edges 1) := by decide +kernel

theorem q179_edge50_2 :
    EdgeChecks BoundedLStarData.q179 50 2 ((BoundedLStarData.q179.core 50).edges 2) := by decide +kernel

theorem q179_edge50_3 :
    EdgeChecks BoundedLStarData.q179 50 3 ((BoundedLStarData.q179.core 50).edges 3) := by decide +kernel

theorem q179_triangles50 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 50) = true := by decide +kernel

theorem q179_descent50 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 50) = true := by
  change allTriangleDescentsCheck (ofSix (2) (1) (-1) (11) (0) (9)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable51 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 51).word) (BoundedLStarData.q179.node 51) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [2,0,1,2,0]) (ofSix (-38) (8) (1) (-299) (-43) (1))
  rw [q179_prefix51]
  intro u v; rfl

theorem q179_cyclic51 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 51) := by decide +kernel

theorem q179_edge51_0 :
    EdgeChecks BoundedLStarData.q179 51 0 ((BoundedLStarData.q179.core 51).edges 0) := by decide +kernel

theorem q179_edge51_1 :
    EdgeChecks BoundedLStarData.q179 51 1 ((BoundedLStarData.q179.core 51).edges 1) := by decide +kernel

theorem q179_edge51_2 :
    EdgeChecks BoundedLStarData.q179 51 2 ((BoundedLStarData.q179.core 51).edges 2) := by decide +kernel

theorem q179_edge51_3 :
    EdgeChecks BoundedLStarData.q179 51 3 ((BoundedLStarData.q179.core 51).edges 3) := by decide +kernel

theorem q179_triangles51 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 51) = true := by decide +kernel

theorem q179_descent51 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 51) = true := by
  change allTriangleDescentsCheck (ofSix (-38) (8) (1) (-299) (-43) (1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

end QuiverProofs.BoundedLStarChecks
