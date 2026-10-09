import QuiverProofs.BoundedLStarQ179Split.Prefix11
namespace QuiverProofs.BoundedLStarChecks
open LStar CertificateSearch
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 4096

theorem q179_reachable64 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 64).word) (BoundedLStarData.q179.node 64) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [0,3,2,0,3,0,2,0]) (ofSix (-6) (1) (-2) (12) (-35) (3))
  rw [q179_prefix88]
  intro u v; rfl

theorem q179_cyclic64 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 64) := by decide +kernel

theorem q179_edge64_0 :
    EdgeChecks BoundedLStarData.q179 64 0 ((BoundedLStarData.q179.core 64).edges 0) := by decide +kernel

theorem q179_edge64_1 :
    EdgeChecks BoundedLStarData.q179 64 1 ((BoundedLStarData.q179.core 64).edges 1) := by decide +kernel

theorem q179_edge64_2 :
    EdgeChecks BoundedLStarData.q179 64 2 ((BoundedLStarData.q179.core 64).edges 2) := by decide +kernel

theorem q179_edge64_3 :
    EdgeChecks BoundedLStarData.q179 64 3 ((BoundedLStarData.q179.core 64).edges 3) := by decide +kernel

theorem q179_triangles64 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 64) = true := by decide +kernel

theorem q179_descent64 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 64) = true := by
  change allTriangleDescentsCheck (ofSix (-6) (1) (-2) (12) (-35) (3)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable65 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 65).word) (BoundedLStarData.q179.node 65) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [2,0,1,0,3,2]) (ofSix (2) (-1) (8) (-11) (99) (-9))
  rw [q179_prefix65]
  intro u v; rfl

theorem q179_cyclic65 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 65) := by decide +kernel

theorem q179_edge65_0 :
    EdgeChecks BoundedLStarData.q179 65 0 ((BoundedLStarData.q179.core 65).edges 0) := by decide +kernel

theorem q179_edge65_1 :
    EdgeChecks BoundedLStarData.q179 65 1 ((BoundedLStarData.q179.core 65).edges 1) := by decide +kernel

theorem q179_edge65_2 :
    EdgeChecks BoundedLStarData.q179 65 2 ((BoundedLStarData.q179.core 65).edges 2) := by decide +kernel

theorem q179_edge65_3 :
    EdgeChecks BoundedLStarData.q179 65 3 ((BoundedLStarData.q179.core 65).edges 3) := by decide +kernel

theorem q179_triangles65 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 65) = true := by decide +kernel

theorem q179_descent65 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 65) = true := by
  change allTriangleDescentsCheck (ofSix (2) (-1) (8) (-11) (99) (-9)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable66 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 66).word) (BoundedLStarData.q179.node 66) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [2,0,1,2,0,2]) (ofSix (2354) (-8) (9) (299) (-43) (-1))
  rw [q179_prefix66]
  intro u v; rfl

theorem q179_cyclic66 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 66) := by decide +kernel

theorem q179_edge66_0 :
    EdgeChecks BoundedLStarData.q179 66 0 ((BoundedLStarData.q179.core 66).edges 0) := by decide +kernel

theorem q179_edge66_1 :
    EdgeChecks BoundedLStarData.q179 66 1 ((BoundedLStarData.q179.core 66).edges 1) := by decide +kernel

theorem q179_edge66_2 :
    EdgeChecks BoundedLStarData.q179 66 2 ((BoundedLStarData.q179.core 66).edges 2) := by decide +kernel

theorem q179_edge66_3 :
    EdgeChecks BoundedLStarData.q179 66 3 ((BoundedLStarData.q179.core 66).edges 3) := by decide +kernel

theorem q179_triangles66 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 66) = true := by decide +kernel

theorem q179_descent66 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 66) = true := by
  change allTriangleDescentsCheck (ofSix (2354) (-8) (9) (299) (-43) (-1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable67 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 67).word) (BoundedLStarData.q179.node 67) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [2,0,1,2,0,3]) (ofSix (5) (8) (-1) (-342) (43) (-1))
  rw [q179_prefix67]
  intro u v; rfl

theorem q179_cyclic67 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 67) := by decide +kernel

theorem q179_edge67_0 :
    EdgeChecks BoundedLStarData.q179 67 0 ((BoundedLStarData.q179.core 67).edges 0) := by decide +kernel

theorem q179_edge67_1 :
    EdgeChecks BoundedLStarData.q179 67 1 ((BoundedLStarData.q179.core 67).edges 1) := by decide +kernel

theorem q179_edge67_2 :
    EdgeChecks BoundedLStarData.q179 67 2 ((BoundedLStarData.q179.core 67).edges 2) := by decide +kernel

theorem q179_edge67_3 :
    EdgeChecks BoundedLStarData.q179 67 3 ((BoundedLStarData.q179.core 67).edges 3) := by decide +kernel

theorem q179_triangles67 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 67) = true := by decide +kernel

theorem q179_descent67 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 67) = true := by
  change allTriangleDescentsCheck (ofSix (5) (8) (-1) (-342) (43) (-1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

end QuiverProofs.BoundedLStarChecks
