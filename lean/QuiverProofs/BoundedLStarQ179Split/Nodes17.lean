import QuiverProofs.BoundedLStarQ179Split.Prefix11
namespace QuiverProofs.BoundedLStarChecks
open LStar CertificateSearch
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 4096

theorem q179_reachable68 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 68).word) (BoundedLStarData.q179.node 68) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [2,0,1,2,3,0]) (ofSix (-38) (9) (-1) (-342) (5) (8))
  rw [q179_prefix68]
  intro u v; rfl

theorem q179_cyclic68 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 68) := by decide +kernel

theorem q179_edge68_0 :
    EdgeChecks BoundedLStarData.q179 68 0 ((BoundedLStarData.q179.core 68).edges 0) := by decide +kernel

theorem q179_edge68_1 :
    EdgeChecks BoundedLStarData.q179 68 1 ((BoundedLStarData.q179.core 68).edges 1) := by decide +kernel

theorem q179_edge68_2 :
    EdgeChecks BoundedLStarData.q179 68 2 ((BoundedLStarData.q179.core 68).edges 2) := by decide +kernel

theorem q179_edge68_3 :
    EdgeChecks BoundedLStarData.q179 68 3 ((BoundedLStarData.q179.core 68).edges 3) := by decide +kernel

theorem q179_triangles68 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 68) = true := by decide +kernel

theorem q179_descent68 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 68) = true := by
  change allTriangleDescentsCheck (ofSix (-38) (9) (-1) (-342) (5) (8)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable69 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 69).word) (BoundedLStarData.q179.node 69) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [3,0,2,0,1,3]) (ofSix (-1) (-73) (7) (9) (-1) (-3))
  rw [q179_prefix69]
  intro u v; rfl

theorem q179_cyclic69 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 69) := by decide +kernel

theorem q179_edge69_0 :
    EdgeChecks BoundedLStarData.q179 69 0 ((BoundedLStarData.q179.core 69).edges 0) := by decide +kernel

theorem q179_edge69_1 :
    EdgeChecks BoundedLStarData.q179 69 1 ((BoundedLStarData.q179.core 69).edges 1) := by decide +kernel

theorem q179_edge69_2 :
    EdgeChecks BoundedLStarData.q179 69 2 ((BoundedLStarData.q179.core 69).edges 2) := by decide +kernel

theorem q179_edge69_3 :
    EdgeChecks BoundedLStarData.q179 69 3 ((BoundedLStarData.q179.core 69).edges 3) := by decide +kernel

theorem q179_triangles69 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 69) = true := by decide +kernel

theorem q179_descent69 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 69) = true := by
  change allTriangleDescentsCheck (ofSix (-1) (-73) (7) (9) (-1) (-3)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable70 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 70).word) (BoundedLStarData.q179.node 70) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [3,0,2,0,3,1]) (ofSix (6) (-73) (1) (12) (-1) (9))
  rw [q179_prefix70]
  intro u v; rfl

theorem q179_cyclic70 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 70) := by decide +kernel

theorem q179_edge70_0 :
    EdgeChecks BoundedLStarData.q179 70 0 ((BoundedLStarData.q179.core 70).edges 0) := by decide +kernel

theorem q179_edge70_1 :
    EdgeChecks BoundedLStarData.q179 70 1 ((BoundedLStarData.q179.core 70).edges 1) := by decide +kernel

theorem q179_edge70_2 :
    EdgeChecks BoundedLStarData.q179 70 2 ((BoundedLStarData.q179.core 70).edges 2) := by decide +kernel

theorem q179_edge70_3 :
    EdgeChecks BoundedLStarData.q179 70 3 ((BoundedLStarData.q179.core 70).edges 3) := by decide +kernel

theorem q179_triangles70 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 70) = true := by decide +kernel

theorem q179_descent70 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 70) = true := by
  change allTriangleDescentsCheck (ofSix (6) (-73) (1) (12) (-1) (9)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable71 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 71).word) (BoundedLStarData.q179.node 71) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [3,0,2,1,0,3]) (ofSix (-1) (-16) (1) (107) (-7) (2))
  rw [q179_prefix71]
  intro u v; rfl

theorem q179_cyclic71 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 71) := by decide +kernel

theorem q179_edge71_0 :
    EdgeChecks BoundedLStarData.q179 71 0 ((BoundedLStarData.q179.core 71).edges 0) := by decide +kernel

theorem q179_edge71_1 :
    EdgeChecks BoundedLStarData.q179 71 1 ((BoundedLStarData.q179.core 71).edges 1) := by decide +kernel

theorem q179_edge71_2 :
    EdgeChecks BoundedLStarData.q179 71 2 ((BoundedLStarData.q179.core 71).edges 2) := by decide +kernel

theorem q179_edge71_3 :
    EdgeChecks BoundedLStarData.q179 71 3 ((BoundedLStarData.q179.core 71).edges 3) := by decide +kernel

theorem q179_triangles71 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 71) = true := by decide +kernel

theorem q179_descent71 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 71) = true := by
  change allTriangleDescentsCheck (ofSix (-1) (-16) (1) (107) (-7) (2)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

end QuiverProofs.BoundedLStarChecks
