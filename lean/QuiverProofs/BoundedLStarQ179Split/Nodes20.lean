import QuiverProofs.BoundedLStarQ179Split.Prefix11
namespace QuiverProofs.BoundedLStarChecks
open LStar CertificateSearch
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 4096

theorem q179_reachable80 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 80).word) (BoundedLStarData.q179.node 80) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [2,0,1,2,0,3,2]) (ofSix (2741) (-8) (-1) (342) (-299) (1))
  rw [q179_prefix81]
  intro u v; rfl

theorem q179_cyclic80 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 80) := by decide +kernel

theorem q179_edge80_0 :
    EdgeChecks BoundedLStarData.q179 80 0 ((BoundedLStarData.q179.core 80).edges 0) := by decide +kernel

theorem q179_edge80_1 :
    EdgeChecks BoundedLStarData.q179 80 1 ((BoundedLStarData.q179.core 80).edges 1) := by decide +kernel

theorem q179_edge80_2 :
    EdgeChecks BoundedLStarData.q179 80 2 ((BoundedLStarData.q179.core 80).edges 2) := by decide +kernel

theorem q179_edge80_3 :
    EdgeChecks BoundedLStarData.q179 80 3 ((BoundedLStarData.q179.core 80).edges 3) := by decide +kernel

theorem q179_triangles80 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 80) = true := by decide +kernel

theorem q179_descent80 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 80) = true := by
  change allTriangleDescentsCheck (ofSix (2741) (-8) (-1) (342) (-299) (1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable81 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 81).word) (BoundedLStarData.q179.node 81) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [3,0,2,0,1,3,0]) (ofSix (1) (73) (-7) (9) (6) (508))
  rw [q179_prefix82]
  intro u v; rfl

theorem q179_cyclic81 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 81) := by decide +kernel

theorem q179_edge81_0 :
    EdgeChecks BoundedLStarData.q179 81 0 ((BoundedLStarData.q179.core 81).edges 0) := by decide +kernel

theorem q179_edge81_1 :
    EdgeChecks BoundedLStarData.q179 81 1 ((BoundedLStarData.q179.core 81).edges 1) := by decide +kernel

theorem q179_edge81_2 :
    EdgeChecks BoundedLStarData.q179 81 2 ((BoundedLStarData.q179.core 81).edges 2) := by decide +kernel

theorem q179_edge81_3 :
    EdgeChecks BoundedLStarData.q179 81 3 ((BoundedLStarData.q179.core 81).edges 3) := by decide +kernel

theorem q179_triangles81 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 81) = true := by decide +kernel

theorem q179_descent81 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 81) = true := by
  change allTriangleDescentsCheck (ofSix (1) (73) (-7) (9) (6) (508)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable82 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 82).word) (BoundedLStarData.q179.node 82) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [3,0,2,1,0,3,1]) (ofSix (1) (-16) (-6) (-107) (7) (-747))
  rw [q179_prefix83]
  intro u v; rfl

theorem q179_cyclic82 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 82) := by decide +kernel

theorem q179_edge82_0 :
    EdgeChecks BoundedLStarData.q179 82 0 ((BoundedLStarData.q179.core 82).edges 0) := by decide +kernel

theorem q179_edge82_1 :
    EdgeChecks BoundedLStarData.q179 82 1 ((BoundedLStarData.q179.core 82).edges 1) := by decide +kernel

theorem q179_edge82_2 :
    EdgeChecks BoundedLStarData.q179 82 2 ((BoundedLStarData.q179.core 82).edges 2) := by decide +kernel

theorem q179_edge82_3 :
    EdgeChecks BoundedLStarData.q179 82 3 ((BoundedLStarData.q179.core 82).edges 3) := by decide +kernel

theorem q179_triangles82 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 82) = true := by decide +kernel

theorem q179_descent82 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 82) = true := by
  change allTriangleDescentsCheck (ofSix (1) (-16) (-6) (-107) (7) (-747)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable83 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 83).word) (BoundedLStarData.q179.node 83) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [3,0,2,1,3,2,3,1,3]) (ofSix (-35) (99) (-12) (-3) (1) (-2))
  rw [q179_prefix92]
  intro u v; rfl

theorem q179_cyclic83 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 83) := by decide +kernel

theorem q179_edge83_0 :
    EdgeChecks BoundedLStarData.q179 83 0 ((BoundedLStarData.q179.core 83).edges 0) := by decide +kernel

theorem q179_edge83_1 :
    EdgeChecks BoundedLStarData.q179 83 1 ((BoundedLStarData.q179.core 83).edges 1) := by decide +kernel

theorem q179_edge83_2 :
    EdgeChecks BoundedLStarData.q179 83 2 ((BoundedLStarData.q179.core 83).edges 2) := by decide +kernel

theorem q179_edge83_3 :
    EdgeChecks BoundedLStarData.q179 83 3 ((BoundedLStarData.q179.core 83).edges 3) := by decide +kernel

theorem q179_triangles83 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 83) = true := by decide +kernel

theorem q179_descent83 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 83) = true := by
  change allTriangleDescentsCheck (ofSix (-35) (99) (-12) (-3) (1) (-2)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

end QuiverProofs.BoundedLStarChecks
