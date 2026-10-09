import QuiverProofs.BoundedLStarQ179Split.Prefix11
namespace QuiverProofs.BoundedLStarChecks
open LStar CertificateSearch
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 4096

theorem q179_reachable8 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 8).word) (BoundedLStarData.q179.node 8) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [1,2]) (ofSix (-2) (4) (-3) (-1) (3) (-1))
  rw [q179_prefix8]
  intro u v; rfl

theorem q179_cyclic8 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 8) := by decide +kernel

theorem q179_edge8_0 :
    EdgeChecks BoundedLStarData.q179 8 0 ((BoundedLStarData.q179.core 8).edges 0) := by decide +kernel

theorem q179_edge8_1 :
    EdgeChecks BoundedLStarData.q179 8 1 ((BoundedLStarData.q179.core 8).edges 1) := by decide +kernel

theorem q179_edge8_2 :
    EdgeChecks BoundedLStarData.q179 8 2 ((BoundedLStarData.q179.core 8).edges 2) := by decide +kernel

theorem q179_edge8_3 :
    EdgeChecks BoundedLStarData.q179 8 3 ((BoundedLStarData.q179.core 8).edges 3) := by decide +kernel

theorem q179_triangles8 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 8) = true := by decide +kernel

theorem q179_descent8 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 8) = true := by
  change allTriangleDescentsCheck (ofSix (-2) (4) (-3) (-1) (3) (-1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable9 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 9).word) (BoundedLStarData.q179.node 9) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [1,3]) (ofSix (-4) (-7) (3) (1) (-2) (-1))
  rw [q179_prefix9]
  intro u v; rfl

theorem q179_cyclic9 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 9) := by decide +kernel

theorem q179_edge9_0 :
    EdgeChecks BoundedLStarData.q179 9 0 ((BoundedLStarData.q179.core 9).edges 0) := by decide +kernel

theorem q179_edge9_1 :
    EdgeChecks BoundedLStarData.q179 9 1 ((BoundedLStarData.q179.core 9).edges 1) := by decide +kernel

theorem q179_edge9_2 :
    EdgeChecks BoundedLStarData.q179 9 2 ((BoundedLStarData.q179.core 9).edges 2) := by decide +kernel

theorem q179_edge9_3 :
    EdgeChecks BoundedLStarData.q179 9 3 ((BoundedLStarData.q179.core 9).edges 3) := by decide +kernel

theorem q179_triangles9 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 9) = true := by decide +kernel

theorem q179_descent9 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 9) = true := by
  change allTriangleDescentsCheck (ofSix (-4) (-7) (3) (1) (-2) (-1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable10 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 10).word) (BoundedLStarData.q179.node 10) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [2,0]) (ofSix (2) (-2) (-1) (5) (0) (-1))
  rw [q179_prefix10]
  intro u v; rfl

theorem q179_cyclic10 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 10) := by decide +kernel

theorem q179_edge10_0 :
    EdgeChecks BoundedLStarData.q179 10 0 ((BoundedLStarData.q179.core 10).edges 0) := by decide +kernel

theorem q179_edge10_1 :
    EdgeChecks BoundedLStarData.q179 10 1 ((BoundedLStarData.q179.core 10).edges 1) := by decide +kernel

theorem q179_edge10_2 :
    EdgeChecks BoundedLStarData.q179 10 2 ((BoundedLStarData.q179.core 10).edges 2) := by decide +kernel

theorem q179_edge10_3 :
    EdgeChecks BoundedLStarData.q179 10 3 ((BoundedLStarData.q179.core 10).edges 3) := by decide +kernel

theorem q179_triangles10 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 10) = true := by decide +kernel

theorem q179_descent10 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 10) = true := by
  change allTriangleDescentsCheck (ofSix (2) (-2) (-1) (5) (0) (-1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable11 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 11).word) (BoundedLStarData.q179.node 11) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [2,1]) (ofSix (2) (2) (-3) (-1) (2) (-3))
  rw [q179_prefix11]
  intro u v; rfl

theorem q179_cyclic11 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 11) := by decide +kernel

theorem q179_edge11_0 :
    EdgeChecks BoundedLStarData.q179 11 0 ((BoundedLStarData.q179.core 11).edges 0) := by decide +kernel

theorem q179_edge11_1 :
    EdgeChecks BoundedLStarData.q179 11 1 ((BoundedLStarData.q179.core 11).edges 1) := by decide +kernel

theorem q179_edge11_2 :
    EdgeChecks BoundedLStarData.q179 11 2 ((BoundedLStarData.q179.core 11).edges 2) := by decide +kernel

theorem q179_edge11_3 :
    EdgeChecks BoundedLStarData.q179 11 3 ((BoundedLStarData.q179.core 11).edges 3) := by decide +kernel

theorem q179_triangles11 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 11) = true := by decide +kernel

theorem q179_descent11 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 11) = true := by
  change allTriangleDescentsCheck (ofSix (2) (2) (-3) (-1) (2) (-3)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

end QuiverProofs.BoundedLStarChecks
