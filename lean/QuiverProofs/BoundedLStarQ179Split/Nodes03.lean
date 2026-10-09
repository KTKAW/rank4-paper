import QuiverProofs.BoundedLStarQ179Split.Prefix11
namespace QuiverProofs.BoundedLStarChecks
open LStar CertificateSearch
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 4096

theorem q179_reachable12 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 12).word) (BoundedLStarData.q179.node 12) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [2,3]) (ofSix (0) (3) (-1) (1) (2) (1))
  rw [q179_prefix12]
  intro u v; rfl

theorem q179_cyclic12 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 12) := by decide +kernel

theorem q179_edge12_0 :
    EdgeChecks BoundedLStarData.q179 12 0 ((BoundedLStarData.q179.core 12).edges 0) := by decide +kernel

theorem q179_edge12_1 :
    EdgeChecks BoundedLStarData.q179 12 1 ((BoundedLStarData.q179.core 12).edges 1) := by decide +kernel

theorem q179_edge12_2 :
    EdgeChecks BoundedLStarData.q179 12 2 ((BoundedLStarData.q179.core 12).edges 2) := by decide +kernel

theorem q179_edge12_3 :
    EdgeChecks BoundedLStarData.q179 12 3 ((BoundedLStarData.q179.core 12).edges 3) := by decide +kernel

theorem q179_triangles12 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 12) = true := by decide +kernel

theorem q179_descent12 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 12) = true := by
  change allTriangleDescentsCheck (ofSix (0) (3) (-1) (1) (2) (1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable13 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 13).word) (BoundedLStarData.q179.node 13) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [3,0]) (ofSix (0) (2) (1) (-3) (2) (-1))
  rw [q179_prefix13]
  intro u v; rfl

theorem q179_cyclic13 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 13) := by decide +kernel

theorem q179_edge13_0 :
    EdgeChecks BoundedLStarData.q179 13 0 ((BoundedLStarData.q179.core 13).edges 0) := by decide +kernel

theorem q179_edge13_1 :
    EdgeChecks BoundedLStarData.q179 13 1 ((BoundedLStarData.q179.core 13).edges 1) := by decide +kernel

theorem q179_edge13_2 :
    EdgeChecks BoundedLStarData.q179 13 2 ((BoundedLStarData.q179.core 13).edges 2) := by decide +kernel

theorem q179_edge13_3 :
    EdgeChecks BoundedLStarData.q179 13 3 ((BoundedLStarData.q179.core 13).edges 3) := by decide +kernel

theorem q179_triangles13 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 13) = true := by decide +kernel

theorem q179_descent13 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 13) = true := by
  change allTriangleDescentsCheck (ofSix (0) (2) (1) (-3) (2) (-1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable14 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 14).word) (BoundedLStarData.q179.node 14) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [3,1]) (ofSix (0) (-2) (-1) (3) (-2) (5))
  rw [q179_prefix14]
  intro u v; rfl

theorem q179_cyclic14 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 14) := by decide +kernel

theorem q179_edge14_0 :
    EdgeChecks BoundedLStarData.q179 14 0 ((BoundedLStarData.q179.core 14).edges 0) := by decide +kernel

theorem q179_edge14_1 :
    EdgeChecks BoundedLStarData.q179 14 1 ((BoundedLStarData.q179.core 14).edges 1) := by decide +kernel

theorem q179_edge14_2 :
    EdgeChecks BoundedLStarData.q179 14 2 ((BoundedLStarData.q179.core 14).edges 2) := by decide +kernel

theorem q179_edge14_3 :
    EdgeChecks BoundedLStarData.q179 14 3 ((BoundedLStarData.q179.core 14).edges 3) := by decide +kernel

theorem q179_triangles14 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 14) = true := by decide +kernel

theorem q179_descent14 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 14) = true := by
  change allTriangleDescentsCheck (ofSix (0) (-2) (-1) (3) (-2) (5)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable15 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 15).word) (BoundedLStarData.q179.node 15) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [3,2]) (ofSix (0) (2) (-3) (3) (-1) (1))
  rw [q179_prefix15]
  intro u v; rfl

theorem q179_cyclic15 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 15) := by decide +kernel

theorem q179_edge15_0 :
    EdgeChecks BoundedLStarData.q179 15 0 ((BoundedLStarData.q179.core 15).edges 0) := by decide +kernel

theorem q179_edge15_1 :
    EdgeChecks BoundedLStarData.q179 15 1 ((BoundedLStarData.q179.core 15).edges 1) := by decide +kernel

theorem q179_edge15_2 :
    EdgeChecks BoundedLStarData.q179 15 2 ((BoundedLStarData.q179.core 15).edges 2) := by decide +kernel

theorem q179_edge15_3 :
    EdgeChecks BoundedLStarData.q179 15 3 ((BoundedLStarData.q179.core 15).edges 3) := by decide +kernel

theorem q179_triangles15 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 15) = true := by decide +kernel

theorem q179_descent15 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 15) = true := by
  change allTriangleDescentsCheck (ofSix (0) (2) (-3) (3) (-1) (1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

end QuiverProofs.BoundedLStarChecks
