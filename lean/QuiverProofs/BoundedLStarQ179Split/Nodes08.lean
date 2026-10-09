import QuiverProofs.BoundedLStarQ179Split.Prefix11
namespace QuiverProofs.BoundedLStarChecks
open LStar CertificateSearch
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 4096

theorem q179_reachable32 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 32).word) (BoundedLStarData.q179.node 32) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [0,3,2,0]) (ofSix (-2) (-1) (2) (1) (-7) (1))
  rw [q179_prefix32]
  intro u v; rfl

theorem q179_cyclic32 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 32) := by decide +kernel

theorem q179_edge32_0 :
    EdgeChecks BoundedLStarData.q179 32 0 ((BoundedLStarData.q179.core 32).edges 0) := by decide +kernel

theorem q179_edge32_1 :
    EdgeChecks BoundedLStarData.q179 32 1 ((BoundedLStarData.q179.core 32).edges 1) := by decide +kernel

theorem q179_edge32_2 :
    EdgeChecks BoundedLStarData.q179 32 2 ((BoundedLStarData.q179.core 32).edges 2) := by decide +kernel

theorem q179_edge32_3 :
    EdgeChecks BoundedLStarData.q179 32 3 ((BoundedLStarData.q179.core 32).edges 3) := by decide +kernel

theorem q179_triangles32 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 32) = true := by decide +kernel

theorem q179_descent32 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 32) = true := by
  change allTriangleDescentsCheck (ofSix (-2) (-1) (2) (1) (-7) (1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable33 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 33).word) (BoundedLStarData.q179.node 33) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [1,3,1,2]) (ofSix (4) (7) (-26) (1) (-1) (3))
  rw [q179_prefix33]
  intro u v; rfl

theorem q179_cyclic33 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 33) := by decide +kernel

theorem q179_edge33_0 :
    EdgeChecks BoundedLStarData.q179 33 0 ((BoundedLStarData.q179.core 33).edges 0) := by decide +kernel

theorem q179_edge33_1 :
    EdgeChecks BoundedLStarData.q179 33 1 ((BoundedLStarData.q179.core 33).edges 1) := by decide +kernel

theorem q179_edge33_2 :
    EdgeChecks BoundedLStarData.q179 33 2 ((BoundedLStarData.q179.core 33).edges 2) := by decide +kernel

theorem q179_edge33_3 :
    EdgeChecks BoundedLStarData.q179 33 3 ((BoundedLStarData.q179.core 33).edges 3) := by decide +kernel

theorem q179_triangles33 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 33) = true := by decide +kernel

theorem q179_descent33 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 33) = true := by
  change allTriangleDescentsCheck (ofSix (4) (7) (-26) (1) (-1) (3)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable34 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 34).word) (BoundedLStarData.q179.node 34) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [1,3,2,1]) (ofSix (11) (-4) (-26) (1) (2) (1))
  rw [q179_prefix34]
  intro u v; rfl

theorem q179_cyclic34 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 34) := by decide +kernel

theorem q179_edge34_0 :
    EdgeChecks BoundedLStarData.q179 34 0 ((BoundedLStarData.q179.core 34).edges 0) := by decide +kernel

theorem q179_edge34_1 :
    EdgeChecks BoundedLStarData.q179 34 1 ((BoundedLStarData.q179.core 34).edges 1) := by decide +kernel

theorem q179_edge34_2 :
    EdgeChecks BoundedLStarData.q179 34 2 ((BoundedLStarData.q179.core 34).edges 2) := by decide +kernel

theorem q179_edge34_3 :
    EdgeChecks BoundedLStarData.q179 34 3 ((BoundedLStarData.q179.core 34).edges 3) := by decide +kernel

theorem q179_triangles34 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 34) = true := by decide +kernel

theorem q179_descent34 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 34) = true := by
  change allTriangleDescentsCheck (ofSix (11) (-4) (-26) (1) (2) (1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable35 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 35).word) (BoundedLStarData.q179.node 35) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [2,0,1,0]) (ofSix (2) (-8) (1) (11) (0) (-9))
  rw [q179_prefix35]
  intro u v; rfl

theorem q179_cyclic35 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 35) := by decide +kernel

theorem q179_edge35_0 :
    EdgeChecks BoundedLStarData.q179 35 0 ((BoundedLStarData.q179.core 35).edges 0) := by decide +kernel

theorem q179_edge35_1 :
    EdgeChecks BoundedLStarData.q179 35 1 ((BoundedLStarData.q179.core 35).edges 1) := by decide +kernel

theorem q179_edge35_2 :
    EdgeChecks BoundedLStarData.q179 35 2 ((BoundedLStarData.q179.core 35).edges 2) := by decide +kernel

theorem q179_edge35_3 :
    EdgeChecks BoundedLStarData.q179 35 3 ((BoundedLStarData.q179.core 35).edges 3) := by decide +kernel

theorem q179_triangles35 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 35) = true := by decide +kernel

theorem q179_descent35 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 35) = true := by
  change allTriangleDescentsCheck (ofSix (2) (-8) (1) (11) (0) (-9)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

end QuiverProofs.BoundedLStarChecks
